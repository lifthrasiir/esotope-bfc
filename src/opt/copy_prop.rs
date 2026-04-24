use std::collections::BTreeMap;

use crate::expr::*;
use crate::nodes::*;
use crate::opt::cleanup;

#[derive(Clone)]
struct CopyState {
    values: BTreeMap<i32, Expr>,
    leaders: BTreeMap<Expr, i32>,
}

impl CopyState {
    fn new() -> Self {
        CopyState {
            values: BTreeMap::new(),
            leaders: BTreeMap::new(),
        }
    }

    fn clear(&mut self) {
        self.values.clear();
        self.leaders.clear();
    }

    fn canonicalize(&self, expr: &Expr) -> Expr {
        expr.with_memory(&self.values)
    }

    fn simplify(&self, canonical: &Expr, offset: i32) -> Expr {
        if canonical.is_simple() || mem_offset(canonical).is_some() {
            canonical.clone()
        } else if let Some(&leader) = self.leaders.get(canonical) {
            if leader != offset {
                Expr::mem(leader)
            } else {
                canonical.clone()
            }
        } else {
            canonical.clone()
        }
    }

    fn simplify_output(&self, canonical: &Expr) -> Expr {
        if canonical.is_simple() || mem_offset(canonical).is_some() {
            canonical.clone()
        } else if let Some(&leader) = self.leaders.get(canonical) {
            Expr::mem(leader)
        } else {
            canonical.clone()
        }
    }

    fn invalidate_cell(&mut self, offset: i32) {
        if let Some(old_val) = self.values.remove(&offset) {
            if let Some(leader_offset) = self.leaders.get(&old_val) {
                if *leader_offset == offset {
                    self.leaders.remove(&old_val);
                }
            }
        }

        let cell_ref = Expr::Int(offset);
        self.leaders
            .retain(|expr, _| !expr.references().contains(&cell_ref));
        self.values
            .retain(|_, v| !v.references().contains(&cell_ref));
    }

    fn invalidate_body_updates(&mut self, body: &[Node]) {
        if stride(body) != Some(0) {
            self.clear();
            return;
        }

        for node in body {
            let updates = node.preupdates();
            if updates.unsure.contains(&None) {
                self.clear();
                return;
            }
            for off in updates.unsure.iter().flatten() {
                self.invalidate_cell(*off);
            }
        }
    }
}

fn merge_states(a: &CopyState, b: &CopyState) -> CopyState {
    let mut values = BTreeMap::new();
    let mut leaders = BTreeMap::new();

    for (offset, val_a) in &a.values {
        if let Some(val_b) = b.values.get(offset) {
            if val_a == val_b {
                values.insert(*offset, val_a.clone());
            }
        }
    }

    for (expr, &leader_a) in &a.leaders {
        if let Some(&leader_b) = b.leaders.get(expr) {
            if leader_a == leader_b
                && (values.get(&leader_a) == Some(expr)
                    || a.values.get(&leader_a) == Some(expr)
                        && b.values.get(&leader_a) == Some(expr))
            {
                leaders.insert(expr.clone(), leader_a);
            }
        }
    }

    CopyState { values, leaders }
}

pub fn transform(node: &mut Node) {
    visit(node);
}

fn visit(node: &mut Node) {
    if let Some(children) = node.children_mut() {
        for child in children.iter_mut() {
            visit(child);
        }
        let _ = copy_prop_pass_with_state(children, &CopyState::new());
    }
}

fn mem_offset(expr: &Expr) -> Option<i32> {
    if let Expr::Reference(inner) = expr {
        inner.to_int()
    } else {
        None
    }
}

fn copy_prop_pass_with_state(children: &mut Vec<Node>, initial_state: &CopyState) -> CopyState {
    let mut state = initial_state.clone();

    for i in 0..children.len() {
        match &children[i] {
            Node::SetMemory { offset, value } => {
                let offset = *offset;
                let canonical = state.canonicalize(value);

                state.invalidate_cell(offset);

                if canonical == Expr::mem(offset) {
                    children[i] = Node::Nop;
                    continue;
                }

                let simplified = state.simplify(&canonical, offset);

                children[i] = Node::SetMemory {
                    offset,
                    value: simplified.clone(),
                };

                state.values.insert(offset, simplified.clone());
                if !simplified.is_simple() && mem_offset(&simplified).is_none() {
                    state.leaders.entry(canonical).or_insert(offset);
                }
            }

            Node::Output { expr } => {
                let canonical = state.canonicalize(expr);
                let simplified = state.simplify_output(&canonical);
                children[i] = Node::Output { expr: simplified };
            }

            Node::Input { offset } => {
                let offset = *offset;
                state.invalidate_cell(offset);
            }

            Node::Nop | Node::OutputConst { .. } | Node::MovePointer { .. } => {}

            Node::If { cond, .. } => {
                if cond.is_never() {
                    // dead branch, state unchanged
                } else if cond.is_always() {
                    let mut node = std::mem::replace(&mut children[i], Node::Nop);
                    if let Node::If {
                        children: ref mut body,
                        ..
                    } = &mut node
                    {
                        state = copy_prop_pass_with_state(body, &state);
                    }
                    children[i] = node;
                } else {
                    let mut node = std::mem::replace(&mut children[i], Node::Nop);
                    let true_state = if let Node::If { children: body, .. } = &mut node {
                        copy_prop_pass_with_state(body, &state)
                    } else {
                        state.clone()
                    };
                    children[i] = node;

                    state = merge_states(&true_state, &state);
                }
            }

            Node::Repeat {
                count,
                children: body,
            } => {
                let canonical = state.canonicalize(count);
                children[i] = Node::Repeat {
                    count: canonical,
                    children: body.clone(),
                };
                if let Node::Repeat { children: body, .. } = &mut children[i] {
                    let _ = copy_prop_pass_with_state(body, &state);
                    state.invalidate_body_updates(body);
                }
            }

            Node::While { .. } => {
                if let Node::While { children: body, .. } = &mut children[i] {
                    let _ = copy_prop_pass_with_state(body, &state);
                    state.invalidate_body_updates(body);
                }
            }

            _ => {
                state.clear();
            }
        }
    }

    cleanup::cleanup(children);
    state
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cond::*;

    fn run_copy_prop(nodes: &mut Vec<Node>) {
        let _ = copy_prop_pass_with_state(nodes, &CopyState::new());
    }

    #[test]
    fn transitive_copy_normalized() {
        // p[1] = p[0]; p[2] = p[1]  =>  p[1] = p[0]; p[2] = p[0]
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        assert_eq!(nodes.len(), 2);
        if let Node::SetMemory { value, .. } = &nodes[1] {
            assert_eq!(*value, Expr::mem(0));
        } else {
            panic!("expected SetMemory");
        }
    }

    #[test]
    fn self_copy_removed() {
        // p[1] = p[0]; p[0] = p[1]  =>  p[1] = p[0]  (second becomes nop)
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        assert_eq!(nodes.len(), 1);
        if let Node::SetMemory { offset: 1, value } = &nodes[0] {
            assert_eq!(*value, Expr::mem(0));
        } else {
            panic!("expected SetMemory at offset 1, got {:?}", nodes[0]);
        }
    }

    #[test]
    fn output_canonicalized() {
        // p[1] = p[0]; output(p[1])  =>  p[1] = p[0]; output(p[0])
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::Output { expr: Expr::mem(1) },
        ];
        run_copy_prop(&mut nodes);
        if let Node::Output { expr } = &nodes[1] {
            assert_eq!(*expr, Expr::mem(0));
        } else {
            panic!("expected Output");
        }
    }

    #[test]
    fn input_invalidates_alias() {
        // p[1] = p[0]; input(p[0]); p[2] = p[1]
        // After input(p[0]), the alias p[1] == p[0] is invalidated.
        // p[2] = p[1] should stay as-is.
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::Input { offset: 0 },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        if let Node::SetMemory { value, .. } = &nodes[2] {
            assert_eq!(*value, Expr::mem(1));
        } else {
            panic!("expected SetMemory");
        }
    }

    #[test]
    fn while_unrelated_control_flow_preserves_state() {
        // p[1] = p[0]; while(...) { p[3] = 0 }; p[2] = p[1]
        // The loop body does not touch p[0] or p[1], so the alias can survive.
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::While {
                cond: Cond::MemNotEqual(3, 0),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::Int(0),
                }],
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let last = nodes.last().unwrap();
        if let Node::SetMemory { offset: 2, value } = last {
            assert_eq!(*value, Expr::mem(0));
        } else {
            panic!("expected SetMemory at offset 2, got {:?}", last);
        }
    }

    #[test]
    fn linear_expr_canonicalized() {
        // p[1] = p[0]; p[2] = p[1] + 3  =>  p[2] = p[0] + 3
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(1) + Expr::Int(3),
            },
        ];
        run_copy_prop(&mut nodes);
        if let Node::SetMemory { value, .. } = &nodes[1] {
            assert_eq!(*value, Expr::mem(0) + Expr::Int(3));
        } else {
            panic!("expected SetMemory");
        }
    }

    #[test]
    fn overwrite_invalidates_old_alias() {
        // p[1] = p[0]; p[1] = 5; p[2] = p[1]  =>  p[2] = 5
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::SetMemory {
                offset: 1,
                value: Expr::Int(5),
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let last = nodes
            .iter()
            .rev()
            .find(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        if let Some(Node::SetMemory { value, .. }) = last {
            assert_eq!(*value, Expr::Int(5));
        } else {
            panic!("expected SetMemory at offset 2");
        }
    }

    #[test]
    fn copy_distribute_pattern() {
        // p[1] = p[0]; p[2] = p[0]; p[3] = p[1]
        // => p[1] = p[0]; p[2] = p[0]; p[3] = p[0]
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(0),
            },
            Node::SetMemory {
                offset: 3,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        if let Node::SetMemory { value, .. } = &nodes[2] {
            assert_eq!(*value, Expr::mem(0));
        } else {
            panic!("expected SetMemory");
        }
    }

    #[test]
    fn value_numbering_reuses_leader() {
        // p[1] = p[0] + 3; p[2] = p[0] + 3  =>  p[2] = p[1]
        let expr = Expr::mem(0) + Expr::Int(3);
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: expr.clone(),
            },
            Node::SetMemory {
                offset: 2,
                value: expr,
            },
        ];
        run_copy_prop(&mut nodes);
        if let Node::SetMemory { value, .. } = &nodes[1] {
            assert_eq!(*value, Expr::mem(1));
        } else {
            panic!("expected SetMemory");
        }
    }

    // --- Branch-aware copy propagation tests ---

    #[test]
    fn if_unrelated_preserves_alias() {
        // p[1] = p[0]; If(p[2] != 0) { p[3] = 5 }; p[4] = p[1]
        // The If doesn't touch p[0] or p[1], so alias should survive.
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::Int(5),
                }],
            },
            Node::SetMemory {
                offset: 4,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let set4 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 4, .. }));
        if let Some(Node::SetMemory { value, .. }) = set4 {
            assert_eq!(
                *value,
                Expr::mem(0),
                "alias p[1]=p[0] should survive unrelated If"
            );
        } else {
            panic!("expected SetMemory at offset 4");
        }
    }

    #[test]
    fn if_both_branches_same_copy_survives() {
        // p[1] = p[0]; If(p[2] != 0) { p[1] = p[0] }; p[3] = p[1]
        // Both branches have p[1] = p[0], so alias survives.
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(0),
                }],
            },
            Node::SetMemory {
                offset: 3,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let set3 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 3, .. }));
        if let Some(Node::SetMemory { value, .. }) = set3 {
            assert_eq!(*value, Expr::mem(0), "both branches set p[1]=p[0]");
        } else {
            panic!("expected SetMemory at offset 3");
        }
    }

    #[test]
    fn if_one_branch_overwrites_loses_alias() {
        // p[1] = p[0]; If(p[2] != 0) { p[1] = 5 }; p[3] = p[1]
        // True branch: p[1] = 5. False branch: p[1] = p[0].
        // Merge should lose the alias since they disagree.
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::SetMemory {
                    offset: 1,
                    value: Expr::Int(5),
                }],
            },
            Node::SetMemory {
                offset: 3,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let set3 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 3, .. }));
        if let Some(Node::SetMemory { value, .. }) = set3 {
            assert_eq!(
                *value,
                Expr::mem(1),
                "alias should be lost after conflicting branch"
            );
        } else {
            panic!("expected SetMemory at offset 3");
        }
    }

    #[test]
    fn if_body_invalidates_reference_loses_alias() {
        // p[1] = p[0]; If(p[2] != 0) { input(p[0]) }; p[3] = p[1]
        // True branch modifies p[0], which p[1]'s value depends on.
        // Merge should lose the alias.
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::Input { offset: 0 }],
            },
            Node::SetMemory {
                offset: 3,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let set3 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 3, .. }));
        if let Some(Node::SetMemory { value, .. }) = set3 {
            assert_eq!(
                *value,
                Expr::mem(1),
                "alias should be lost when referenced cell is modified"
            );
        } else {
            panic!("expected SetMemory at offset 3");
        }
    }

    #[test]
    fn if_dead_branch_preserves_state() {
        // p[1] = p[0]; If(Never) { p[1] = 5 }; p[2] = p[1]
        // Dead branch shouldn't affect state.
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::Never,
                children: vec![Node::SetMemory {
                    offset: 1,
                    value: Expr::Int(5),
                }],
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let set2 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        if let Some(Node::SetMemory { value, .. }) = set2 {
            assert_eq!(*value, Expr::mem(0), "dead branch should not affect state");
        } else {
            panic!("expected SetMemory at offset 2");
        }
    }

    #[test]
    fn if_always_inlines_state() {
        // p[1] = p[0]; If(Always) { p[1] = p[3] }; p[2] = p[1]
        // Always branch means only the body path is taken.
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::Always,
                children: vec![Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(3),
                }],
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let set2 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        if let Some(Node::SetMemory { value, .. }) = set2 {
            assert_eq!(*value, Expr::mem(3), "always branch should inline state");
        } else {
            panic!("expected SetMemory at offset 2");
        }
    }

    #[test]
    fn output_after_if_canonicalized() {
        // p[1] = p[0]; If(p[2] != 0) { p[3] = 5 }; Output(p[1])
        // Alias survives the unrelated If, so Output should use p[0].
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::Int(5),
                }],
            },
            Node::Output { expr: Expr::mem(1) },
        ];
        run_copy_prop(&mut nodes);
        let output = nodes.iter().find(|n| matches!(n, Node::Output { .. }));
        if let Some(Node::Output { expr }) = output {
            assert_eq!(
                *expr,
                Expr::mem(0),
                "Output should be canonicalized after unrelated If"
            );
        } else {
            panic!("expected Output");
        }
    }

    #[test]
    fn nested_if_preserves_alias() {
        // p[1] = p[0]; If(p[2]) { If(p[3]) { p[4] = 5 } }; p[5] = p[1]
        // Neither nested If touches p[0] or p[1].
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::If {
                    cond: Cond::MemNotEqual(3, 0),
                    children: vec![Node::SetMemory {
                        offset: 4,
                        value: Expr::Int(5),
                    }],
                }],
            },
            Node::SetMemory {
                offset: 5,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let set5 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 5, .. }));
        if let Some(Node::SetMemory { value, .. }) = set5 {
            assert_eq!(*value, Expr::mem(0), "alias should survive nested If");
        } else {
            panic!("expected SetMemory at offset 5");
        }
    }

    #[test]
    fn if_body_sees_outer_alias() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::mem(1),
                }],
            },
        ];
        run_copy_prop(&mut nodes);
        if let Some(Node::If { children, .. }) = nodes.iter().find(|n| matches!(n, Node::If { .. }))
        {
            let set3 = children
                .iter()
                .find(|n| matches!(n, Node::SetMemory { offset: 3, .. }));
            if let Some(Node::SetMemory { value, .. }) = set3 {
                assert_eq!(*value, Expr::mem(0));
            } else {
                panic!("expected SetMemory in if body");
            }
        } else {
            panic!("expected If node");
        }
    }

    #[test]
    fn repeat_body_sees_outer_alias_and_post_state_survives() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::Repeat {
                count: Expr::mem(2),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::mem(1),
                }],
            },
            Node::SetMemory {
                offset: 4,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);

        let repeat = nodes.iter().find_map(|n| match n {
            Node::Repeat { children, .. } => Some(children),
            _ => None,
        });
        let body = repeat.expect("expected repeat");
        assert!(body
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 3, value } if *value == Expr::mem(0))));

        let set4 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 4, .. }));
        if let Some(Node::SetMemory { value, .. }) = set4 {
            assert_eq!(*value, Expr::mem(0));
        } else {
            panic!("expected SetMemory at offset 4");
        }
    }

    #[test]
    fn while_unrelated_updates_preserve_alias_after_loop() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::While {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::Int(5),
                }],
            },
            Node::SetMemory {
                offset: 4,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let set4 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 4, .. }));
        if let Some(Node::SetMemory { value, .. }) = set4 {
            assert_eq!(*value, Expr::mem(0));
        } else {
            panic!("expected SetMemory at offset 4");
        }
    }

    #[test]
    fn while_modified_alias_is_invalidated_after_loop() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::While {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(5),
                }],
            },
            Node::SetMemory {
                offset: 4,
                value: Expr::mem(1),
            },
        ];
        run_copy_prop(&mut nodes);
        let set4 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 4, .. }));
        if let Some(Node::SetMemory { value, .. }) = set4 {
            assert_eq!(*value, Expr::mem(1));
        } else {
            panic!("expected SetMemory at offset 4");
        }
    }
}
