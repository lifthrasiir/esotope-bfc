use std::collections::BTreeMap;

use crate::expr::*;
use crate::nodes::*;
use crate::opt::cleanup;

pub fn transform(node: &mut Node) {
    visit(node);
}

fn visit(node: &mut Node) {
    if let Some(children) = node.children_mut() {
        for child in children.iter_mut() {
            visit(child);
        }
        copy_prop_pass(children);
    }
}

fn canonicalize(expr: &Expr, values: &BTreeMap<i32, Expr>) -> Expr {
    expr.with_memory(values)
}

fn mem_offset(expr: &Expr) -> Option<i32> {
    if let Expr::Reference(inner) = expr {
        inner.to_int()
    } else {
        None
    }
}

fn copy_prop_pass(children: &mut Vec<Node>) {
    let mut values: BTreeMap<i32, Expr> = BTreeMap::new();
    let mut leaders: BTreeMap<Expr, i32> = BTreeMap::new();

    for i in 0..children.len() {
        match &children[i] {
            Node::SetMemory { offset, value } => {
                let offset = *offset;
                let canonical = canonicalize(value, &values);

                invalidate_cell(offset, &mut values, &mut leaders);

                if canonical == Expr::mem(offset) {
                    children[i] = Node::Nop;
                    continue;
                }

                let simplified = if canonical.is_simple() || mem_offset(&canonical).is_some() {
                    canonical.clone()
                } else if let Some(&leader) = leaders.get(&canonical) {
                    if leader != offset {
                        Expr::mem(leader)
                    } else {
                        canonical.clone()
                    }
                } else {
                    canonical.clone()
                };

                children[i] = Node::SetMemory {
                    offset,
                    value: simplified.clone(),
                };

                values.insert(offset, simplified.clone());
                if !simplified.is_simple() && mem_offset(&simplified).is_none() {
                    leaders.entry(canonical).or_insert(offset);
                }
            }

            Node::Output { expr } => {
                let canonical = canonicalize(expr, &values);
                let simplified = if canonical.is_simple() || mem_offset(&canonical).is_some() {
                    canonical
                } else if let Some(&leader) = leaders.get(&canonical) {
                    Expr::mem(leader)
                } else {
                    canonical
                };
                children[i] = Node::Output { expr: simplified };
            }

            Node::Input { offset } => {
                let offset = *offset;
                invalidate_cell(offset, &mut values, &mut leaders);
            }

            Node::Nop | Node::OutputConst { .. } | Node::MovePointer { .. } => {}

            _ => {
                values.clear();
                leaders.clear();
            }
        }
    }

    cleanup::cleanup(children);
}

fn invalidate_cell(
    offset: i32,
    values: &mut BTreeMap<i32, Expr>,
    leaders: &mut BTreeMap<Expr, i32>,
) {
    if let Some(old_val) = values.remove(&offset) {
        if let Some(leader_offset) = leaders.get(&old_val) {
            if *leader_offset == offset {
                leaders.remove(&old_val);
            }
        }
    }

    let cell_ref = Expr::Int(offset);
    leaders.retain(|expr, _| !expr.references().contains(&cell_ref));
    values.retain(|_, v| !v.references().contains(&cell_ref));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cond::*;

    fn run_copy_prop(nodes: &mut Vec<Node>) {
        copy_prop_pass(nodes);
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
            Node::Output {
                expr: Expr::mem(1),
            },
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
    fn control_flow_flushes_state() {
        // p[1] = p[0]; while(...) { p[3] = 0 }; p[2] = p[1]
        // After control flow, state is flushed, so p[2] = p[1] stays
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
            assert_eq!(*value, Expr::mem(1));
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
}
