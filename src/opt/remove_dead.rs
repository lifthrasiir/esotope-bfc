use std::collections::{BTreeMap, BTreeSet};

use crate::nodes::*;
use crate::opt::cleanup;

pub fn transform(node: &mut Node) {
    visit(node, &TailDead::All);
}

#[derive(Clone)]
enum TailDead {
    All,
    AllExcept(BTreeSet<i32>),
    Set(BTreeSet<i32>),
}

impl TailDead {
    fn none() -> Self {
        TailDead::Set(BTreeSet::new())
    }

    fn is_dead(&self, cell: i32) -> bool {
        match self {
            TailDead::All => true,
            TailDead::AllExcept(live) => !live.contains(&cell),
            TailDead::Set(dead) => dead.contains(&cell),
        }
    }

    fn has_any_dead(&self) -> bool {
        match self {
            TailDead::All | TailDead::AllExcept(_) => true,
            TailDead::Set(dead) => !dead.is_empty(),
        }
    }

    fn is_all_dead(&self) -> bool {
        matches!(self, TailDead::All)
    }

    fn mark_live(&mut self, cell: i32) {
        match self {
            TailDead::All => {
                *self = TailDead::AllExcept(BTreeSet::from([cell]));
            }
            TailDead::AllExcept(live) => {
                live.insert(cell);
            }
            TailDead::Set(dead) => {
                dead.remove(&cell);
            }
        }
    }

    fn mark_dead(&mut self, cell: i32) {
        match self {
            TailDead::All => {}
            TailDead::AllExcept(live) => {
                live.remove(&cell);
            }
            TailDead::Set(dead) => {
                dead.insert(cell);
            }
        }
    }

    fn reset(&mut self) {
        *self = TailDead::none();
    }

    fn retain_disjoint(&mut self, modulus: i32, residue: i32) {
        match self {
            TailDead::All | TailDead::AllExcept(_) => {
                *self = TailDead::none();
            }
            TailDead::Set(dead) => {
                dead.retain(|cell| cell.rem_euclid(modulus) != residue);
            }
        }
    }

    fn shift(&self, offset: i32) -> TailDead {
        if offset == 0 {
            return self.clone();
        }
        match self {
            TailDead::All => TailDead::All,
            TailDead::AllExcept(live) => {
                TailDead::AllExcept(live.iter().map(|c| c + offset).collect())
            }
            TailDead::Set(dead) => TailDead::Set(dead.iter().map(|c| c + offset).collect()),
        }
    }
}

fn visit(node: &mut Node, parent_tail: &TailDead) {
    let is_program = matches!(node, Node::Program { .. });
    let block_dead = if is_program {
        TailDead::All
    } else {
        parent_tail.clone()
    };

    if let Some(children) = node.children_mut() {
        let child_tails = compute_child_tails(children, &block_dead);
        let no_dead = TailDead::none();

        for i in 0..children.len() {
            let propagate = child_tails[i].has_any_dead()
                && matches!(
                    &children[i],
                    Node::If { children: kids, .. } if stride(kids) == Some(0)
                );
            let child_dead = if propagate { &child_tails[i] } else { &no_dead };
            visit(&mut children[i], child_dead);
        }

        remove_dead_pass(children, &block_dead);
    }
}

fn seek_congruence_for_node(node: &Node) -> Option<(i32, i32)> {
    match node {
        Node::SeekMemory { stride, target, .. } => {
            let abs_s = stride.abs();
            if abs_s >= 2 {
                Some((abs_s, *target))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn invalidate_for_unknown_refs(
    unusedcells: &mut BTreeMap<i32, usize>,
    unusednodes: &mut BTreeSet<usize>,
    modulus: Option<i32>,
    base: i32,
) {
    match modulus {
        Some(m) if m >= 2 => {
            let residue = base.rem_euclid(m);
            let to_remove: Vec<i32> = unusedcells
                .keys()
                .filter(|&&cell| cell.rem_euclid(m) == residue)
                .copied()
                .collect();
            for cell in to_remove {
                if let Some(idx) = unusedcells.remove(&cell) {
                    unusednodes.remove(&idx);
                }
            }
        }
        _ => {
            unusedcells.clear();
            unusednodes.clear();
        }
    }
}

fn compute_child_tails(children: &[Node], block_dead: &TailDead) -> Vec<TailDead> {
    let n = children.len();
    if n == 0 {
        return vec![];
    }

    let mut cum = vec![0i32; n + 1];
    let mut barriers = vec![false; n];
    for i in 0..n {
        match children[i].offsets() {
            Some(o) => cum[i + 1] = cum[i] + o,
            None => {
                cum[i + 1] = cum[i];
                barriers[i] = true;
            }
        }
    }

    let mut dead = block_dead.shift(cum[n]);
    let mut result = vec![TailDead::none(); n];

    for i in (0..n).rev() {
        if barriers[i] {
            result[i] = dead.shift(-cum[i]);
            if let Some((modulus, target)) = seek_congruence_for_node(&children[i]) {
                let residue = (cum[i] + target).rem_euclid(modulus);
                dead.retain_disjoint(modulus, residue);
            } else {
                dead.reset();
            }
            continue;
        }

        result[i] = dead.shift(-cum[i]);

        let reads = children[i].prereferences().unsure;
        let writes = children[i].preupdates().sure;

        if reads.contains(&None) || writes.contains(&None) {
            if let Some((modulus, target)) = seek_congruence_for_node(&children[i]) {
                let residue = (cum[i] + target).rem_euclid(modulus);
                dead.retain_disjoint(modulus, residue);
            } else {
                dead.reset();
            }
        } else {
            for u in writes.iter().flatten() {
                dead.mark_dead(*u + cum[i]);
            }
            for r in reads.iter().flatten() {
                dead.mark_live(*r + cum[i]);
            }
        }
    }

    result
}

fn remove_dead_pass(children: &mut Vec<Node>, tail_dead: &TailDead) {
    let mut unusedcells: BTreeMap<i32, usize> = BTreeMap::new();
    let mut unusednodes: BTreeSet<usize> = BTreeSet::new();
    let mut unusedmoves: Vec<usize> = Vec::new();

    let mut offsets: i32 = 0;

    for i in 0..children.len() {
        let seek_cong = seek_congruence_for_node(&children[i]);

        if let Some(o) = children[i].offsets() {
            offsets += o;
        } else {
            invalidate_for_unknown_refs(
                &mut unusedcells,
                &mut unusednodes,
                seek_cong.map(|(m, _)| m),
                offsets + seek_cong.map_or(0, |(_, t)| t),
            );
        }

        let pure = children[i].is_pure() && children[i].returns();
        if pure {
            unusedmoves.push(i);
        }

        let irefs = children[i].postreferences().unsure;
        let iupdates = children[i].postupdates().sure;
        let removable = pure && children[i].offsets() == Some(0);

        if !irefs.is_empty() || !iupdates.is_empty() {
            unusedmoves.clear();
        }

        if irefs.contains(&None) {
            invalidate_for_unknown_refs(
                &mut unusedcells,
                &mut unusednodes,
                seek_cong.map(|(m, _)| m),
                offsets + seek_cong.map_or(0, |(_, t)| t),
            );
        } else {
            for j in irefs.iter().flatten() {
                let j = j + offsets;
                if let Some(old_idx) = unusedcells.remove(&j) {
                    unusednodes.remove(&old_idx);
                }
            }
        }

        for &j in iupdates.iter().flatten() {
            let j = j + offsets;
            if let Some(&old_i) = unusedcells.get(&j) {
                if unusednodes.remove(&old_i) {
                    children[old_i] = Node::Nop;
                }
            }
            if removable {
                unusedcells.insert(j, i);
                unusednodes.insert(i);
            }
        }
    }

    if tail_dead.is_all_dead() {
        for i in &unusednodes {
            children[*i] = Node::Nop;
        }
        for i in &unusedmoves {
            children[*i] = Node::Nop;
        }
    } else if tail_dead.has_any_dead() {
        for (&cell, &idx) in &unusedcells {
            if tail_dead.is_dead(cell) && unusednodes.contains(&idx) {
                children[idx] = Node::Nop;
            }
        }
    }

    cleanup::cleanup(children);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cond::*;
    use crate::expr::*;

    fn run_remove_dead(nodes: Vec<Node>) -> Vec<Node> {
        let mut prog = Node::Program { children: nodes };
        transform(&mut prog);
        match prog {
            Node::Program { children } => children,
            _ => panic!("expected Program"),
        }
    }

    #[test]
    fn dead_store_at_program_end() {
        let nodes = vec![Node::SetMemory {
            offset: 0,
            value: Expr::Int(5),
        }];
        let result = run_remove_dead(nodes);
        assert!(result.is_empty(), "trailing dead store should be removed");
    }

    #[test]
    fn dead_store_overwritten() {
        let nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(10),
            },
            Node::Output { expr: Expr::mem(0) },
        ];
        let result = run_remove_dead(nodes);
        assert_eq!(result.len(), 2);
        assert!(matches!(
            &result[0],
            Node::SetMemory {
                value: Expr::Int(10),
                ..
            }
        ));
    }

    #[test]
    fn dead_store_inside_if_removed_when_overwritten_after() {
        // If(cond) { p[0] = 5 }; p[0] = 10; Output(p[0])
        // The p[0] = 5 inside If is dead because p[0] is overwritten after
        let nodes = vec![
            Node::Input { offset: 1 },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(5),
                }],
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(10),
            },
            Node::Output { expr: Expr::mem(0) },
        ];
        let result = run_remove_dead(nodes);
        // The If should become empty/nop and be removed
        assert!(
            !result.iter().any(|n| matches!(n, Node::If { .. })),
            "If with dead store should be eliminated: {:?}",
            result
        );
    }

    #[test]
    fn live_store_inside_if_preserved() {
        // If(cond) { p[0] = 5 }; Output(p[0])
        // The p[0] = 5 is NOT dead because p[0] is read after
        let nodes = vec![
            Node::Input { offset: 1 },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(5),
                }],
            },
            Node::Output { expr: Expr::mem(0) },
        ];
        let result = run_remove_dead(nodes);
        assert!(
            result.iter().any(|n| matches!(n, Node::If { .. })),
            "If with live store should be preserved: {:?}",
            result
        );
    }

    #[test]
    fn dead_store_inside_if_at_program_end() {
        // If(cond) { p[0] = 5 } at program end
        // p[0] = 5 is dead because it's the end of the program
        let nodes = vec![
            Node::Input { offset: 1 },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(5),
                }],
            },
        ];
        let result = run_remove_dead(nodes);
        assert!(
            !result.iter().any(|n| matches!(n, Node::If { .. })),
            "If with dead store at program end should be eliminated: {:?}",
            result
        );
    }

    #[test]
    fn nested_if_dead_store_propagation() {
        // If(c1) { If(c2) { p[0] = 5 } }; p[0] = 10; Output(p[0])
        let nodes = vec![
            Node::Input { offset: 1 },
            Node::Input { offset: 2 },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::If {
                    cond: Cond::MemNotEqual(2, 0),
                    children: vec![Node::SetMemory {
                        offset: 0,
                        value: Expr::Int(5),
                    }],
                }],
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(10),
            },
            Node::Output { expr: Expr::mem(0) },
        ];
        let result = run_remove_dead(nodes);
        assert!(
            !result.iter().any(|n| matches!(n, Node::If { .. })),
            "nested If with dead store should be eliminated: {:?}",
            result
        );
    }

    #[test]
    fn partial_dead_store_in_if() {
        // If(cond) { p[0] = 5; p[1] = 10 }; p[0] = 20; Output(p[1])
        // p[0] = 5 is dead (overwritten), p[1] = 10 is live (read after)
        let nodes = vec![
            Node::Input { offset: 2 },
            Node::If {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![
                    Node::SetMemory {
                        offset: 0,
                        value: Expr::Int(5),
                    },
                    Node::SetMemory {
                        offset: 1,
                        value: Expr::Int(10),
                    },
                ],
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(20),
            },
            Node::Output { expr: Expr::mem(1) },
        ];
        let result = run_remove_dead(nodes);
        // If should still exist (has live store for p[1])
        assert!(
            result.iter().any(|n| matches!(n, Node::If { .. })),
            "If with partial live store should be preserved: {:?}",
            result
        );
        // Check that the If body only has p[1] = 10
        for n in &result {
            if let Node::If { children, .. } = n {
                assert_eq!(children.len(), 1);
                assert!(
                    matches!(&children[0], Node::SetMemory { offset: 1, .. }),
                    "only p[1] store should remain in If: {:?}",
                    children
                );
            }
        }
    }

    #[test]
    fn dead_store_with_pointer_offset() {
        // MovePointer(3); If(cond) { p[0] = 5 }; p[0] = 10; Output(p[0])
        // At offset 3: p[0] = p[3] in absolute. The dead store should still be detected.
        let nodes = vec![
            Node::Input { offset: 4 },
            Node::MovePointer { offset: 3 },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(5),
                }],
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(10),
            },
            Node::Output { expr: Expr::mem(0) },
        ];
        let result = run_remove_dead(nodes);
        assert!(
            !result.iter().any(|n| matches!(n, Node::If { .. })),
            "If with dead store after pointer offset should be eliminated: {:?}",
            result
        );
    }

    #[test]
    fn while_body_not_propagated() {
        // While loops should NOT get dead info propagated (body may loop)
        let nodes = vec![
            Node::Input { offset: 0 },
            Node::While {
                cond: Cond::MemNotEqual(0, 0),
                children: vec![
                    Node::SetMemory {
                        offset: 1,
                        value: Expr::Int(5),
                    },
                    Node::SetMemory {
                        offset: 0,
                        value: Expr::mem(0) + Expr::Int(-1),
                    },
                ],
            },
        ];
        let result = run_remove_dead(nodes);
        // While should still exist with both stores
        if let Some(Node::While { children, .. }) =
            result.iter().find(|n| matches!(n, Node::While { .. }))
        {
            assert!(
                children
                    .iter()
                    .any(|n| matches!(n, Node::SetMemory { offset: 1, .. })),
                "While body store should be preserved: {:?}",
                children
            );
        }
    }

    #[test]
    fn if_with_output_not_removed() {
        // If(cond) { Output(p[0]) }; p[0] = 10
        // The If has side effects (Output) so should not be removed
        let nodes = vec![
            Node::Input { offset: 1 },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::Output { expr: Expr::mem(0) }],
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(10),
            },
        ];
        let result = run_remove_dead(nodes);
        assert!(
            result.iter().any(|n| matches!(n, Node::If { .. })),
            "If with Output should be preserved: {:?}",
            result
        );
    }

    #[test]
    fn seek_stride3_preserves_disjoint_dead_store() {
        // p[1] = 5; SeekMemory(stride=3); (end of program)
        // SeekMemory(stride=3) reads cells at offsets 0, 3, 6, ...
        // p[1] is in lane 1 mod 3, disjoint from lane 0 mod 3
        // So p[1] = 5 should still be recognized as dead at program end
        let nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::Int(5),
            },
            Node::SeekMemory {
                target: 0,
                stride: 3,
                value: 0,
            },
        ];
        let result = run_remove_dead(nodes);
        assert!(
            !result
                .iter()
                .any(|n| matches!(n, Node::SetMemory { offset: 1, .. })),
            "dead store in disjoint lane should be removed after SeekMemory: {:?}",
            result
        );
    }

    #[test]
    fn seek_stride3_preserves_same_lane_store() {
        // p[0] = 5; SeekMemory(stride=3, target=0); Output(p[0])
        // SeekMemory reads cells at offsets 0, 3, 6, ...
        // p[0] is in lane 0 mod 3, same as the seek lane
        // So p[0] = 5 must be preserved (it's read by SeekMemory)
        let nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::SeekMemory {
                target: 0,
                stride: 3,
                value: 0,
            },
            Node::Output { expr: Expr::mem(0) },
        ];
        let result = run_remove_dead(nodes);
        assert!(
            result
                .iter()
                .any(|n| matches!(n, Node::SetMemory { offset: 0, .. })),
            "store in same lane as SeekMemory should be preserved: {:?}",
            result
        );
    }

    #[test]
    fn seek_stride1_clears_all() {
        // SeekMemory(stride=1) can reach any cell, so all tracking must be cleared
        // p[1] = 5; SeekMemory(stride=1); (but p[1] might be read by seek)
        let nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::Int(5),
            },
            Node::SeekMemory {
                target: 0,
                stride: 1,
                value: 0,
            },
            Node::Output { expr: Expr::mem(0) },
        ];
        let result = run_remove_dead(nodes);
        assert!(
            result
                .iter()
                .any(|n| matches!(n, Node::SetMemory { offset: 1, .. })),
            "store should be preserved with stride=1 (no congruence info): {:?}",
            result
        );
    }

    #[test]
    fn seek_stride3_dead_at_program_end_disjoint_lanes() {
        // p[0] = 1; p[1] = 2; p[2] = 3; SeekMemory(stride=3); (program end)
        // Seek reads lane 0 mod 3. After seek, all stores are dead (program end).
        // But the seek itself reads lane 0 cells, making p[0] = 1 live.
        // p[1] and p[2] are in different lanes so remain dead.
        let nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(1),
            },
            Node::SetMemory {
                offset: 1,
                value: Expr::Int(2),
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::Int(3),
            },
            Node::SeekMemory {
                target: 0,
                stride: 3,
                value: 0,
            },
        ];
        let result = run_remove_dead(nodes);
        let has_offset_1 = result
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 1, .. }));
        let has_offset_2 = result
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        assert!(
            !has_offset_1,
            "p[1] (lane 1) should be dead after stride-3 seek at program end: {:?}",
            result
        );
        assert!(
            !has_offset_2,
            "p[2] (lane 2) should be dead after stride-3 seek at program end: {:?}",
            result
        );
    }

    #[test]
    fn dynamic_pointer_fallback_preserves_behavior() {
        // A While with non-zero stride is also a barrier, but not a SeekMemory
        // All tracking should be cleared (fallback)
        let nodes = vec![
            Node::SetMemory {
                offset: 1,
                value: Expr::Int(5),
            },
            Node::Input { offset: 0 },
            Node::While {
                cond: Cond::MemNotEqual(0, 0),
                children: vec![Node::MovePointer { offset: 1 }],
            },
            Node::Output { expr: Expr::mem(1) },
        ];
        let result = run_remove_dead(nodes);
        assert!(
            result
                .iter()
                .any(|n| matches!(n, Node::SetMemory { offset: 1, .. })),
            "store should be preserved with dynamic pointer (non-SeekMemory): {:?}",
            result
        );
    }
}
