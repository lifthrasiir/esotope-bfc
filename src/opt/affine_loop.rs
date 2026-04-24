use std::collections::{BTreeMap, BTreeSet};

use crate::cond::*;
use crate::expr::*;
use crate::math::gcdex_i64;
use crate::nodes::*;
use crate::opt::cleanup;

#[derive(Clone, Debug, PartialEq, Eq)]
enum CellSummary {
    Add(Expr),
    Set(Expr),
}

pub fn transform(node: &mut Node, cellsize: u32) {
    visit(node, cellsize);
}

fn visit(node: &mut Node, cellsize: u32) {
    if let Some(children) = node.children_mut() {
        for child in children.iter_mut() {
            visit(child, cellsize);
        }
        affine_loop_pass(children, cellsize);
        affine_repeat_pass(children);
    }
}

fn summarize_body(kids: &[Node]) -> Option<BTreeMap<i32, i32>> {
    let mut deltas: BTreeMap<i32, i32> = BTreeMap::new();

    for inode in kids {
        match inode {
            Node::SetMemory { offset, value } => {
                let delta = value - &Expr::mem(*offset);
                let delta_val = delta.to_int()?;
                *deltas.entry(*offset).or_insert(0) += delta_val;
            }
            _ => return None,
        }
    }

    Some(deltas)
}

/// Symbolically execute the body and compute per-cell deltas as expressions.
/// Returns None if:
/// - any node is not SetMemory
/// - any delta references a cell that is modified in the body (not loop-invariant)
fn summarize_body_general(kids: &[Node]) -> Option<BTreeMap<i32, CellSummary>> {
    let mut env: BTreeMap<i32, Expr> = BTreeMap::new();
    let mut modified: BTreeSet<i32> = BTreeSet::new();

    for inode in kids {
        match inode {
            Node::SetMemory { offset, value } => {
                let resolved = value.with_memory(&env);
                env.insert(*offset, resolved);
                modified.insert(*offset);
            }
            _ => return None,
        }
    }

    let mut summaries: BTreeMap<i32, CellSummary> = BTreeMap::new();
    for (&offset, value) in &env {
        let delta = value - &Expr::mem(offset);

        if delta.to_int() == Some(0) {
            continue;
        }

        let delta_refs = delta.references();
        let delta_ok = delta_refs.iter().all(|r| match r.to_int() {
            Some(cell) if !modified.contains(&cell) => true,
            _ => false,
        });
        if delta_ok {
            summaries.insert(offset, CellSummary::Add(delta));
            continue;
        }

        let value_refs = value.references();
        let value_ok = value_refs.iter().all(|r| match r.to_int() {
            Some(cell) if !modified.contains(&cell) => true,
            _ => false,
        });
        if value_ok {
            summaries.insert(offset, CellSummary::Set(value.clone()));
            continue;
        }

        if modified.contains(&offset) {
            for r in &value_refs {
                match r.to_int() {
                    Some(cell) if cell == offset => return None,
                    _ => {}
                }
            }
        }

        return None;
    }

    Some(summaries)
}

fn affine_loop_pass(children: &mut Vec<Node>, cellsize: u32) {
    let overflow: i64 = 1i64 << cellsize;

    let mut i = 0;
    while i < children.len() {
        let (cond, kids) = match &children[i] {
            Node::While {
                cond,
                children: kids,
            } if cond.is_mem_not_equal() => (cond.clone(), kids.clone()),
            _ => {
                i += 1;
                continue;
            }
        };

        let target = cond.get_target().unwrap();
        let value = cond.get_value().unwrap();

        if stride(&kids) != Some(0) {
            i += 1;
            continue;
        }

        if !kids.iter().all(|k| k.is_pure()) {
            i += 1;
            continue;
        }

        // Try constant-delta summary first (fast path)
        if let Some(deltas) = summarize_body(&kids) {
            let control_delta = *deltas.get(&target).unwrap_or(&0);
            if control_delta == 0 {
                i += 1;
                continue;
            }

            let delta =
                ((i64::from(value) - i64::from(control_delta)) % overflow + overflow) % overflow;

            if delta == 0 {
                children[i] = Node::While {
                    cond: Cond::Always,
                    children: Vec::new(),
                };
                i += 1;
                continue;
            }

            let (u, _v, gcd) = gcdex_i64(delta, overflow);
            if gcd > i64::from(i32::MAX) {
                i += 1;
                continue;
            }
            let diff = Expr::mem(target) - Expr::Int(value);
            let count = Expr::Int((((u % overflow) + overflow) % overflow) as i32)
                * Expr::div(diff.clone(), Expr::Int(gcd as i32));

            let mut replacement = Vec::new();

            if gcd > 1 {
                replacement.push(Node::If {
                    cond: Cond::not_equal(Expr::modulo(diff, Expr::Int(gcd as i32)), 0),
                    children: vec![Node::While {
                        cond: Cond::Always,
                        children: Vec::new(),
                    }],
                });
            }

            for (&offset, &delta_val) in &deltas {
                if offset == target || delta_val == 0 {
                    continue;
                }
                replacement.push(Node::SetMemory {
                    offset,
                    value: Expr::mem(offset) + Expr::Int(delta_val) * count.clone(),
                });
            }

            replacement.push(Node::SetMemory {
                offset: target,
                value: Expr::Int(value),
            });

            children.splice(i..=i, replacement.clone());
            i += replacement.len();
            continue;
        }

        // Try general affine summary (handles non-constant deltas referencing invariant cells)
        if let Some(summaries) = summarize_body_general(&kids) {
            let control_delta = match summaries.get(&target) {
                Some(CellSummary::Add(d)) => match d.to_int() {
                    Some(v) => v,
                    None => {
                        i += 1;
                        continue;
                    }
                },
                Some(CellSummary::Set(_)) => {
                    i += 1;
                    continue;
                }
                None => {
                    i += 1;
                    continue;
                }
            };

            if control_delta == 0 {
                i += 1;
                continue;
            }

            let delta =
                ((i64::from(value) - i64::from(control_delta)) % overflow + overflow) % overflow;

            if delta == 0 {
                children[i] = Node::While {
                    cond: Cond::Always,
                    children: Vec::new(),
                };
                i += 1;
                continue;
            }

            let (u, _v, gcd) = gcdex_i64(delta, overflow);
            if gcd > i64::from(i32::MAX) {
                i += 1;
                continue;
            }
            let diff = Expr::mem(target) - Expr::Int(value);
            let count = Expr::Int((((u % overflow) + overflow) % overflow) as i32)
                * Expr::div(diff.clone(), Expr::Int(gcd as i32));

            let mut replacement = Vec::new();

            if gcd > 1 {
                replacement.push(Node::If {
                    cond: Cond::not_equal(Expr::modulo(diff, Expr::Int(gcd as i32)), 0),
                    children: vec![Node::While {
                        cond: Cond::Always,
                        children: Vec::new(),
                    }],
                });
            }

            for (&offset, summary) in &summaries {
                if offset == target {
                    continue;
                }
                match summary {
                    CellSummary::Add(delta_expr) => replacement.push(Node::SetMemory {
                        offset,
                        value: Expr::mem(offset) + delta_expr.clone() * count.clone(),
                    }),
                    CellSummary::Set(value_expr) => replacement.push(Node::If {
                        cond: cond.clone(),
                        children: vec![Node::SetMemory {
                            offset,
                            value: value_expr.clone(),
                        }],
                    }),
                }
            }

            replacement.push(Node::SetMemory {
                offset: target,
                value: Expr::Int(value),
            });

            children.splice(i..=i, replacement.clone());
            i += replacement.len();
            continue;
        }

        i += 1;
    }

    cleanup::cleanup(children);
}

/// Flatten Repeat nodes where all children are SetMemory with invariant deltas.
fn affine_repeat_pass(children: &mut Vec<Node>) {
    let mut i = 0;
    while i < children.len() {
        let (count, kids) = match &children[i] {
            Node::Repeat {
                count,
                children: kids,
            } => (count.clone(), kids.clone()),
            _ => {
                i += 1;
                continue;
            }
        };

        let summaries = match summarize_body_general(&kids) {
            Some(d) => d,
            None => {
                i += 1;
                continue;
            }
        };

        let mut replacement = Vec::new();
        for (&offset, summary) in &summaries {
            match summary {
                CellSummary::Add(delta_expr) => replacement.push(Node::SetMemory {
                    offset,
                    value: Expr::mem(offset) + delta_expr.clone() * count.clone(),
                }),
                CellSummary::Set(value_expr) => replacement.push(Node::If {
                    cond: Cond::not_equal(count.clone(), 0),
                    children: vec![Node::SetMemory {
                        offset,
                        value: value_expr.clone(),
                    }],
                }),
            }
        }

        if replacement.is_empty() {
            children[i] = Node::Nop;
            i += 1;
        } else {
            let n = replacement.len();
            children.splice(i..=i, replacement);
            i += n;
        }
    }

    cleanup::cleanup(children);
}

#[cfg(test)]
mod tests {
    use std::io::BufReader;

    use super::*;
    use crate::parser::brainfuck;

    fn parse_and_flatten(src: &str) -> Vec<Node> {
        let mut node = brainfuck::parse(BufReader::new(src.as_bytes())).unwrap();
        crate::opt::flatten::transform(&mut node);
        match node {
            Node::Program { children } => children,
            _ => panic!("expected Program"),
        }
    }

    fn run_on(kids: &mut Vec<Node>) {
        affine_loop_pass(kids, 8);
    }

    #[test]
    fn move_loop() {
        let mut kids = parse_and_flatten("[->+<]");
        run_on(&mut kids);
        assert!(
            kids.iter().any(
                |n| matches!(n, Node::SetMemory { offset: 0, value } if *value == Expr::Int(0))
            ),
            "control cell should be set to 0"
        );
        assert!(
            kids.iter()
                .any(|n| matches!(n, Node::SetMemory { offset: 1, .. })),
            "cell 1 should be updated"
        );
        assert!(
            !kids.iter().any(|n| matches!(n, Node::While { .. })),
            "while loop should be eliminated"
        );
    }

    #[test]
    fn move_loop_value() {
        let mut kids = parse_and_flatten("[->+<]");
        run_on(&mut kids);
        let cell1 = kids
            .iter()
            .find_map(|n| match n {
                Node::SetMemory { offset: 1, value } => Some(value.clone()),
                _ => None,
            })
            .expect("cell 1 should have SetMemory");
        // {1} + {0} (since count = {0}, delta = 1)
        let expected = Expr::mem(1) + Expr::mem(0);
        assert_eq!(cell1, expected);
    }

    #[test]
    fn multiply_loop() {
        let mut kids = parse_and_flatten("[->++<]");
        run_on(&mut kids);
        assert!(!kids.iter().any(|n| matches!(n, Node::While { .. })));
        let cell1 = kids
            .iter()
            .find_map(|n| match n {
                Node::SetMemory { offset: 1, value } => Some(value.clone()),
                _ => None,
            })
            .unwrap();
        // {1} + 2*{0}
        let expected = Expr::mem(1) + Expr::Int(2) * Expr::mem(0);
        assert_eq!(cell1, expected);
    }

    #[test]
    fn distribute_loop() {
        let mut kids = parse_and_flatten("[->+>+<<]");
        run_on(&mut kids);
        assert!(!kids.iter().any(|n| matches!(n, Node::While { .. })));
        assert!(kids
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 1, .. })));
        assert!(kids
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 2, .. })));
    }

    #[test]
    fn multi_coefficient() {
        let mut kids = parse_and_flatten("[->+>++>+++<<<]");
        run_on(&mut kids);
        assert!(!kids.iter().any(|n| matches!(n, Node::While { .. })));
        let cell3 = kids
            .iter()
            .find_map(|n| match n {
                Node::SetMemory { offset: 3, value } => Some(value.clone()),
                _ => None,
            })
            .unwrap();
        // {3} + 3*{0}
        let expected = Expr::mem(3) + Expr::Int(3) * Expr::mem(0);
        assert_eq!(cell3, expected);
    }

    #[test]
    fn gcd_greater_than_one() {
        let mut kids = parse_and_flatten("[-->+<]");
        run_on(&mut kids);
        assert!(
            kids.iter().any(|n| matches!(n, Node::If { .. })),
            "should have GCD guard"
        );
        assert!(
            !kids
                .iter()
                .any(|n| matches!(n, Node::While { cond, .. } if cond.is_mem_not_equal())),
            "original while should be eliminated"
        );
    }

    #[test]
    fn non_zero_stride_skipped() {
        let mut kids = parse_and_flatten("[>+]");
        let before = kids.clone();
        run_on(&mut kids);
        assert_eq!(kids, before);
    }

    #[test]
    fn non_constant_delta_skipped() {
        // Delta of cell 1 is {0}, which references the control cell (modified).
        // This must be skipped because the delta changes each iteration.
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::mem(0),
                },
            ],
        }];
        run_on(&mut kids);
        assert!(
            kids.iter().any(|n| matches!(n, Node::While { .. })),
            "should be unchanged"
        );
    }

    #[test]
    fn impure_body_skipped() {
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
                Node::Output { expr: Expr::mem(0) },
            ],
        }];
        run_on(&mut kids);
        assert!(kids.iter().any(|n| matches!(n, Node::While { .. })));
    }

    #[test]
    fn zero_control_delta_skipped() {
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![Node::SetMemory {
                offset: 1,
                value: Expr::mem(1) + Expr::Int(1),
            }],
        }];
        run_on(&mut kids);
        assert!(kids.iter().any(|n| matches!(n, Node::While { .. })));
    }

    #[test]
    fn non_mem_not_equal_skipped() {
        let mut kids = vec![Node::While {
            cond: Cond::Always,
            children: vec![Node::SetMemory {
                offset: 0,
                value: Expr::mem(0) + Expr::Int(-1),
            }],
        }];
        let before = kids.clone();
        run_on(&mut kids);
        assert_eq!(kids, before);
    }

    #[test]
    fn cellsize_16() {
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::Int(1),
                },
            ],
        }];
        affine_loop_pass(&mut kids, 16);
        assert!(!kids.iter().any(|n| matches!(n, Node::While { .. })));
    }

    // --- Generalized affine loop tests ---

    #[test]
    fn invariant_cell_reference_while() {
        // While(NE(0,0)) { p[0]-=1, p[1]+={2} }
        // Cell 2 is not modified, so delta {2} is constant across iterations.
        // Should be eliminated: p[1] += {2} * count; p[0] = 0
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::mem(2),
                },
            ],
        }];
        run_on(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::While { .. })),
            "while loop should be eliminated"
        );
        assert!(
            kids.iter().any(
                |n| matches!(n, Node::SetMemory { offset: 0, value } if *value == Expr::Int(0))
            ),
            "control cell should be set to 0"
        );
        assert!(
            kids.iter()
                .any(|n| matches!(n, Node::SetMemory { offset: 1, .. })),
            "cell 1 should be updated"
        );
    }

    #[test]
    fn invariant_cell_reference_value() {
        // While(NE(0,0)) { p[0]-=1, p[1]+={2} }
        // Final p[1] = {1} + {2} * {0}
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::mem(2),
                },
            ],
        }];
        run_on(&mut kids);
        let cell1 = kids
            .iter()
            .find_map(|n| match n {
                Node::SetMemory { offset: 1, value } => Some(value.clone()),
                _ => None,
            })
            .expect("cell 1 should have SetMemory");
        // {1} + {2} * {0}  (count = {0}, delta = {2})
        let expected = Expr::mem(1) + Expr::mem(2) * Expr::mem(0);
        assert_eq!(cell1, expected);
    }

    #[test]
    fn multiple_invariant_references() {
        // While(NE(0,0)) { p[0]-=1, p[1]+={2}+{3} }
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::mem(2) + Expr::mem(3),
                },
            ],
        }];
        run_on(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::While { .. })),
            "while loop should be eliminated"
        );
    }

    #[test]
    fn mixed_const_and_invariant_deltas() {
        // While(NE(0,0)) { p[0]-=1, p[1]+=3, p[2]+={3} }
        // All constant or invariant deltas.
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::Int(3),
                },
                Node::SetMemory {
                    offset: 2,
                    value: Expr::mem(2) + Expr::mem(3),
                },
            ],
        }];
        run_on(&mut kids);
        // The constant-delta fast path handles this (all deltas: -1, 3, {3}).
        // Actually only delta 3 and -1 are constant; {3} is not. So fast path fails,
        // general path handles it.
        assert!(
            !kids.iter().any(|n| matches!(n, Node::While { .. })),
            "while loop should be eliminated"
        );
    }

    #[test]
    fn modified_cell_reference_skipped() {
        // While(NE(0,0)) { p[0]-=1, p[1]+=1, p[2]+={1} }
        // Cell 1 IS modified, so delta {1} for cell 2 is NOT invariant.
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::Int(1),
                },
                Node::SetMemory {
                    offset: 2,
                    value: Expr::mem(2) + Expr::mem(1),
                },
            ],
        }];
        run_on(&mut kids);
        // The constant-delta fast path handles p[0] and p[1] (deltas -1, 1) but
        // p[2] has non-constant delta {1}. Fast path fails.
        // General path: p[2] delta after symbolic exec = {1}+1 (p[1] was already
        // updated to {1}+1 by the time we reach p[2]). References {1} which IS modified.
        // So general path also fails.
        assert!(
            kids.iter().any(|n| matches!(n, Node::While { .. })),
            "should be unchanged due to modified cell reference"
        );
    }

    #[test]
    fn cross_dependency_skipped() {
        // While(NE(0,0)) { p[0]-=1, p[1]+={2}, p[2]+=1 }
        // Cell 2 IS modified, so delta {2} for cell 1 is NOT invariant.
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::mem(2),
                },
                Node::SetMemory {
                    offset: 2,
                    value: Expr::mem(2) + Expr::Int(1),
                },
            ],
        }];
        run_on(&mut kids);
        assert!(
            kids.iter().any(|n| matches!(n, Node::While { .. })),
            "should be unchanged due to cross-cell dependency"
        );
    }

    #[test]
    fn body_order_matters_for_general() {
        // While(NE(0,0)) { p[1]+={2}, p[0]-=1 }
        // Order: p[1] reads p[2] (invariant), then p[0] decremented.
        // After symbolic exec: p[1] = {1}+{2}, p[0] = {0}-1. Deltas: {2} and -1.
        // {2} references only invariant cell 2. Should be eliminated.
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::mem(2),
                },
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
            ],
        }];
        run_on(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::While { .. })),
            "while loop should be eliminated"
        );
    }

    #[test]
    fn non_constant_control_delta_skipped() {
        // While(NE(0,0)) { p[0]={2}, p[1]+=1 }
        // Control cell delta = {2}-{0}, non-constant. Must skip.
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(2),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::Int(1),
                },
            ],
        }];
        run_on(&mut kids);
        assert!(
            kids.iter().any(|n| matches!(n, Node::While { .. })),
            "should be unchanged"
        );
    }

    // --- Repeat flattening tests ---

    #[test]
    fn repeat_invariant_delta_flattened() {
        // Repeat { count: {0}, [SM(1, {1}+{2})] }
        // Delta {2} is invariant. Should flatten to SM(1, {1}+{2}*{0}).
        let mut kids = vec![Node::Repeat {
            count: Expr::mem(0),
            children: vec![Node::SetMemory {
                offset: 1,
                value: Expr::mem(1) + Expr::mem(2),
            }],
        }];
        affine_repeat_pass(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::Repeat { .. })),
            "repeat should be eliminated"
        );
        let cell1 = kids
            .iter()
            .find_map(|n| match n {
                Node::SetMemory { offset: 1, value } => Some(value.clone()),
                _ => None,
            })
            .expect("cell 1 should have SetMemory");
        let expected = Expr::mem(1) + Expr::mem(2) * Expr::mem(0);
        assert_eq!(cell1, expected);
    }

    #[test]
    fn repeat_multiple_invariant_deltas() {
        // Repeat { count: {0}, [SM(1, {1}+{3}), SM(2, {2}+{3})] }
        let mut kids = vec![Node::Repeat {
            count: Expr::mem(0),
            children: vec![
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::mem(3),
                },
                Node::SetMemory {
                    offset: 2,
                    value: Expr::mem(2) + Expr::mem(3),
                },
            ],
        }];
        affine_repeat_pass(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::Repeat { .. })),
            "repeat should be eliminated"
        );
        assert!(kids
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 1, .. })),);
        assert!(kids
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 2, .. })),);
    }

    #[test]
    fn repeat_modified_cell_ref_kept() {
        // Repeat { count: {0}, [SM(1, {1}+{2}), SM(2, {2}+1)] }
        // Cell 2 IS modified, so delta {2} for cell 1 is not invariant.
        let mut kids = vec![Node::Repeat {
            count: Expr::mem(0),
            children: vec![
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(1) + Expr::mem(2),
                },
                Node::SetMemory {
                    offset: 2,
                    value: Expr::mem(2) + Expr::Int(1),
                },
            ],
        }];
        affine_repeat_pass(&mut kids);
        assert!(
            kids.iter().any(|n| matches!(n, Node::Repeat { .. })),
            "repeat should be preserved"
        );
    }

    #[test]
    fn repeat_const_delta_flattened() {
        // Repeat { count: {0}, [SM(1, {1}+5)] }
        // Constant delta 5, invariant. Should flatten.
        let mut kids = vec![Node::Repeat {
            count: Expr::mem(0),
            children: vec![Node::SetMemory {
                offset: 1,
                value: Expr::mem(1) + Expr::Int(5),
            }],
        }];
        affine_repeat_pass(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::Repeat { .. })),
            "repeat should be eliminated"
        );
        let cell1 = kids
            .iter()
            .find_map(|n| match n {
                Node::SetMemory { offset: 1, value } => Some(value.clone()),
                _ => None,
            })
            .unwrap();
        let expected = Expr::mem(1) + Expr::Int(5) * Expr::mem(0);
        assert_eq!(cell1, expected);
    }

    #[test]
    fn repeat_invariant_set_from_other_cell_flattened() {
        // Repeat { count: {0}, [SM(1, {3})] }
        // Each iteration overwrites cell 1 with invariant cell 3.
        // Final result is: if count != 0 then p[1] = p[3].
        let mut kids = vec![Node::Repeat {
            count: Expr::mem(0),
            children: vec![Node::SetMemory {
                offset: 1,
                value: Expr::mem(3),
            }],
        }];
        affine_repeat_pass(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::Repeat { .. })),
            "repeat should be eliminated"
        );
        assert!(kids.iter().any(|n| matches!(
            n,
            Node::If {
                cond: Cond::MemNotEqual(0, 0),
                children
            } if matches!(children.as_slice(), [Node::SetMemory { offset: 1, value }] if *value == Expr::mem(3))
        )));
    }

    #[test]
    fn repeat_set_to_self_kept() {
        // Repeat { count: {0}, [SM(1, {1})] }
        // This is a no-op body, so the repeat should disappear via cleanup rather than
        // becoming a conditional set.
        let mut kids = vec![Node::Repeat {
            count: Expr::mem(0),
            children: vec![Node::SetMemory {
                offset: 1,
                value: Expr::mem(1),
            }],
        }];
        affine_repeat_pass(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::Repeat { .. })),
            "repeat should be eliminated"
        );
    }

    #[test]
    fn while_invariant_set_becomes_conditional_set() {
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(2),
                },
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
            ],
        }];
        run_on(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::While { .. })),
            "while loop should be eliminated"
        );
        assert!(kids.iter().any(|n| matches!(
            n,
            Node::If {
                cond: Cond::MemNotEqual(0, 0),
                children
            } if matches!(children.as_slice(), [Node::SetMemory { offset: 1, value }] if *value == Expr::mem(2))
        )));
    }

    #[test]
    fn while_mixed_add_and_set_summary() {
        let mut kids = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(2),
                },
                Node::SetMemory {
                    offset: 3,
                    value: Expr::mem(3) + Expr::Int(4),
                },
                Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(-1),
                },
            ],
        }];
        run_on(&mut kids);
        assert!(
            kids.iter()
                .any(|n| matches!(n, Node::SetMemory { offset: 3, value } if *value == Expr::mem(3) + Expr::Int(4) * Expr::mem(0)))
        );
        assert!(kids.iter().any(|n| matches!(n, Node::If { .. })));
    }

    #[test]
    fn repeat_invariant_set_becomes_conditional_set() {
        let mut kids = vec![Node::Repeat {
            count: Expr::mem(0),
            children: vec![Node::SetMemory {
                offset: 1,
                value: Expr::mem(2),
            }],
        }];
        affine_repeat_pass(&mut kids);
        assert!(
            !kids.iter().any(|n| matches!(n, Node::Repeat { .. })),
            "repeat should be eliminated"
        );
        assert!(kids.iter().any(|n| matches!(
            n,
            Node::If {
                cond: Cond::MemNotEqual(0, 0),
                children
            } if matches!(children.as_slice(), [Node::SetMemory { offset: 1, value }] if *value == Expr::mem(2))
        )));
    }

    #[test]
    fn repeat_set_using_modified_cell_is_kept() {
        let mut kids = vec![Node::Repeat {
            count: Expr::mem(0),
            children: vec![
                Node::SetMemory {
                    offset: 2,
                    value: Expr::mem(2) + Expr::Int(1),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(2),
                },
            ],
        }];
        affine_repeat_pass(&mut kids);
        assert!(
            kids.iter().any(|n| matches!(n, Node::Repeat { .. })),
            "repeat should be preserved"
        );
    }
}
