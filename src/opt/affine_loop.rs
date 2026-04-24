use std::collections::BTreeMap;

use crate::cond::*;
use crate::expr::*;
use crate::math::gcdex;
use crate::nodes::*;
use crate::opt::cleanup;

pub fn transform(node: &mut Node, cellsize: u32) {
    visit(node, cellsize);
}

fn visit(node: &mut Node, cellsize: u32) {
    if let Some(children) = node.children_mut() {
        for child in children.iter_mut() {
            visit(child, cellsize);
        }
        affine_loop_pass(children, cellsize);
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

fn affine_loop_pass(children: &mut Vec<Node>, cellsize: u32) {
    let overflow: i32 = 1 << cellsize;

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

        let deltas = match summarize_body(&kids) {
            Some(d) => d,
            None => {
                i += 1;
                continue;
            }
        };

        let control_delta = *deltas.get(&target).unwrap_or(&0);
        if control_delta == 0 {
            i += 1;
            continue;
        }

        let delta = ((value - control_delta) % overflow + overflow) % overflow;

        if delta == 0 {
            children[i] = Node::While {
                cond: Cond::Always,
                children: Vec::new(),
            };
            i += 1;
            continue;
        }

        let (u, _v, gcd) = gcdex(delta, overflow);
        let diff = Expr::mem(target) - Expr::Int(value);
        let count = Expr::Int(((u % overflow) + overflow) % overflow)
            * Expr::div(diff.clone(), Expr::Int(gcd));

        let mut replacement = Vec::new();

        if gcd > 1 {
            replacement.push(Node::If {
                cond: Cond::not_equal(Expr::modulo(diff, Expr::Int(gcd)), 0),
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
            kids.iter()
                .any(|n| matches!(n, Node::SetMemory { offset: 0, value } if *value == Expr::Int(0))),
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
                Node::Output {
                    expr: Expr::mem(0),
                },
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
}
