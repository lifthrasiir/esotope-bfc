use crate::cond::*;
use crate::expr::*;
use crate::nodes::*;

pub fn cleanup(children: &mut Vec<Node>) {
    let mut offsets: i32 = 0;
    let mut result = Vec::new();

    for cur in children.drain(..) {
        if cur.is_nop() {
            continue;
        }

        let mut cur = cur;
        cur.move_pointer(offsets);
        if let Some(o) = cur.offsets() {
            offsets += o;
        }

        if matches!(&cur, Node::MovePointer { .. }) {
            continue;
        }

        match cur {
            Node::If {
                cond,
                children: kids,
            } if cond.is_always() => {
                result.extend(kids);
                continue;
            }
            Node::Repeat {
                count: ref _count,
                children: ref kids,
            } => {
                let all_set_memory = kids.iter().all(|c| matches!(c, Node::SetMemory { .. }));
                let all_deltas_simple = all_set_memory
                    && kids.iter().all(|c| {
                        matches!(c, Node::SetMemory { offset, value } if (value - &Expr::mem(*offset)).is_simple())
                    });
                if all_deltas_simple {
                    let has_set = kids
                        .iter()
                        .any(|c| matches!(c, Node::SetMemory { value, .. } if value.is_simple()));

                    if let Node::Repeat {
                        count,
                        mut children,
                    } = cur
                    {
                        for inode in &mut children {
                            if let Node::SetMemory { offset, value } = inode {
                                let delta = &*value - &Expr::mem(*offset);
                                *value = Expr::mem(*offset) + delta * count.clone();
                            }
                        }
                        if has_set {
                            result.push(Node::If {
                                cond: Cond::not_equal(count, 0),
                                children,
                            });
                        } else {
                            result.extend(children);
                        }
                        continue;
                    }
                }
                result.push(cur);
            }
            _ => {
                let does_return = cur.returns();
                result.push(cur);
                if !does_return {
                    break;
                }
            }
        }
    }

    if offsets != 0 {
        result.push(Node::MovePointer { offset: offsets });
    }
    *children = result;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn removes_nop() {
        let mut kids = vec![Node::Nop, Node::adjust_memory_by(0, 1), Node::Nop];
        cleanup(&mut kids);
        assert_eq!(kids.len(), 1);
        assert!(matches!(&kids[0], Node::SetMemory { .. }));
    }

    #[test]
    fn removes_zero_move() {
        let mut kids = vec![Node::MovePointer { offset: 0 }];
        cleanup(&mut kids);
        assert!(kids.is_empty());
    }

    #[test]
    fn absorbs_move_pointer() {
        // MovePointer[3] followed by SetMemory at 0 -> SetMemory at 3
        let mut kids = vec![
            Node::MovePointer { offset: 3 },
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(0),
            },
        ];
        cleanup(&mut kids);
        // The MovePointer gets absorbed, SetMemory shifted, then trailing MovePointer appended
        let has_set_at_3 = kids
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 3, .. }));
        assert!(has_set_at_3);
    }

    #[test]
    fn if_always_flattened() {
        let mut kids = vec![Node::If {
            cond: Cond::Always,
            children: vec![Node::adjust_memory_by(0, 1)],
        }];
        cleanup(&mut kids);
        assert!(kids.iter().all(|n| !matches!(n, Node::If { .. })));
    }

    #[test]
    fn truncates_after_non_returning() {
        let mut kids = vec![
            Node::While {
                cond: Cond::Always,
                children: vec![],
            },
            Node::adjust_memory_by(0, 1), // dead code
        ];
        cleanup(&mut kids);
        assert_eq!(kids.len(), 1);
        assert!(matches!(&kids[0], Node::While { .. }));
    }

    #[test]
    fn trailing_offset_appended() {
        let mut kids = vec![Node::MovePointer { offset: 5 }];
        cleanup(&mut kids);
        assert_eq!(kids.len(), 1);
        assert!(matches!(&kids[0], Node::MovePointer { offset: 5 }));
    }

    #[test]
    fn repeat_with_non_simple_delta_preserved() {
        let mut kids = vec![Node::Repeat {
            count: Expr::mem(0),
            children: vec![Node::SetMemory {
                offset: 1,
                value: Expr::mem(1) + Expr::mem(2),
            }],
        }];
        cleanup(&mut kids);
        assert!(
            kids.iter().any(|n| matches!(n, Node::Repeat { .. })),
            "Repeat with non-simple delta must not be flattened"
        );
    }
}
