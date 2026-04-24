use std::collections::BTreeSet;

use crate::cond::*;
use crate::expr::*;
use crate::nodes::*;

pub fn analyze(node: &Node) -> Option<BTreeSet<i32>> {
    let mut cells = BTreeSet::new();
    collect_cells(node, 0, &mut cells)?;
    Some(cells)
}

fn collect_cells(node: &Node, ptr: i32, cells: &mut BTreeSet<i32>) -> Option<i32> {
    match node {
        Node::Nop => Some(ptr),
        Node::SetMemory { offset, value } => {
            cells.insert(ptr + offset);
            collect_expr_refs(value, ptr, cells)?;
            Some(ptr)
        }
        Node::MovePointer { offset } => Some(ptr + offset),
        Node::Input { offset } => {
            cells.insert(ptr + offset);
            Some(ptr)
        }
        Node::Output { expr } => {
            collect_expr_refs(expr, ptr, cells)?;
            Some(ptr)
        }
        Node::OutputConst { .. } => Some(ptr),
        Node::SeekMemory { .. } => None,
        Node::Program { children } => collect_children(children, ptr, cells),
        Node::If { cond, children } => {
            collect_cond_refs(cond, ptr, cells)?;
            collect_children(children, ptr, cells)?;
            if stride(children) == Some(0) {
                Some(ptr)
            } else {
                None
            }
        }
        Node::While { cond, children } => {
            collect_cond_refs(cond, ptr, cells)?;
            if stride(children) != Some(0) {
                return None;
            }
            collect_children(children, ptr, cells)?;
            Some(ptr)
        }
        Node::Repeat { count, children } => {
            collect_expr_refs(count, ptr, cells)?;
            if stride(children) != Some(0) {
                return None;
            }
            collect_children(children, ptr, cells)?;
            Some(ptr)
        }
    }
}

fn collect_children(children: &[Node], mut ptr: i32, cells: &mut BTreeSet<i32>) -> Option<i32> {
    for child in children {
        ptr = collect_cells(child, ptr, cells)?;
    }
    Some(ptr)
}

fn collect_expr_refs(expr: &Expr, ptr: i32, cells: &mut BTreeSet<i32>) -> Option<()> {
    for r in expr.references() {
        cells.insert(ptr + r.to_int()?);
    }
    Some(())
}

fn collect_cond_refs(cond: &Cond, ptr: i32, cells: &mut BTreeSet<i32>) -> Option<()> {
    for r in cond.references() {
        cells.insert(ptr + r.to_int()?);
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_program() {
        let node = Node::Program { children: vec![] };
        let cells = analyze(&node).unwrap();
        assert!(cells.is_empty());
    }

    #[test]
    fn simple_cells() {
        let node = Node::Program {
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(65),
                },
                Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(0) + Expr::Int(1),
                },
                Node::Output { expr: Expr::mem(1) },
            ],
        };
        let cells = analyze(&node).unwrap();
        assert_eq!(cells, BTreeSet::from([0, 1]));
    }

    #[test]
    fn move_pointer_tracks_offset() {
        let node = Node::Program {
            children: vec![
                Node::MovePointer { offset: 3 },
                Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(1),
                },
                Node::Output { expr: Expr::mem(0) },
            ],
        };
        let cells = analyze(&node).unwrap();
        assert_eq!(cells, BTreeSet::from([3]));
    }

    #[test]
    fn seek_memory_returns_none() {
        let node = Node::Program {
            children: vec![Node::SeekMemory {
                target: 0,
                stride: 1,
                value: 0,
            }],
        };
        assert!(analyze(&node).is_none());
    }

    #[test]
    fn while_stride_zero() {
        let node = Node::Program {
            children: vec![
                Node::Input { offset: 0 },
                Node::While {
                    cond: Cond::MemNotEqual(0, 0),
                    children: vec![
                        Node::SetMemory {
                            offset: 1,
                            value: Expr::mem(1) + Expr::Int(1),
                        },
                        Node::SetMemory {
                            offset: 0,
                            value: Expr::mem(0) + Expr::Int(-1),
                        },
                    ],
                },
            ],
        };
        let cells = analyze(&node).unwrap();
        assert_eq!(cells, BTreeSet::from([0, 1]));
    }

    #[test]
    fn while_nonzero_stride_returns_none() {
        let node = Node::Program {
            children: vec![
                Node::Input { offset: 0 },
                Node::While {
                    cond: Cond::MemNotEqual(0, 0),
                    children: vec![Node::MovePointer { offset: 1 }],
                },
            ],
        };
        assert!(analyze(&node).is_none());
    }

    #[test]
    fn if_stride_zero() {
        let node = Node::Program {
            children: vec![
                Node::Input { offset: 0 },
                Node::If {
                    cond: Cond::MemNotEqual(0, 0),
                    children: vec![Node::SetMemory {
                        offset: 1,
                        value: Expr::Int(5),
                    }],
                },
            ],
        };
        let cells = analyze(&node).unwrap();
        assert_eq!(cells, BTreeSet::from([0, 1]));
    }

    #[test]
    fn if_nonzero_stride_returns_none() {
        let node = Node::Program {
            children: vec![
                Node::Input { offset: 0 },
                Node::If {
                    cond: Cond::MemNotEqual(0, 0),
                    children: vec![Node::MovePointer { offset: 1 }],
                },
            ],
        };
        assert!(analyze(&node).is_none());
    }

    #[test]
    fn nested_move_and_access() {
        let node = Node::Program {
            children: vec![
                Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(1),
                },
                Node::MovePointer { offset: 2 },
                Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(2),
                },
                Node::MovePointer { offset: -2 },
                Node::Output { expr: Expr::mem(0) },
            ],
        };
        let cells = analyze(&node).unwrap();
        assert_eq!(cells, BTreeSet::from([0, 2]));
    }

    #[test]
    fn input_cell_tracked() {
        let node = Node::Program {
            children: vec![
                Node::Input { offset: 0 },
                Node::MovePointer { offset: 5 },
                Node::Input { offset: 0 },
            ],
        };
        let cells = analyze(&node).unwrap();
        assert_eq!(cells, BTreeSet::from([0, 5]));
    }

    #[test]
    fn repeat_stride_zero() {
        let node = Node::Program {
            children: vec![Node::Repeat {
                count: Expr::Int(10),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::mem(0) + Expr::Int(1),
                }],
            }],
        };
        let cells = analyze(&node).unwrap();
        assert_eq!(cells, BTreeSet::from([0]));
    }

    #[test]
    fn expr_with_multiple_refs() {
        let node = Node::Program {
            children: vec![Node::SetMemory {
                offset: 3,
                value: Expr::mem(0) + Expr::mem(1) + Expr::mem(2),
            }],
        };
        let cells = analyze(&node).unwrap();
        assert_eq!(cells, BTreeSet::from([0, 1, 2, 3]));
    }
}
