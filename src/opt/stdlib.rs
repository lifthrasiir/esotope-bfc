use std::mem;

use crate::nodes::*;

pub fn transform(node: &mut Node) {
    visit(node);
}

fn visit(node: &mut Node) {
    if let Some(children) = node.children_mut() {
        for child in children.iter_mut() {
            visit(child);
        }
        stdlib_pass(children);
    }
}

fn stdlib_pass(children: &mut Vec<Node>) {
    let mut result = Vec::new();
    let mut laststr: Vec<u8> = Vec::new();

    for cur in children.drain(..) {
        match &cur {
            Node::Output { expr } if expr.is_simple() => {
                let val = expr.to_int().unwrap();
                laststr.push((val & 0xff) as u8);
            }
            Node::OutputConst { s } => {
                laststr.extend_from_slice(s);
            }
            _ if !cur.is_pure() => {
                if !laststr.is_empty() {
                    result.push(Node::OutputConst {
                        s: mem::take(&mut laststr),
                    });
                }
                result.push(cur);
            }
            _ => {
                result.push(cur);
            }
        }
    }

    if !laststr.is_empty() {
        result.push(Node::OutputConst { s: laststr });
    }

    *children = result;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Expr;

    fn prog(kids: Vec<Node>) -> Node {
        Node::Program { children: kids }
    }

    #[test]
    fn merge_const_outputs() {
        let mut node = prog(vec![
            Node::Output {
                expr: Expr::Int(72),
            }, // H
            Node::Output {
                expr: Expr::Int(101),
            }, // e
        ]);
        transform(&mut node);
        if let Node::Program { children } = &node {
            assert_eq!(children.len(), 1);
            assert!(matches!(&children[0], Node::OutputConst { s } if s == &[72, 101]));
        }
    }

    #[test]
    fn non_const_output_not_merged() {
        let mut node = prog(vec![Node::Output { expr: Expr::mem(0) }]);
        transform(&mut node);
        if let Node::Program { children } = &node {
            assert_eq!(children.len(), 1);
            assert!(matches!(&children[0], Node::Output { .. }));
        }
    }

    #[test]
    fn io_boundary_splits() {
        // const output, then non-pure (Input), then const output
        let mut node = prog(vec![
            Node::Output {
                expr: Expr::Int(65),
            },
            Node::Input { offset: 0 },
            Node::Output {
                expr: Expr::Int(66),
            },
        ]);
        transform(&mut node);
        if let Node::Program { children } = &node {
            // Should be OutputConst("A"), Input, OutputConst("B")
            assert_eq!(children.len(), 3);
            assert!(matches!(&children[0], Node::OutputConst { s } if s == &[65]));
            assert!(matches!(&children[1], Node::Input { .. }));
            assert!(matches!(&children[2], Node::OutputConst { s } if s == &[66]));
        }
    }

    #[test]
    fn existing_output_const_merged() {
        let mut node = prog(vec![
            Node::OutputConst { s: vec![65, 66] },
            Node::Output {
                expr: Expr::Int(67),
            },
        ]);
        transform(&mut node);
        if let Node::Program { children } = &node {
            assert_eq!(children.len(), 1);
            assert!(matches!(&children[0], Node::OutputConst { s } if s == &[65, 66, 67]));
        }
    }

    #[test]
    fn pure_nodes_pass_through() {
        let mut node = prog(vec![
            Node::Output {
                expr: Expr::Int(65),
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(0),
            },
            Node::Output {
                expr: Expr::Int(66),
            },
        ]);
        transform(&mut node);
        if let Node::Program { children } = &node {
            // SetMemory is pure, so outputs should still be merged around it
            // The set memory node remains, and two outputs become OutputConst
            assert!(children.iter().any(|n| matches!(n, Node::SetMemory { .. })));
        }
    }
}
