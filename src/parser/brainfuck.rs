use std::io::BufRead;

use crate::cond::*;
use crate::expr::*;
use crate::nodes::*;

pub fn parse<R: BufRead>(reader: R) -> Result<Node, String> {
    let mut nodestack: Vec<Vec<Node>> = vec![Vec::new()];

    let mut repch: Option<u8> = None;
    let mut repcount: i32 = 0;

    for (lineno, line) in reader.lines().enumerate() {
        let line = line.map_err(|e| format!("Read error: {}", e))?;
        for &ch in line.as_bytes() {
            if repch == Some(ch) {
                repcount += 1;
            } else {
                if repcount > 0 {
                    if let Some(rc) = repch {
                        let node = match rc {
                            b'+' => Some(Node::adjust_memory_by(0, repcount)),
                            b'-' => Some(Node::adjust_memory_by(0, -repcount)),
                            b'>' => Some(Node::MovePointer { offset: repcount }),
                            b'<' => Some(Node::MovePointer { offset: -repcount }),
                            _ => None,
                        };
                        if let Some(n) = node {
                            nodestack.last_mut().unwrap().push(n);
                        }
                    }
                }

                repch = None;
                repcount = 0;

                match ch {
                    b'+' | b'-' | b'>' | b'<' => {
                        repch = Some(ch);
                        repcount = 1;
                    }
                    b'.' => {
                        nodestack
                            .last_mut()
                            .unwrap()
                            .push(Node::Output { expr: Expr::mem(0) });
                    }
                    b',' => {
                        nodestack
                            .last_mut()
                            .unwrap()
                            .push(Node::Input { offset: 0 });
                    }
                    b'[' => {
                        nodestack.push(Vec::new());
                    }
                    b']' => {
                        if nodestack.len() < 2 {
                            return Err(format!("Not matching ] at line {}", lineno + 1));
                        }
                        let children = nodestack.pop().unwrap();
                        let loop_node = Node::While {
                            cond: Cond::MemNotEqual(0, 0),
                            children,
                        };
                        nodestack.last_mut().unwrap().push(loop_node);
                    }
                    _ => {}
                }
            }
        }
    }

    if repcount > 0 {
        if let Some(rc) = repch {
            let node = match rc {
                b'+' => Some(Node::adjust_memory_by(0, repcount)),
                b'-' => Some(Node::adjust_memory_by(0, -repcount)),
                b'>' => Some(Node::MovePointer { offset: repcount }),
                b'<' => Some(Node::MovePointer { offset: -repcount }),
                _ => None,
            };
            if let Some(n) = node {
                nodestack.last_mut().unwrap().push(n);
            }
        }
    }

    if nodestack.len() != 1 {
        return Err("Premature end of the loop".to_string());
    }

    Ok(Node::Program {
        children: nodestack.pop().unwrap(),
    })
}

#[cfg(test)]
mod tests {
    use std::io::BufReader;

    use super::*;

    fn parse_str(s: &str) -> Node {
        parse(BufReader::new(s.as_bytes())).unwrap()
    }

    fn children(node: &Node) -> &Vec<Node> {
        match node {
            Node::Program { children } => children,
            _ => panic!("expected Program"),
        }
    }

    #[test]
    fn empty_program() {
        let prog = parse_str("");
        assert!(children(&prog).is_empty());
    }

    #[test]
    fn single_plus() {
        let prog = parse_str("+");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        assert!(matches!(&kids[0], Node::SetMemory { offset: 0, .. }));
    }

    #[test]
    fn merged_plus() {
        let prog = parse_str("+++");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        // delta should be 3
        assert_eq!(kids[0].get_delta(), Expr::Int(3));
    }

    #[test]
    fn plus_minus_separate() {
        let prog = parse_str("++--");
        let kids = children(&prog);
        // ++ and -- are separate nodes (not merged across different chars)
        assert_eq!(kids.len(), 2);
    }

    #[test]
    fn move_right() {
        let prog = parse_str(">>>");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        assert!(matches!(&kids[0], Node::MovePointer { offset: 3 }));
    }

    #[test]
    fn move_left() {
        let prog = parse_str("<<");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        assert!(matches!(&kids[0], Node::MovePointer { offset: -2 }));
    }

    #[test]
    fn input_output() {
        let prog = parse_str(",.");
        let kids = children(&prog);
        assert_eq!(kids.len(), 2);
        assert!(matches!(&kids[0], Node::Input { offset: 0 }));
        assert!(matches!(&kids[1], Node::Output { .. }));
    }

    #[test]
    fn simple_loop() {
        let prog = parse_str("[-]");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        match &kids[0] {
            Node::While { cond, children } => {
                assert!(cond.is_mem_not_equal());
                assert_eq!(children.len(), 1);
            }
            _ => panic!("expected While"),
        }
    }

    #[test]
    fn nested_loops() {
        let prog = parse_str("[[-]]");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        if let Node::While {
            children: outer, ..
        } = &kids[0]
        {
            assert_eq!(outer.len(), 1);
            assert!(matches!(&outer[0], Node::While { .. }));
        } else {
            panic!("expected While");
        }
    }

    #[test]
    fn unmatched_close_bracket() {
        let result = parse(BufReader::new("]".as_bytes()));
        assert!(result.is_err());
    }

    #[test]
    fn unmatched_open_bracket() {
        let result = parse(BufReader::new("[".as_bytes()));
        assert!(result.is_err());
    }

    #[test]
    fn comments_ignored() {
        let prog = parse_str("this is a comment + more comment");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1); // only the +
    }

    #[test]
    fn trailing_operations() {
        let prog = parse_str("+>");
        let kids = children(&prog);
        assert_eq!(kids.len(), 2);
    }
}
