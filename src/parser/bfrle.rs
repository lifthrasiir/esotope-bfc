use std::io::BufRead;
use std::str;

use crate::cond::*;
use crate::expr::*;
use crate::nodes::*;

pub fn parse<R: BufRead>(reader: R) -> Result<Node, String> {
    let mut nodestack: Vec<Vec<Node>> = vec![Vec::new()];

    for (lineno, line) in reader.lines().enumerate() {
        let line = line.map_err(|e| format!("Read error: {}", e))?;
        let bytes = line.as_bytes();
        let lline = bytes.len();
        let mut i = 0;

        while i < lline {
            let ch = bytes[i];
            i += 1;

            if ch == b'+' || ch == b'-' || ch == b'>' || ch == b'<' {
                let repcount;
                if i + 1 < lline && bytes[i] == b'*' && bytes[i + 1] >= b'1' && bytes[i + 1] <= b'9'
                {
                    let mut nexti = i + 2;
                    while nexti < lline && bytes[nexti] >= b'0' && bytes[nexti] <= b'9' {
                        nexti += 1;
                    }
                    let s = str::from_utf8(&bytes[i + 1..nexti]).unwrap();
                    repcount = s.parse::<i32>().unwrap();
                    i = nexti;
                } else {
                    repcount = 1;
                }

                let node = match ch {
                    b'+' => Node::adjust_memory_by(0, repcount),
                    b'-' => Node::adjust_memory_by(0, -repcount),
                    b'>' => Node::MovePointer { offset: repcount },
                    b'<' => Node::MovePointer { offset: -repcount },
                    _ => unreachable!(),
                };
                nodestack.last_mut().unwrap().push(node);
            } else if ch == b'.' {
                nodestack
                    .last_mut()
                    .unwrap()
                    .push(Node::Output { expr: Expr::mem(0) });
            } else if ch == b',' {
                nodestack
                    .last_mut()
                    .unwrap()
                    .push(Node::Input { offset: 0 });
            } else if ch == b'[' {
                nodestack.push(Vec::new());
            } else if ch == b']' {
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
    fn rle_plus() {
        let prog = parse_str("+*10");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        assert_eq!(kids[0].get_delta(), Expr::Int(10));
    }

    #[test]
    fn rle_minus() {
        let prog = parse_str("-*5");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        assert_eq!(kids[0].get_delta(), Expr::Int(-5));
    }

    #[test]
    fn rle_move_right() {
        let prog = parse_str(">*100");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        assert!(matches!(&kids[0], Node::MovePointer { offset: 100 }));
    }

    #[test]
    fn rle_move_left() {
        let prog = parse_str("<*20");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        assert!(matches!(&kids[0], Node::MovePointer { offset: -20 }));
    }

    #[test]
    fn no_rle_star_without_digit() {
        // *x where x is not a digit -> treated as comment
        let prog = parse_str("+*x");
        let kids = children(&prog);
        // + is parsed as single increment, * and x are ignored
        assert_eq!(kids.len(), 1);
        assert_eq!(kids[0].get_delta(), Expr::Int(1));
    }

    #[test]
    fn plain_bf_still_works() {
        let prog = parse_str("+++");
        let kids = children(&prog);
        assert_eq!(kids.len(), 3); // bfrle doesn't merge repeated chars
    }

    #[test]
    fn loop_and_io() {
        let prog = parse_str("[,.]");
        let kids = children(&prog);
        assert_eq!(kids.len(), 1);
        if let Node::While { children: body, .. } = &kids[0] {
            assert_eq!(body.len(), 2);
        } else {
            panic!("expected While");
        }
    }

    #[test]
    fn unmatched_brackets() {
        assert!(parse(BufReader::new("[".as_bytes())).is_err());
        assert!(parse(BufReader::new("]".as_bytes())).is_err());
    }

    #[test]
    fn rle_large_number() {
        let prog = parse_str("+*255");
        let kids = children(&prog);
        assert_eq!(kids[0].get_delta(), Expr::Int(255));
    }
}
