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
        simple_loop_pass(children, cellsize);
    }
}

fn simple_loop_pass(children: &mut Vec<Node>, cellsize: u32) {
    let overflow: i32 = 1 << cellsize;

    let mut i = 0;
    while i < children.len() {
        let is_while = matches!(&children[i], Node::While { .. });
        if !is_while {
            i += 1;
            continue;
        }

        let (cond, kids) = if let Node::While {
            ref cond,
            ref children,
        } = &children[i]
        {
            (cond.clone(), children.clone())
        } else {
            i += 1;
            continue;
        };

        if !cond.is_mem_not_equal() {
            i += 1;
            continue;
        }

        let target = cond.get_target().unwrap();
        let value = cond.get_value().unwrap();

        // While[cond; MovePointer[y]] -> SeekMemory
        if kids.len() == 1 {
            if let Node::MovePointer { offset } = &kids[0] {
                children[i] = Node::SeekMemory {
                    target,
                    stride: *offset,
                    value,
                };
                i += 1;
                continue;
            }
        }

        if stride(&kids) != Some(0) {
            i += 1;
            continue;
        }

        let mut flag = true;
        let mut cell = Expr::Int(0);
        let mut mode: i32 = 0; // 0:adjust, 1:set, -1:unknown

        for inode in &kids {
            match inode {
                Node::SetMemory { offset, value, .. } if *offset == target => {
                    let delta = value - &Expr::mem(*offset);
                    if delta.is_simple() {
                        cell = &cell + &delta;
                    } else {
                        cell = value.clone();
                        mode = 1;
                    }
                }
                Node::SetMemory { .. } => {}
                _ => {
                    if !inode.is_pure() {
                        flag = false;
                    }
                    if inode.offsets() != Some(0) {
                        flag = false;
                        mode = -1;
                    }
                    let updates = inode.postupdates().unsure;
                    if updates.contains(&None) || updates.contains(&Some(target)) {
                        flag = false;
                        mode = -1;
                    }
                    let refs = &inode.postreferences().unsure - &inode.postupdates().sure;
                    if refs.contains(&None) || refs.contains(&Some(target)) {
                        flag = false;
                    }
                }
            }
        }

        if mode < 0 || !cell.is_simple() {
            i += 1;
            continue;
        }
        let cell_val = cell.to_int().unwrap();
        let delta = ((value - cell_val) % overflow + overflow) % overflow;

        if mode > 0 {
            if delta == 0 {
                let replacement = vec![
                    Node::If {
                        cond: cond.clone(),
                        children: kids,
                    },
                    Node::SetMemory {
                        offset: target,
                        value: Expr::Int(value),
                    },
                ];
                children.splice(i..=i, replacement);
                i += 2;
            } else {
                let mut infloop = Node::While {
                    cond: Cond::Always,
                    children: Vec::new(),
                };
                if !kids.iter().all(|k| k.is_pure()) {
                    infloop = Node::While {
                        cond: Cond::Always,
                        children: kids,
                    };
                }
                children[i] = infloop;
                i += 1;
            }
        } else if flag {
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

            let inodes: Vec<Node> = kids
                .into_iter()
                .filter(
                    |inode| !matches!(inode, Node::SetMemory { offset, .. } if *offset == target),
                )
                .collect();

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
            if !inodes.is_empty() {
                replacement.push(Node::Repeat {
                    count,
                    children: inodes,
                });
            }
            replacement.push(Node::SetMemory {
                offset: target,
                value: Expr::Int(value),
            });

            children.splice(i..=i, replacement.clone());
            i += replacement.len();
        } else {
            i += 1;
        }
    }

    cleanup::cleanup(children);
}

#[cfg(test)]
mod tests {
    use std::io::BufReader;

    use super::*;
    use crate::parser::brainfuck;

    fn compile_and_get_children(src: &str) -> Vec<Node> {
        let mut node = brainfuck::parse(BufReader::new(src.as_bytes())).unwrap();
        crate::opt::flatten::transform(&mut node);
        transform(&mut node, 8);
        match node {
            Node::Program { children } => children,
            _ => panic!("expected Program"),
        }
    }

    #[test]
    fn clear_loop_becomes_set_zero() {
        // [-] -> SetMemory(0, 0)
        let kids = compile_and_get_children("[-]");
        assert!(kids
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 0, value } if *value == Expr::Int(0))));
    }

    #[test]
    fn seek_loop() {
        // [>] -> SeekMemory
        let kids = compile_and_get_children("[>]");
        assert!(kids.iter().any(|n| matches!(n, Node::SeekMemory { .. })));
    }

    #[test]
    fn move_value_loop() {
        // [->+<] moves cell 0 to cell 1
        let kids = compile_and_get_children("[->+<]");
        // Should produce Repeat or If + SetMemory pattern
        let has_set_zero = kids
            .iter()
            .any(|n| matches!(n, Node::SetMemory { offset: 0, value } if *value == Expr::Int(0)));
        assert!(has_set_zero);
    }

    #[test]
    fn nonzero_stride_skipped() {
        // [>+] has stride 1 != 0 with non-move body, not a simple loop
        let kids = compile_and_get_children("[>+]");
        // Should still be a While
        assert!(kids.iter().any(|n| matches!(n, Node::While { .. })));
    }
}
