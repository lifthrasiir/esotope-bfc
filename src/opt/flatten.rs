use std::collections::BTreeMap;
use std::mem;

use crate::expr::*;
use crate::nodes::*;

pub fn transform(node: &mut Node) {
    visit(node, flatten_pass);
}

fn visit(node: &mut Node, func: fn(&mut Vec<Node>)) {
    if let Some(children) = node.children_mut() {
        for child in children.iter_mut() {
            visit(child, func);
        }
        func(children);
    }
}

fn flatten_pass(children: &mut Vec<Node>) {
    let mut result = Vec::new();
    let mut changes: BTreeMap<i32, i32> = BTreeMap::new();
    let mut changes_abs: BTreeMap<i32, Expr> = BTreeMap::new();
    let mut offset: i32 = 0;

    for cur in children.drain(..) {
        match cur {
            Node::SetMemory {
                offset: o, value, ..
            } => {
                let ioffset = offset + o;
                let delta = &value - &Expr::mem(o);
                if delta.is_simple() {
                    let dv = delta.to_int().unwrap();
                    *changes.entry(ioffset).or_insert(0) += dv;
                } else {
                    changes.remove(&ioffset);
                    changes_abs.insert(ioffset, value);
                }
            }
            Node::MovePointer { offset: o } => {
                offset += o;
            }
            _ => {
                flush_changes(&mut result, &mut changes, &mut changes_abs);

                let mut cur = cur;
                cur.move_pointer(offset);
                result.push(cur);
            }
        }
    }

    flush_changes(&mut result, &mut changes, &mut changes_abs);
    if offset != 0 {
        result.push(Node::MovePointer { offset });
    }

    *children = result;
}

fn flush_changes(
    result: &mut Vec<Node>,
    changes: &mut BTreeMap<i32, i32>,
    changes_abs: &mut BTreeMap<i32, Expr>,
) {
    for (k, v) in mem::take(changes_abs) {
        result.push(Node::SetMemory {
            offset: k,
            value: v,
        });
    }
    for (k, v) in mem::take(changes) {
        if v != 0 {
            result.push(Node::adjust_memory_by(k, v));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cond::Cond;

    fn prog(kids: Vec<Node>) -> Node {
        Node::Program { children: kids }
    }

    fn prog_children(node: &Node) -> &Vec<Node> {
        match node {
            Node::Program { children } => children,
            _ => panic!("expected Program"),
        }
    }

    #[test]
    fn merge_consecutive_adjusts() {
        // {0}+=1, {0}+=2 -> {0}+=3
        let mut node = prog(vec![
            Node::adjust_memory_by(0, 1),
            Node::adjust_memory_by(0, 2),
        ]);
        transform(&mut node);
        let kids = prog_children(&node);
        assert_eq!(kids.len(), 1);
        assert_eq!(kids[0].get_delta(), Expr::Int(3));
    }

    #[test]
    fn cancel_adjusts() {
        // {0}+=5, {0}-=5 -> empty
        let mut node = prog(vec![
            Node::adjust_memory_by(0, 5),
            Node::adjust_memory_by(0, -5),
        ]);
        transform(&mut node);
        assert!(prog_children(&node).is_empty());
    }

    #[test]
    fn propagate_pointer_offset() {
        // {0}+=1, MovePointer[2], {0}+=1 -> {0}+=1, {2}+=1, MovePointer[2]
        let mut node = prog(vec![
            Node::adjust_memory_by(0, 1),
            Node::MovePointer { offset: 2 },
            Node::adjust_memory_by(0, 1),
        ]);
        transform(&mut node);
        let kids = prog_children(&node);
        // Should have {0}+=1, {2}+=1, MovePointer[2]
        assert!(kids
            .iter()
            .any(|n| matches!(n, Node::MovePointer { offset: 2 })));
    }

    #[test]
    fn non_memory_flushes() {
        // {0}+=1, Output[{0}], {0}+=2
        let mut node = prog(vec![
            Node::adjust_memory_by(0, 1),
            Node::Output { expr: Expr::mem(0) },
            Node::adjust_memory_by(0, 2),
        ]);
        transform(&mut node);
        let kids = prog_children(&node);
        assert!(kids.len() >= 3); // flush before output, output, then after
    }

    #[test]
    fn nested_loop_flattened() {
        let mut node = prog(vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![Node::adjust_memory_by(0, 1), Node::adjust_memory_by(0, 2)],
        }]);
        transform(&mut node);
        let kids = prog_children(&node);
        if let Node::While { children, .. } = &kids[0] {
            assert_eq!(children.len(), 1);
            assert_eq!(children[0].get_delta(), Expr::Int(3));
        }
    }
}
