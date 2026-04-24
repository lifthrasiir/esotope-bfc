use std::collections::BTreeSet;

use crate::expr::*;
use crate::nodes::*;

pub fn transform(node: &mut Node) {
    if !matches!(node, Node::Program { .. }) {
        return;
    }

    let children = match node {
        Node::Program { children } => children,
        _ => return,
    };

    let mut offsets: i32 = 0;
    let mut changed: BTreeSet<Option<i32>> = BTreeSet::new();
    changed.insert(None);

    let mut insertions: Vec<(usize, Vec<Node>)> = Vec::new();

    for (i, child) in children.iter().enumerate() {
        let refs = child.prereferences().move_pointer(offsets);
        let updates = child.preupdates().move_pointer(offsets);

        let zerorefs: Vec<Option<i32>> = refs
            .unsure
            .iter()
            .filter(|r| !changed.contains(r))
            .cloned()
            .collect();

        if !zerorefs.is_empty() {
            let nodes: Vec<Node> = zerorefs
                .iter()
                .filter_map(|j| {
                    j.map(|jv| Node::SetMemory {
                        offset: jv - offsets,
                        value: Expr::Int(0),
                    })
                })
                .collect();
            if !nodes.is_empty() {
                insertions.push((i, nodes));
            }
            changed.extend(zerorefs);
        }
        changed.extend(updates.unsure.iter().cloned());

        match child.offsets() {
            Some(o) => offsets += o,
            None => break,
        }
    }

    // Apply insertions in reverse to preserve indices
    for (idx, nodes) in insertions.into_iter().rev() {
        for (j, n) in nodes.into_iter().enumerate() {
            children.insert(idx + j, n);
        }
    }
}
