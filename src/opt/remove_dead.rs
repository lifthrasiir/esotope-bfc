use std::collections::{BTreeMap, BTreeSet};

use crate::nodes::*;
use crate::opt::cleanup;

pub fn transform(node: &mut Node) {
    visit(node);
}

fn visit(node: &mut Node) {
    let is_program = matches!(node, Node::Program { .. });
    if let Some(children) = node.children_mut() {
        for child in children.iter_mut() {
            visit(child);
        }
        remove_dead_pass(children, is_program);
    }
}

fn remove_dead_pass(children: &mut Vec<Node>, is_program: bool) {
    let mut unusedcells: BTreeMap<i32, usize> = BTreeMap::new();
    let mut unusednodes: BTreeSet<usize> = BTreeSet::new();
    let mut unusedmoves: Vec<usize> = Vec::new();

    let mut offsets: i32 = 0;

    for i in 0..children.len() {
        if let Some(o) = children[i].offsets() {
            offsets += o;
        } else {
            unusedcells.clear();
            unusednodes.clear();
        }

        let pure = children[i].is_pure() && children[i].returns();
        if pure {
            unusedmoves.push(i);
        }

        let irefs = children[i].postreferences().unsure;
        let iupdates = children[i].postupdates().sure;
        let removable = pure && children[i].offsets() == Some(0);

        if !irefs.is_empty() || !iupdates.is_empty() {
            unusedmoves.clear();
        }

        if irefs.contains(&None) {
            unusedcells.clear();
            unusednodes.clear();
        } else {
            for j in irefs.iter().flatten() {
                let j = j + offsets;
                if let Some(old_idx) = unusedcells.remove(&j) {
                    unusednodes.remove(&old_idx);
                }
            }
        }

        for &j in iupdates.iter().flatten() {
            let j = j + offsets;
            if let Some(&old_i) = unusedcells.get(&j) {
                if unusednodes.remove(&old_i) {
                    children[old_i] = Node::Nop;
                }
            }
            if removable {
                unusedcells.insert(j, i);
                unusednodes.insert(i);
            }
        }
    }

    if is_program {
        for i in &unusednodes {
            children[*i] = Node::Nop;
        }
        for i in &unusedmoves {
            children[*i] = Node::Nop;
        }
    }

    cleanup::cleanup(children);
}
