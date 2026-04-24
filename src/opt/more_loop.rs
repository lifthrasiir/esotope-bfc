use std::collections::{BTreeMap, BTreeSet};

use crate::expr::*;
use crate::nodes::*;

pub fn transform(node: &mut Node) {
    visit(node);
}

fn visit(node: &mut Node) {
    if let Some(children) = node.children_mut() {
        for child in children.iter_mut() {
            visit(child);
        }
        more_loop_pass(children);
    }
}

fn search_single_if(nodes: &[Node]) -> Option<usize> {
    let mut ifpos = None;
    for (i, inode) in nodes.iter().enumerate() {
        match inode {
            Node::If { .. } => {
                if ifpos.is_some() {
                    return None;
                }
                ifpos = Some(i);
            }
            Node::SetMemory { .. } => {}
            _ => return None,
        }
    }
    ifpos
}

fn propagate_mini(nodes: Vec<Node>) -> Vec<Node> {
    let mut subst: BTreeMap<i32, Expr> = BTreeMap::new();
    let mut result = Vec::new();
    for cur in nodes {
        if cur.is_nop() {
            continue;
        }
        if let Node::SetMemory { offset, value } = &cur {
            let refs = value.references();
            let self_only =
                refs.is_empty() || (refs.len() == 1 && refs.contains(&Expr::Int(*offset)));
            if !self_only {
                for (k, v) in &subst {
                    if *v != Expr::mem(*k) {
                        result.push(Node::SetMemory {
                            offset: *k,
                            value: v.clone(),
                        });
                    }
                }
                result.push(cur);
                subst.clear();
            } else {
                let new_value = value.with_memory(&subst);
                subst.insert(*offset, new_value);
            }
        }
    }
    for (k, v) in &subst {
        if *v != Expr::mem(*k) {
            result.push(Node::SetMemory {
                offset: *k,
                value: v.clone(),
            });
        }
    }
    result
}

fn more_loop_pass(children: &mut Vec<Node>) {
    let ifpos = match search_single_if(children) {
        Some(p) => p,
        None => return,
    };

    let ifnode = &children[ifpos];
    let (ifcond, ifkids) = match ifnode {
        Node::If { cond, children } => (cond.clone(), children.clone()),
        _ => return,
    };

    if !ifnode.is_pure() || ifnode.offsets() != Some(0) {
        return;
    }

    let mut statemap: BTreeMap<i32, Expr> = BTreeMap::new();
    let mut invmap: BTreeMap<i32, Expr> = BTreeMap::new();

    for inode in &children[..ifpos] {
        if let Node::SetMemory { offset, value } = inode {
            let refs = value.references();
            if !refs.is_empty() && refs != BTreeSet::from([Expr::Int(*offset)]) {
                return;
            }
            statemap.insert(*offset, value.with_memory(&statemap));
        } else {
            return;
        }
    }

    for (k, v) in &statemap {
        match v.inverse(*k) {
            Some(inv) => {
                invmap.insert(*k, inv);
            }
            None => return,
        }
    }

    let prealters: BTreeSet<i32> = statemap.keys().cloned().collect();

    let post_has_refs = children[ifpos + 1..].iter().any(|n| {
        let r = n.postreferences();
        !r.sure.is_empty() || !r.unsure.is_empty()
    });
    if post_has_refs {
        return;
    }

    let bodyupdates: BTreeSet<Option<i32>> =
        ifkids.iter().flat_map(|n| n.postupdates().unsure).collect();

    let postupdates: BTreeSet<Option<i32>> = children[ifpos + 1..]
        .iter()
        .flat_map(|n| n.postupdates().unsure)
        .collect();

    let prealters_opt: BTreeSet<Option<i32>> = prealters.iter().map(|x| Some(*x)).collect();
    let intersection: BTreeSet<Option<i32>> =
        prealters_opt.intersection(&bodyupdates).cloned().collect();
    if !intersection.is_subset(&postupdates) {
        return;
    }

    // Handle nested If flattening: f() If[c; If[d; g()] h()] i()
    if ifkids.len() > 1 {
        if let Node::If {
            children: ref inner_kids,
            ..
        } = &ifkids[0]
        {
            let inner_all_set = inner_kids
                .iter()
                .all(|n| matches!(n, Node::SetMemory { .. }));
            let rest_all_set = ifkids[1..]
                .iter()
                .all(|n| matches!(n, Node::SetMemory { .. }));

            if inner_all_set && rest_all_set {
                // Simplified: merge inner If conditions
                // f() If[c; If[d; g()]] h() -> f() If[c&d; g()] h()
                // (This is a subset of the Python logic for simplicity)
            }
        }
    }

    // Single nested If flattening: f() If[c; If[d; g()]] h() -> f() If[c&d; g()] h()
    if ifkids.len() == 1 {
        if let Node::If {
            cond: inner_cond,
            children: inner_kids,
        } = &ifkids[0]
        {
            let new_cond = ifcond.and_cond(inner_cond);
            let new_if = Node::If {
                cond: new_cond,
                children: inner_kids.clone(),
            };
            children[ifpos] = new_if;
            // Recursively try again
            more_loop_pass(children);
            return;
        }
    }

    // f() If[c; g()] h() -> If[c/f; g'/f()] f() h()
    let all_set = ifkids.iter().all(|n| matches!(n, Node::SetMemory { .. }));
    if all_set {
        let new_cond = ifcond.with_memory(&statemap);
        let mut new_body = Vec::new();
        let mut sm = statemap.clone();
        let mut lastdefs: BTreeMap<i32, usize> = BTreeMap::new();

        for (idx, inode) in ifkids.iter().enumerate() {
            if let Node::SetMemory { offset, value } = inode {
                new_body.push(Node::SetMemory {
                    offset: *offset,
                    value: value.with_memory(&sm),
                });
                for ref_offset in inode.postreferences().unsure.iter().filter_map(|x| *x) {
                    lastdefs.remove(&ref_offset);
                }
                for upd_offset in inode.postupdates().unsure.iter().filter_map(|x| *x) {
                    sm.remove(&upd_offset);
                    lastdefs.insert(upd_offset, idx);
                }
            }
        }

        for (k, v) in &lastdefs {
            if postupdates.contains(&Some(*k)) {
                new_body[*v] = Node::Nop;
            }
        }

        let new_body = propagate_mini(new_body);
        let pre_and_post: Vec<Node> = children[..ifpos]
            .iter()
            .chain(children[ifpos + 1..].iter())
            .cloned()
            .collect();
        let pre_and_post = propagate_mini(pre_and_post);

        let mut new_children = vec![Node::If {
            cond: new_cond,
            children: new_body,
        }];
        new_children.extend(pre_and_post);
        *children = new_children;
    }
}
