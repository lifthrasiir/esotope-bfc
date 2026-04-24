use std::collections::BTreeMap;

use crate::cond::*;
use crate::expr::*;
use crate::nodes::*;
use crate::opt::cleanup;

pub fn transform(node: &mut Node) {
    visit(node);
}

fn visit(node: &mut Node) {
    if let Some(children) = node.children_mut() {
        for child in children.iter_mut() {
            visit(child);
        }
        propagate_pass(children);
    }
}

fn propagate_pass(children: &mut Vec<Node>) {
    let mut backrefs: BTreeMap<i32, usize> = BTreeMap::new();
    let mut usedrefs: BTreeMap<i32, usize> = BTreeMap::new();
    let mut substs: BTreeMap<i32, Expr> = BTreeMap::new();

    let mut i = 0;
    while i < children.len() {
        children[i].with_memory(&substs);

        let mut alters = false;
        let mut mergable = false;
        let mut offset: Option<i32> = None;

        match &children[i] {
            Node::Nop => {}
            Node::SetMemory { offset: o, value } => {
                alters = true;
                mergable = true;
                offset = Some(*o);
                let o = *o;
                let delta = value - &Expr::mem(o);
                if value.is_simple() {
                    substs.insert(o, value.clone());
                } else if delta.is_simple() {
                    if let Some(existing) = substs.get_mut(&o) {
                        *existing = &*existing + &delta;
                        if substs[&o].is_simple() {
                            let val = substs[&o].clone();
                            children[i] = Node::SetMemory {
                                offset: o,
                                value: val,
                            };
                        } else {
                            substs.remove(&o);
                        }
                    }
                } else {
                    substs.remove(&o);
                }
            }
            Node::Input { offset: o } => {
                alters = true;
                offset = Some(*o);
                substs.remove(o);
            }
            Node::Output { .. } => {}
            _ => {
                backrefs.clear();
                usedrefs.clear();
                substs.clear();
                match &children[i] {
                    Node::While { cond, .. } | Node::If { cond, .. } => {
                        if let Cond::MemNotEqual(target, value) = cond {
                            substs.insert(*target, Expr::Int(*value));
                        }
                    }
                    Node::SeekMemory { target, value, .. } => {
                        substs.insert(*target, Expr::Int(*value));
                    }
                    _ => {}
                }
            }
        }

        let refs: Vec<i32> = children[i]
            .postreferences()
            .unsure
            .iter()
            .filter_map(|x| *x)
            .collect();

        let mut merged = false;
        if alters {
            if let Some(off) = offset {
                if !mergable {
                    backrefs.remove(&off);
                } else if let Some(&target_idx) = backrefs.get(&off) {
                    let used_ok = usedrefs.get(&off).is_none_or(|&u| target_idx >= u);
                    let refs_ok = refs
                        .iter()
                        .all(|ioff| backrefs.get(ioff).is_none_or(|&b| target_idx >= b));

                    if used_ok && refs_ok {
                        let cur_value = if let Node::SetMemory { value, .. } = &children[i] {
                            value.clone()
                        } else {
                            unreachable!()
                        };
                        if let Node::SetMemory {
                            value: target_value,
                            offset: target_off,
                        } = &mut children[target_idx]
                        {
                            let assume = BTreeMap::from([(*target_off, target_value.clone())]);
                            *target_value = cur_value.with_memory(&assume);
                            children[i] = Node::Nop;
                            merged = true;
                        }
                    }
                    if !merged {
                        backrefs.insert(off, i);
                    }
                } else {
                    backrefs.insert(off, i);
                }
            }
        }

        let target = if merged {
            backrefs.get(&offset.unwrap()).copied().unwrap_or(i)
        } else {
            i
        };
        for &ioffset in &refs {
            usedrefs.insert(ioffset, target);
        }

        i += 1;
    }

    cleanup::cleanup(children);
}
