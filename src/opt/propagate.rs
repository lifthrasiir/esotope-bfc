use std::collections::BTreeMap;

use crate::cond::*;
use crate::expr::*;
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
        propagate_pass(children, cellsize);
    }
}

fn wrap_value(value: i64, cellsize: u32) -> i64 {
    if cellsize >= 63 {
        value
    } else {
        let modulus = 1i64 << cellsize;
        value.rem_euclid(modulus)
    }
}

fn wrap_to_expr_int(value: i64, cellsize: u32) -> i32 {
    let wrapped = wrap_value(value, cellsize);
    if cellsize == 32 {
        wrapped as u32 as i32
    } else {
        wrapped as i32
    }
}

fn eval_expr(expr: &Expr, known: &BTreeMap<i32, i64>) -> Option<i64> {
    match expr {
        Expr::Int(v) => Some(*v as i64),
        Expr::Reference(offset) => {
            let off = eval_expr(offset, known)?;
            let off = i32::try_from(off).ok()?;
            known.get(&off).copied()
        }
        Expr::Linear(lin) => {
            let mut total = lin.constant as i64;
            for (coeff, term) in &lin.terms {
                total += (*coeff as i64) * eval_expr(term, known)?;
            }
            Some(total)
        }
        Expr::Multiply(factors) => {
            let mut total = 1i64;
            for factor in factors {
                total *= eval_expr(factor, known)?;
            }
            Some(total)
        }
        Expr::Division(lhs, rhs) => {
            let l = eval_expr(lhs, known)?;
            let r = eval_expr(rhs, known)?;
            Some(l.div_euclid(r))
        }
        Expr::ExactDivision(lhs, rhs) => {
            let l = eval_expr(lhs, known)?;
            let r = eval_expr(rhs, known)?;
            if r == 0 || l % r != 0 {
                None
            } else {
                Some(l / r)
            }
        }
        Expr::Modulo(lhs, rhs) => {
            let l = eval_expr(lhs, known)?;
            let r = eval_expr(rhs, known)?;
            Some(l.rem_euclid(r))
        }
    }
}

fn propagate_pass(children: &mut Vec<Node>, cellsize: u32) {
    let mut backrefs: BTreeMap<i32, usize> = BTreeMap::new();
    let mut usedrefs: BTreeMap<i32, usize> = BTreeMap::new();
    let mut substs: BTreeMap<i32, Expr> = BTreeMap::new();
    let mut known_values: BTreeMap<i32, i64> = BTreeMap::new();

    let mut i = 0;
    while i < children.len() {
        let known_output = match &children[i] {
            Node::Output { expr } => {
                eval_expr(expr, &known_values).map(|v| wrap_to_expr_int(v, cellsize))
            }
            _ => None,
        };
        let known_set = match &children[i] {
            Node::SetMemory { offset, value } => eval_expr(value, &known_values).map(|v| {
                (
                    *offset,
                    wrap_value(v, cellsize),
                    wrap_to_expr_int(v, cellsize),
                )
            }),
            _ => None,
        };

        if let Some(value) = known_output {
            children[i] = Node::Output {
                expr: Expr::Int(value),
            };
        } else if let Some((offset, wrapped_i64, wrapped_i32)) = known_set {
            children[i] = Node::SetMemory {
                offset,
                value: Expr::Int(wrapped_i32),
            };
            substs.insert(offset, Expr::Int(wrapped_i32));
            known_values.insert(offset, wrapped_i64);
        } else {
            children[i].with_memory(&substs);
        }

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
                    if let Some(v) = value.to_int() {
                        known_values.insert(o, wrap_value(v as i64, cellsize));
                    } else {
                        known_values.remove(&o);
                    }
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
                    known_values.remove(&o);
                } else {
                    substs.remove(&o);
                    known_values.remove(&o);
                }
            }
            Node::Input { offset: o } => {
                alters = true;
                offset = Some(*o);
                substs.remove(o);
                known_values.remove(o);
            }
            Node::Output { .. } => {}
            _ => {
                backrefs.clear();
                usedrefs.clear();
                substs.clear();
                known_values.clear();
                match &children[i] {
                    Node::While { cond, .. } | Node::If { cond, .. } => {
                        if let Cond::MemNotEqual(target, value) = cond {
                            substs.insert(*target, Expr::Int(*value));
                            known_values.insert(*target, wrap_value(*value as i64, cellsize));
                        }
                    }
                    Node::SeekMemory { target, value, .. } => {
                        substs.insert(*target, Expr::Int(*value));
                        known_values.insert(*target, wrap_value(*value as i64, cellsize));
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
