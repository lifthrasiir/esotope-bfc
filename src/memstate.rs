use std::collections::{BTreeMap, BTreeSet};

use crate::expr::*;
use crate::nodes::*;

#[derive(Default, Clone)]
#[allow(dead_code)]
pub struct MemoryState {
    memory: BTreeMap<i32, Expr>,
    backrefs: BTreeMap<i32, BTreeSet<i32>>,
}

#[allow(dead_code)]
impl MemoryState {
    pub fn new() -> Self {
        Self::default()
    }

    fn replace(&mut self, offset: i32, expr: &Expr) {
        let Some(affected_set) = self.backrefs.get(&offset).cloned() else {
            return;
        };

        let map = BTreeMap::from([(offset, expr.clone())]);
        for &affected in &affected_set {
            if let Some(val) = self.memory.get(&affected) {
                let new_val = val.with_memory(&map);
                self.memory.insert(affected, new_val);
            }
        }

        let refs = expr.references();
        for r in &refs {
            if let Some(ref_offset) = r.to_int() {
                self.backrefs
                    .entry(ref_offset)
                    .or_default()
                    .extend(&affected_set);
            }
        }
        if !refs.iter().any(|r| r.to_int() == Some(offset)) {
            self.backrefs.remove(&offset);
        }
    }

    pub fn set(&mut self, offset: i32, expr: Expr) -> Vec<Node> {
        let mut flushed = Vec::new();
        let expr = expr.with_memory(&self.memory);
        let has_self_ref = expr.references().iter().any(|r| r.to_int() == Some(offset));

        if has_self_ref {
            if let Some(invexpr) = expr.inverse(offset) {
                self.replace(offset, &invexpr);
            } else if let Some(affected_set) = self.backrefs.remove(&offset) {
                for affected in affected_set {
                    if let Some(val) = self.memory.remove(&affected) {
                        flushed.push(Node::SetMemory {
                            offset: affected,
                            value: val,
                        });
                    }
                }
            }
            flushed.push(Node::SetMemory {
                offset,
                value: expr,
            });
        } else {
            self.replace(offset, &expr);
            let refs = expr.references();
            self.memory.insert(offset, expr);
            for r in &refs {
                if let Some(ref_offset) = r.to_int() {
                    self.backrefs.entry(ref_offset).or_default().insert(offset);
                }
            }
        }

        flushed
    }

    pub fn nodes(&self) -> Vec<Node> {
        self.memory
            .iter()
            .map(|(&offset, value)| Node::SetMemory {
                offset,
                value: value.clone(),
            })
            .collect()
    }

    pub fn flush(&mut self) -> Vec<Node> {
        let flushed = self.nodes();
        self.clear();
        flushed
    }

    pub fn clear(&mut self) {
        self.memory.clear();
        self.backrefs.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_empty() {
        let ms = MemoryState::new();
        assert!(ms.memory.is_empty());
        assert!(ms.backrefs.is_empty());
    }

    #[test]
    fn set_simple_value() {
        let mut ms = MemoryState::new();
        let flushed = ms.set(0, Expr::Int(42));
        assert!(flushed.is_empty());
        assert_eq!(ms.memory.get(&0), Some(&Expr::Int(42)));
    }

    #[test]
    fn set_propagates_substitution() {
        let mut ms = MemoryState::new();
        ms.set(0, Expr::Int(10));
        // set {1} = {0} should substitute to {1} = 10
        let flushed = ms.set(1, Expr::mem(0));
        assert!(flushed.is_empty());
        assert_eq!(ms.memory.get(&1), Some(&Expr::Int(10)));
    }

    #[test]
    fn set_self_referencing_invertible() {
        let mut ms = MemoryState::new();
        // Set {0} = {0} + 5 on empty state: self-ref, produces a flush
        let flushed = ms.set(0, Expr::mem(0) + Expr::Int(5));
        // Self-referencing always produces a SetMemory in flushed output
        assert!(!flushed.is_empty());
        assert!(flushed.iter().all(|n| matches!(n, Node::SetMemory { .. })));
    }

    #[test]
    fn flush_returns_all_and_clears() {
        let mut ms = MemoryState::new();
        ms.set(0, Expr::Int(1));
        ms.set(1, Expr::Int(2));
        let flushed = ms.flush();
        assert_eq!(flushed.len(), 2);
        assert!(ms.memory.is_empty());
    }

    #[test]
    fn clear_empties_state() {
        let mut ms = MemoryState::new();
        ms.set(0, Expr::Int(42));
        ms.clear();
        assert!(ms.memory.is_empty());
        assert!(ms.backrefs.is_empty());
    }

    #[test]
    fn nodes_snapshot() {
        let mut ms = MemoryState::new();
        ms.set(0, Expr::Int(42));
        let nodes = ms.nodes();
        assert_eq!(nodes.len(), 1);
        assert!(
            matches!(&nodes[0], Node::SetMemory { offset: 0, value } if *value == Expr::Int(42))
        );
    }

    #[test]
    fn clone_is_independent() {
        let mut ms = MemoryState::new();
        ms.set(0, Expr::Int(42));
        let ms2 = ms.clone();
        ms.clear();
        assert!(ms.memory.is_empty());
        assert_eq!(ms2.memory.get(&0), Some(&Expr::Int(42)));
    }
}
