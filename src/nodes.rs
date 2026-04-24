use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt;

use crate::cond::*;
use crate::expr::*;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct CellSet {
    pub sure: BTreeSet<Option<i32>>,
    pub unsure: BTreeSet<Option<i32>>,
}

impl CellSet {
    pub fn new() -> Self {
        CellSet::default()
    }

    pub fn with_sure(sure: impl IntoIterator<Item = Option<i32>>) -> Self {
        let sure_set: BTreeSet<Option<i32>> = sure.into_iter().collect();
        let unsure_set = sure_set.clone();
        CellSet {
            sure: sure_set,
            unsure: unsure_set,
        }
    }

    pub fn from_refs(refs: &BTreeSet<Expr>) -> Self {
        let items: BTreeSet<Option<i32>> = refs.iter().map(|e| e.to_int()).collect();
        CellSet {
            sure: items.clone(),
            unsure: items,
        }
    }

    pub fn with_sure_unsure(sure: BTreeSet<Option<i32>>, unsure: BTreeSet<Option<i32>>) -> Self {
        let mut u = unsure;
        u.extend(&sure);
        CellSet { sure, unsure: u }
    }

    pub fn add_sure(&mut self, item: Option<i32>) {
        self.sure.insert(item);
        self.unsure.insert(item);
    }

    pub fn add_unsure(&mut self, item: Option<i32>) {
        self.unsure.insert(item);
    }

    pub fn update_sure(&mut self, items: impl IntoIterator<Item = Option<i32>>) {
        for item in items {
            self.sure.insert(item);
            self.unsure.insert(item);
        }
    }

    pub fn update_unsure(&mut self, items: impl IntoIterator<Item = Option<i32>>) {
        self.unsure.extend(items);
    }

    pub fn union_assign(&mut self, other: &CellSet) {
        self.sure.extend(&other.sure);
        self.unsure.extend(&other.unsure);
    }

    pub fn move_pointer(&self, offset: i32) -> CellSet {
        if offset == 0 {
            return self.clone();
        }
        let shift = |i: &Option<i32>| i.map(|v| v + offset);
        CellSet {
            sure: self.sure.iter().map(shift).collect(),
            unsure: self.unsure.iter().map(shift).collect(),
        }
    }
}

fn set_move_pointer(cells: &BTreeSet<Option<i32>>, offset: i32) -> BTreeSet<Option<i32>> {
    cells.iter().map(|i| i.map(|v| v + offset)).collect()
}

fn refs_to_opts(refs: &BTreeSet<Expr>) -> BTreeSet<Option<i32>> {
    refs.iter().map(|e| e.to_int()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- CellSet tests ---

    #[test]
    fn cellset_new_empty() {
        let cs = CellSet::new();
        assert!(cs.sure.is_empty());
        assert!(cs.unsure.is_empty());
    }

    #[test]
    fn cellset_with_sure() {
        let cs = CellSet::with_sure([Some(0), Some(1)]);
        assert!(cs.sure.contains(&Some(0)));
        assert!(cs.sure.contains(&Some(1)));
        assert_eq!(cs.sure, cs.unsure);
    }

    #[test]
    fn cellset_add_sure_adds_both() {
        let mut cs = CellSet::new();
        cs.add_sure(Some(5));
        assert!(cs.sure.contains(&Some(5)));
        assert!(cs.unsure.contains(&Some(5)));
    }

    #[test]
    fn cellset_add_unsure_only_unsure() {
        let mut cs = CellSet::new();
        cs.add_unsure(Some(5));
        assert!(!cs.sure.contains(&Some(5)));
        assert!(cs.unsure.contains(&Some(5)));
    }

    #[test]
    fn cellset_move_pointer() {
        let cs = CellSet::with_sure([Some(0), Some(3), None]);
        let moved = cs.move_pointer(2);
        assert!(moved.sure.contains(&Some(2)));
        assert!(moved.sure.contains(&Some(5)));
        assert!(moved.sure.contains(&None)); // None stays None
    }

    #[test]
    fn cellset_move_pointer_zero_unchanged() {
        let cs = CellSet::with_sure([Some(0)]);
        let moved = cs.move_pointer(0);
        assert_eq!(cs, moved);
    }

    #[test]
    fn cellset_union_assign() {
        let mut a = CellSet::with_sure([Some(0)]);
        let b = CellSet::with_sure([Some(1)]);
        a.union_assign(&b);
        assert!(a.sure.contains(&Some(0)));
        assert!(a.sure.contains(&Some(1)));
    }

    #[test]
    fn cellset_from_refs() {
        let mut refs = BTreeSet::new();
        refs.insert(Expr::Int(0));
        refs.insert(Expr::Int(3));
        let cs = CellSet::from_refs(&refs);
        assert!(cs.sure.contains(&Some(0)));
        assert!(cs.sure.contains(&Some(3)));
    }

    // --- Node construction tests ---

    #[test]
    fn nop_is_nop() {
        assert!(Node::Nop.is_nop());
    }

    #[test]
    fn set_memory_identity_is_nop() {
        // {0} = {0} is a no-op
        let n = Node::SetMemory {
            offset: 0,
            value: Expr::mem(0),
        };
        assert!(n.is_nop());
    }

    #[test]
    fn set_memory_nonidentity_not_nop() {
        let n = Node::SetMemory {
            offset: 0,
            value: Expr::Int(5),
        };
        assert!(!n.is_nop());
    }

    #[test]
    fn move_pointer_zero_is_nop() {
        assert!(Node::MovePointer { offset: 0 }.is_nop());
    }

    #[test]
    fn move_pointer_nonzero_not_nop() {
        assert!(!Node::MovePointer { offset: 3 }.is_nop());
    }

    #[test]
    fn adjust_memory_by() {
        let n = Node::adjust_memory_by(0, 5);
        match &n {
            Node::SetMemory { offset, value } => {
                assert_eq!(*offset, 0);
                assert_eq!(*value, Expr::mem(0) + Expr::Int(5));
            }
            _ => panic!("expected SetMemory"),
        }
    }

    #[test]
    fn output_const_empty_is_nop() {
        assert!(Node::OutputConst { s: vec![] }.is_nop());
    }

    #[test]
    fn is_pure() {
        assert!(Node::Nop.is_pure());
        assert!(Node::SetMemory {
            offset: 0,
            value: Expr::Int(0)
        }
        .is_pure());
        assert!(Node::MovePointer { offset: 1 }.is_pure());
        assert!(!Node::Input { offset: 0 }.is_pure());
        assert!(!Node::Output {
            expr: Expr::Int(65)
        }
        .is_pure());
        assert!(!Node::OutputConst { s: vec![65] }.is_pure());
    }

    #[test]
    fn returns_basic() {
        assert!(Node::Nop.returns());
        assert!(Node::SetMemory {
            offset: 0,
            value: Expr::Int(0)
        }
        .returns());
        // Infinite loop doesn't return
        let inf = Node::While {
            cond: Cond::Always,
            children: vec![],
        };
        assert!(!inf.returns());
        // Normal while returns
        let w = Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![],
        };
        assert!(w.returns());
    }

    #[test]
    fn offsets_basic() {
        assert_eq!(Node::Nop.offsets(), Some(0));
        assert_eq!(Node::MovePointer { offset: 5 }.offsets(), Some(5));
        assert_eq!(
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(0)
            }
            .offsets(),
            Some(0)
        );
        assert_eq!(
            Node::SeekMemory {
                target: 0,
                stride: 1,
                value: 0
            }
            .offsets(),
            None
        );
    }

    #[test]
    fn get_delta() {
        let n = Node::SetMemory {
            offset: 0,
            value: Expr::mem(0) + Expr::Int(3),
        };
        assert_eq!(n.get_delta(), Expr::Int(3));
    }

    #[test]
    fn move_pointer_set_memory() {
        let mut n = Node::SetMemory {
            offset: 0,
            value: Expr::mem(0) + Expr::Int(1),
        };
        n.move_pointer(3);
        match &n {
            Node::SetMemory { offset, value } => {
                assert_eq!(*offset, 3);
                assert_eq!(*value, Expr::mem(3) + Expr::Int(1));
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn move_pointer_zero_noop() {
        let n = Node::SetMemory {
            offset: 5,
            value: Expr::mem(5),
        };
        let mut n2 = n.clone();
        n2.move_pointer(0);
        assert_eq!(n, n2);
    }

    #[test]
    fn children_mut_on_complex() {
        let mut prog = Node::Program {
            children: vec![Node::Nop],
        };
        assert!(prog.children_mut().is_some());
        assert!(Node::Nop.children_mut().is_none());
    }

    // --- stride tests ---

    #[test]
    fn stride_empty() {
        assert_eq!(stride(&[]), Some(0));
    }

    #[test]
    fn stride_single_move() {
        let nodes = vec![Node::MovePointer { offset: 3 }];
        assert_eq!(stride(&nodes), Some(3));
    }

    #[test]
    fn stride_with_set_memory() {
        let nodes = vec![
            Node::adjust_memory_by(0, 1),
            Node::MovePointer { offset: 2 },
        ];
        assert_eq!(stride(&nodes), Some(2));
    }

    #[test]
    fn stride_with_seek_is_none() {
        let nodes = vec![Node::SeekMemory {
            target: 0,
            stride: 1,
            value: 0,
        }];
        assert_eq!(stride(&nodes), None);
    }

    // --- prereferences / preupdates tests ---

    #[test]
    fn prereferences_set_memory() {
        let n = Node::SetMemory {
            offset: 0,
            value: Expr::mem(1) + Expr::mem(2),
        };
        let refs = n.prereferences();
        assert!(refs.sure.contains(&Some(1)));
        assert!(refs.sure.contains(&Some(2)));
    }

    #[test]
    fn preupdates_set_memory() {
        let n = Node::SetMemory {
            offset: 5,
            value: Expr::Int(0),
        };
        let upd = n.preupdates();
        assert!(upd.sure.contains(&Some(5)));
    }

    #[test]
    fn preupdates_input() {
        let n = Node::Input { offset: 3 };
        let upd = n.preupdates();
        assert!(upd.sure.contains(&Some(3)));
    }

    // --- compactrepr tests ---

    #[test]
    fn display_nop() {
        assert_eq!(Node::Nop.to_string(), "Nop[]");
    }

    #[test]
    fn display_move_pointer() {
        assert_eq!(
            Node::MovePointer { offset: 3 }.to_string(),
            "MovePointer[3]"
        );
    }

    #[test]
    fn display_input() {
        assert_eq!(Node::Input { offset: 0 }.to_string(), "{0}=Input[]");
    }

    #[test]
    fn display_trait() {
        assert_eq!(format!("{}", Node::Nop), "Nop[]");
    }

    // --- with_memory tests ---

    #[test]
    fn with_memory_set_memory() {
        let mut n = Node::SetMemory {
            offset: 0,
            value: Expr::mem(1),
        };
        let map = BTreeMap::from([(1, Expr::Int(42))]);
        n.with_memory(&map);
        assert_eq!(
            n,
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(42)
            }
        );
    }

    #[test]
    fn with_memory_while_never() {
        // While condition becomes Never -> condition updated
        let mut n = Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![],
        };
        let map = BTreeMap::from([(0, Expr::Int(0))]);
        n.with_memory(&map);
        match &n {
            Node::While { cond, .. } => assert!(cond.is_never()),
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn with_memory_while_not_never_unchanged() {
        let mut n = Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![],
        };
        let map = BTreeMap::from([(0, Expr::Int(5))]);
        n.with_memory(&map);
        // Condition evaluates to Always, but While only updates if Never
        match &n {
            Node::While { cond, .. } => assert!(!cond.is_never()),
            _ => panic!("wrong variant"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Nop,
    SetMemory {
        offset: i32,
        value: Expr,
    },
    MovePointer {
        offset: i32,
    },
    Input {
        offset: i32,
    },
    Output {
        expr: Expr,
    },
    OutputConst {
        s: Vec<u8>,
    },
    SeekMemory {
        target: i32,
        stride: i32,
        value: i32,
    },
    Program {
        children: Vec<Node>,
    },
    If {
        cond: Cond,
        children: Vec<Node>,
    },
    Repeat {
        count: Expr,
        children: Vec<Node>,
    },
    While {
        cond: Cond,
        children: Vec<Node>,
    },
}

impl Node {
    pub fn adjust_memory(offset: i32, delta: Expr) -> Self {
        Node::SetMemory {
            offset,
            value: Expr::mem(offset) + delta,
        }
    }

    pub fn adjust_memory_by(offset: i32, delta: i32) -> Self {
        Self::adjust_memory(offset, Expr::Int(delta))
    }

    pub fn is_nop(&self) -> bool {
        match self {
            Node::Nop => true,
            Node::SetMemory { offset, value } => *value == Expr::mem(*offset),
            Node::MovePointer { offset } => *offset == 0,
            Node::If { cond, children } => cond.is_never() || children.is_empty(),
            Node::Repeat { count, children } => !count.is_nonzero() || children.is_empty(),
            Node::While { cond, .. } => cond.is_never(),
            Node::OutputConst { s } => s.is_empty(),
            _ => false,
        }
    }

    pub fn is_pure(&self) -> bool {
        match self {
            Node::Input { .. } | Node::Output { .. } | Node::OutputConst { .. } => false,
            Node::Program { children }
            | Node::If { children, .. }
            | Node::Repeat { children, .. }
            | Node::While { children, .. } => children.iter().all(Node::is_pure),
            _ => true,
        }
    }

    pub fn returns(&self) -> bool {
        !matches!(
            self,
            Node::While {
                cond: Cond::Always,
                ..
            }
        )
    }

    pub fn offsets(&self) -> Option<i32> {
        match self {
            Node::MovePointer { offset } => Some(*offset),
            Node::SeekMemory { .. } => None,
            Node::If { children, .. }
            | Node::Repeat { children, .. }
            | Node::While { children, .. } => {
                if stride(children) == Some(0) {
                    Some(0)
                } else {
                    None
                }
            }
            _ => Some(0),
        }
    }

    pub fn move_pointer(&mut self, offset: i32) {
        if offset == 0 {
            return;
        }
        match self {
            Node::Nop | Node::MovePointer { .. } | Node::OutputConst { .. } => {}
            Node::SetMemory { offset: o, value } => {
                *o += offset;
                *value = value.move_pointer(offset);
            }
            Node::Input { offset: o } | Node::SeekMemory { target: o, .. } => {
                *o += offset;
            }
            Node::Output { expr } => {
                *expr = expr.move_pointer(offset);
            }
            Node::Program { children } => {
                for child in children {
                    child.move_pointer(offset);
                }
            }
            Node::If { cond, children } | Node::While { cond, children } => {
                for child in children.iter_mut() {
                    child.move_pointer(offset);
                }
                *cond = cond.move_pointer(offset);
            }
            Node::Repeat { count, children } => {
                for child in children.iter_mut() {
                    child.move_pointer(offset);
                }
                *count = count.move_pointer(offset);
            }
        }
    }

    pub fn with_memory(&mut self, map: &BTreeMap<i32, Expr>) {
        match self {
            Node::SetMemory { value, .. } => *value = value.with_memory(map),
            Node::Output { expr } => *expr = expr.with_memory(map),
            Node::If { cond, .. } => *cond = cond.with_memory(map),
            Node::While { cond, .. } => {
                let newcond = cond.with_memory(map);
                if newcond.is_never() {
                    *cond = newcond;
                }
            }
            Node::Repeat { count, .. } => *count = count.with_memory(map),
            _ => {}
        }
    }

    #[cfg(test)]
    pub fn get_delta(&self) -> Expr {
        match self {
            Node::SetMemory { offset, value } => value - &Expr::mem(*offset),
            _ => panic!("get_delta on non-SetMemory"),
        }
    }

    pub fn children_mut(&mut self) -> Option<&mut Vec<Node>> {
        match self {
            Node::Program { children }
            | Node::If { children, .. }
            | Node::Repeat { children, .. }
            | Node::While { children, .. } => Some(children),
            _ => None,
        }
    }

    pub fn prereferences(&self) -> CellSet {
        match self {
            Node::SetMemory { value, .. } => CellSet::from_refs(&value.references()),
            Node::Output { expr } => CellSet::from_refs(&expr.references()),
            Node::SeekMemory { target, .. } => {
                let mut cs = CellSet::with_sure([Some(*target)]);
                cs.unsure.insert(None);
                cs
            }
            Node::If { cond, children, .. } => {
                let mut cs = CellSet::from_refs(&cond.references());
                cs.update_unsure(body_prereferences(children).unsure);
                cs
            }
            Node::Repeat {
                count, children, ..
            } => {
                let mut cs = CellSet::from_refs(&count.references());
                cs.update_unsure(body_prereferences(children).unsure);
                if stride(children) != Some(0) {
                    cs.add_unsure(None);
                }
                cs
            }
            Node::While { cond, children, .. } => {
                let mut cs = CellSet::from_refs(&cond.references());
                cs.update_unsure(body_prereferences(children).unsure);
                if stride(children) != Some(0) {
                    cs.add_unsure(None);
                }
                cs
            }
            _ => CellSet::new(),
        }
    }

    pub fn postreferences(&self) -> CellSet {
        match self {
            Node::SetMemory { value, .. } => CellSet::from_refs(&value.references()),
            Node::Output { expr } => CellSet::from_refs(&expr.references()),
            Node::SeekMemory { target, .. } => {
                let mut cs = CellSet::with_sure([Some(*target)]);
                cs.unsure.insert(None);
                cs
            }
            Node::If { cond, children, .. } => {
                let mut bodyrefs = CellSet::new();
                bodyrefs.update_unsure(body_postreferences(children).unsure);
                if let Some(s) = stride(children) {
                    bodyrefs.update_sure(set_move_pointer(&refs_to_opts(&cond.references()), -s));
                } else {
                    bodyrefs.add_sure(None);
                }
                bodyrefs
            }
            Node::Repeat {
                count, children, ..
            } => {
                let mut bodyrefs = CellSet::new();
                bodyrefs.update_unsure(body_postreferences(children).unsure);
                if let Some(s) = stride(children) {
                    bodyrefs.update_sure(set_move_pointer(&refs_to_opts(&count.references()), -s));
                }
                if stride(children) != Some(0) {
                    bodyrefs.add_unsure(None);
                }
                bodyrefs
            }
            Node::While { cond, children, .. } => {
                let mut bodyrefs = CellSet::from_refs(&cond.references());
                bodyrefs.update_unsure(body_postreferences(children).unsure);
                if stride(children) != Some(0) {
                    bodyrefs.add_unsure(None);
                }
                bodyrefs
            }
            _ => CellSet::new(),
        }
    }

    pub fn preupdates(&self) -> CellSet {
        match self {
            Node::SetMemory { offset, .. } | Node::Input { offset } => {
                CellSet::with_sure([Some(*offset)])
            }
            Node::If { children, .. } => {
                CellSet::with_sure_unsure(BTreeSet::new(), body_preupdates(children).unsure)
            }
            Node::Repeat { children, .. } | Node::While { children, .. } => {
                let mut cs = CellSet::new();
                cs.update_unsure(body_preupdates(children).unsure);
                if stride(children) != Some(0) {
                    cs.add_unsure(None);
                }
                cs
            }
            _ => CellSet::new(),
        }
    }

    pub fn postupdates(&self) -> CellSet {
        match self {
            Node::SetMemory { offset, .. } | Node::Input { offset } => {
                CellSet::with_sure([Some(*offset)])
            }
            Node::If { children, .. } => {
                CellSet::with_sure_unsure(BTreeSet::new(), body_postupdates(children).unsure)
            }
            Node::Repeat { children, .. } | Node::While { children, .. } => {
                let mut cs = CellSet::new();
                cs.update_unsure(body_postupdates(children).unsure);
                if stride(children) != Some(0) {
                    cs.add_unsure(None);
                }
                cs
            }
            _ => CellSet::new(),
        }
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Nop => f.write_str("Nop[]"),
            Node::SetMemory { offset, value } => {
                let ce = CompactExpr(value, 0);
                let delta = value - &Expr::mem(*offset);
                let ds = CompactExpr(&delta, 0).to_string();
                let short = if let Some(rest) = ds.strip_prefix('-') {
                    format!("{{{offset}}}-={rest}")
                } else {
                    format!("{{{offset}}}+={ds}")
                };
                let full = format!("{{{offset}}}={ce}");
                if short.len() < full.len() {
                    f.write_str(&short)
                } else {
                    f.write_str(&full)
                }
            }
            Node::MovePointer { offset } => write!(f, "MovePointer[{offset}]"),
            Node::Input { offset } => write!(f, "{{{offset}}}=Input[]"),
            Node::Output { expr } => write!(f, "Output[{}]", CompactExpr(expr, 0)),
            Node::OutputConst { s } => {
                write!(f, "OutputConst[{:?}]", String::from_utf8_lossy(s))
            }
            Node::SeekMemory {
                target,
                stride,
                value,
            } => {
                if *target == 0 {
                    write!(f, "SeekMemory[{{{stride}*k}}!={value}]")
                } else if *stride < 0 {
                    write!(f, "SeekMemory[{{{target}-{}*k}}!={value}]", -stride)
                } else {
                    write!(f, "SeekMemory[{{{target}+{stride}*k}}!={value}]")
                }
            }
            Node::Program { children } => {
                f.write_str("Program[")?;
                write_children(f, children)?;
                f.write_str("]")
            }
            Node::If { cond, children } => {
                write!(f, "If[{}; ", CompactCond(cond, 0))?;
                write_children(f, children)?;
                f.write_str("]")
            }
            Node::Repeat { count, children } => {
                write!(f, "Repeat[{}; ", CompactExpr(count, 0))?;
                write_children(f, children)?;
                f.write_str("]")
            }
            Node::While { cond, children } => {
                write!(f, "While[{}; ", CompactCond(cond, 0))?;
                write_children(f, children)?;
                f.write_str("]")
            }
        }
    }
}

fn write_children(f: &mut fmt::Formatter<'_>, children: &[Node]) -> fmt::Result {
    for (i, child) in children.iter().enumerate() {
        if i > 0 {
            f.write_str(", ")?;
        }
        write!(f, "{child}")?;
    }
    Ok(())
}

pub fn stride(children: &[Node]) -> Option<i32> {
    children
        .iter()
        .try_fold(0i32, |acc, child| child.offsets().map(|o| acc + o))
}

pub fn body_prereferences(children: &[Node]) -> CellSet {
    let mut offsets = 0i32;
    let mut refs = CellSet::new();
    for child in children {
        refs.union_assign(&child.prereferences().move_pointer(offsets));
        match child.offsets() {
            Some(o) => offsets += o,
            None => {
                refs.add_sure(None);
                break;
            }
        }
    }
    refs
}

pub fn body_preupdates(children: &[Node]) -> CellSet {
    let mut offsets = 0i32;
    let mut updates = CellSet::new();
    for child in children {
        updates.union_assign(&child.preupdates().move_pointer(offsets));
        match child.offsets() {
            Some(o) => offsets += o,
            None => {
                updates.add_sure(None);
                break;
            }
        }
    }
    updates
}

pub fn body_postreferences(children: &[Node]) -> CellSet {
    let mut offsets = 0i32;
    let mut refs = CellSet::new();
    for child in children.iter().rev() {
        match child.offsets() {
            Some(o) => offsets -= o,
            None => {
                refs.add_sure(None);
                break;
            }
        }
        refs.union_assign(&child.postreferences().move_pointer(offsets));
    }
    refs
}

pub fn body_postupdates(children: &[Node]) -> CellSet {
    let mut offsets = 0i32;
    let mut updates = CellSet::new();
    for child in children.iter().rev() {
        match child.offsets() {
            Some(o) => offsets -= o,
            None => {
                updates.add_sure(None);
                break;
            }
        }
        updates.union_assign(&child.postupdates().move_pointer(offsets));
    }
    updates
}
