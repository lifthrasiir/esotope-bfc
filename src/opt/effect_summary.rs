#![allow(dead_code)]

use crate::nodes::*;
use crate::opt::alias_oracle;

#[derive(Clone, Debug)]
pub struct EffectSummary {
    pub stride: Option<i32>,
    pub prereads: CellSet,
    pub postreads: CellSet,
    pub prewrites: CellSet,
    pub postwrites: CellSet,
    pub seek_modulus: Option<i32>,
    pub has_io: bool,
    pub is_pure: bool,
    pub may_not_return: bool,
}

impl EffectSummary {
    pub fn of_body(body: &[Node]) -> Self {
        let s = stride(body);
        let modulus = alias_oracle::body_modulus(body);
        let pure = body.iter().all(Node::is_pure);
        let io = body.iter().any(has_io);
        let no_return = body.iter().any(|n| !n.returns());

        EffectSummary {
            stride: s,
            prereads: body_prereferences(body),
            postreads: body_postreferences(body),
            prewrites: body_preupdates(body),
            postwrites: body_postupdates(body),
            seek_modulus: modulus,
            has_io: io,
            is_pure: pure,
            may_not_return: no_return,
        }
    }

    pub fn has_unknown_prereads(&self) -> bool {
        self.prereads.unsure.contains(&None)
    }

    pub fn has_unknown_postreads(&self) -> bool {
        self.postreads.unsure.contains(&None)
    }

    pub fn has_unknown_prewrites(&self) -> bool {
        self.prewrites.unsure.contains(&None)
    }

    pub fn has_unknown_postwrites(&self) -> bool {
        self.postwrites.unsure.contains(&None)
    }

    pub fn moves_pointer(&self) -> bool {
        self.stride != Some(0)
    }

    pub fn cell_is_disjoint(&self, offset: i32) -> bool {
        match self.seek_modulus {
            Some(m) => alias_oracle::cell_disjoint_from_seek(offset, m),
            None => false,
        }
    }

    pub fn invalidate_env<F>(&self, mut remove_cell: F, mut clear_all: impl FnMut())
    where
        F: FnMut(i32),
    {
        if self.moves_pointer() {
            match self.seek_modulus {
                Some(_) => {}
                None => {
                    clear_all();
                    return;
                }
            }
        }

        for node_updates in self.prewrites.unsure.iter() {
            match node_updates {
                Some(off) => remove_cell(*off),
                None => {
                    if let Some(m) = self.seek_modulus {
                        let _ = m;
                    } else {
                        clear_all();
                        return;
                    }
                }
            }
        }
    }
}

fn has_io(node: &Node) -> bool {
    match node {
        Node::Input { .. } | Node::Output { .. } | Node::OutputConst { .. } => true,
        Node::Program { children }
        | Node::If { children, .. }
        | Node::Repeat { children, .. }
        | Node::While { children, .. } => children.iter().any(has_io),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cond::*;
    use crate::expr::*;

    #[test]
    fn empty_body() {
        let s = EffectSummary::of_body(&[]);
        assert_eq!(s.stride, Some(0));
        assert!(!s.moves_pointer());
        assert!(!s.has_io);
        assert!(s.is_pure);
        assert!(!s.may_not_return);
        assert!(s.seek_modulus.is_none());
    }

    #[test]
    fn simple_set_memory() {
        let body = vec![Node::SetMemory {
            offset: 0,
            value: Expr::Int(5),
        }];
        let s = EffectSummary::of_body(&body);
        assert_eq!(s.stride, Some(0));
        assert!(s.is_pure);
        assert!(!s.has_io);
        assert!(s.prewrites.sure.contains(&Some(0)));
    }

    #[test]
    fn move_pointer_stride() {
        let body = vec![
            Node::adjust_memory_by(0, -1),
            Node::MovePointer { offset: 3 },
        ];
        let s = EffectSummary::of_body(&body);
        assert_eq!(s.stride, Some(3));
        assert!(s.moves_pointer());
    }

    #[test]
    fn seek_memory_stride3() {
        let body = vec![Node::SeekMemory {
            target: 0,
            stride: 3,
            value: 0,
        }];
        let s = EffectSummary::of_body(&body);
        assert_eq!(s.stride, None);
        assert!(s.moves_pointer());
        assert_eq!(s.seek_modulus, Some(3));
        assert!(s.cell_is_disjoint(1));
        assert!(s.cell_is_disjoint(2));
        assert!(!s.cell_is_disjoint(0));
        assert!(!s.cell_is_disjoint(3));
    }

    #[test]
    fn io_detection() {
        let body = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::Output { expr: Expr::mem(0) },
        ];
        let s = EffectSummary::of_body(&body);
        assert!(s.has_io);
        assert!(!s.is_pure);
    }

    #[test]
    fn input_detection() {
        let body = vec![Node::Input { offset: 0 }];
        let s = EffectSummary::of_body(&body);
        assert!(s.has_io);
        assert!(!s.is_pure);
    }

    #[test]
    fn nested_io() {
        let body = vec![Node::If {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![Node::Output { expr: Expr::mem(0) }],
        }];
        let s = EffectSummary::of_body(&body);
        assert!(s.has_io);
        assert!(!s.is_pure);
    }

    #[test]
    fn infinite_loop_may_not_return() {
        let body = vec![Node::While {
            cond: Cond::Always,
            children: vec![],
        }];
        let s = EffectSummary::of_body(&body);
        assert!(s.may_not_return);
    }

    #[test]
    fn normal_while_returns() {
        let body = vec![Node::While {
            cond: Cond::MemNotEqual(0, 0),
            children: vec![Node::adjust_memory_by(0, -1)],
        }];
        let s = EffectSummary::of_body(&body);
        assert!(!s.may_not_return);
    }

    #[test]
    fn unknown_reads_with_seek() {
        let body = vec![Node::SeekMemory {
            target: 0,
            stride: 3,
            value: 0,
        }];
        let s = EffectSummary::of_body(&body);
        assert!(s.has_unknown_prereads());
    }

    #[test]
    fn prereads_include_references() {
        let body = vec![Node::SetMemory {
            offset: 0,
            value: Expr::mem(1) + Expr::mem(2),
        }];
        let s = EffectSummary::of_body(&body);
        assert!(s.prereads.sure.contains(&Some(1)));
        assert!(s.prereads.sure.contains(&Some(2)));
    }

    #[test]
    fn cell_disjoint_no_modulus() {
        let body = vec![Node::MovePointer { offset: 1 }];
        let s = EffectSummary::of_body(&body);
        assert!(!s.cell_is_disjoint(1));
        assert!(!s.cell_is_disjoint(0));
    }

    #[test]
    fn invalidate_env_zero_stride() {
        let body = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::Int(10),
            },
        ];
        let s = EffectSummary::of_body(&body);
        let mut removed = vec![];
        let mut cleared = false;
        s.invalidate_env(|off| removed.push(off), || cleared = true);
        assert!(!cleared);
        assert!(removed.contains(&0));
        assert!(removed.contains(&2));
    }

    #[test]
    fn invalidate_env_with_seek_modulus() {
        let body = vec![Node::SeekMemory {
            target: 0,
            stride: 3,
            value: 0,
        }];
        let s = EffectSummary::of_body(&body);
        let mut cleared = false;
        s.invalidate_env(|_| {}, || cleared = true);
        assert!(!cleared, "should not clear all with seek modulus");
    }

    #[test]
    fn invalidate_env_no_modulus_clears() {
        let body = vec![Node::MovePointer { offset: 1 }];
        let s = EffectSummary::of_body(&body);
        let mut cleared = false;
        s.invalidate_env(|_| {}, || cleared = true);
        assert!(cleared, "should clear all without seek modulus");
    }
}
