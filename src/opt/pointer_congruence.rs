#![allow(dead_code)]

use crate::math;
use crate::nodes::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PtrCongruence {
    Top,
    Mod { modulus: i32, residue: i32 },
}

const MODULUS_CAP: i32 = 64;

impl PtrCongruence {
    pub fn exact() -> Self {
        PtrCongruence::Mod {
            modulus: 0,
            residue: 0,
        }
    }

    pub fn apply_move(&self, offset: i32) -> PtrCongruence {
        match self {
            PtrCongruence::Top => PtrCongruence::Top,
            PtrCongruence::Mod { modulus, residue } => {
                if *modulus == 0 {
                    PtrCongruence::Mod {
                        modulus: 0,
                        residue: residue + offset,
                    }
                } else {
                    PtrCongruence::Mod {
                        modulus: *modulus,
                        residue: (residue + offset).rem_euclid(*modulus),
                    }
                }
            }
        }
    }

    pub fn apply_seek(&self, seek_stride: i32) -> PtrCongruence {
        if seek_stride == 0 {
            return PtrCongruence::Top;
        }
        match self {
            PtrCongruence::Top => PtrCongruence::Top,
            PtrCongruence::Mod { modulus, residue } => {
                let abs_stride = seek_stride.abs();
                if *modulus == 0 {
                    let new_mod = abs_stride;
                    if new_mod <= 1 || new_mod > MODULUS_CAP {
                        return PtrCongruence::Top;
                    }
                    PtrCongruence::Mod {
                        modulus: new_mod,
                        residue: residue.rem_euclid(new_mod),
                    }
                } else {
                    let new_mod = math::gcd(*modulus, abs_stride);
                    if new_mod > MODULUS_CAP {
                        return PtrCongruence::Top;
                    }
                    if new_mod <= 1 {
                        return PtrCongruence::Top;
                    }
                    PtrCongruence::Mod {
                        modulus: new_mod,
                        residue: residue.rem_euclid(new_mod),
                    }
                }
            }
        }
    }

    pub fn join(&self, other: &PtrCongruence) -> PtrCongruence {
        match (self, other) {
            (PtrCongruence::Top, _) | (_, PtrCongruence::Top) => PtrCongruence::Top,
            (
                PtrCongruence::Mod {
                    modulus: m1,
                    residue: r1,
                },
                PtrCongruence::Mod {
                    modulus: m2,
                    residue: r2,
                },
            ) => {
                if *m1 == 0 && *m2 == 0 {
                    if r1 == r2 {
                        return self.clone();
                    }
                    let diff = (r1 - r2).abs();
                    if diff > MODULUS_CAP {
                        return PtrCongruence::Top;
                    }
                    return PtrCongruence::Mod {
                        modulus: diff,
                        residue: r1.rem_euclid(diff),
                    };
                }
                let g = if *m1 == 0 {
                    *m2
                } else if *m2 == 0 {
                    *m1
                } else {
                    math::gcd(*m1, *m2)
                };
                let diff = (r1 - r2).abs();
                let new_mod = math::gcd(g, diff);
                if new_mod <= 1 || new_mod > MODULUS_CAP {
                    return PtrCongruence::Top;
                }
                PtrCongruence::Mod {
                    modulus: new_mod,
                    residue: r1.rem_euclid(new_mod),
                }
            }
        }
    }
}

pub fn definitely_disjoint(offset_a: i32, offset_b: i32, state: &PtrCongruence) -> bool {
    if offset_a == offset_b {
        return false;
    }
    match state {
        PtrCongruence::Top => false,
        PtrCongruence::Mod { modulus, .. } => {
            if *modulus == 0 {
                true
            } else {
                let diff = (offset_a - offset_b).rem_euclid(*modulus);
                diff != 0
            }
        }
    }
}

pub fn compute_block_congruence(children: &[Node]) -> PtrCongruence {
    let mut state = PtrCongruence::exact();
    for child in children {
        state = apply_node(&state, child);
        if state == PtrCongruence::Top {
            break;
        }
    }
    state
}

fn apply_node(state: &PtrCongruence, node: &Node) -> PtrCongruence {
    match node {
        Node::MovePointer { offset } => state.apply_move(*offset),
        Node::SeekMemory { stride, .. } => state.apply_seek(*stride),
        Node::Nop
        | Node::SetMemory { .. }
        | Node::Input { .. }
        | Node::Output { .. }
        | Node::OutputConst { .. } => state.clone(),
        Node::If { children, .. } => {
            if stride(children) == Some(0) {
                state.clone()
            } else {
                let body_state = compute_body_congruence(state, children);
                state.join(&body_state)
            }
        }
        Node::Repeat { children, .. } | Node::While { children, .. } => {
            if stride(children) == Some(0) {
                state.clone()
            } else {
                let body_state = compute_body_congruence(state, children);
                state.join(&body_state)
            }
        }
        Node::Program { children } => compute_body_congruence(state, children),
    }
}

fn compute_body_congruence(initial: &PtrCongruence, children: &[Node]) -> PtrCongruence {
    let mut state = initial.clone();
    for child in children {
        state = apply_node(&state, child);
    }
    state
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_initial_state() {
        let s = PtrCongruence::exact();
        assert_eq!(
            s,
            PtrCongruence::Mod {
                modulus: 0,
                residue: 0
            }
        );
    }

    #[test]
    fn move_pointer_from_exact() {
        let s = PtrCongruence::exact().apply_move(5);
        assert_eq!(
            s,
            PtrCongruence::Mod {
                modulus: 0,
                residue: 5
            }
        );
    }

    #[test]
    fn move_pointer_preserves_modulus() {
        let s = PtrCongruence::Mod {
            modulus: 3,
            residue: 1,
        };
        let s2 = s.apply_move(2);
        assert_eq!(
            s2,
            PtrCongruence::Mod {
                modulus: 3,
                residue: 0
            }
        );
    }

    #[test]
    fn seek_memory_stride_3_preserves_residue() {
        let s = PtrCongruence::exact().apply_move(1);
        let s2 = s.apply_seek(3);
        assert_eq!(
            s2,
            PtrCongruence::Mod {
                modulus: 3,
                residue: 1
            }
        );
    }

    #[test]
    fn seek_memory_stride_3_from_zero() {
        let s = PtrCongruence::exact();
        let s2 = s.apply_seek(3);
        assert_eq!(
            s2,
            PtrCongruence::Mod {
                modulus: 3,
                residue: 0
            }
        );
    }

    #[test]
    fn seek_memory_negative_stride() {
        let s = PtrCongruence::exact().apply_move(2);
        let s2 = s.apply_seek(-3);
        assert_eq!(
            s2,
            PtrCongruence::Mod {
                modulus: 3,
                residue: 2
            }
        );
    }

    #[test]
    fn seek_from_mod_refines_with_gcd() {
        let s = PtrCongruence::Mod {
            modulus: 6,
            residue: 2,
        };
        let s2 = s.apply_seek(4);
        assert_eq!(
            s2,
            PtrCongruence::Mod {
                modulus: 2,
                residue: 0
            }
        );
    }

    #[test]
    fn seek_stride_zero_is_top() {
        let s = PtrCongruence::exact();
        assert_eq!(s.apply_seek(0), PtrCongruence::Top);
    }

    #[test]
    fn top_stays_top_on_move() {
        assert_eq!(PtrCongruence::Top.apply_move(3), PtrCongruence::Top);
    }

    #[test]
    fn top_stays_top_on_seek() {
        assert_eq!(PtrCongruence::Top.apply_seek(3), PtrCongruence::Top);
    }

    #[test]
    fn disjoint_same_offset_never() {
        let s = PtrCongruence::exact();
        assert!(!definitely_disjoint(0, 0, &s));
    }

    #[test]
    fn disjoint_exact_different_offsets() {
        let s = PtrCongruence::exact();
        assert!(definitely_disjoint(0, 1, &s));
        assert!(definitely_disjoint(3, 7, &s));
    }

    #[test]
    fn disjoint_mod3_different_lanes() {
        let s = PtrCongruence::Mod {
            modulus: 3,
            residue: 0,
        };
        assert!(definitely_disjoint(0, 1, &s));
        assert!(definitely_disjoint(0, 2, &s));
    }

    #[test]
    fn not_disjoint_mod3_same_lane() {
        let s = PtrCongruence::Mod {
            modulus: 3,
            residue: 0,
        };
        assert!(!definitely_disjoint(0, 3, &s));
        assert!(!definitely_disjoint(1, 4, &s));
    }

    #[test]
    fn disjoint_top_is_false() {
        assert!(!definitely_disjoint(0, 1, &PtrCongruence::Top));
    }

    #[test]
    fn move_then_seek_combined() {
        let s = PtrCongruence::exact().apply_move(2).apply_seek(3);
        assert_eq!(
            s,
            PtrCongruence::Mod {
                modulus: 3,
                residue: 2
            }
        );
        assert!(definitely_disjoint(0, 1, &s));
        assert!(!definitely_disjoint(0, 3, &s));
    }

    #[test]
    fn compute_block_basic() {
        let children = vec![
            Node::MovePointer { offset: 1 },
            Node::SeekMemory {
                target: 0,
                stride: 3,
                value: 0,
            },
        ];
        let state = compute_block_congruence(&children);
        assert_eq!(
            state,
            PtrCongruence::Mod {
                modulus: 3,
                residue: 1,
            }
        );
    }

    #[test]
    fn compute_block_set_memory_no_effect() {
        let children = vec![
            Node::SetMemory {
                offset: 0,
                value: crate::expr::Expr::Int(5),
            },
            Node::SeekMemory {
                target: 0,
                stride: 2,
                value: 0,
            },
        ];
        let state = compute_block_congruence(&children);
        assert_eq!(
            state,
            PtrCongruence::Mod {
                modulus: 2,
                residue: 0,
            }
        );
    }

    #[test]
    fn join_exact_states() {
        let a = PtrCongruence::exact().apply_move(3);
        let b = PtrCongruence::exact().apply_move(6);
        let j = a.join(&b);
        assert_eq!(
            j,
            PtrCongruence::Mod {
                modulus: 3,
                residue: 0
            }
        );
    }

    #[test]
    fn join_with_top() {
        let a = PtrCongruence::exact();
        assert_eq!(a.join(&PtrCongruence::Top), PtrCongruence::Top);
    }

    #[test]
    fn if_zero_stride_preserves_state() {
        let children = vec![Node::If {
            cond: crate::cond::Cond::MemNotEqual(0, 0),
            children: vec![Node::SetMemory {
                offset: 0,
                value: crate::expr::Expr::Int(0),
            }],
        }];
        let state = compute_block_congruence(&children);
        assert_eq!(state, PtrCongruence::exact());
    }

    #[test]
    fn seek_stride_1_from_exact_gives_top() {
        let s = PtrCongruence::exact();
        let s2 = s.apply_seek(1);
        assert_eq!(s2, PtrCongruence::Top);
    }

    #[test]
    fn gcd_reduces_modulus() {
        let s = PtrCongruence::Mod {
            modulus: 6,
            residue: 3,
        };
        let s2 = s.apply_seek(9);
        assert_eq!(
            s2,
            PtrCongruence::Mod {
                modulus: 3,
                residue: 0
            }
        );
    }

    #[test]
    fn large_stride_caps_to_top() {
        let s = PtrCongruence::exact();
        let s2 = s.apply_seek(100);
        assert_eq!(s2, PtrCongruence::Top);
    }
}
