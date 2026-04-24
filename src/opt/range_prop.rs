use std::collections::BTreeMap;

use crate::cond::*;
use crate::expr::*;
use crate::math::gcd;
use crate::nodes::*;
use crate::opt::cleanup;

#[derive(Clone, Debug, PartialEq)]
enum CellValue {
    Const(i32),
    Mod(i32, i32), // value ≡ residue (mod modulus), modulus >= 2, 0 <= residue < modulus
}

type Env = BTreeMap<i32, CellValue>;

fn mem_offset(expr: &Expr) -> Option<i32> {
    if let Expr::Reference(inner) = expr {
        inner.to_int()
    } else {
        None
    }
}

pub fn transform(node: &mut Node) {
    if let Some(children) = node.children_mut() {
        range_prop_block(children, &Env::new());
    }
}

fn env_to_substs(env: &Env) -> BTreeMap<i32, Expr> {
    env.iter()
        .filter_map(|(&k, v)| match v {
            CellValue::Const(c) => Some((k, Expr::Int(*c))),
            _ => None,
        })
        .collect()
}

fn derive_cell_value(expr: &Expr, env: &Env) -> Option<CellValue> {
    if let Some(c) = expr.to_int() {
        return Some(CellValue::Const(c));
    }

    match expr {
        Expr::Reference(inner) => {
            if let Some(off) = inner.to_int() {
                return env.get(&off).cloned();
            }
            None
        }
        Expr::Linear(lin) => {
            let mut overall_mod: i32 = 0;
            let mut overall_residue: i64 = lin.constant as i64;

            for (coeff, term) in &lin.terms {
                let abs_coeff = coeff.abs();

                if let Some(off) = mem_offset(term) {
                    match env.get(&off) {
                        Some(CellValue::Const(c)) => {
                            overall_residue += *coeff as i64 * *c as i64;
                            continue;
                        }
                        Some(CellValue::Mod(m, r)) => {
                            let term_mod = abs_coeff * m;
                            overall_residue += *coeff as i64 * *r as i64;
                            overall_mod = if overall_mod == 0 {
                                term_mod
                            } else {
                                gcd(overall_mod, term_mod)
                            };
                        }
                        None => {
                            if abs_coeff <= 1 {
                                return None;
                            }
                            overall_mod = if overall_mod == 0 {
                                abs_coeff
                            } else {
                                gcd(overall_mod, abs_coeff)
                            };
                        }
                    }
                } else {
                    if abs_coeff <= 1 {
                        return None;
                    }
                    overall_mod = if overall_mod == 0 {
                        abs_coeff
                    } else {
                        gcd(overall_mod, abs_coeff)
                    };
                }
            }

            if overall_mod == 0 {
                return Some(CellValue::Const(overall_residue as i32));
            }

            if overall_mod >= 2 {
                let r = (overall_residue.rem_euclid(overall_mod as i64)) as i32;
                Some(CellValue::Mod(overall_mod, r))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn simplify_cond_with_env(cond: &mut Cond, env: &Env) {
    match cond {
        Cond::MemEqual(t, v) => {
            if let Some(CellValue::Mod(m, r)) = env.get(t) {
                if v.rem_euclid(*m) != *r {
                    *cond = Cond::Never;
                }
            }
        }
        Cond::MemNotEqual(t, v) => {
            if let Some(CellValue::Mod(m, r)) = env.get(t) {
                if v.rem_euclid(*m) != *r {
                    *cond = Cond::Always;
                }
            }
        }
        Cond::Equal(expr, v) => {
            if let Some(off) = mem_offset(expr) {
                if let Some(CellValue::Mod(m, r)) = env.get(&off) {
                    if v.rem_euclid(*m) != *r {
                        *cond = Cond::Never;
                    }
                }
            }
        }
        Cond::NotEqual(expr, v) => {
            if let Some(off) = mem_offset(expr) {
                if let Some(CellValue::Mod(m, r)) = env.get(&off) {
                    if v.rem_euclid(*m) != *r {
                        *cond = Cond::Always;
                    }
                }
            }
        }
        _ => {}
    }
}

fn merge_cell_value(a: &CellValue, b: &CellValue) -> Option<CellValue> {
    match (a, b) {
        (CellValue::Const(x), CellValue::Const(y)) if x == y => Some(CellValue::Const(*x)),
        (CellValue::Const(x), CellValue::Mod(m, r)) | (CellValue::Mod(m, r), CellValue::Const(x)) => {
            if x.rem_euclid(*m) == *r {
                Some(CellValue::Mod(*m, *r))
            } else {
                None
            }
        }
        (CellValue::Mod(m1, r1), CellValue::Mod(m2, r2)) => {
            let g = gcd(*m1, *m2);
            if g >= 2 && r1.rem_euclid(g) == r2.rem_euclid(g) {
                Some(CellValue::Mod(g, r1.rem_euclid(g)))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn merge_envs(a: &Env, b: &Env) -> Env {
    let mut result = Env::new();
    for (k, va) in a {
        if let Some(vb) = b.get(k) {
            if let Some(merged) = merge_cell_value(va, vb) {
                result.insert(*k, merged);
            }
        }
    }
    result
}

fn refine_env(env: &mut Env, cond: &Cond) {
    match cond {
        Cond::MemEqual(t, v) => {
            env.insert(*t, CellValue::Const(*v));
        }
        Cond::Conjunction(clauses) => {
            for c in clauses {
                refine_env(env, c);
            }
        }
        _ => {}
    }
}

fn refine_env_false(env: &mut Env, cond: &Cond) {
    match cond {
        Cond::MemNotEqual(t, v) => {
            env.insert(*t, CellValue::Const(*v));
        }
        Cond::MemEqual(t, v) => {
            if let Some(CellValue::Const(c)) = env.get(t) {
                if *c == *v {
                    env.remove(t);
                }
            }
        }
        Cond::Disjunction(clauses) => {
            for c in clauses {
                refine_env_false(env, c);
            }
        }
        _ => {}
    }
}

fn invalidate_env_for_body(env: &mut Env, body: &[Node]) {
    for node in body {
        let updates = node.preupdates();
        if updates.unsure.contains(&None) {
            env.clear();
            return;
        }
        for opt in &updates.unsure {
            if let Some(off) = opt {
                env.remove(off);
            }
        }
    }
}

fn update_env_from_body(env: &mut Env, body: &[Node]) {
    for node in body {
        match node {
            Node::SetMemory { offset, value } => {
                if let Some(cv) = derive_cell_value(value, env) {
                    env.insert(*offset, cv);
                } else {
                    env.remove(offset);
                }
            }
            Node::Input { offset } => {
                env.remove(offset);
            }
            _ => {
                let updates = node.preupdates();
                if updates.unsure.contains(&None) {
                    env.clear();
                    return;
                }
                for opt in &updates.unsure {
                    if let Some(off) = opt {
                        env.remove(off);
                    }
                }
            }
        }
    }
}

fn range_prop_block(children: &mut Vec<Node>, initial_env: &Env) {
    let mut env = initial_env.clone();

    for i in 0..children.len() {
        let mut node = std::mem::replace(&mut children[i], Node::Nop);

        match &mut node {
            Node::Nop | Node::OutputConst { .. } | Node::MovePointer { .. } => {}

            Node::SetMemory { offset, value } => {
                let substs = env_to_substs(&env);
                if !substs.is_empty() {
                    *value = value.with_memory(&substs);
                }
                if let Some(cv) = derive_cell_value(value, &env) {
                    env.insert(*offset, cv);
                } else {
                    env.remove(offset);
                }
            }

            Node::Input { offset } => {
                env.remove(offset);
            }

            Node::Output { expr } => {
                let substs = env_to_substs(&env);
                if !substs.is_empty() {
                    *expr = expr.with_memory(&substs);
                }
            }

            Node::If { cond, children: body } => {
                let substs = env_to_substs(&env);
                if !substs.is_empty() {
                    *cond = cond.with_memory(&substs);
                }
                simplify_cond_with_env(cond, &env);

                if cond.is_never() {
                    // Dead branch — cleanup will remove
                } else if cond.is_always() {
                    range_prop_block(body, &env);
                    update_env_from_body(&mut env, body);
                } else {
                    let mut true_env = env.clone();
                    refine_env(&mut true_env, cond);
                    range_prop_block(body, &true_env);
                    update_env_from_body(&mut true_env, body);

                    let mut false_env = env.clone();
                    refine_env_false(&mut false_env, cond);

                    env = merge_envs(&true_env, &false_env);
                }
            }

            Node::While { cond, children: body } => {
                let substs = env_to_substs(&env);
                if !substs.is_empty() {
                    let eval = cond.with_memory(&substs);
                    if eval.is_never() {
                        *cond = Cond::Never;
                    }
                }

                if !cond.is_never() {
                    range_prop_block(body, &Env::new());
                    invalidate_env_for_body(&mut env, body);
                    refine_env_false(&mut env, cond);
                }
            }

            Node::Repeat { count, children: body } => {
                let substs = env_to_substs(&env);
                if !substs.is_empty() {
                    *count = count.with_memory(&substs);
                }
                range_prop_block(body, &Env::new());
                invalidate_env_for_body(&mut env, body);
            }

            Node::SeekMemory { target, value, .. } => {
                env.clear();
                env.insert(*target, CellValue::Const(*value));
            }

            Node::Program { children: body } => {
                range_prop_block(body, &env);
                env.clear();
            }
        }

        children[i] = node;
    }

    cleanup::cleanup(children);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(nodes: &mut Vec<Node>) {
        range_prop_block(nodes, &Env::new());
    }

    // --- Existing tests (constant propagation) ---

    #[test]
    fn dead_branch_eliminated() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(0),
            },
            Node::If {
                cond: Cond::MemNotEqual(0, 0),
                children: vec![Node::SetMemory {
                    offset: 1,
                    value: Expr::Int(5),
                }],
            },
        ];
        run(&mut nodes);
        assert!(nodes.iter().all(|n| !matches!(n, Node::If { .. })));
    }

    #[test]
    fn always_branch_inlined() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::If {
                cond: Cond::MemNotEqual(0, 0),
                children: vec![Node::SetMemory {
                    offset: 1,
                    value: Expr::mem(0),
                }],
            },
        ];
        run(&mut nodes);
        let set1 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 1, .. }));
        assert!(set1.is_some(), "p[1] assignment missing: {:?}", nodes);
        if let Some(Node::SetMemory { value, .. }) = set1 {
            assert_eq!(*value, Expr::Int(5));
        }
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If should be inlined: {:?}",
            nodes
        );
    }

    #[test]
    fn constant_prop_in_if_body() {
        let mut nodes = vec![Node::If {
            cond: Cond::MemEqual(0, 65),
            children: vec![Node::Output {
                expr: Expr::mem(0),
            }],
        }];
        run(&mut nodes);
        if let Some(Node::If { children, .. }) = nodes.first() {
            if let Some(Node::Output { expr }) = children.first() {
                assert_eq!(*expr, Expr::Int(65));
            } else {
                panic!("expected Output in If body");
            }
        } else {
            panic!("expected If node");
        }
    }

    #[test]
    fn while_never_eliminated() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(0),
            },
            Node::While {
                cond: Cond::MemNotEqual(0, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(0),
                }],
            },
        ];
        run(&mut nodes);
        assert!(nodes.iter().all(|n| !matches!(n, Node::While { .. })));
    }

    #[test]
    fn post_while_constant() {
        let mut nodes = vec![
            Node::While {
                cond: Cond::MemNotEqual(0, 0),
                children: vec![Node::adjust_memory_by(0, -1)],
            },
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
        ];
        run(&mut nodes);
        let set1 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 1, .. }));
        if let Some(Node::SetMemory { value, .. }) = set1 {
            assert_eq!(*value, Expr::Int(0));
        } else {
            panic!("expected SetMemory at offset 1");
        }
    }

    #[test]
    fn nested_if_propagation() {
        let mut nodes = vec![Node::If {
            cond: Cond::MemEqual(0, 5),
            children: vec![Node::If {
                cond: Cond::MemEqual(1, 10),
                children: vec![Node::SetMemory {
                    offset: 2,
                    value: Expr::mem(0) + Expr::mem(1),
                }],
            }],
        }];
        run(&mut nodes);
        if let Some(Node::If {
            children: outer_body,
            ..
        }) = nodes.first()
        {
            if let Some(Node::If {
                children: inner_body,
                ..
            }) = outer_body.first()
            {
                if let Some(Node::SetMemory { value, .. }) = inner_body.first() {
                    assert_eq!(*value, Expr::Int(15));
                } else {
                    panic!("expected SetMemory in inner If body");
                }
            } else {
                panic!("expected inner If");
            }
        } else {
            panic!("expected outer If");
        }
    }

    #[test]
    fn input_invalidates_constant() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::Input { offset: 0 },
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
        ];
        run(&mut nodes);
        let set1 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 1, .. }));
        if let Some(Node::SetMemory { value, .. }) = set1 {
            assert_eq!(*value, Expr::mem(0));
        } else {
            panic!("expected SetMemory at offset 1");
        }
    }

    #[test]
    fn if_body_invalidates_outer_env() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(10),
                }],
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(0),
            },
        ];
        run(&mut nodes);
        let set2 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        if let Some(Node::SetMemory { value, .. }) = set2 {
            assert_eq!(*value, Expr::mem(0));
        } else {
            panic!("expected SetMemory at offset 2");
        }
    }

    #[test]
    fn conjunction_condition_refines() {
        let mut nodes = vec![Node::If {
            cond: Cond::conjunction(vec![Cond::MemEqual(0, 5), Cond::MemEqual(1, 10)]),
            children: vec![Node::SetMemory {
                offset: 2,
                value: Expr::mem(0) + Expr::mem(1),
            }],
        }];
        run(&mut nodes);
        if let Some(Node::If { children, .. }) = nodes.first() {
            if let Some(Node::SetMemory { value, .. }) = children.first() {
                assert_eq!(*value, Expr::Int(15));
            } else {
                panic!("expected SetMemory");
            }
        } else {
            panic!("expected If");
        }
    }

    #[test]
    fn env_survives_unrelated_if() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 1,
                    value: Expr::Int(0),
                }],
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(0),
            },
        ];
        run(&mut nodes);
        let set2 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        if let Some(Node::SetMemory { value, .. }) = set2 {
            assert_eq!(*value, Expr::Int(5));
        } else {
            panic!("expected SetMemory at offset 2");
        }
    }

    #[test]
    fn seek_memory_sets_env() {
        let mut nodes = vec![
            Node::SeekMemory {
                target: 0,
                stride: 1,
                value: 0,
            },
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
        ];
        run(&mut nodes);
        let set1 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 1, .. }));
        if let Some(Node::SetMemory { value, .. }) = set1 {
            assert_eq!(*value, Expr::Int(0));
        } else {
            panic!("expected SetMemory at offset 1");
        }
    }

    #[test]
    fn mem_equal_dead_branch() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::If {
                cond: Cond::MemEqual(0, 3),
                children: vec![Node::SetMemory {
                    offset: 1,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]==3) should be dead when p[0]==5: {:?}",
            nodes
        );
    }

    #[test]
    fn constant_chains_through_set() {
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0) + Expr::Int(3),
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(1),
            },
        ];
        run(&mut nodes);
        let set2 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        if let Some(Node::SetMemory { value, .. }) = set2 {
            assert_eq!(*value, Expr::Int(8));
        } else {
            panic!("expected SetMemory at offset 2");
        }
    }

    // --- Congruence / modular analysis tests ---

    #[test]
    fn congruence_even_eliminates_odd_equal() {
        // p[0] = 2 * p[1] → p[0] ≡ 0 (mod 2)
        // If(p[0] == 3) → dead (3 is odd)
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(1),
            },
            Node::If {
                cond: Cond::MemEqual(0, 3),
                children: vec![Node::SetMemory {
                    offset: 2,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]==3) should be dead when p[0] is even: {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_even_keeps_even_equal() {
        // p[0] = 2 * p[1] → p[0] ≡ 0 (mod 2)
        // If(p[0] == 4) → NOT dead (4 is even)
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(1),
            },
            Node::If {
                cond: Cond::MemEqual(0, 4),
                children: vec![Node::SetMemory {
                    offset: 2,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().any(|n| matches!(n, Node::If { .. })),
            "If(p[0]==4) should NOT be dead when p[0] is even: {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_not_equal_becomes_always() {
        // p[0] = 2 * p[1] → p[0] ≡ 0 (mod 2)
        // If(p[0] != 3) → always (3 is odd, can never equal even p[0])
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(1),
            },
            Node::If {
                cond: Cond::MemNotEqual(0, 3),
                children: vec![Node::SetMemory {
                    offset: 2,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]!=3) should be always-true (inlined): {:?}",
            nodes
        );
        assert!(
            nodes
                .iter()
                .any(|n| matches!(n, Node::SetMemory { offset: 2, .. })),
            "body should be inlined: {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_odd_via_linear() {
        // p[0] = 2 * p[1] + 1 → p[0] ≡ 1 (mod 2), always odd
        // If(p[0] == 4) → dead (4 is even)
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(1) + Expr::Int(1),
            },
            Node::If {
                cond: Cond::MemEqual(0, 4),
                children: vec![Node::SetMemory {
                    offset: 2,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]==4) should be dead when p[0] is odd: {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_propagates_through_copy() {
        // p[0] = 2 * p[2] → p[0] ≡ 0 (mod 2)
        // p[1] = p[0]     → p[1] ≡ 0 (mod 2)
        // If(p[1] == 3) → dead
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(2),
            },
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
            Node::If {
                cond: Cond::MemEqual(1, 3),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[1]==3) should be dead when p[1] is even: {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_survives_even_add() {
        // p[0] = 2 * p[2] → p[0] ≡ 0 (mod 2)
        // p[0] += 4       → p[0] ≡ 0 (mod 2), still even
        // If(p[0] == 3) → dead
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(2),
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::mem(0) + Expr::Int(4),
            },
            Node::If {
                cond: Cond::MemEqual(0, 3),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]==3) should be dead when p[0] is even: {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_residue_shift() {
        // p[0] = 2 * p[2] → p[0] ≡ 0 (mod 2)
        // p[0] += 3       → p[0] ≡ 1 (mod 2), now odd
        // If(p[0] == 4) → dead (4 is even, p[0] is odd)
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(2),
            },
            Node::SetMemory {
                offset: 0,
                value: Expr::mem(0) + Expr::Int(3),
            },
            Node::If {
                cond: Cond::MemEqual(0, 4),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]==4) should be dead when p[0] is odd: {:?}",
            nodes
        );
    }

    #[test]
    fn input_invalidates_congruence() {
        // p[0] = 2 * p[1] → p[0] ≡ 0 (mod 2)
        // input p[0]       → unknown
        // If(p[0] == 3) → NOT dead
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(1),
            },
            Node::Input { offset: 0 },
            Node::If {
                cond: Cond::MemEqual(0, 3),
                children: vec![Node::SetMemory {
                    offset: 2,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().any(|n| matches!(n, Node::If { .. })),
            "If should remain after input invalidates congruence: {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_mod3() {
        // p[0] = 3 * p[1] → p[0] ≡ 0 (mod 3)
        // If(p[0] == 1) → dead (1 % 3 ≠ 0)
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(3) * Expr::mem(1),
            },
            Node::If {
                cond: Cond::MemEqual(0, 1),
                children: vec![Node::SetMemory {
                    offset: 2,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]==1) should be dead when p[0] ≡ 0 (mod 3): {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_mod3_compatible_value() {
        // p[0] = 3 * p[1] → p[0] ≡ 0 (mod 3)
        // If(p[0] == 6) → NOT dead (6 % 3 == 0)
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(3) * Expr::mem(1),
            },
            Node::If {
                cond: Cond::MemEqual(0, 6),
                children: vec![Node::SetMemory {
                    offset: 2,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().any(|n| matches!(n, Node::If { .. })),
            "If(p[0]==6) should NOT be dead when p[0] ≡ 0 (mod 3): {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_multiterm_gcd() {
        // p[0] = 2*p[1] + 4*p[2] → p[0] ≡ 0 (mod gcd(2,4)) = 0 (mod 2)
        // If(p[0] == 3) → dead
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::linear(0, vec![(2, Expr::mem(1)), (4, Expr::mem(2))]),
            },
            Node::If {
                cond: Cond::MemEqual(0, 3),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]==3) should be dead when p[0] is even: {:?}",
            nodes
        );
    }

    #[test]
    fn congruence_negative_value() {
        // p[0] = 2 * p[1] → p[0] ≡ 0 (mod 2)
        // If(p[0] == -3) → dead (-3 is odd)
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(1),
            },
            Node::If {
                cond: Cond::MemEqual(0, -3),
                children: vec![Node::SetMemory {
                    offset: 2,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]==-3) should be dead when p[0] is even: {:?}",
            nodes
        );
    }

    #[test]
    fn derive_cell_value_const() {
        let env = Env::new();
        assert_eq!(
            derive_cell_value(&Expr::Int(42), &env),
            Some(CellValue::Const(42))
        );
    }

    #[test]
    fn derive_cell_value_copy_mod() {
        let mut env = Env::new();
        env.insert(0, CellValue::Mod(3, 1));
        assert_eq!(
            derive_cell_value(&Expr::mem(0), &env),
            Some(CellValue::Mod(3, 1))
        );
    }

    #[test]
    fn derive_cell_value_scaled() {
        // 2 * mem(1) where mem(1) is Mod(3, 1)
        // Result: Mod(6, 2) since 2*(3k+1) = 6k+2
        let mut env = Env::new();
        env.insert(1, CellValue::Mod(3, 1));
        let expr = Expr::Int(2) * Expr::mem(1);
        assert_eq!(
            derive_cell_value(&expr, &env),
            Some(CellValue::Mod(6, 2))
        );
    }

    #[test]
    fn derive_cell_value_unknown_scaled() {
        // 2 * mem(1) where mem(1) is unknown → Mod(2, 0)
        let env = Env::new();
        let expr = Expr::Int(2) * Expr::mem(1);
        assert_eq!(
            derive_cell_value(&expr, &env),
            Some(CellValue::Mod(2, 0))
        );
    }

    #[test]
    fn derive_cell_value_no_useful_mod() {
        // mem(0) + mem(1), both unknown → None (no useful congruence)
        let env = Env::new();
        let expr = Expr::mem(0) + Expr::mem(1);
        assert_eq!(derive_cell_value(&expr, &env), None);
    }

    // --- Branch-sensitive tests ---

    #[test]
    fn if_merge_preserves_constant_both_branches() {
        // p[0] = 5
        // If(p[1] != 0) { p[0] = 5 } (body sets p[0] to same value)
        // After If: p[0] should still be 5
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(5),
                }],
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(0),
            },
        ];
        run(&mut nodes);
        let set2 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        if let Some(Node::SetMemory { value, .. }) = set2 {
            assert_eq!(*value, Expr::Int(5), "p[0] should remain 5 after merge");
        } else {
            panic!("expected SetMemory at offset 2");
        }
    }

    #[test]
    fn if_merge_loses_conflicting_constant() {
        // p[0] = 5
        // If(p[1] != 0) { p[0] = 10 }
        // After If: p[0] is 5 or 10, should be unknown
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(10),
                }],
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(0),
            },
        ];
        run(&mut nodes);
        let set2 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        if let Some(Node::SetMemory { value, .. }) = set2 {
            assert_eq!(*value, Expr::mem(0), "p[0] should be unknown after merge");
        } else {
            panic!("expected SetMemory at offset 2");
        }
    }

    #[test]
    fn if_merge_preserves_mod_info() {
        // p[0] = 2*p[2] (even)
        // If(p[1] != 0) { p[0] = 4*p[3] } (still even)
        // After If: p[0] should still be Mod(2, 0) → can eliminate odd test
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(2) * Expr::mem(2),
            },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(4) * Expr::mem(3),
                }],
            },
            Node::If {
                cond: Cond::MemEqual(0, 3),
                children: vec![Node::SetMemory {
                    offset: 5,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        // The second If(p[0]==3) should be dead because p[0] is even in both branches
        let if_count = nodes
            .iter()
            .filter(|n| matches!(n, Node::If { .. }))
            .count();
        assert!(
            if_count <= 1,
            "If(p[0]==3) should be dead after merge preserving even info: {:?}",
            nodes
        );
    }

    #[test]
    fn if_merge_const_and_mod_yields_mod() {
        // p[0] = 4 (Const(4))
        // If(p[1] != 0) { p[0] = 2*p[3] } (Mod(2, 0))
        // After merge: Const(4) ∩ Mod(2, 0) → Mod(2, 0) since 4 ≡ 0 (mod 2)
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(4),
            },
            Node::If {
                cond: Cond::MemNotEqual(1, 0),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(2) * Expr::mem(3),
                }],
            },
            Node::If {
                cond: Cond::MemEqual(0, 3),
                children: vec![Node::SetMemory {
                    offset: 5,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        let if_count = nodes
            .iter()
            .filter(|n| matches!(n, Node::If { .. }))
            .count();
        assert!(
            if_count <= 1,
            "If(p[0]==3) should be dead since p[0] ≡ 0 (mod 2): {:?}",
            nodes
        );
    }

    #[test]
    fn false_branch_not_equal_gives_constant() {
        // If(p[0] != 5) { output something }
        // In false branch: p[0] == 5
        // If body doesn't modify p[0], and p[0] was unknown before,
        // then after If:
        //   true branch: p[0] is unknown (was unknown, body doesn't change it)
        //   false branch: p[0] == 5
        // merge → unknown
        // But if p[0] is already 5 before the If, the If condition is Always and gets inlined.
        // Let's test: If(p[0] != 5) with p[0] already known as 5 → dead code
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::If {
                cond: Cond::MemNotEqual(0, 5),
                children: vec![Node::SetMemory {
                    offset: 1,
                    value: Expr::Int(99),
                }],
            },
        ];
        run(&mut nodes);
        assert!(
            nodes.iter().all(|n| !matches!(n, Node::If { .. })),
            "If(p[0]!=5) should be dead when p[0]==5: {:?}",
            nodes
        );
    }

    #[test]
    fn while_exit_conjunction() {
        // While(p[0] != 0 && p[1] != 0) { ... }
        // After exit: at least one is 0, but we can't say which
        // The Disjunction false refinement should apply
        // Actually, refine_env_false on Conjunction does nothing (since false = disjunction of negations)
        // This test just verifies no crash
        let mut nodes = vec![
            Node::While {
                cond: Cond::conjunction(vec![Cond::MemNotEqual(0, 0), Cond::MemNotEqual(1, 0)]),
                children: vec![Node::adjust_memory_by(0, -1)],
            },
            Node::SetMemory {
                offset: 2,
                value: Expr::mem(0),
            },
        ];
        run(&mut nodes);
        // Can't determine p[0] after exit of conjunction while, so p[2] should stay as mem(0)
        let set2 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 2, .. }));
        if let Some(Node::SetMemory { value, .. }) = set2 {
            assert_eq!(*value, Expr::mem(0));
        }
    }

    #[test]
    fn merge_cell_value_const_const_same() {
        assert_eq!(
            merge_cell_value(&CellValue::Const(5), &CellValue::Const(5)),
            Some(CellValue::Const(5))
        );
    }

    #[test]
    fn merge_cell_value_const_const_diff() {
        assert_eq!(
            merge_cell_value(&CellValue::Const(5), &CellValue::Const(3)),
            None
        );
    }

    #[test]
    fn merge_cell_value_const_mod_compatible() {
        assert_eq!(
            merge_cell_value(&CellValue::Const(4), &CellValue::Mod(2, 0)),
            Some(CellValue::Mod(2, 0))
        );
    }

    #[test]
    fn merge_cell_value_const_mod_incompatible() {
        assert_eq!(
            merge_cell_value(&CellValue::Const(3), &CellValue::Mod(2, 0)),
            None
        );
    }

    #[test]
    fn merge_cell_value_mod_mod_same() {
        assert_eq!(
            merge_cell_value(&CellValue::Mod(4, 2), &CellValue::Mod(6, 2)),
            Some(CellValue::Mod(2, 0))
        );
    }

    #[test]
    fn merge_cell_value_mod_mod_incompatible() {
        assert_eq!(
            merge_cell_value(&CellValue::Mod(2, 0), &CellValue::Mod(2, 1)),
            None
        );
    }

    #[test]
    fn if_unrelated_cells_survive_merge() {
        // p[0] = 5, p[1] = 10
        // If(p[2] != 0) { p[3] = 99 }
        // After If: p[0] and p[1] should still be known
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::SetMemory {
                offset: 1,
                value: Expr::Int(10),
            },
            Node::If {
                cond: Cond::MemNotEqual(2, 0),
                children: vec![Node::SetMemory {
                    offset: 3,
                    value: Expr::Int(99),
                }],
            },
            Node::SetMemory {
                offset: 4,
                value: Expr::mem(0) + Expr::mem(1),
            },
        ];
        run(&mut nodes);
        let set4 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 4, .. }));
        if let Some(Node::SetMemory { value, .. }) = set4 {
            assert_eq!(
                *value,
                Expr::Int(15),
                "p[0]+p[1] should be 15 after unrelated If"
            );
        } else {
            panic!("expected SetMemory at offset 4");
        }
    }

    #[test]
    fn if_with_mem_equal_false_path_loses_const() {
        // p[0] = 5
        // If(p[0] == 5) { p[0] = 10 }
        // true branch: enters with p[0]=5, then sets p[0]=10 → p[0]=10
        // false branch: p[0] was 5, but MemEqual(0,5) false → p[0] != 5
        //   refine_env_false removes Const(5) from env → unknown
        // merge: Const(10) vs unknown → unknown
        let mut nodes = vec![
            Node::SetMemory {
                offset: 0,
                value: Expr::Int(5),
            },
            Node::If {
                cond: Cond::MemEqual(0, 5),
                children: vec![Node::SetMemory {
                    offset: 0,
                    value: Expr::Int(10),
                }],
            },
            Node::SetMemory {
                offset: 1,
                value: Expr::mem(0),
            },
        ];
        run(&mut nodes);
        // Since cond is MemEqual(0,5) and p[0] IS 5, the condition is Always
        // so the branch gets inlined and p[0]=10 after.
        // That's actually a constant fold! Let's check:
        let set1 = nodes
            .iter()
            .find(|n| matches!(n, Node::SetMemory { offset: 1, .. }));
        if let Some(Node::SetMemory { value, .. }) = set1 {
            assert_eq!(*value, Expr::Int(10));
        } else {
            panic!("expected SetMemory at offset 1");
        }
    }
}
