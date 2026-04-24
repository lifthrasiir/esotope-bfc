use std::collections::BTreeMap;

use crate::cond::*;
use crate::expr::*;
use crate::nodes::*;
use crate::opt::cleanup;

pub fn transform(node: &mut Node) {
    if let Some(children) = node.children_mut() {
        range_prop_block(children, &BTreeMap::new());
    }
}

fn env_to_substs(env: &BTreeMap<i32, i32>) -> BTreeMap<i32, Expr> {
    env.iter().map(|(&k, &v)| (k, Expr::Int(v))).collect()
}

fn refine_env(env: &mut BTreeMap<i32, i32>, cond: &Cond) {
    match cond {
        Cond::MemEqual(t, v) => {
            env.insert(*t, *v);
        }
        Cond::Conjunction(clauses) => {
            for c in clauses {
                refine_env(env, c);
            }
        }
        _ => {}
    }
}

fn invalidate_env_for_body(env: &mut BTreeMap<i32, i32>, body: &[Node]) {
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

fn update_env_from_body(env: &mut BTreeMap<i32, i32>, body: &[Node]) {
    for node in body {
        match node {
            Node::SetMemory { offset, value } => {
                if let Some(c) = value.to_int() {
                    env.insert(*offset, c);
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

fn range_prop_block(children: &mut Vec<Node>, initial_env: &BTreeMap<i32, i32>) {
    let mut env = initial_env.clone();

    for i in 0..children.len() {
        let mut node = std::mem::replace(&mut children[i], Node::Nop);

        match &mut node {
            Node::Nop | Node::OutputConst { .. } | Node::MovePointer { .. } => {}

            Node::SetMemory { offset, value } => {
                if !env.is_empty() {
                    let substs = env_to_substs(&env);
                    *value = value.with_memory(&substs);
                }
                if let Some(c) = value.to_int() {
                    env.insert(*offset, c);
                } else {
                    env.remove(offset);
                }
            }

            Node::Input { offset } => {
                env.remove(offset);
            }

            Node::Output { expr } => {
                if !env.is_empty() {
                    let substs = env_to_substs(&env);
                    *expr = expr.with_memory(&substs);
                }
            }

            Node::If { cond, children: body } => {
                if !env.is_empty() {
                    let substs = env_to_substs(&env);
                    *cond = cond.with_memory(&substs);
                }

                if cond.is_never() {
                    // Dead branch — cleanup will remove
                } else if cond.is_always() {
                    range_prop_block(body, &env);
                    update_env_from_body(&mut env, body);
                } else {
                    let mut body_env = env.clone();
                    refine_env(&mut body_env, cond);
                    range_prop_block(body, &body_env);
                    invalidate_env_for_body(&mut env, body);
                }
            }

            Node::While { cond, children: body } => {
                if !env.is_empty() {
                    let substs = env_to_substs(&env);
                    let eval = cond.with_memory(&substs);
                    if eval.is_never() {
                        *cond = Cond::Never;
                    }
                }

                if !cond.is_never() {
                    range_prop_block(body, &BTreeMap::new());
                    invalidate_env_for_body(&mut env, body);
                    if let Cond::MemNotEqual(t, v) = cond {
                        env.insert(*t, *v);
                    }
                }
            }

            Node::Repeat { count, children: body } => {
                if !env.is_empty() {
                    let substs = env_to_substs(&env);
                    *count = count.with_memory(&substs);
                }
                range_prop_block(body, &BTreeMap::new());
                invalidate_env_for_body(&mut env, body);
            }

            Node::SeekMemory { target, value, .. } => {
                env.clear();
                env.insert(*target, *value);
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
        range_prop_block(nodes, &BTreeMap::new());
    }

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
}
