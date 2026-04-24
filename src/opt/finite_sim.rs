use std::collections::BTreeMap;

use crate::cond::Cond;
use crate::expr::Expr;
use crate::nodes::Node;
use crate::opt::cleanup;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config {
    pub max_steps: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config { max_steps: 100_000 }
    }
}

#[derive(Clone, Debug)]
struct State {
    ptr: i32,
    memory: BTreeMap<i32, i32>,
    output: Vec<u8>,
    steps: usize,
    cell_mask: i64,
    max_steps: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Stop {
    Blocked(Vec<Node>),
    StepLimit(Vec<Node>),
}

type SimResult = Result<(), Stop>;

pub fn transform(node: &mut Node, cellsize: u32, max_steps: usize) {
    let Node::Program { children } = node else {
        return;
    };
    if max_steps == 0 || children.is_empty() {
        return;
    }

    let original = children.clone();
    let mut state = State {
        ptr: 0,
        memory: BTreeMap::new(),
        output: Vec::new(),
        steps: 0,
        cell_mask: (1i64 << cellsize) - 1,
        max_steps,
    };

    let residual = match run_block(&original, &mut state) {
        Ok(()) => Vec::new(),
        Err(Stop::Blocked(residual)) if state.steps == 0 && state.output.is_empty() && state.memory.is_empty() && state.ptr == 0 => {
            residual
        }
        Err(Stop::Blocked(residual)) | Err(Stop::StepLimit(residual)) => residual,
    };

    if state.steps == 0 && state.output.is_empty() && state.memory.is_empty() && state.ptr == 0 {
        return;
    }

    let mut replacement = snapshot_nodes(&state);
    replacement.extend(residual);
    cleanup::cleanup(&mut replacement);
    *children = replacement;
}

fn run_block(children: &[Node], state: &mut State) -> SimResult {
    for (i, child) in children.iter().enumerate() {
        match run_node(child, state) {
            Ok(()) => {}
            Err(Stop::Blocked(mut residual)) => {
                residual.extend_from_slice(&children[i + 1..]);
                return Err(Stop::Blocked(residual));
            }
            Err(Stop::StepLimit(mut residual)) => {
                residual.extend_from_slice(&children[i + 1..]);
                return Err(Stop::StepLimit(residual));
            }
        }
    }
    Ok(())
}

fn run_node(node: &Node, state: &mut State) -> SimResult {
    match node {
        Node::Input { .. } => return Err(Stop::Blocked(vec![node.clone()])),
        Node::SetMemory { offset, value } => {
            step_or_limit(state, vec![node.clone()])?;
            let value = eval_expr(value, state).ok_or_else(|| Stop::Blocked(vec![node.clone()]))?;
            set_cell(state, state.ptr + offset, value);
            Ok(())
        }
        Node::MovePointer { offset } => {
            step_or_limit(state, vec![node.clone()])?;
            state.ptr = state.ptr.wrapping_add(*offset);
            Ok(())
        }
        Node::Output { expr } => {
            step_or_limit(state, vec![node.clone()])?;
            let value = eval_expr(expr, state).ok_or_else(|| Stop::Blocked(vec![node.clone()]))?;
            state.output.push(wrap_cell(state, value) as u8);
            Ok(())
        }
        Node::OutputConst { s } => {
            step_or_limit(state, vec![node.clone()])?;
            state.output.extend_from_slice(s);
            Ok(())
        }
        Node::SeekMemory {
            target,
            stride,
            value,
        } => {
            loop {
                if get_cell(state, state.ptr + target) == wrap_cell(state, *value) {
                    return Ok(());
                }
                step_or_limit(state, vec![node.clone()])?;
                state.ptr = state.ptr.wrapping_add(*stride);
            }
        }
        Node::Program { children } => run_block(children, state),
        Node::If { cond, children } => {
            step_or_limit(state, vec![node.clone()])?;
            match eval_cond(cond, state) {
                Some(false) => Ok(()),
                Some(true) => run_block(children, state),
                None => Err(Stop::Blocked(vec![node.clone()])),
            }
        }
        Node::Repeat { count, children } => {
            let count_value = eval_expr(count, state).ok_or_else(|| Stop::Blocked(vec![node.clone()]))?;
            let total = wrap_cell(state, count_value) as usize;
            for i in 0..total {
                step_or_limit(state, repeat_residual(children, total - i))?;
                match run_block(children, state) {
                    Ok(()) => {}
                    Err(Stop::Blocked(mut residual)) => {
                        residual.extend(repeat_residual(children, total - i - 1));
                        return Err(Stop::Blocked(residual));
                    }
                    Err(Stop::StepLimit(mut residual)) => {
                        residual.extend(repeat_residual(children, total - i - 1));
                        return Err(Stop::StepLimit(residual));
                    }
                }
            }
            Ok(())
        }
        Node::While { cond, children } => loop {
            step_or_limit(state, vec![node.clone()])?;
            match eval_cond(cond, state) {
                Some(false) => return Ok(()),
                Some(true) => match run_block(children, state) {
                    Ok(()) => {}
                    Err(Stop::Blocked(mut residual)) => {
                        residual.push(node.clone());
                        return Err(Stop::Blocked(residual));
                    }
                    Err(Stop::StepLimit(mut residual)) => {
                        residual.push(node.clone());
                        return Err(Stop::StepLimit(residual));
                    }
                },
                None => return Err(Stop::Blocked(vec![node.clone()])),
            }
        },
        Node::Nop => Ok(()),
    }
}

fn repeat_residual(children: &[Node], remaining: usize) -> Vec<Node> {
    if remaining == 0 {
        Vec::new()
    } else {
        vec![Node::Repeat {
            count: Expr::Int(remaining as i32),
            children: children.to_vec(),
        }]
    }
}

fn step_or_limit(state: &mut State, residual: Vec<Node>) -> SimResult {
    if state.steps >= state.max_steps {
        Err(Stop::StepLimit(residual))
    } else {
        state.steps += 1;
        Ok(())
    }
}

fn snapshot_nodes(state: &State) -> Vec<Node> {
    let mut nodes = Vec::new();
    if !state.output.is_empty() {
        nodes.push(Node::OutputConst {
            s: state.output.clone(),
        });
    }
    for (offset, value) in &state.memory {
        if *value != 0 {
            nodes.push(Node::SetMemory {
                offset: *offset,
                value: Expr::Int(*value),
            });
        }
    }
    if state.ptr != 0 {
        nodes.push(Node::MovePointer { offset: state.ptr });
    }
    nodes
}

fn eval_cond(cond: &Cond, state: &State) -> Option<bool> {
    match cond {
        Cond::Always => Some(true),
        Cond::Never => Some(false),
        Cond::Equal(expr, value) => Some(eval_expr(expr, state)? == wrap_cell(state, *value)),
        Cond::NotEqual(expr, value) => Some(eval_expr(expr, state)? != wrap_cell(state, *value)),
        Cond::MemEqual(offset, value) => Some(get_cell(state, state.ptr + offset) == wrap_cell(state, *value)),
        Cond::MemNotEqual(offset, value) => Some(get_cell(state, state.ptr + offset) != wrap_cell(state, *value)),
        Cond::Range(expr, ranges) => {
            let value = eval_expr(expr, state)?;
            Some(ranges.iter().any(|(min, max)| {
                min.is_none_or(|min| min <= value) && max.is_none_or(|max| value <= max)
            }))
        }
        Cond::Conjunction(clauses) => {
            let mut unknown = false;
            for clause in clauses {
                match eval_cond(clause, state) {
                    Some(false) => return Some(false),
                    Some(true) => {}
                    None => unknown = true,
                }
            }
            if unknown { None } else { Some(true) }
        }
        Cond::Disjunction(clauses) => {
            let mut unknown = false;
            for clause in clauses {
                match eval_cond(clause, state) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => unknown = true,
                }
            }
            if unknown { None } else { Some(false) }
        }
    }
}

fn eval_expr(expr: &Expr, state: &State) -> Option<i32> {
    match expr {
        Expr::Int(value) => Some(wrap_cell(state, *value)),
        Expr::Reference(offset) => {
            let offset = eval_offset(offset, state)?;
            Some(get_cell(state, state.ptr + offset))
        }
        Expr::Linear(linear) => {
            let mut value = linear.constant;
            for (coeff, term) in &linear.terms {
                value = value.wrapping_add(coeff.wrapping_mul(eval_expr(term, state)?));
            }
            Some(wrap_cell(state, value))
        }
        Expr::Multiply(factors) => {
            let mut value = 1i32;
            for factor in factors {
                value = value.wrapping_mul(eval_expr(factor, state)?);
            }
            Some(wrap_cell(state, value))
        }
        Expr::Division(lhs, rhs) => {
            let rhs = eval_expr(rhs, state)?;
            if rhs == 0 {
                None
            } else {
                Some(wrap_cell(state, eval_expr(lhs, state)?.div_euclid(rhs)))
            }
        }
        Expr::ExactDivision(lhs, rhs) => {
            let rhs = eval_expr(rhs, state)?;
            let lhs = eval_expr(lhs, state)?;
            if rhs == 0 || lhs % rhs != 0 {
                None
            } else {
                Some(wrap_cell(state, lhs / rhs))
            }
        }
        Expr::Modulo(lhs, rhs) => {
            let rhs = eval_expr(rhs, state)?;
            if rhs == 0 {
                None
            } else {
                Some(wrap_cell(state, eval_expr(lhs, state)?.rem_euclid(rhs)))
            }
        }
    }
}

fn eval_offset(expr: &Expr, state: &State) -> Option<i32> {
    match expr {
        Expr::Int(value) => Some(*value),
        Expr::Reference(_) => eval_expr(expr, state),
        Expr::Linear(linear) => {
            let mut value = linear.constant;
            for (coeff, term) in &linear.terms {
                value = value.wrapping_add(coeff.wrapping_mul(eval_offset(term, state)?));
            }
            Some(value)
        }
        Expr::Multiply(factors) => {
            let mut value = 1i32;
            for factor in factors {
                value = value.wrapping_mul(eval_offset(factor, state)?);
            }
            Some(value)
        }
        Expr::Division(lhs, rhs) => {
            let rhs = eval_offset(rhs, state)?;
            if rhs == 0 {
                None
            } else {
                Some(eval_offset(lhs, state)?.div_euclid(rhs))
            }
        }
        Expr::ExactDivision(lhs, rhs) => {
            let rhs = eval_offset(rhs, state)?;
            let lhs = eval_offset(lhs, state)?;
            if rhs == 0 || lhs % rhs != 0 {
                None
            } else {
                Some(lhs / rhs)
            }
        }
        Expr::Modulo(lhs, rhs) => {
            let rhs = eval_offset(rhs, state)?;
            if rhs == 0 {
                None
            } else {
                Some(eval_offset(lhs, state)?.rem_euclid(rhs))
            }
        }
    }
}

fn get_cell(state: &State, offset: i32) -> i32 {
    *state.memory.get(&offset).unwrap_or(&0)
}

fn set_cell(state: &mut State, offset: i32, value: i32) {
    let value = wrap_cell(state, value);
    if value == 0 {
        state.memory.remove(&offset);
    } else {
        state.memory.insert(offset, value);
    }
}

fn wrap_cell(state: &State, value: i32) -> i32 {
    (i64::from(value) & state.cell_mask) as i32
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::brainfuck;
    use std::io::BufReader;

    fn parse(src: &str) -> Node {
        let mut node = brainfuck::parse(BufReader::new(src.as_bytes())).unwrap();
        crate::opt::flatten::transform(&mut node);
        node
    }

    fn children(node: &Node) -> &[Node] {
        match node {
            Node::Program { children } => children,
            _ => panic!("expected program"),
        }
    }

    #[test]
    fn simulates_const_prefix_to_snapshot() {
        let mut node = parse("+++.");
        transform(&mut node, 8, 100);
        let kids = children(&node);
        assert!(kids.iter().any(|n| matches!(n, Node::OutputConst { s } if s == &[3])));
    }

    #[test]
    fn stops_before_input_and_keeps_residual() {
        let mut node = parse("++,."); 
        transform(&mut node, 8, 100);
        let kids = children(&node);
        assert!(kids.iter().any(|n| matches!(n, Node::SetMemory { offset: 0, value } if *value == Expr::Int(2))));
        assert!(kids.iter().any(|n| matches!(n, Node::Input { offset: 0 })));
        assert!(kids.iter().any(|n| matches!(n, Node::Output { .. })));
    }

    #[test]
    fn step_limit_keeps_last_snapshot_and_continuation() {
        let mut node = parse("+++>+++>+++.");
        transform(&mut node, 8, 3);
        let kids = children(&node);
        assert!(kids.iter().any(|n| matches!(n, Node::SetMemory { offset: 0, value } if *value == Expr::Int(3))));
        assert!(kids.iter().any(|n| matches!(n, Node::Output { .. })));
    }

    #[test]
    fn simulates_nonzero_stride_loop() {
        let mut node = parse("+[>+<-]>.");
        transform(&mut node, 8, 100);
        let kids = children(&node);
        assert!(kids.iter().any(|n| matches!(n, Node::OutputConst { s } if s == &[1])));
        assert!(!kids.iter().any(|n| matches!(n, Node::While { .. })));
    }

    #[test]
    fn simulates_bad_b_raw_to_hello_world() {
        let mut node = parse(
            ">++++++++[-<+++++++++>]<.>[][<-]>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.\n\
             >->+++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        );
        transform(&mut node, 8, 100_000);
        let kids = children(&node);
        assert!(kids.iter().any(|n| matches!(n, Node::OutputConst { s } if s == b"Hello World!\n")));
    }
}
