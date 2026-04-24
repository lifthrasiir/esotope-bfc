use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt;
use std::mem;

use crate::expr::*;

type RangeMap = BTreeMap<Expr, Vec<(Option<i32>, Option<i32>)>>;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Cond {
    Always,
    Never,
    Equal(Expr, i32),
    NotEqual(Expr, i32),
    MemEqual(i32, i32),
    MemNotEqual(i32, i32),
    Range(Expr, Vec<(Option<i32>, Option<i32>)>),
    Conjunction(Vec<Cond>),
    Disjunction(Vec<Cond>),
}

impl Cond {
    pub fn is_always(&self) -> bool {
        matches!(self, Cond::Always)
    }

    pub fn is_never(&self) -> bool {
        matches!(self, Cond::Never)
    }

    pub fn is_mem_not_equal(&self) -> bool {
        matches!(self, Cond::MemNotEqual(_, _))
    }

    pub fn get_target(&self) -> Option<i32> {
        match self {
            Cond::MemEqual(t, _) | Cond::MemNotEqual(t, _) => Some(*t),
            _ => None,
        }
    }

    pub fn get_value(&self) -> Option<i32> {
        match self {
            Cond::Equal(_, v)
            | Cond::NotEqual(_, v)
            | Cond::MemEqual(_, v)
            | Cond::MemNotEqual(_, v) => Some(*v),
            _ => None,
        }
    }

    pub fn references(&self) -> BTreeSet<Expr> {
        match self {
            Cond::Always | Cond::Never => BTreeSet::new(),
            Cond::Equal(expr, _) | Cond::NotEqual(expr, _) => expr.references(),
            Cond::MemEqual(target, _) | Cond::MemNotEqual(target, _) => {
                [Expr::Int(*target)].into_iter().collect()
            }
            Cond::Range(expr, _) => expr.references(),
            Cond::Conjunction(clauses) | Cond::Disjunction(clauses) => {
                clauses.iter().flat_map(|c| c.references()).collect()
            }
        }
    }

    pub fn move_pointer(&self, offset: i32) -> Cond {
        if offset == 0 {
            return self.clone();
        }
        match self {
            Cond::Always | Cond::Never => self.clone(),
            Cond::Equal(expr, value) => Cond::equal(expr.move_pointer(offset), *value),
            Cond::NotEqual(expr, value) => Cond::not_equal(expr.move_pointer(offset), *value),
            Cond::MemEqual(target, value) => Cond::equal(Expr::mem(target + offset), *value),
            Cond::MemNotEqual(target, value) => Cond::not_equal(Expr::mem(target + offset), *value),
            Cond::Range(expr, ranges) => Cond::range(expr.move_pointer(offset), ranges.clone()),
            Cond::Conjunction(clauses) => {
                Cond::conjunction(clauses.iter().map(|c| c.move_pointer(offset)).collect())
            }
            Cond::Disjunction(clauses) => {
                Cond::disjunction(clauses.iter().map(|c| c.move_pointer(offset)).collect())
            }
        }
    }

    pub fn with_memory(&self, map: &BTreeMap<i32, Expr>) -> Cond {
        match self {
            Cond::Always | Cond::Never => self.clone(),
            Cond::Equal(expr, value) => Cond::equal(expr.with_memory(map), *value),
            Cond::NotEqual(expr, value) => Cond::not_equal(expr.with_memory(map), *value),
            Cond::MemEqual(target, value) => {
                Cond::equal(Expr::mem(*target).with_memory(map), *value)
            }
            Cond::MemNotEqual(target, value) => {
                Cond::not_equal(Expr::mem(*target).with_memory(map), *value)
            }
            Cond::Range(expr, ranges) => Cond::range(expr.with_memory(map), ranges.clone()),
            Cond::Conjunction(clauses) => {
                Cond::conjunction(clauses.iter().map(|c| c.with_memory(map)).collect())
            }
            Cond::Disjunction(clauses) => {
                Cond::disjunction(clauses.iter().map(|c| c.with_memory(map)).collect())
            }
        }
    }

    pub fn and_cond(&self, other: &Cond) -> Cond {
        Cond::conjunction(vec![self.clone(), other.clone()])
    }
}

pub struct CompactCond<'a>(pub &'a Cond, pub u32);

impl fmt::Display for CompactCond<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let CompactCond(cond, prec) = *self;
        match cond {
            Cond::Always => f.write_str("True"),
            Cond::Never => f.write_str("False"),
            Cond::Equal(expr, 0) => write!(f, "!{}", CompactExpr(expr, 9)),
            Cond::Equal(expr, value) => write!(f, "{}=={value}", CompactExpr(expr, 0)),
            Cond::NotEqual(expr, 0) => CompactExpr(expr, 0).fmt(f),
            Cond::NotEqual(expr, value) => write!(f, "{}!={value}", CompactExpr(expr, 0)),
            Cond::MemEqual(t, 0) => write!(f, "!{{{t}}}"),
            Cond::MemEqual(t, value) => write!(f, "{{{t}}}=={value}"),
            Cond::MemNotEqual(t, 0) => write!(f, "{{{t}}}"),
            Cond::MemNotEqual(t, value) => write!(f, "{{{t}}}!={value}"),
            Cond::Range(expr, ranges) => {
                let e = CompactExpr(expr, 0);
                if ranges.len() == 1 {
                    match ranges[0] {
                        (None, Some(mx)) => write!(f, "{e}<={mx}"),
                        (Some(mn), None) => write!(f, "{mn}<={e}"),
                        (Some(mn), Some(mx)) => write!(f, "{mn}<={e}<={mx}"),
                        (None, None) => f.write_str("True"),
                    }
                } else {
                    write!(f, "{e}~(")?;
                    for (i, &(mn, mx)) in ranges.iter().enumerate() {
                        if i > 0 {
                            f.write_str(",")?;
                        }
                        match (mn, mx) {
                            (None, Some(mx)) => write!(f, "..{mx}")?,
                            (Some(mn), None) => write!(f, "{mn}..")?,
                            (Some(mn), Some(mx)) if mn == mx => write!(f, "{mn}")?,
                            (Some(mn), Some(mx)) => write!(f, "{mn}..{mx}")?,
                            (None, None) => f.write_str("..")?,
                        }
                    }
                    f.write_str(")")
                }
            }
            Cond::Conjunction(clauses) => {
                let need_paren = prec > 1 && clauses.len() > 1;
                if need_paren {
                    f.write_str("(")?;
                }
                for (i, c) in clauses.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" && ")?;
                    }
                    CompactCond(c, 2).fmt(f)?;
                }
                if need_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
            Cond::Disjunction(clauses) => {
                let need_paren = prec > 1 && clauses.len() > 1;
                if need_paren {
                    f.write_str("(")?;
                }
                for (i, c) in clauses.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" || ")?;
                    }
                    CompactCond(c, 2).fmt(f)?;
                }
                if need_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Cond {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<Cond: {}>", CompactCond(self, 0))
    }
}

fn cond_to_expr_key(cond: &Cond) -> Option<Expr> {
    match cond {
        Cond::Equal(e, _) | Cond::NotEqual(e, _) | Cond::Range(e, _) => Some(e.clone()),
        Cond::MemEqual(t, _) | Cond::MemNotEqual(t, _) => Some(Expr::mem(*t)),
        _ => None,
    }
}

fn cond_to_ranges(cond: &Cond) -> Vec<(Option<i32>, Option<i32>)> {
    match cond {
        Cond::Range(_, ranges) => ranges.clone(),
        Cond::Equal(_, v) | Cond::MemEqual(_, v) => vec![(Some(*v), Some(*v))],
        Cond::NotEqual(_, v) | Cond::MemNotEqual(_, v) => {
            vec![(None, Some(*v - 1)), (Some(*v + 1), None)]
        }
        _ => vec![(None, None)],
    }
}

impl Cond {
    pub fn equal(expr: Expr, value: i32) -> Cond {
        if let Some(v) = expr.to_int() {
            return if v == value {
                Cond::Always
            } else {
                Cond::Never
            };
        }
        if let Expr::Reference(inner) = &expr {
            if let Some(off) = inner.to_int() {
                return Cond::MemEqual(off, value);
            }
        }
        if let Expr::Linear(lin) = &expr {
            if lin.constant != 0 {
                return Cond::equal(Expr::linear(0, lin.terms.clone()), value - lin.constant);
            }
            if lin.terms.len() == 1 {
                let coeff = lin.terms[0].0;
                if value % coeff.abs() == 0 {
                    return Cond::equal(lin.terms[0].1.clone(), value / coeff);
                } else {
                    return Cond::Never;
                }
            }
        }
        if let Expr::ExactDivision(lhs, rhs) = &expr {
            if let Some(rv) = rhs.to_int() {
                return Cond::equal((**lhs).clone(), value * rv);
            }
        }
        Cond::Equal(expr, value)
    }

    pub fn not_equal(expr: Expr, value: i32) -> Cond {
        if let Some(v) = expr.to_int() {
            return if v != value {
                Cond::Always
            } else {
                Cond::Never
            };
        }
        if let Expr::Reference(inner) = &expr {
            if let Some(off) = inner.to_int() {
                return Cond::MemNotEqual(off, value);
            }
        }
        if let Expr::Linear(lin) = &expr {
            if lin.constant != 0 {
                return Cond::not_equal(Expr::linear(0, lin.terms.clone()), value - lin.constant);
            }
            if lin.terms.len() == 1 {
                let coeff = lin.terms[0].0;
                if value % coeff.abs() == 0 {
                    return Cond::not_equal(lin.terms[0].1.clone(), value / coeff);
                } else {
                    return Cond::Always;
                }
            }
        }
        if let Expr::ExactDivision(lhs, rhs) = &expr {
            if let Some(rv) = rhs.to_int() {
                return Cond::not_equal((**lhs).clone(), value * rv);
            }
        }
        Cond::NotEqual(expr, value)
    }
}

fn intersect_range(
    lhs: &[(Option<i32>, Option<i32>)],
    rhs: &[(Option<i32>, Option<i32>)],
) -> Vec<(Option<i32>, Option<i32>)> {
    if lhs.is_empty() || rhs.is_empty() {
        return Vec::new();
    }
    let mut result = Vec::new();
    let mut li = 0;
    let mut ri = 0;
    let (mut lmin, mut lmax) = lhs[0];
    let (mut rmin, mut rmax) = rhs[0];
    li += 1;
    ri += 1;

    loop {
        let min = match (lmin, rmin) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.max(b)),
        };
        let max = match (lmax, rmax) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.min(b)),
        };
        match (min, max) {
            (Some(mn), Some(mx)) if mn <= mx => result.push((Some(mn), Some(mx))),
            (None, _) | (_, None) => result.push((min, max)),
            _ => {}
        }
        let advance_l = max == lmax;
        let advance_r = max == rmax;
        if advance_l {
            if li >= lhs.len() {
                break;
            }
            (lmin, lmax) = lhs[li];
            li += 1;
        }
        if advance_r {
            if ri >= rhs.len() {
                break;
            }
            (rmin, rmax) = rhs[ri];
            ri += 1;
        }
    }
    result
}

impl Cond {
    pub fn range(expr: Expr, ranges: Vec<(Option<i32>, Option<i32>)>) -> Cond {
        let mut ranges: Vec<_> = ranges
            .into_iter()
            .filter(|(min, max)| match (min, max) {
                (Some(mn), Some(mx)) => mn <= mx,
                _ => true,
            })
            .collect();

        if let Some(v) = expr.to_int() {
            let in_range = ranges
                .iter()
                .any(|(min, max)| min.is_none_or(|mn| mn <= v) && max.is_none_or(|mx| v <= mx));
            return if in_range { Cond::Always } else { Cond::Never };
        }

        let mut expr = expr;
        loop {
            let mut changed = false;
            if let Expr::Linear(ref lin) = expr {
                if lin.constant != 0 {
                    let c = lin.constant;
                    expr = Expr::linear(0, lin.terms.clone());
                    ranges = ranges
                        .into_iter()
                        .map(|(min, max)| (min.map(|v| v - c), max.map(|v| v - c)))
                        .filter(|(min, max)| !matches!((min, max), (Some(mn), Some(mx)) if mn > mx))
                        .collect();
                    changed = true;
                } else if lin.terms.len() == 1 {
                    let coeff = lin.terms[0].0.abs();
                    let changesign = lin.terms[0].0 < 0;
                    expr = lin.terms[0].1.clone();
                    ranges = ranges
                        .into_iter()
                        .filter_map(|(mut min, mut max)| {
                            if changesign {
                                mem::swap(&mut min, &mut max);
                                min = min.map(|v| (-v - 1) / coeff + 1);
                                max = max.map(|v| -v / coeff);
                            } else {
                                min = min.map(|v| (v - 1) / coeff + 1);
                                max = max.map(|v| v / coeff);
                            }
                            match (min, max) {
                                (Some(mn), Some(mx)) if mn > mx => None,
                                _ => Some((min, max)),
                            }
                        })
                        .collect();
                    changed = true;
                }
            }
            if let Expr::ExactDivision(ref lhs, ref rhs) = expr {
                if let Some(rv) = rhs.to_int() {
                    ranges = ranges
                        .into_iter()
                        .map(|(min, max)| (min.map(|v| v * rv), max.map(|v| v * rv)))
                        .collect();
                    expr = (**lhs).clone();
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        if ranges.is_empty() {
            return Cond::Never;
        }

        ranges.sort_by_key(|&(min, max)| (min.is_some(), min, max.is_none(), max));

        // Merge overlapping/adjacent ranges
        let mut merged = vec![ranges[0]];
        for &(min, max) in &ranges[1..] {
            let (_, last_max) = merged.last_mut().unwrap();
            if last_max.is_none() || min.is_none() || last_max.unwrap() + 1 >= min.unwrap() {
                if max.is_none() || (last_max.is_some() && last_max.unwrap() < max.unwrap()) {
                    *last_max = max;
                }
            } else {
                merged.push((min, max));
            }
        }

        match merged.as_slice() {
            [] => Cond::Never,
            [(min, max)] if min == max => {
                if min.is_none() {
                    Cond::Always
                } else {
                    Cond::equal(expr, min.unwrap())
                }
            }
            [(lo, lo_max), (hi_min, hi)]
                if lo.is_none()
                    && hi.is_none()
                    && lo_max.is_some()
                    && hi_min.is_some()
                    && lo_max.unwrap() == hi_min.unwrap() - 2 =>
            {
                Cond::not_equal(expr, lo_max.unwrap() + 1)
            }
            _ => Cond::Range(expr, merged),
        }
    }

    pub fn conjunction(clauses: Vec<Cond>) -> Cond {
        let mut ranges: RangeMap = BTreeMap::new();
        let mut result = Vec::new();

        for clause in clauses {
            let items: Vec<Cond> = match clause {
                Cond::Conjunction(inner) => inner,
                other => vec![other],
            };
            for iclause in items {
                match &iclause {
                    Cond::Always => continue,
                    Cond::Never => return Cond::Never,
                    _ => {}
                }
                if let Some(key) = cond_to_expr_key(&iclause) {
                    let newrr = cond_to_ranges(&iclause);
                    let rr = ranges.entry(key).or_insert_with(|| vec![(None, None)]);
                    *rr = intersect_range(rr, &newrr);
                } else {
                    result.push(iclause);
                }
            }
        }

        for (expr, rr) in ranges {
            let c = Cond::range(expr, rr);
            match c {
                Cond::Never => return Cond::Never,
                Cond::Always => {}
                other => result.push(other),
            }
        }
        result.sort();

        match result.len() {
            0 => Cond::Always,
            1 => result.remove(0),
            _ => Cond::Conjunction(result),
        }
    }

    pub fn disjunction(clauses: Vec<Cond>) -> Cond {
        let mut ranges: RangeMap = BTreeMap::new();
        let mut result = Vec::new();

        for clause in clauses {
            let items: Vec<Cond> = match clause {
                Cond::Disjunction(inner) => inner,
                other => vec![other],
            };
            for iclause in items {
                match &iclause {
                    Cond::Always => return Cond::Always,
                    Cond::Never => continue,
                    _ => {}
                }
                if let Some(key) = cond_to_expr_key(&iclause) {
                    ranges
                        .entry(key)
                        .or_default()
                        .extend(cond_to_ranges(&iclause));
                } else {
                    result.push(iclause);
                }
            }
        }

        for (expr, rr) in ranges {
            let c = Cond::range(expr, rr);
            match c {
                Cond::Always => return Cond::Always,
                Cond::Never => {}
                other => result.push(other),
            }
        }
        result.sort();

        match result.len() {
            0 => Cond::Never,
            1 => result.remove(0),
            _ => Cond::Disjunction(result),
        }
    }

    pub fn between(min: i32, expr: Expr, max: i32) -> Cond {
        Cond::range(expr, vec![(Some(min), Some(max))])
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;

    #[test]
    fn always_never() {
        assert!(Cond::Always.is_always());
        assert!(!Cond::Always.is_never());
        assert!(Cond::Never.is_never());
        assert!(!Cond::Never.is_always());
    }

    #[test]
    fn make_equal_const_true() {
        assert_eq!(Cond::equal(Expr::Int(5), 5), Cond::Always);
    }

    #[test]
    fn make_equal_const_false() {
        assert_eq!(Cond::equal(Expr::Int(5), 3), Cond::Never);
    }

    #[test]
    fn make_equal_mem_ref() {
        assert_eq!(Cond::equal(Expr::mem(0), 0), Cond::MemEqual(0, 0));
        assert_eq!(Cond::equal(Expr::mem(3), 5), Cond::MemEqual(3, 5));
    }

    #[test]
    fn make_not_equal_const() {
        assert_eq!(Cond::not_equal(Expr::Int(5), 5), Cond::Never);
        assert_eq!(Cond::not_equal(Expr::Int(5), 3), Cond::Always);
    }

    #[test]
    fn make_not_equal_mem_ref() {
        assert_eq!(Cond::not_equal(Expr::mem(0), 0), Cond::MemNotEqual(0, 0));
    }

    #[test]
    fn mem_not_equal_query() {
        let c = Cond::MemNotEqual(0, 0);
        assert!(c.is_mem_not_equal());
        assert_eq!(c.get_target(), Some(0));
        assert_eq!(c.get_value(), Some(0));
    }

    #[test]
    fn make_equal_strips_constant() {
        // Equal({0} + 3, 5) -> Equal({0}, 2) -> MemEqual(0, 2)
        let e = Expr::mem(0) + Expr::Int(3);
        assert_eq!(Cond::equal(e, 5), Cond::MemEqual(0, 2));
    }

    #[test]
    fn make_not_equal_strips_constant() {
        let e = Expr::mem(0) + Expr::Int(3);
        assert_eq!(Cond::not_equal(e, 5), Cond::MemNotEqual(0, 2));
    }

    #[test]
    fn between_const_in_range() {
        assert_eq!(Cond::between(0, Expr::Int(5), 10), Cond::Always);
    }

    #[test]
    fn between_const_out_of_range() {
        assert_eq!(Cond::between(0, Expr::Int(15), 10), Cond::Never);
    }

    #[test]
    fn between_creates_range() {
        let c = Cond::between(1, Expr::mem(0), 5);
        match c {
            Cond::Range(_, ranges) => {
                assert_eq!(ranges, vec![(Some(1), Some(5))]);
            }
            _ => panic!("expected Range, got {:?}", c),
        }
    }

    #[test]
    fn range_single_point_becomes_equal() {
        let c = Cond::range(Expr::mem(0), vec![(Some(5), Some(5))]);
        assert_eq!(c, Cond::MemEqual(0, 5));
    }

    #[test]
    fn range_complement_becomes_not_equal() {
        // (.., 4), (6, ..) = everything except 5
        let c = Cond::range(Expr::mem(0), vec![(None, Some(4)), (Some(6), None)]);
        assert_eq!(c, Cond::MemNotEqual(0, 5));
    }

    #[test]
    fn range_merges_adjacent() {
        // (1..3) and (4..6) should merge to (1..6)
        let c = Cond::range(Expr::mem(0), vec![(Some(1), Some(3)), (Some(4), Some(6))]);
        match c {
            Cond::Range(_, ranges) => {
                assert_eq!(ranges, vec![(Some(1), Some(6))]);
            }
            _ => panic!("expected Range"),
        }
    }

    #[test]
    fn range_empty_is_never() {
        // invalid range (5..3) filtered out
        let c = Cond::range(Expr::mem(0), vec![(Some(5), Some(3))]);
        assert_eq!(c, Cond::Never);
    }

    #[test]
    fn conjunction_always_absorbed() {
        let c = Cond::conjunction(vec![Cond::Always, Cond::MemNotEqual(0, 0)]);
        assert_eq!(c, Cond::MemNotEqual(0, 0));
    }

    #[test]
    fn conjunction_never_short_circuits() {
        let c = Cond::conjunction(vec![Cond::Never, Cond::MemNotEqual(0, 0)]);
        assert_eq!(c, Cond::Never);
    }

    #[test]
    fn conjunction_all_always() {
        assert_eq!(
            Cond::conjunction(vec![Cond::Always, Cond::Always]),
            Cond::Always
        );
    }

    #[test]
    fn disjunction_always_short_circuits() {
        let c = Cond::disjunction(vec![Cond::Always, Cond::MemNotEqual(0, 0)]);
        assert_eq!(c, Cond::Always);
    }

    #[test]
    fn disjunction_never_absorbed() {
        let c = Cond::disjunction(vec![Cond::Never, Cond::MemNotEqual(0, 0)]);
        assert_eq!(c, Cond::MemNotEqual(0, 0));
    }

    #[test]
    fn disjunction_all_never() {
        assert_eq!(
            Cond::disjunction(vec![Cond::Never, Cond::Never]),
            Cond::Never
        );
    }

    #[test]
    fn and_cond_method() {
        let a = Cond::MemNotEqual(0, 0);
        let b = Cond::MemNotEqual(1, 0);
        let c = a.and_cond(&b);
        assert!(matches!(c, Cond::Conjunction(_)));
    }

    #[test]
    fn move_pointer_mem_equal() {
        let c = Cond::MemEqual(3, 5);
        assert_eq!(c.move_pointer(2), Cond::MemEqual(5, 5));
    }

    #[test]
    fn move_pointer_always() {
        assert_eq!(Cond::Always.move_pointer(10), Cond::Always);
    }

    #[test]
    fn move_pointer_zero_noop() {
        let c = Cond::MemNotEqual(0, 0);
        assert_eq!(c.move_pointer(0), c);
    }

    #[test]
    fn with_memory_resolves() {
        let c = Cond::MemNotEqual(0, 0);
        let map = BTreeMap::from([(0, Expr::Int(0))]);
        assert_eq!(c.with_memory(&map), Cond::Never);
    }

    #[test]
    fn with_memory_nonzero() {
        let c = Cond::MemNotEqual(0, 0);
        let map = BTreeMap::from([(0, Expr::Int(5))]);
        assert_eq!(c.with_memory(&map), Cond::Always);
    }

    #[test]
    fn references_mem_equal() {
        let c = Cond::MemEqual(3, 0);
        let refs = c.references();
        assert!(refs.contains(&Expr::Int(3)));
    }

    #[test]
    fn references_always_empty() {
        assert!(Cond::Always.references().is_empty());
    }

    #[test]
    fn display_basics() {
        assert_eq!(CompactCond(&Cond::Always, 0).to_string(), "True");
        assert_eq!(CompactCond(&Cond::Never, 0).to_string(), "False");
        assert_eq!(CompactCond(&Cond::MemNotEqual(0, 0), 0).to_string(), "{0}");
        assert_eq!(CompactCond(&Cond::MemEqual(0, 0), 0).to_string(), "!{0}");
        assert_eq!(
            CompactCond(&Cond::MemNotEqual(0, 5), 0).to_string(),
            "{0}!=5"
        );
        assert_eq!(CompactCond(&Cond::MemEqual(0, 5), 0).to_string(), "{0}==5");
    }
}
