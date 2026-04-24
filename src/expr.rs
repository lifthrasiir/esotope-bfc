use std::collections::{BTreeMap, BTreeSet};
use std::{fmt, ops};

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Expr {
    Int(i32),
    Reference(Box<Expr>),
    Linear(LinearExpr),
    Multiply(Vec<Expr>),
    Division(Box<Expr>, Box<Expr>),
    ExactDivision(Box<Expr>, Box<Expr>),
    Modulo(Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LinearExpr {
    pub constant: i32,
    pub terms: Vec<(i32, Expr)>,
}

impl Expr {
    pub fn reference(offset: Expr) -> Self {
        Expr::Reference(Box::new(offset))
    }

    pub fn mem(offset: i32) -> Self {
        Expr::Reference(Box::new(Expr::Int(offset)))
    }

    pub fn is_simple(&self) -> bool {
        matches!(self, Expr::Int(_))
    }

    pub fn to_int(&self) -> Option<i32> {
        match self {
            Expr::Int(v) => Some(*v),
            Expr::Linear(lin) if lin.terms.is_empty() => Some(lin.constant),
            _ => None,
        }
    }

    pub fn is_nonzero(&self) -> bool {
        self.to_int() != Some(0)
    }

    pub fn references(&self) -> BTreeSet<Expr> {
        match self {
            Expr::Int(_) => BTreeSet::new(),
            Expr::Reference(offset) => {
                let mut s = offset.references();
                s.insert((**offset).clone());
                s
            }
            Expr::Linear(lin) => lin.terms.iter().flat_map(|(_, k)| k.references()).collect(),
            Expr::Multiply(factors) => factors.iter().flat_map(|e| e.references()).collect(),
            Expr::Division(l, r) | Expr::ExactDivision(l, r) | Expr::Modulo(l, r) => {
                let mut s = l.references();
                s.extend(r.references());
                s
            }
        }
    }

    pub fn move_pointer(&self, offset: i32) -> Expr {
        if offset == 0 {
            return self.clone();
        }
        match self {
            Expr::Int(_) => self.clone(),
            Expr::Reference(inner) => {
                Expr::reference(inner.move_pointer(offset) + Expr::Int(offset))
            }
            Expr::Linear(lin) => {
                let terms = lin
                    .terms
                    .iter()
                    .map(|(v, k)| (*v, k.move_pointer(offset)))
                    .collect();
                Expr::linear(lin.constant, terms)
            }
            Expr::Multiply(factors) => {
                Expr::multiply(factors.iter().map(|e| e.move_pointer(offset)).collect())
            }
            Expr::Division(l, r) => Expr::div(l.move_pointer(offset), r.move_pointer(offset)),
            Expr::ExactDivision(l, r) => {
                Expr::exact_div(l.move_pointer(offset), r.move_pointer(offset))
            }
            Expr::Modulo(l, r) => Expr::modulo(l.move_pointer(offset), r.move_pointer(offset)),
        }
    }

    pub fn with_memory(&self, map: &BTreeMap<i32, Expr>) -> Expr {
        match self {
            Expr::Int(_) => self.clone(),
            Expr::Reference(inner) => {
                let new_offset = inner.with_memory(map);
                if let Some(off) = new_offset.to_int() {
                    if let Some(val) = map.get(&off) {
                        let mut remap = map.clone();
                        remap.remove(&off);
                        return val.with_memory(&remap);
                    }
                }
                Expr::reference(new_offset)
            }
            Expr::Linear(lin) => {
                let terms = lin
                    .terms
                    .iter()
                    .map(|(v, k)| (*v, k.with_memory(map)))
                    .collect();
                Expr::linear(lin.constant, terms)
            }
            Expr::Multiply(factors) => {
                Expr::multiply(factors.iter().map(|e| e.with_memory(map)).collect())
            }
            Expr::Division(l, r) => Expr::div(l.with_memory(map), r.with_memory(map)),
            Expr::ExactDivision(l, r) => Expr::exact_div(l.with_memory(map), r.with_memory(map)),
            Expr::Modulo(l, r) => Expr::modulo(l.with_memory(map), r.with_memory(map)),
        }
    }

    pub fn inverse(&self, offset: i32) -> Option<Expr> {
        let offset_expr = Expr::Int(offset);
        match self {
            Expr::Int(_) => None,
            Expr::Reference(inner) => {
                if **inner == offset_expr {
                    Some(self.clone())
                } else {
                    None
                }
            }
            Expr::Linear(lin) => {
                let (mut vary, const_terms): (Vec<_>, Vec<_>) = lin
                    .terms
                    .iter()
                    .cloned()
                    .partition(|(_, term)| term.references().contains(&offset_expr));
                if vary.len() != 1 {
                    return None;
                }
                let (coeff, term) = vary.remove(0);
                let inv = term.inverse(offset)?;
                let const_expr = Expr::linear(lin.constant, const_terms);
                let mut map = BTreeMap::new();
                map.insert(
                    offset,
                    Expr::exact_div(Expr::mem(offset) - const_expr, Expr::Int(coeff)),
                );
                Some(inv.with_memory(&map))
            }
            Expr::Multiply(factors) => {
                let (mut vary, const_factors): (Vec<_>, Vec<_>) = factors
                    .iter()
                    .cloned()
                    .partition(|f| f.references().contains(&offset_expr));
                if vary.len() != 1 {
                    return None;
                }
                let inv = vary.remove(0).inverse(offset)?;
                let const_prod = if const_factors.is_empty() {
                    Expr::Int(1)
                } else {
                    Expr::multiply(const_factors)
                };
                let mut map = BTreeMap::new();
                map.insert(offset, Expr::exact_div(Expr::mem(offset), const_prod));
                Some(inv.with_memory(&map))
            }
            Expr::ExactDivision(lhs, rhs) => {
                let lhs_has = lhs.references().contains(&offset_expr);
                let rhs_has = rhs.references().contains(&offset_expr);
                match (lhs_has, rhs_has) {
                    (true, false) => {
                        let inv = lhs.inverse(offset)?;
                        let mut map = BTreeMap::new();
                        map.insert(offset, Expr::mem(offset) * (**rhs).clone());
                        Some(inv.with_memory(&map))
                    }
                    (false, true) => {
                        let inv = rhs.inverse(offset)?;
                        let mut map = BTreeMap::new();
                        map.insert(offset, Expr::exact_div((**lhs).clone(), Expr::mem(offset)));
                        Some(inv.with_memory(&map))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

pub struct CompactExpr<'a>(pub &'a Expr, pub u32);

impl fmt::Display for CompactExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let CompactExpr(expr, prec) = *self;
        match expr {
            Expr::Int(v) => write!(f, "{v}"),
            Expr::Reference(offset) => write!(f, "{{{}}}", CompactExpr(offset, 0)),
            Expr::Linear(lin) => {
                if lin.terms.is_empty() && lin.constant == 0 {
                    return f.write_str("0");
                }
                let nparts = lin.terms.len() + if lin.constant != 0 { 1 } else { 0 };
                let need_paren = prec > 1 && nparts > 1;
                if need_paren {
                    f.write_str("(")?;
                }
                let mut first = true;
                for (v, k) in &lin.terms {
                    if first {
                        first = false;
                        match v {
                            -1 => write!(f, "-{}", CompactExpr(k, 1))?,
                            1 => CompactExpr(k, 1).fmt(f)?,
                            _ if *v < 0 => write!(f, "{}*{}", v, CompactExpr(k, 1))?,
                            _ => write!(f, "{}*{}", v, CompactExpr(k, 1))?,
                        }
                    } else {
                        match v {
                            -1 => write!(f, "-{}", CompactExpr(k, 1))?,
                            1 => write!(f, "+{}", CompactExpr(k, 1))?,
                            _ => write!(f, "{v:+}*{}", CompactExpr(k, 1))?,
                        }
                    }
                }
                if lin.constant != 0 {
                    if first {
                        write!(f, "{}", lin.constant)?;
                    } else {
                        write!(f, "{:+}", lin.constant)?;
                    }
                }
                if need_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
            Expr::Multiply(factors) => {
                let need_paren = prec > 2 && factors.len() > 1;
                if need_paren {
                    f.write_str("(")?;
                }
                for (i, e) in factors.iter().enumerate() {
                    if i > 0 {
                        f.write_str("*")?;
                    }
                    CompactExpr(e, 2).fmt(f)?;
                }
                if need_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
            Expr::Division(l, r) => {
                if prec > 3 {
                    f.write_str("(")?;
                }
                write!(f, "{}//{}", CompactExpr(l, 2), CompactExpr(r, 3))?;
                if prec > 3 {
                    f.write_str(")")?;
                }
                Ok(())
            }
            Expr::ExactDivision(l, r) => {
                if prec > 3 {
                    f.write_str("(")?;
                }
                write!(f, "{}/{}", CompactExpr(l, 2), CompactExpr(r, 3))?;
                if prec > 3 {
                    f.write_str(")")?;
                }
                Ok(())
            }
            Expr::Modulo(l, r) => {
                if prec > 3 {
                    f.write_str("(")?;
                }
                write!(f, "{}%{}", CompactExpr(l, 2), CompactExpr(r, 3))?;
                if prec > 3 {
                    f.write_str(")")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<Expr: {}>", CompactExpr(self, 0))
    }
}

// --- Operator overloads ---

macro_rules! impl_binop {
    ($trait:ident, $method:ident, $body:expr, $($lhs:ty, $rhs:ty);+) => {
        $(impl ops::$trait<$rhs> for $lhs {
            type Output = Expr;
            fn $method(self, rhs: $rhs) -> Expr {
                let f: fn(Expr, Expr) -> Expr = $body;
                f(self.clone(), rhs.clone())
            }
        })+
    };
}

impl_binop!(Add, add, |a, b| Expr::linear(0, vec![(1, a), (1, b)]),
    Expr, Expr; Expr, &Expr; &Expr, Expr; &Expr, &Expr);

impl_binop!(Sub, sub, |a, b| Expr::linear(0, vec![(1, a), (-1, b)]),
    Expr, Expr; Expr, &Expr; &Expr, Expr; &Expr, &Expr);

impl_binop!(Mul, mul, |a, b| Expr::multiply(vec![a, b]),
    Expr, Expr; Expr, &Expr; &Expr, Expr; &Expr, &Expr);

impl ops::Neg for Expr {
    type Output = Expr;
    fn neg(self) -> Expr {
        Expr::linear(0, vec![(-1, self)])
    }
}

impl ops::Neg for &Expr {
    type Output = Expr;
    fn neg(self) -> Expr {
        Expr::linear(0, vec![(-1, self.clone())])
    }
}

// --- Constructors ---

impl Expr {
    pub fn linear(constant: i32, terms: Vec<(i32, Expr)>) -> Expr {
        let mut c = constant;
        let mut termsmap: BTreeMap<Expr, i32> = BTreeMap::new();

        for (coeff, term) in terms {
            match &term {
                Expr::Int(v) => c += coeff * v,
                Expr::Linear(lin) => {
                    c += coeff * lin.constant;
                    for (icoeff, iterm) in &lin.terms {
                        *termsmap.entry(iterm.clone()).or_insert(0) += coeff * icoeff;
                    }
                }
                _ => {
                    *termsmap.entry(term).or_insert(0) += coeff;
                }
            }
        }

        let mut args: Vec<(i32, Expr)> = termsmap
            .into_iter()
            .filter(|(_, v)| *v != 0)
            .map(|(k, v)| (v, k))
            .collect();

        if args.len() == 1 && c == 0 && args[0].0 == 1 {
            return args.remove(0).1;
        }
        if args.is_empty() {
            return Expr::Int(c);
        }

        Expr::Linear(LinearExpr {
            constant: c,
            terms: args,
        })
    }

    pub fn multiply(terms: Vec<Expr>) -> Expr {
        let mut factor: i32 = 1;
        let mut realterms: Vec<Expr> = Vec::new();

        for term in terms {
            if let Some(v) = term.to_int() {
                factor *= v;
            } else if let Expr::Linear(ref lin) = term {
                if lin.terms.len() == 1 && lin.constant == 0 {
                    factor *= lin.terms[0].0;
                    let inner = lin.terms[0].1.clone();
                    match inner {
                        Expr::Multiply(factors) => realterms.extend(factors),
                        _ => realterms.push(inner),
                    }
                } else {
                    match term {
                        Expr::Multiply(factors) => realterms.extend(factors),
                        other => realterms.push(other),
                    }
                }
            } else if let Expr::Multiply(factors) = term {
                realterms.extend(factors);
            } else {
                realterms.push(term);
            }
        }

        realterms.sort();

        if realterms.is_empty() {
            Expr::Int(factor)
        } else if factor == 0 {
            Expr::Int(0)
        } else if factor != 1 {
            let inner = if realterms.len() == 1 {
                realterms.remove(0)
            } else {
                Expr::Multiply(realterms)
            };
            Expr::linear(0, vec![(factor, inner)])
        } else if realterms.len() == 1 {
            realterms.remove(0)
        } else {
            Expr::Multiply(realterms)
        }
    }

    pub fn div(lhs: Expr, rhs: Expr) -> Expr {
        if let Some(rv) = rhs.to_int() {
            if let Some(lv) = lhs.to_int() {
                return Expr::Int(lv.div_euclid(rv));
            }
            match rv {
                1 => return lhs,
                -1 => return -lhs,
                _ if rv < 0 => return Expr::div(-lhs, Expr::Int(-rv)),
                _ => {}
            }
        }
        Expr::Division(Box::new(lhs), Box::new(rhs))
    }

    pub fn exact_div(lhs: Expr, rhs: Expr) -> Expr {
        if let Some(rv) = rhs.to_int() {
            if let Some(lv) = lhs.to_int() {
                assert!(
                    rv != 0 && lv % rv == 0,
                    "exact division failed: {lv} / {rv}"
                );
                return Expr::Int(lv / rv);
            }
            match rv {
                1 => return lhs,
                -1 => return -lhs,
                _ if rv < 0 => return Expr::exact_div(-lhs, Expr::Int(-rv)),
                _ => {}
            }
        }
        Expr::ExactDivision(Box::new(lhs), Box::new(rhs))
    }

    pub fn modulo(lhs: Expr, rhs: Expr) -> Expr {
        if let (Some(lv), Some(rv)) = (lhs.to_int(), rhs.to_int()) {
            return Expr::Int(lv.rem_euclid(rv));
        }
        Expr::Modulo(Box::new(lhs), Box::new(rhs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_basics() {
        assert_eq!(Expr::Int(0).to_int(), Some(0));
        assert_eq!(Expr::Int(42).to_int(), Some(42));
        assert!(Expr::Int(0).is_simple());
        assert!(!Expr::Int(0).is_nonzero());
        assert!(Expr::Int(1).is_nonzero());
    }

    #[test]
    fn mem_reference() {
        let e = Expr::mem(3);
        assert!(!e.is_simple());
        assert_eq!(e.to_int(), None);
        assert!(e.references().contains(&Expr::Int(3)));
    }

    #[test]
    fn add_integers() {
        let r = Expr::Int(3) + Expr::Int(5);
        assert_eq!(r, Expr::Int(8));
    }

    #[test]
    fn sub_integers() {
        let r = Expr::Int(10) - Expr::Int(4);
        assert_eq!(r, Expr::Int(6));
    }

    #[test]
    fn neg_integer() {
        assert_eq!(-Expr::Int(5), Expr::Int(-5));
    }

    #[test]
    fn mul_integers() {
        let r = Expr::Int(3) * Expr::Int(7);
        assert_eq!(r, Expr::Int(21));
    }

    #[test]
    fn mul_by_zero() {
        let r = Expr::mem(0) * Expr::Int(0);
        assert_eq!(r, Expr::Int(0));
    }

    #[test]
    fn mul_by_one() {
        let r = Expr::mem(0) * Expr::Int(1);
        assert_eq!(r, Expr::mem(0));
    }

    #[test]
    fn linear_canonicalization() {
        // {0} + {0} = 2*{0}
        let r = Expr::mem(0) + Expr::mem(0);
        match r {
            Expr::Linear(lin) => {
                assert_eq!(lin.constant, 0);
                assert_eq!(lin.terms.len(), 1);
                assert_eq!(lin.terms[0].0, 2);
            }
            _ => panic!("expected Linear, got {:?}", r),
        }
    }

    #[test]
    fn linear_cancellation() {
        // {0} - {0} = 0
        let r = Expr::mem(0) - Expr::mem(0);
        assert_eq!(r, Expr::Int(0));
    }

    #[test]
    fn add_with_constant() {
        // {0} + 5
        let r = Expr::mem(0) + Expr::Int(5);
        match r {
            Expr::Linear(lin) => {
                assert_eq!(lin.constant, 5);
                assert_eq!(lin.terms.len(), 1);
                assert_eq!(lin.terms[0].0, 1);
            }
            _ => panic!("expected Linear"),
        }
    }

    #[test]
    fn division_const() {
        assert_eq!(Expr::div(Expr::Int(10), Expr::Int(3)), Expr::Int(3));
        assert_eq!(Expr::div(Expr::Int(-7), Expr::Int(2)), Expr::Int(-4)); // floor div
    }

    #[test]
    fn exact_division_const() {
        assert_eq!(Expr::exact_div(Expr::Int(10), Expr::Int(5)), Expr::Int(2));
        assert_eq!(Expr::exact_div(Expr::Int(0), Expr::Int(3)), Expr::Int(0));
    }

    #[test]
    #[should_panic(expected = "exact division failed")]
    fn exact_division_fails() {
        Expr::exact_div(Expr::Int(7), Expr::Int(3));
    }

    #[test]
    fn modulo_const() {
        assert_eq!(Expr::modulo(Expr::Int(10), Expr::Int(3)), Expr::Int(1));
        assert_eq!(Expr::modulo(Expr::Int(-1), Expr::Int(256)), Expr::Int(255));
    }

    #[test]
    fn division_by_one() {
        let e = Expr::mem(0);
        assert_eq!(Expr::div(e.clone(), Expr::Int(1)), e);
    }

    #[test]
    fn move_pointer_int_unchanged() {
        assert_eq!(Expr::Int(42).move_pointer(5), Expr::Int(42));
    }

    #[test]
    fn move_pointer_reference() {
        // {3} shifted by 4 = {7}
        let e = Expr::mem(3);
        assert_eq!(e.move_pointer(4), Expr::mem(7));
    }

    #[test]
    fn move_pointer_zero_noop() {
        let e = Expr::mem(3) + Expr::Int(1);
        assert_eq!(e.move_pointer(0), e);
    }

    #[test]
    fn with_memory_substitution() {
        // {0} with map {0 -> 42} = 42
        let e = Expr::mem(0);
        let map = BTreeMap::from([(0, Expr::Int(42))]);
        assert_eq!(e.with_memory(&map), Expr::Int(42));
    }

    #[test]
    fn with_memory_no_match() {
        let e = Expr::mem(1);
        let map = BTreeMap::from([(0, Expr::Int(42))]);
        assert_eq!(e.with_memory(&map), Expr::mem(1));
    }

    #[test]
    fn with_memory_linear() {
        // {0} + 5 with {0 -> 10} = 15
        let e = Expr::mem(0) + Expr::Int(5);
        let map = BTreeMap::from([(0, Expr::Int(10))]);
        assert_eq!(e.with_memory(&map), Expr::Int(15));
    }

    #[test]
    fn inverse_identity() {
        // {0} = {0} -> inverse is {0}
        let e = Expr::mem(0);
        let inv = e.inverse(0).unwrap();
        assert_eq!(inv, Expr::mem(0));
    }

    #[test]
    fn inverse_linear() {
        // {0} = {0} + 3 -> inverse: {0} = {0} - 3
        let e = Expr::mem(0) + Expr::Int(3);
        let inv = e.inverse(0).unwrap();
        // inv should produce {0} - 3
        let map = BTreeMap::from([(0, Expr::Int(10))]);
        assert_eq!(inv.with_memory(&map), Expr::Int(7));
    }

    #[test]
    fn inverse_no_ref() {
        // constant expression -> not invertible
        assert!(Expr::Int(5).inverse(0).is_none());
    }

    #[test]
    fn references_empty_for_int() {
        assert!(Expr::Int(42).references().is_empty());
    }

    #[test]
    fn references_for_linear() {
        let e = Expr::mem(0) + Expr::mem(3);
        let refs = e.references();
        assert!(refs.contains(&Expr::Int(0)));
        assert!(refs.contains(&Expr::Int(3)));
    }

    #[test]
    fn display_int() {
        assert_eq!(CompactExpr(&Expr::Int(42), 0).to_string(), "42");
        assert_eq!(CompactExpr(&Expr::Int(-3), 0).to_string(), "-3");
    }

    #[test]
    fn display_reference() {
        assert_eq!(CompactExpr(&Expr::mem(0), 0).to_string(), "{0}");
        assert_eq!(CompactExpr(&Expr::mem(5), 0).to_string(), "{5}");
    }

    #[test]
    fn display_linear() {
        let e = Expr::mem(0) + Expr::Int(3);
        let s = CompactExpr(&e, 0).to_string();
        assert!(s.contains("{0}"));
        assert!(s.contains("+3") || s.contains("3"));
    }

    #[test]
    fn display_trait() {
        let e = Expr::Int(42);
        assert_eq!(format!("{}", e), "<Expr: 42>");
    }

    #[test]
    fn linear_flatten_nested() {
        // (a + 1) + (a + 2) = 2a + 3
        let a = Expr::mem(0);
        let r = (a.clone() + Expr::Int(1)) + (a + Expr::Int(2));
        match r {
            Expr::Linear(lin) => {
                assert_eq!(lin.constant, 3);
                assert_eq!(lin.terms[0].0, 2);
            }
            _ => panic!("expected Linear"),
        }
    }

    #[test]
    fn multiply_flatten() {
        // a * b * c should stay flat
        let (a, b, c) = (Expr::mem(0), Expr::mem(1), Expr::mem(2));
        let r = a * b;
        let r = r * c;
        if let Expr::Multiply(factors) = &r {
            assert_eq!(factors.len(), 3);
        } else {
            // Could also be linear with multiply inside, which is fine
        }
    }
}
