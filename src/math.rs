pub fn gcd(a: i32, b: i32) -> i32 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

pub fn gcdex(mut x: i32, mut y: i32) -> (i32, i32, i32) {
    let (mut a, mut b) = (0i32, 1i32);
    let (mut c, mut d) = (1i32, 0i32);
    while x != 0 {
        let q = y / x;
        let r = y % x;
        let u = a - c * q;
        let v = b - d * q;
        y = x;
        x = r;
        a = c;
        b = d;
        c = u;
        d = v;
    }
    (a, b, y)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcdex_coprime() {
        let (u, _v, gcd) = gcdex(1, 256);
        assert_eq!(gcd, 1);
        assert_eq!((u % 256 + 256) % 256, 1);
    }

    #[test]
    fn gcdex_even() {
        let (_u, _v, gcd) = gcdex(2, 256);
        assert_eq!(gcd, 2);
    }

    #[test]
    fn gcdex_identity() {
        let (u, v, gcd) = gcdex(35, 15);
        assert_eq!(gcd, 5);
        assert_eq!(u * 35 + v * 15, gcd);
    }

    #[test]
    fn gcdex_zero() {
        let (_u, _v, gcd) = gcdex(0, 256);
        assert_eq!(gcd, 256);
    }
}
