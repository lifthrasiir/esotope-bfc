pub fn gcd(a: i32, b: i32) -> i32 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

pub fn gcdex_i64(mut x: i64, mut y: i64) -> (i64, i64, i64) {
    let (mut a, mut b) = (0i64, 1i64);
    let (mut c, mut d) = (1i64, 0i64);
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
        let (u, _v, gcd) = gcdex_i64(1, 256);
        assert_eq!(gcd, 1);
        assert_eq!((u % 256 + 256) % 256, 1);
    }

    #[test]
    fn gcdex_even() {
        let (_u, _v, gcd) = gcdex_i64(2, 256);
        assert_eq!(gcd, 2);
    }

    #[test]
    fn gcdex_identity() {
        let (u, v, gcd) = gcdex_i64(35, 15);
        assert_eq!(gcd, 5);
        assert_eq!(u * 35 + v * 15, gcd);
    }

    #[test]
    fn gcdex_zero() {
        let (_u, _v, gcd) = gcdex_i64(0, 256);
        assert_eq!(gcd, 256);
    }

    #[test]
    fn gcdex_i64_32_bit_modulus() {
        let (u, _v, gcd) = gcdex_i64((1i64 << 32) - 1, 1i64 << 32);
        assert_eq!(gcd, 1);
        assert_eq!(
            (u % (1i64 << 32) + (1i64 << 32)) % (1i64 << 32),
            (1i64 << 32) - 1
        );
    }
}
