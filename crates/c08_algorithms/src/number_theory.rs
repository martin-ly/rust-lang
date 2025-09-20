//! 数论基础：快速幂、扩展欧几里得、模逆、Miller–Rabin、Pollard Rho

pub fn mod_pow(mut a: u128, mut e: u128, m: u128) -> u128 {
    let mut r = 1u128;
    a %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = r.saturating_mul(a) % m;
        }
        a = a.saturating_mul(a) % m;
        e >>= 1;
    }
    r
}

pub fn egcd(a: i128, b: i128) -> (i128, i128, i128) {
    if b == 0 {
        (a.abs(), a.signum(), 0)
    } else {
        let (g, x, y) = egcd(b, a % b);
        (g, y, x - (a / b) * y)
    }
}

pub fn mod_inv(a: i128, m: i128) -> Option<i128> {
    let (g, x, _) = egcd(a, m);
    if g != 1 { None } else { Some((x % m + m) % m) }
}

fn is_probable_prime_u64(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n.is_multiple_of(p) {
            return n == p;
        }
    }
    let d = (n - 1) >> (n - 1).trailing_zeros();
    let s = (n - 1).trailing_zeros();
    let bases: [u64; 7] = [2, 325, 9375, 28178, 450775, 9780504, 1795265022]; // 对 64-bit 完整
    'a: for &a in &bases {
        let mut x = mod_pow(a as u128 % n as u128, d as u128, n as u128) as u64;
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 1..s {
            x = ((x as u128 * x as u128) % n as u128) as u64;
            if x == n - 1 {
                continue 'a;
            }
        }
        return false;
    }
    true
}

pub fn is_prime(n: u64) -> bool {
    is_probable_prime_u64(n)
}

fn f_rho(x: u128, c: u128, n: u128) -> u128 {
    (x.saturating_mul(x).saturating_add(c)) % n
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}
pub fn pollard_rho(n: u128) -> u128 {
    if n.is_multiple_of(2) {
        return 2;
    }
    use rand::{Rng, rngs::ThreadRng};
    let mut rng = ThreadRng::default();
    loop {
        let c = rng.random_range(1..n);
        let mut x = rng.random_range(0..n);
        let mut y = x;
        let mut d: u128 = 1;
        while d == 1 {
            x = f_rho(x, c, n);
            y = f_rho(f_rho(y, c, n), c, n);
            let diff = x.abs_diff(y);
            d = gcd_u128(diff, n);
        }
        if d != n {
            return d;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_mod_pow_inv() {
        assert_eq!(mod_pow(2, 10, 1_000_000_007), 1024);
        assert_eq!(mod_inv(3, 11), Some(4)); // 3*4 = 12 ≡ 1 (mod 11)
    }
    #[test]
    fn test_mr_pollard() {
        assert!(is_prime(1_000_000_007));
        let n: u128 = 91; // 7*13
        let f = pollard_rho(n);
        assert!(f == 7 || f == 13);
    }
}
