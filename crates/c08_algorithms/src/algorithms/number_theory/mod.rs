//! # 数论算法模块
//! 
//! 本模块实现了各种数论算法。

//use serde::{Serialize, Deserialize};

/// 数论算法实现
pub struct NumberTheoryAlgorithms;

impl NumberTheoryAlgorithms {
    /// 最大公约数 (GCD)
    pub fn gcd(a: u64, b: u64) -> u64 {
        if b == 0 {
            a
        } else {
            Self::gcd(b, a % b)
        }
    }

    /// 最小公倍数 (LCM)
    pub fn lcm(a: u64, b: u64) -> u64 {
        a * b / Self::gcd(a, b)
    }

    /// 快速幂
    pub fn fast_power(base: u64, exponent: u64, modulus: u64) -> u64 {
        let mut result = 1;
        let mut base = base % modulus;
        let mut exp = exponent;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = (result * base) % modulus;
            }
            exp >>= 1;
            base = (base * base) % modulus;
        }
        
        result
    }

    /// 素数检测
    pub fn is_prime(n: u64) -> bool {
        if n < 2 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n.is_multiple_of(2) {
            return false;
        }
        
        let mut i = 3;
        while i * i <= n {
            if n.is_multiple_of(i) {
                return false;
            }
            i += 2;
        }
        
        true
    }

    /// 埃拉托斯特尼筛法
    pub fn sieve_of_eratosthenes(n: usize) -> Vec<bool> {
        let mut is_prime = vec![true; n + 1];
        is_prime[0] = false;
        is_prime[1] = false;
        
        let mut p = 2;
        while p * p <= n {
            if is_prime[p] {
                let mut i = p * p;
                while i <= n {
                    is_prime[i] = false;
                    i += p;
                }
            }
            p += 1;
        }
        
        is_prime
    }
}
