//! 密码学算法实现模块
//! 
//! 本模块提供了Rust中的密码学算法实现，包括：
//! - RSA加密算法
//! - AES加密算法
//! - SHA-256哈希算法
//! - 椭圆曲线密码学

use std::collections::HashMap;

/// RSA加密算法实现
pub struct RSA {
    public_key: (u64, u64),
    private_key: (u64, u64),
}

impl RSA {
    pub fn new(bit_length: usize) -> Self {
        // 生成大素数
        let p = Self::generate_prime(bit_length / 2);
        let q = Self::generate_prime(bit_length / 2);
        
        let n = p * q;
        let phi = (p - 1) * (q - 1);
        
        // 选择公钥指数
        let e = 65537; // 常用的公钥指数
        
        // 计算私钥指数
        let d = Self::mod_inverse(e, phi);
        
        Self {
            public_key: (e, n),
            private_key: (d, n),
        }
    }
    
    pub fn encrypt(&self, message: u64) -> u64 {
        Self::mod_pow(message, self.public_key.0, self.public_key.1)
    }
    
    pub fn decrypt(&self, ciphertext: u64) -> u64 {
        Self::mod_pow(ciphertext, self.private_key.0, self.private_key.1)
    }
    
    pub fn get_public_key(&self) -> (u64, u64) {
        self.public_key
    }
    
    pub fn get_private_key(&self) -> (u64, u64) {
        self.private_key
    }
    
    fn generate_prime(bits: usize) -> u64 {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        loop {
            let candidate = rng.gen_range(2u64.pow(bits as u32)..2u64.pow((bits + 1) as u32));
            if Self::is_prime(candidate) {
                return candidate;
            }
        }
    }
    
    fn is_prime(n: u64) -> bool {
        if n < 2 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }
        
        let mut d = n - 1;
        let mut s = 0;
        while d % 2 == 0 {
            d /= 2;
            s += 1;
        }
        
        // Miller-Rabin素性测试
        for _ in 0..5 {
            let a = rand::thread_rng().gen_range(2..n);
            let mut x = Self::mod_pow(a, d, n);
            
            if x == 1 || x == n - 1 {
                continue;
            }
            
            let mut is_composite = true;
            for _ in 0..s - 1 {
                x = (x * x) % n;
                if x == n - 1 {
                    is_composite = false;
                    break;
                }
            }
            
            if is_composite {
                return false;
            }
        }
        
        true
    }
    
    fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
        let mut result = 1;
        base %= modulus;
        
        while exponent > 0 {
            if exponent % 2 == 1 {
                result = (result * base) % modulus;
            }
            base = (base * base) % modulus;
            exponent /= 2;
        }
        
        result
    }
    
    fn mod_inverse(a: u64, m: u64) -> u64 {
        let mut t = 0;
        let mut new_t = 1;
        let mut r = m;
        let mut new_r = a;
        
        while new_r != 0 {
            let quotient = r / new_r;
            let temp_t = t;
            t = new_t;
            new_t = temp_t - quotient * new_t;
            let temp_r = r;
            r = new_r;
            new_r = temp_r - quotient * new_r;
        }
        
        if r > 1 {
            panic!("Modular inverse does not exist");
        }
        
        if t < 0 {
            t += m;
        }
        
        t
    }
}

/// AES加密算法实现 (简化版)
pub struct AES {
    key: [u8; 16],
    round_keys: [[u8; 16]; 11],
}

impl AES {
    pub fn new(key: [u8; 16]) -> Self {
        let mut aes = Self {
            key,
            round_keys: [[0; 16]; 11],
        };
        aes.key_expansion();
        aes
    }
    
    pub fn encrypt(&self, plaintext: [u8; 16]) -> [u8; 16] {
        let mut state = plaintext;
        
        // 初始轮密钥加
        Self::add_round_key(&mut state, &self.round_keys[0]);
        
        // 9个主轮
        for round in 1..10 {
            Self::sub_bytes(&mut state);
            Self::shift_rows(&mut state);
            Self::mix_columns(&mut state);
            Self::add_round_key(&mut state, &self.round_keys[round]);
        }
        
        // 最后一轮
        Self::sub_bytes(&mut state);
        Self::shift_rows(&mut state);
        Self::add_round_key(&mut state, &self.round_keys[10]);
        
        state
    }
    
    pub fn decrypt(&self, ciphertext: [u8; 16]) -> [u8; 16] {
        let mut state = ciphertext;
        
        // 初始轮密钥加
        Self::add_round_key(&mut state, &self.round_keys[10]);
        
        // 9个主轮
        for round in (1..10).rev() {
            Self::inv_shift_rows(&mut state);
            Self::inv_sub_bytes(&mut state);
            Self::add_round_key(&mut state, &self.round_keys[round]);
            Self::inv_mix_columns(&mut state);
        }
        
        // 最后一轮
        Self::inv_shift_rows(&mut state);
        Self::inv_sub_bytes(&mut state);
        Self::add_round_key(&mut state, &self.round_keys[0]);
        
        state
    }
    
    fn key_expansion(&mut self) {
        // 简化的密钥扩展
        for i in 0..11 {
            for j in 0..16 {
                self.round_keys[i][j] = self.key[j] ^ (i as u8);
            }
        }
    }
    
    fn sub_bytes(state: &mut [u8; 16]) {
        // 简化的S盒替换
        for byte in state.iter_mut() {
            *byte = (*byte + 1) % 256;
        }
    }
    
    fn inv_sub_bytes(state: &mut [u8; 16]) {
        // 简化的逆S盒替换
        for byte in state.iter_mut() {
            *byte = (*byte + 255) % 256;
        }
    }
    
    fn shift_rows(state: &mut [u8; 16]) {
        // 行移位
        let temp = state[1];
        state[1] = state[5];
        state[5] = state[9];
        state[9] = state[13];
        state[13] = temp;
        
        let temp1 = state[2];
        let temp2 = state[6];
        state[2] = state[10];
        state[6] = state[14];
        state[10] = temp1;
        state[14] = temp2;
        
        let temp = state[15];
        state[15] = state[11];
        state[11] = state[7];
        state[7] = state[3];
        state[3] = temp;
    }
    
    fn inv_shift_rows(state: &mut [u8; 16]) {
        // 逆行移位
        let temp = state[13];
        state[13] = state[9];
        state[9] = state[5];
        state[5] = state[1];
        state[1] = temp;
        
        let temp1 = state[10];
        let temp2 = state[14];
        state[10] = state[2];
        state[14] = state[6];
        state[2] = temp1;
        state[6] = temp2;
        
        let temp = state[3];
        state[3] = state[7];
        state[7] = state[11];
        state[11] = state[15];
        state[15] = temp;
    }
    
    fn mix_columns(state: &mut [u8; 16]) {
        // 简化的列混合
        for i in 0..4 {
            let col_start = i * 4;
            let temp = state[col_start];
            state[col_start] = state[col_start + 1];
            state[col_start + 1] = state[col_start + 2];
            state[col_start + 2] = state[col_start + 3];
            state[col_start + 3] = temp;
        }
    }
    
    fn inv_mix_columns(state: &mut [u8; 16]) {
        // 简化的逆列混合
        for i in 0..4 {
            let col_start = i * 4;
            let temp = state[col_start + 3];
            state[col_start + 3] = state[col_start + 2];
            state[col_start + 2] = state[col_start + 1];
            state[col_start + 1] = state[col_start];
            state[col_start] = temp;
        }
    }
    
    fn add_round_key(state: &mut [u8; 16], round_key: &[u8; 16]) {
        for i in 0..16 {
            state[i] ^= round_key[i];
        }
    }
}

/// SHA-256哈希算法实现
pub struct SHA256 {
    state: [u32; 8],
}

impl SHA256 {
    pub fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
            ],
        }
    }
    
    pub fn hash(&mut self, data: &[u8]) -> [u8; 32] {
        let mut message = data.to_vec();
        let original_length = message.len() * 8;
        
        // 填充
        message.push(0x80);
        while (message.len() + 8) % 64 != 0 {
            message.push(0x00);
        }
        
        // 添加长度
        for i in 0..8 {
            message.push(((original_length >> (56 - i * 8)) & 0xFF) as u8);
        }
        
        // 处理每个512位块
        for chunk in message.chunks(64) {
            self.process_block(chunk);
        }
        
        // 返回哈希值
        let mut result = [0u8; 32];
        for i in 0..8 {
            let bytes = self.state[i].to_be_bytes();
            result[i * 4..(i + 1) * 4].copy_from_slice(&bytes);
        }
        result
    }
    
    fn process_block(&mut self, block: &[u8]) {
        let mut w = [0u32; 64];
        
        // 准备消息调度
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[i * 4],
                block[i * 4 + 1],
                block[i * 4 + 2],
                block[i * 4 + 3],
            ]);
        }
        
        for i in 16..64 {
            let s0 = Self::right_rotate(w[i - 15], 7) ^ Self::right_rotate(w[i - 15], 18) ^ (w[i - 15] >> 3);
            let s1 = Self::right_rotate(w[i - 2], 17) ^ Self::right_rotate(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        
        let mut a = self.state[0];
        let mut b = self.state[1];
        let mut c = self.state[2];
        let mut d = self.state[3];
        let mut e = self.state[4];
        let mut f = self.state[5];
        let mut g = self.state[6];
        let mut h = self.state[7];
        
        // 主循环
        for i in 0..64 {
            let s1 = Self::right_rotate(e, 6) ^ Self::right_rotate(e, 11) ^ Self::right_rotate(e, 25);
            let ch = (e & f) ^ (!e & g);
            let temp1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(Self::K[i]).wrapping_add(w[i]);
            let s0 = Self::right_rotate(a, 2) ^ Self::right_rotate(a, 13) ^ Self::right_rotate(a, 22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        
        // 更新状态
        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
        self.state[5] = self.state[5].wrapping_add(f);
        self.state[6] = self.state[6].wrapping_add(g);
        self.state[7] = self.state[7].wrapping_add(h);
    }
    
    fn right_rotate(value: u32, shift: u32) -> u32 {
        (value >> shift) | (value << (32 - shift))
    }
    
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
}

/// 椭圆曲线密码学 (简化版)
pub struct EllipticCurve {
    p: u64,  // 素数域
    a: u64,  // 曲线参数a
    b: u64,  // 曲线参数b
    g: Point, // 生成点
    n: u64,  // 生成点的阶
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Point {
    x: u64,
    y: u64,
    is_infinity: bool,
}

impl Point {
    fn new(x: u64, y: u64) -> Self {
        Self {
            x,
            y,
            is_infinity: false,
        }
    }
    
    fn infinity() -> Self {
        Self {
            x: 0,
            y: 0,
            is_infinity: true,
        }
    }
}

impl EllipticCurve {
    pub fn new(p: u64, a: u64, b: u64, g_x: u64, g_y: u64, n: u64) -> Self {
        Self {
            p,
            a,
            b,
            g: Point::new(g_x, g_y),
            n,
        }
    }
    
    pub fn add(&self, p1: Point, p2: Point) -> Point {
        if p1.is_infinity {
            return p2;
        }
        if p2.is_infinity {
            return p1;
        }
        
        if p1.x == p2.x && p1.y != p2.y {
            return Point::infinity();
        }
        
        let lambda = if p1.x == p2.x {
            // 点加倍
            let numerator = (3 * p1.x * p1.x + self.a) % self.p;
            let denominator = (2 * p1.y) % self.p;
            (numerator * Self::mod_inverse(denominator, self.p)) % self.p
        } else {
            // 点相加
            let numerator = (p2.y + self.p - p1.y) % self.p;
            let denominator = (p2.x + self.p - p1.x) % self.p;
            (numerator * Self::mod_inverse(denominator, self.p)) % self.p
        };
        
        let x3 = (lambda * lambda + self.p - p1.x + self.p - p2.x) % self.p;
        let y3 = (lambda * (p1.x + self.p - x3) + self.p - p1.y) % self.p;
        
        Point::new(x3, y3)
    }
    
    pub fn scalar_multiply(&self, k: u64, point: Point) -> Point {
        let mut result = Point::infinity();
        let mut current = point;
        let mut scalar = k;
        
        while scalar > 0 {
            if scalar % 2 == 1 {
                result = self.add(result, current);
            }
            current = self.add(current, current);
            scalar /= 2;
        }
        
        result
    }
    
    pub fn generate_keypair(&self) -> (u64, Point) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        let private_key = rng.gen_range(1..self.n);
        let public_key = self.scalar_multiply(private_key, self.g);
        
        (private_key, public_key)
    }
    
    pub fn encrypt(&self, message: u64, public_key: Point) -> (Point, Point) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        let k = rng.gen_range(1..self.n);
        let c1 = self.scalar_multiply(k, self.g);
        let c2 = self.scalar_multiply(k, public_key);
        
        // 简化的消息编码
        let encoded_message = Point::new(message, 0);
        let ciphertext = self.add(c2, encoded_message);
        
        (c1, ciphertext)
    }
    
    pub fn decrypt(&self, ciphertext: (Point, Point), private_key: u64) -> u64 {
        let (c1, c2) = ciphertext;
        let s = self.scalar_multiply(private_key, c1);
        let s_inv = Point::new(s.x, (self.p - s.y) % self.p);
        let message_point = self.add(c2, s_inv);
        
        message_point.x
    }
    
    fn mod_inverse(a: u64, m: u64) -> u64 {
        let mut t = 0;
        let mut new_t = 1;
        let mut r = m;
        let mut new_r = a;
        
        while new_r != 0 {
            let quotient = r / new_r;
            let temp_t = t;
            t = new_t;
            new_t = temp_t - quotient * new_t;
            let temp_r = r;
            r = new_r;
            new_r = temp_r - quotient * new_r;
        }
        
        if r > 1 {
            panic!("Modular inverse does not exist");
        }
        
        if t < 0 {
            t += m;
        }
        
        t
    }
}

/// 数字签名算法
pub struct DigitalSignature {
    curve: EllipticCurve,
}

impl DigitalSignature {
    pub fn new(curve: EllipticCurve) -> Self {
        Self { curve }
    }
    
    pub fn sign(&self, message: &[u8], private_key: u64) -> (u64, u64) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        let message_hash = self.hash_message(message);
        
        loop {
            let k = rng.gen_range(1..self.curve.n);
            let r_point = self.curve.scalar_multiply(k, self.curve.g);
            let r = r_point.x % self.curve.n;
            
            if r == 0 {
                continue;
            }
            
            let k_inv = Self::mod_inverse(k, self.curve.n);
            let s = (k_inv * (message_hash + private_key * r)) % self.curve.n;
            
            if s != 0 {
                return (r, s);
            }
        }
    }
    
    pub fn verify(&self, message: &[u8], signature: (u64, u64), public_key: Point) -> bool {
        let (r, s) = signature;
        
        if r == 0 || r >= self.curve.n || s == 0 || s >= self.curve.n {
            return false;
        }
        
        let message_hash = self.hash_message(message);
        let w = Self::mod_inverse(s, self.curve.n);
        let u1 = (message_hash * w) % self.curve.n;
        let u2 = (r * w) % self.curve.n;
        
        let point1 = self.curve.scalar_multiply(u1, self.curve.g);
        let point2 = self.curve.scalar_multiply(u2, public_key);
        let v_point = self.curve.add(point1, point2);
        
        v_point.x % self.curve.n == r
    }
    
    fn hash_message(&self, message: &[u8]) -> u64 {
        let mut sha256 = SHA256::new();
        let hash = sha256.hash(message);
        
        // 取前8字节作为哈希值
        let mut result = 0u64;
        for i in 0..8 {
            result = (result << 8) | hash[i] as u64;
        }
        result % self.curve.n
    }
    
    fn mod_inverse(a: u64, m: u64) -> u64 {
        let mut t = 0;
        let mut new_t = 1;
        let mut r = m;
        let mut new_r = a;
        
        while new_r != 0 {
            let quotient = r / new_r;
            let temp_t = t;
            t = new_t;
            new_t = temp_t - quotient * new_t;
            let temp_r = r;
            r = new_r;
            new_r = temp_r - quotient * new_r;
        }
        
        if r > 1 {
            panic!("Modular inverse does not exist");
        }
        
        if t < 0 {
            t += m;
        }
        
        t
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_rsa_encryption() {
        let rsa = RSA::new(64);
        let message = 12345;
        
        let encrypted = rsa.encrypt(message);
        let decrypted = rsa.decrypt(encrypted);
        
        assert_eq!(message, decrypted);
    }
    
    #[test]
    fn test_aes_encryption() {
        let key = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let aes = AES::new(key);
        let plaintext = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        
        let encrypted = aes.encrypt(plaintext);
        let decrypted = aes.decrypt(encrypted);
        
        assert_eq!(plaintext, decrypted);
    }
    
    #[test]
    fn test_sha256() {
        let mut sha256 = SHA256::new();
        let data = b"Hello, World!";
        let hash = sha256.hash(data);
        
        assert_eq!(hash.len(), 32);
        assert_ne!(hash, [0u8; 32]);
    }
    
    #[test]
    fn test_elliptic_curve() {
        // 使用简化的椭圆曲线参数
        let curve = EllipticCurve::new(23, 1, 1, 3, 10, 28);
        let point1 = Point::new(3, 10);
        let point2 = Point::new(9, 7);
        
        let sum = curve.add(point1, point2);
        assert!(!sum.is_infinity);
    }
    
    #[test]
    fn test_digital_signature() {
        let curve = EllipticCurve::new(23, 1, 1, 3, 10, 28);
        let ds = DigitalSignature::new(curve);
        
        let (private_key, public_key) = curve.generate_keypair();
        let message = b"Hello, World!";
        
        let signature = ds.sign(message, private_key);
        let is_valid = ds.verify(message, signature, public_key);
        
        assert!(is_valid);
    }
}
