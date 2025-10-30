//! # WASI-Crypto 加密操作示例
//!
//! 本示例展示如何使用 WASI-Crypto API 进行密码学操作
//!
//! ## 支持的操作
//! - 对称加密 (AES-GCM, ChaCha20-Poly1305)
//! - 非对称加密 (RSA, ECDSA, Ed25519)
//! - 哈希函数 (SHA-256, SHA-512, BLAKE3)
//! - 密钥派生 (HKDF, PBKDF2)
//! - 数字签名
//! - 消息认证码 (HMAC)
//!
//! ## 编译
//! ```bash
//! cargo build --example 11_crypto_operations --target wasm32-wasi --release
//! ```
//!
//! ## 运行
//! ```bash
//! # 使用 WasmEdge（需要安装 WASI-Crypto 插件）
//! wasmedge --dir .:. target/wasm32-wasi/release/examples/11_crypto_operations.wasm
//! ```
//!
//! ## 安装 WASI-Crypto 插件
//! ```bash
//! curl -sSf https://raw.githubusercontent.com/WasmEdge/WasmEdge/master/utils/install.sh | \
//!   bash -s -- --plugins wasi_crypto
//! ```

use std::fmt;

/// 密码学错误类型
#[derive(Debug)]
pub enum CryptoError {
    EncryptionFailed(String),
    DecryptionFailed(String),
    SignatureFailed(String),
    VerificationFailed,
    KeyGenerationFailed(String),
    InvalidInput(String),
    UnsupportedAlgorithm(String),
}

impl fmt::Display for CryptoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EncryptionFailed(msg) => write!(f, "Encryption failed: {}", msg),
            Self::DecryptionFailed(msg) => write!(f, "Decryption failed: {}", msg),
            Self::SignatureFailed(msg) => write!(f, "Signature failed: {}", msg),
            Self::VerificationFailed => write!(f, "Verification failed"),
            Self::KeyGenerationFailed(msg) => write!(f, "Key generation failed: {}", msg),
            Self::InvalidInput(msg) => write!(f, "Invalid input: {}", msg),
            Self::UnsupportedAlgorithm(msg) => write!(f, "Unsupported algorithm: {}", msg),
        }
    }
}

/// 对称加密算法
#[derive(Debug, Clone, Copy)]
pub enum SymmetricAlgorithm {
    AesGcm256,
    ChaCha20Poly1305,
    Aes256Ctr,
}

impl SymmetricAlgorithm {
    fn name(&self) -> &str {
        match self {
            Self::AesGcm256 => "AES-256-GCM",
            Self::ChaCha20Poly1305 => "ChaCha20-Poly1305",
            Self::Aes256Ctr => "AES-256-CTR",
        }
    }

    fn key_size(&self) -> usize {
        match self {
            Self::AesGcm256 | Self::ChaCha20Poly1305 | Self::Aes256Ctr => 32,
        }
    }

    fn nonce_size(&self) -> usize {
        match self {
            Self::AesGcm256 => 12,
            Self::ChaCha20Poly1305 => 12,
            Self::Aes256Ctr => 16,
        }
    }
}

/// 对称加密器
pub struct SymmetricCipher {
    algorithm: SymmetricAlgorithm,
}

impl SymmetricCipher {
    pub fn new(algorithm: SymmetricAlgorithm) -> Self {
        Self { algorithm }
    }

    /// 生成密钥
    pub fn generate_key(&self) -> Result<Vec<u8>, CryptoError> {
        println!("Generating {} key...", self.algorithm.name());

        // 在实际实现中，这会调用 WASI-Crypto API
        // 这里我们模拟密钥生成
        let key_size = self.algorithm.key_size();
        let key = vec![0x42u8; key_size]; // 模拟密钥

        println!("Generated {}-byte key", key.len());
        Ok(key)
    }

    /// 生成随机 nonce
    fn generate_nonce(&self) -> Vec<u8> {
        let nonce_size = self.algorithm.nonce_size();
        vec![0x11u8; nonce_size] // 模拟 nonce
    }

    /// 加密数据
    pub fn encrypt(&self, key: &[u8], plaintext: &[u8]) -> Result<EncryptedData, CryptoError> {
        println!("\n=== Encryption ===");
        println!("Algorithm: {}", self.algorithm.name());
        println!("Plaintext size: {} bytes", plaintext.len());

        // 验证密钥长度
        if key.len() != self.algorithm.key_size() {
            return Err(CryptoError::InvalidInput(format!(
                "Expected {}-byte key, got {}",
                self.algorithm.key_size(),
                key.len()
            )));
        }

        // 生成 nonce
        let nonce = self.generate_nonce();

        // 实际实现中会调用 WASI-Crypto API
        // 这里提供模拟实现
        let ciphertext = self.mock_encrypt(plaintext, key, &nonce)?;

        // AEAD 算法会生成认证标签
        let tag = vec![0xAAu8; 16];

        println!("Ciphertext size: {} bytes", ciphertext.len());
        println!("Authentication tag: {} bytes", tag.len());

        Ok(EncryptedData {
            ciphertext,
            nonce,
            tag: Some(tag),
        })
    }

    /// 解密数据
    pub fn decrypt(
        &self,
        key: &[u8],
        encrypted: &EncryptedData,
    ) -> Result<Vec<u8>, CryptoError> {
        println!("\n=== Decryption ===");
        println!("Algorithm: {}", self.algorithm.name());
        println!("Ciphertext size: {} bytes", encrypted.ciphertext.len());

        // 验证
        if key.len() != self.algorithm.key_size() {
            return Err(CryptoError::InvalidInput("Invalid key length".to_string()));
        }

        if encrypted.nonce.len() != self.algorithm.nonce_size() {
            return Err(CryptoError::InvalidInput("Invalid nonce length".to_string()));
        }

        // 实际实现中会调用 WASI-Crypto API
        let plaintext = self.mock_decrypt(&encrypted.ciphertext, key, &encrypted.nonce)?;

        println!("Decrypted size: {} bytes", plaintext.len());
        Ok(plaintext)
    }

    // 模拟实现
    fn mock_encrypt(
        &self,
        plaintext: &[u8],
        _key: &[u8],
        _nonce: &[u8],
    ) -> Result<Vec<u8>, CryptoError> {
        // 简单 XOR 作为演示（实际使用真正的加密）
        Ok(plaintext.to_vec())
    }

    fn mock_decrypt(
        &self,
        ciphertext: &[u8],
        _key: &[u8],
        _nonce: &[u8],
    ) -> Result<Vec<u8>, CryptoError> {
        Ok(ciphertext.to_vec())
    }
}

/// 加密数据结构
#[derive(Debug)]
pub struct EncryptedData {
    pub ciphertext: Vec<u8>,
    pub nonce: Vec<u8>,
    pub tag: Option<Vec<u8>>,
}

/// 非对称加密算法
#[derive(Debug, Clone, Copy)]
pub enum AsymmetricAlgorithm {
    Ed25519,
    Rsa2048,
    Ecdsa256,
}

impl AsymmetricAlgorithm {
    fn name(&self) -> &str {
        match self {
            Self::Ed25519 => "Ed25519",
            Self::Rsa2048 => "RSA-2048",
            Self::Ecdsa256 => "ECDSA-P256",
        }
    }
}

/// 密钥对
#[derive(Debug)]
pub struct KeyPair {
    pub public_key: Vec<u8>,
    pub private_key: Vec<u8>,
}

/// 数字签名器
pub struct DigitalSignature {
    algorithm: AsymmetricAlgorithm,
}

impl DigitalSignature {
    pub fn new(algorithm: AsymmetricAlgorithm) -> Self {
        Self { algorithm }
    }

    /// 生成密钥对
    pub fn generate_keypair(&self) -> Result<KeyPair, CryptoError> {
        println!("\n=== Key Pair Generation ===");
        println!("Algorithm: {}", self.algorithm.name());

        // 实际实现中调用 WASI-Crypto API
        let keypair = KeyPair {
            public_key: vec![0x50u8; 32],  // 模拟公钥 (0x50 = 'P' in ASCII)
            private_key: vec![0x52u8; 32], // 模拟私钥 (0x52 = 'R' in ASCII)
        };

        println!("Public key: {} bytes", keypair.public_key.len());
        println!("Private key: {} bytes", keypair.private_key.len());

        Ok(keypair)
    }

    /// 签名数据
    pub fn sign(&self, _private_key: &[u8], message: &[u8]) -> Result<Vec<u8>, CryptoError> {
        println!("\n=== Digital Signature ===");
        println!("Algorithm: {}", self.algorithm.name());
        println!("Message size: {} bytes", message.len());

        // 实际实现中调用 WASI-Crypto API
        let signature = vec![0x53u8; 64]; // 模拟签名 (0x53 = 'S' in ASCII)

        println!("Signature size: {} bytes", signature.len());
        Ok(signature)
    }

    /// 验证签名
    pub fn verify(
        &self,
        _public_key: &[u8],
        message: &[u8],
        signature: &[u8],
    ) -> Result<bool, CryptoError> {
        println!("\n=== Signature Verification ===");
        println!("Algorithm: {}", self.algorithm.name());
        println!("Message size: {} bytes", message.len());
        println!("Signature size: {} bytes", signature.len());

        // 实际实现中调用 WASI-Crypto API
        let valid = signature.len() == 64; // 简单验证

        if valid {
            println!("✓ Signature is valid");
        } else {
            println!("✗ Signature is invalid");
        }

        Ok(valid)
    }
}

/// 哈希算法
#[derive(Debug, Clone, Copy)]
pub enum HashAlgorithm {
    Sha256,
    Sha512,
    Blake3,
}

impl HashAlgorithm {
    fn name(&self) -> &str {
        match self {
            Self::Sha256 => "SHA-256",
            Self::Sha512 => "SHA-512",
            Self::Blake3 => "BLAKE3",
        }
    }

    fn output_size(&self) -> usize {
        match self {
            Self::Sha256 => 32,
            Self::Sha512 => 64,
            Self::Blake3 => 32,
        }
    }
}

/// 哈希计算器
pub struct Hasher {
    algorithm: HashAlgorithm,
}

impl Hasher {
    pub fn new(algorithm: HashAlgorithm) -> Self {
        Self { algorithm }
    }

    /// 计算哈希
    pub fn hash(&self, data: &[u8]) -> Result<Vec<u8>, CryptoError> {
        println!("\n=== Hash Computation ===");
        println!("Algorithm: {}", self.algorithm.name());
        println!("Input size: {} bytes", data.len());

        // 实际实现中调用 WASI-Crypto API
        let hash = vec![0xABu8; self.algorithm.output_size()]; // 模拟哈希值

        println!("Hash size: {} bytes", hash.len());
        println!("Hash (hex): {}", hex_encode(&hash[..8.min(hash.len())]));

        Ok(hash)
    }

    /// HMAC 计算
    pub fn hmac(&self, key: &[u8], data: &[u8]) -> Result<Vec<u8>, CryptoError> {
        println!("\n=== HMAC ===");
        println!("Algorithm: HMAC-{}", self.algorithm.name());
        println!("Key size: {} bytes", key.len());
        println!("Data size: {} bytes", data.len());

        // 实际实现中调用 WASI-Crypto API
        let mac = vec![0x4Du8; self.algorithm.output_size()]; // 模拟 MAC (0x4D = 'M' in ASCII)

        println!("MAC size: {} bytes", mac.len());
        Ok(mac)
    }
}

/// 密钥派生函数
pub struct KeyDerivation;

impl KeyDerivation {
    /// HKDF 密钥派生
    pub fn hkdf(
        hash_algo: HashAlgorithm,
        ikm: &[u8],  // Input Key Material
        salt: &[u8],
        info: &[u8],
        output_len: usize,
    ) -> Result<Vec<u8>, CryptoError> {
        println!("\n=== HKDF Key Derivation ===");
        println!("Hash algorithm: {}", hash_algo.name());
        println!("IKM length: {} bytes", ikm.len());
        println!("Salt length: {} bytes", salt.len());
        println!("Info length: {} bytes", info.len());
        println!("Output length: {} bytes", output_len);

        // 实际实现中调用 WASI-Crypto API
        let derived = vec![0x4Bu8; output_len]; // 模拟派生密钥 (0x4B = 'K' in ASCII)

        println!("Derived key generated");
        Ok(derived)
    }

    /// PBKDF2 密钥派生
    pub fn pbkdf2(
        hash_algo: HashAlgorithm,
        password: &[u8],
        salt: &[u8],
        iterations: u32,
        output_len: usize,
    ) -> Result<Vec<u8>, CryptoError> {
        println!("\n=== PBKDF2 Key Derivation ===");
        println!("Hash algorithm: {}", hash_algo.name());
        println!("Password length: {} bytes", password.len());
        println!("Salt length: {} bytes", salt.len());
        println!("Iterations: {}", iterations);
        println!("Output length: {} bytes", output_len);

        // 实际实现中调用 WASI-Crypto API
        let derived = vec![0x50u8; output_len]; // 模拟 PBKDF2 派生密钥

        println!("Derived key generated");
        Ok(derived)
    }
}

/// 实用工具
mod utils {
    use super::*;

    /// 打印二进制数据为十六进制
    pub fn print_hex(label: &str, data: &[u8], max_len: usize) {
        let display_data = &data[..data.len().min(max_len)];
        println!("{}: {}", label, hex_encode(display_data));
        if data.len() > max_len {
            println!("  ... ({} more bytes)", data.len() - max_len);
        }
    }

    /// 比较两个字节数组
    pub fn compare_data(a: &[u8], b: &[u8]) -> bool {
        if a.len() != b.len() {
            return false;
        }
        a.iter().zip(b.iter()).all(|(x, y)| x == y)
    }
}

/// 简单的十六进制编码
fn hex_encode(data: &[u8]) -> String {
    data.iter().map(|b| format!("{:02x}", b)).collect()
}

fn main() {
    println!("=========================================");
    println!("  WASI-Crypto Operations Example");
    println!("  Cryptographic Operations in WebAssembly");
    println!("=========================================\n");

    // 演示 1: 对称加密
    demo_symmetric_encryption();

    // 演示 2: 数字签名
    demo_digital_signature();

    // 演示 3: 哈希函数
    demo_hashing();

    // 演示 4: 密钥派生
    demo_key_derivation();

    // 演示 5: 完整的加密通信流程
    demo_secure_communication();

    println!("\n=========================================");
    println!("  All cryptographic demonstrations completed!");
    println!("=========================================");
}

fn demo_symmetric_encryption() {
    println!("\n╔═══════════════════════════════════════╗");
    println!("║  Demo 1: Symmetric Encryption        ║");
    println!("╚═══════════════════════════════════════╝");

    let algorithms = vec![
        SymmetricAlgorithm::AesGcm256,
        SymmetricAlgorithm::ChaCha20Poly1305,
    ];

    for algo in algorithms {
        let cipher = SymmetricCipher::new(algo);

        match cipher.generate_key() {
            Ok(key) => {
                let plaintext = b"Secret message that needs encryption!";

                match cipher.encrypt(&key, plaintext) {
                    Ok(encrypted) => {
                        utils::print_hex("Nonce", &encrypted.nonce, 16);
                        utils::print_hex("Ciphertext", &encrypted.ciphertext, 32);

                        match cipher.decrypt(&key, &encrypted) {
                            Ok(decrypted) => {
                                let success = utils::compare_data(plaintext, &decrypted);
                                println!(
                                    "Decryption {}: {}",
                                    if success { "SUCCESS" } else { "FAILED" },
                                    String::from_utf8_lossy(&decrypted)
                                );
                            }
                            Err(e) => eprintln!("Decryption error: {}", e),
                        }
                    }
                    Err(e) => eprintln!("Encryption error: {}", e),
                }
            }
            Err(e) => eprintln!("Key generation error: {}", e),
        }
        println!();
    }
}

fn demo_digital_signature() {
    println!("\n╔═══════════════════════════════════════╗");
    println!("║  Demo 2: Digital Signatures          ║");
    println!("╚═══════════════════════════════════════╝");

    let algorithms = vec![AsymmetricAlgorithm::Ed25519, AsymmetricAlgorithm::Ecdsa256];

    for algo in algorithms {
        let signer = DigitalSignature::new(algo);

        match signer.generate_keypair() {
            Ok(keypair) => {
                utils::print_hex("Public Key", &keypair.public_key, 16);

                let message = b"Important message to be signed";

                match signer.sign(&keypair.private_key, message) {
                    Ok(signature) => {
                        utils::print_hex("Signature", &signature, 16);

                        match signer.verify(&keypair.public_key, message, &signature) {
                            Ok(valid) => {
                                println!("Verification result: {}", if valid { "VALID" } else { "INVALID" });
                            }
                            Err(e) => eprintln!("Verification error: {}", e),
                        }
                    }
                    Err(e) => eprintln!("Signing error: {}", e),
                }
            }
            Err(e) => eprintln!("Key generation error: {}", e),
        }
        println!();
    }
}

fn demo_hashing() {
    println!("\n╔═══════════════════════════════════════╗");
    println!("║  Demo 3: Hashing & HMAC              ║");
    println!("╚═══════════════════════════════════════╝");

    let algorithms = vec![HashAlgorithm::Sha256, HashAlgorithm::Blake3];

    for algo in algorithms {
        let hasher = Hasher::new(algo);

        let data = b"Data to be hashed";

        match hasher.hash(data) {
            Ok(hash) => {
                utils::print_hex("Hash", &hash, 32);
            }
            Err(e) => eprintln!("Hashing error: {}", e),
        }

        // HMAC
        let key = b"secret-key-for-hmac";
        match hasher.hmac(key, data) {
            Ok(mac) => {
                utils::print_hex("HMAC", &mac, 32);
            }
            Err(e) => eprintln!("HMAC error: {}", e),
        }
        println!();
    }
}

fn demo_key_derivation() {
    println!("\n╔═══════════════════════════════════════╗");
    println!("║  Demo 4: Key Derivation              ║");
    println!("╚═══════════════════════════════════════╝");

    // HKDF
    match KeyDerivation::hkdf(
        HashAlgorithm::Sha256,
        b"input-key-material",
        b"salt",
        b"application-info",
        32,
    ) {
        Ok(key) => {
            utils::print_hex("HKDF Derived Key", &key, 32);
        }
        Err(e) => eprintln!("HKDF error: {}", e),
    }

    // PBKDF2
    match KeyDerivation::pbkdf2(
        HashAlgorithm::Sha256,
        b"password123",
        b"random-salt",
        100_000,
        32,
    ) {
        Ok(key) => {
            utils::print_hex("PBKDF2 Derived Key", &key, 32);
        }
        Err(e) => eprintln!("PBKDF2 error: {}", e),
    }
}

fn demo_secure_communication() {
    println!("\n╔═══════════════════════════════════════╗");
    println!("║  Demo 5: Secure Communication        ║");
    println!("╚═══════════════════════════════════════╝");

    println!("\n[Scenario: Alice sends encrypted message to Bob]");

    // 1. Bob 生成密钥对
    println!("\n1. Bob generates key pair...");
    let signer = DigitalSignature::new(AsymmetricAlgorithm::Ed25519);
    let _bob_keypair = signer.generate_keypair().unwrap();

    // 2. Alice 准备消息
    println!("\n2. Alice prepares message...");
    let message = b"Secret meeting at noon";

    // 3. Alice 加密消息
    println!("\n3. Alice encrypts message...");
    let cipher = SymmetricCipher::new(SymmetricAlgorithm::ChaCha20Poly1305);
    let sym_key = cipher.generate_key().unwrap();
    let encrypted = cipher.encrypt(&sym_key, message).unwrap();

    // 4. Alice 签名消息
    println!("\n4. Alice signs message...");
    let alice_keypair = signer.generate_keypair().unwrap();
    let signature = signer.sign(&alice_keypair.private_key, message).unwrap();

    // 5. Bob 接收并验证
    println!("\n5. Bob receives and verifies...");
    let decrypted = cipher.decrypt(&sym_key, &encrypted).unwrap();
    let verified = signer.verify(&alice_keypair.public_key, &decrypted, &signature).unwrap();

    println!(
        "\n✓ Message: {}",
        String::from_utf8_lossy(&decrypted)
    );
    println!("✓ Signature: {}", if verified { "VERIFIED" } else { "FAILED" });
    println!("\n[Secure communication successful!]");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symmetric_algorithms() {
        assert_eq!(SymmetricAlgorithm::AesGcm256.key_size(), 32);
        assert_eq!(SymmetricAlgorithm::ChaCha20Poly1305.nonce_size(), 12);
    }

    #[test]
    fn test_hash_output_sizes() {
        assert_eq!(HashAlgorithm::Sha256.output_size(), 32);
        assert_eq!(HashAlgorithm::Sha512.output_size(), 64);
    }

    #[test]
    fn test_hex_encoding() {
        let data = vec![0x01, 0x02, 0x0A, 0xFF];
        assert_eq!(hex_encode(&data), "01020aff");
    }
}

