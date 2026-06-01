//! # 安全密码学基础演示 —— `ring`
//! # foundation demonstration —— `ring`
//! 本示例使用 [`ring`](https://docs.rs/ring) 库演示现代密码学原语，
//! this example [`ring`](https://docs.rs/ring) library demonstration ，
//! 覆盖哈希、HMAC、AEAD 加密和数字签名。
//! 、HMAC、AEAD and number 。
//! 、HMAC、AEAD and 。
//! ## 运行
//! ## Run
//! ```bash
//! cargo run -p c10_networks --example security_cryptography_demo
//! ```
//!
//! [来源: Ring Documentation](https://docs.rs/ring/0.17.14)

use ring::{
    aead::{self, Aad, Nonce, AES_128_GCM},
    digest, hmac,
    rand::SecureRandom,
    signature::{self, Ed25519KeyPair, KeyPair},
};

fn main() {
    println!("🔐 安全密码学基础演示 —— ring\n");

    demo_01_hashing();
    demo_02_hmac();
    demo_03_aead_encryption();
    demo_04_digital_signature();

    println!("\n✅ 密码学演示完成！");
}

/// ## 演示 1: 哈希函数 (SHA-256 / SHA-384)
/// ## demonstration 1: function (SHA-256 / SHA-384)
/// ## Demonstration of 1: 哈希function (SHA-256 / SHA-384)
fn demo_01_hashing() {
    println!("📦 演示 1: 哈希函数");
    println!("-------------------");

    let message = b"Hello, Rust cryptography!";

    let sha256_digest = digest::digest(&digest::SHA256, message);
    println!("SHA-256:  {}", hex_encode(sha256_digest.as_ref()));

    let sha384_digest = digest::digest(&digest::SHA384, message);
    println!("SHA-384:  {}", hex_encode(sha384_digest.as_ref()));

    let sha256_digest2 = digest::digest(&digest::SHA256, message);
    assert_eq!(sha256_digest.as_ref(), sha256_digest2.as_ref());
    println!("✓ 相同输入 → 相同摘要");

    let modified = b"Hello, Rust cryptography?";
    let sha256_modified = digest::digest(&digest::SHA256, modified);
    assert_ne!(sha256_digest.as_ref(), sha256_modified.as_ref());
    println!("✓ 雪崩效应验证通过");

    println!();
}

/// ## 演示 2: HMAC (Hash-based Message Authentication Code)
fn demo_02_hmac() {
    println!("🔑 演示 2: HMAC-SHA256 消息认证");
    println!("--------------------------------");

    let key_value = b"my-secret-key-32-bytes-long!!!!!";
    let message = b"Transfer $100 to Alice";

    let key = hmac::Key::new(hmac::HMAC_SHA256, key_value);
    let tag = hmac::sign(&key, message);
    println!("消息:    {}", String::from_utf8_lossy(message));
    println!("HMAC:    {}", hex_encode(tag.as_ref()));

    hmac::verify(&key, message, tag.as_ref()).expect("HMAC 验证失败");
    println!("✓ HMAC 验证通过");

    let tampered = b"Transfer $999 to Alice";
    assert!(hmac::verify(&key, tampered, tag.as_ref()).is_err());
    println!("✓ 篡改检测: 修改消息后 HMAC 验证失败");

    println!();
}

/// ## 演示 3: AEAD 对称加密 (AES-128-GCM)
/// ## demonstration 3: AEAD to (AES-128-GCM)
/// ## Demonstration of 3: AEAD to称Encrypt (AES-128-GCM)
fn demo_03_aead_encryption() {
    println!("🔒 演示 3: AES-128-GCM 认证加密");
    println!("---------------------------------");

    let plaintext = b"Secret message: meeting at 0900";
    let associated_data = b"header:v1;seq:42";

    let rng = ring::rand::SystemRandom::new();
    let mut key_bytes = [0u8; 16];
    let mut nonce_bytes = [0u8; 12];
    rng.fill(&mut key_bytes).unwrap();
    rng.fill(&mut nonce_bytes).unwrap();

    // 加密
    let nonce = Nonce::try_assume_unique_for_key(&nonce_bytes).unwrap();
    let mut in_out = plaintext.to_vec();
    let key = aead::LessSafeKey::new(aead::UnboundKey::new(&AES_128_GCM, &key_bytes).unwrap());
    key.seal_in_place_append_tag(nonce, Aad::from(associated_data), &mut in_out)
        .unwrap();

    println!("明文:      {}", String::from_utf8_lossy(plaintext));
    println!("密文+标签: {}", hex_encode(&in_out));
    println!("AAD:       {}", String::from_utf8_lossy(associated_data));

    // 解密
    let nonce = Nonce::try_assume_unique_for_key(&nonce_bytes).unwrap();
    let key = aead::LessSafeKey::new(aead::UnboundKey::new(&AES_128_GCM, &key_bytes).unwrap());
    let plain_len = key
        .open_in_place(nonce, Aad::from(associated_data), &mut in_out)
        .unwrap()
        .len();

    assert_eq!(&in_out[..plain_len], plaintext);
    println!("✓ 解密成功，内容匹配");

    // AAD 篡改检测
    let mut tampered = b"Secret message: meeting at 0900".to_vec();
    let nonce2 = Nonce::try_assume_unique_for_key(&nonce_bytes).unwrap();
    let key = aead::LessSafeKey::new(aead::UnboundKey::new(&AES_128_GCM, &key_bytes).unwrap());
    key.seal_in_place_append_tag(nonce2, Aad::from(associated_data), &mut tampered)
        .unwrap();
    let nonce3 = Nonce::try_assume_unique_for_key(&nonce_bytes).unwrap();
    let result = key.open_in_place(nonce3, Aad::from(b"wrong-aad"), &mut tampered);
    assert!(result.is_err());
    println!("✓ AAD 篡改检测: 解密失败");

    println!();
}

/// ## 演示 4: 数字签名 (Ed25519)
/// ## demonstration 4: number (Ed25519)
/// ## demonstration 4: (Ed25519)
/// ## Demonstration of 4: 数字签名 (Ed25519)
fn demo_04_digital_signature() {
    println!("✍️  演示 4: Ed25519 数字签名");
    println!("-----------------------------");

    let message = b"Contract: Alice agrees to pay Bob 100 BTC";

    let rng = ring::rand::SystemRandom::new();
    let mut seed = [0u8; 32];
    rng.fill(&mut seed).unwrap();
    let key_pair = Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();

    let signature = key_pair.sign(message);
    println!("消息:     {}", String::from_utf8_lossy(message));
    println!("公钥:     {}", hex_encode(key_pair.public_key().as_ref()));
    println!("签名:     {}", hex_encode(signature.as_ref()));

    let peer_public_key =
        signature::UnparsedPublicKey::new(&signature::ED25519, key_pair.public_key().as_ref());
    peer_public_key.verify(message, signature.as_ref()).expect("签名验证失败");
    println!("✓ 签名验证通过");

    let tampered = b"Contract: Alice agrees to pay Bob 999 BTC";
    assert!(peer_public_key.verify(tampered, signature.as_ref()).is_err());
    println!("✓ 篡改检测: 修改消息后签名验证失败");

    println!();
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}
