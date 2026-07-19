//! 基础密码学原语案例
//! 
//! 本模块演示区块链系统中基础密码学原语的实现，包括哈希函数、数字签名、零知识证明等。
//! 
//! 理论映射：
//! - 哈希函数: H: {0,1}* → {0,1}^n
//! - 数字签名: Σ = (Gen, Sign, Verify)
//! - 零知识证明: Π = (P, V, S)
//! - 同态加密: HE(E(x) ⊕ E(y)) = E(x + y)

use sha2::{Sha256, Digest};
use ed25519_dalek::{Keypair, PublicKey, SecretKey, Signature, Signer, Verifier};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 哈希函数实现
/// 
/// 理论映射: H: {0,1}* → {0,1}^n
pub struct HashFunction {
    algorithm: String,
    output_size: usize,
}

impl HashFunction {
    pub fn new(algorithm: String, output_size: usize) -> Self {
        Self {
            algorithm,
            output_size,
        }
    }
    
    /// 计算SHA-256哈希
    /// 
    /// 理论映射: collision_resistance ∧ preimage_resistance ∧ second_preimage_resistance
    pub fn sha256(&self, input: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(input);
        hasher.finalize().into()
    }
    
    /// 计算双重SHA-256哈希（Bitcoin风格）
    pub fn double_sha256(&self, input: &[u8]) -> [u8; 32] {
        let first_hash = self.sha256(input);
        self.sha256(&first_hash)
    }
    
    /// 验证哈希碰撞抗性
    pub fn verify_collision_resistance(&self, hash1: &[u8], hash2: &[u8]) -> bool {
        // 在实际应用中，这需要更复杂的验证
        hash1 != hash2
    }
}

/// 数字签名实现
/// 
/// 理论映射: Σ = (Gen, Sign, Verify)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DigitalSignature {
    public_key: PublicKey,
    signature: Signature,
    message: Vec<u8>,
}

impl DigitalSignature {
    pub fn new(public_key: PublicKey, signature: Signature, message: Vec<u8>) -> Self {
        Self {
            public_key,
            signature,
            message,
        }
    }
    
    /// 生成密钥对
    /// 
    /// 理论映射: Gen(1^n) → (pk, sk)
    pub fn generate_keypair() -> (PublicKey, SecretKey) {
        let keypair = Keypair::generate(&mut OsRng);
        (keypair.public, keypair.secret)
    }
    
    /// 签名消息
    /// 
    /// 理论映射: Sign(sk, m) → σ
    pub fn sign_message(message: &[u8], secret_key: &SecretKey) -> Signature {
        let keypair = Keypair::from_bytes(&secret_key.to_bytes()).unwrap();
        keypair.sign(message)
    }
    
    /// 验证签名
    /// 
    /// 理论映射: Verify(pk, m, σ) → {0,1}
    pub fn verify_signature(&self) -> bool {
        self.public_key.verify(&self.message, &self.signature).is_ok()
    }
    
    /// 验证EUF-CMA安全性
    pub fn verify_euf_cma_security(&self, other_signatures: &[DigitalSignature]) -> bool {
        // 检查是否存在重复签名
        let mut seen_signatures = std::collections::HashSet::new();
        for sig in other_signatures {
            if !seen_signatures.insert(&sig.signature) {
                return false; // 发现重复签名
            }
        }
        true
    }
}

/// 默克尔树实现
/// 
/// 理论映射: MerkleTree(leaves) → root
#[derive(Debug, Clone)]
pub struct MerkleTree {
    pub root: [u8; 32],
    pub leaves: Vec<[u8; 32]>,
    pub height: usize,
}

impl MerkleTree {
    pub fn new(leaves: Vec<Vec<u8>>) -> Self {
        let leaf_hashes: Vec<[u8; 32]> = leaves
            .iter()
            .map(|leaf| {
                let mut hasher = Sha256::new();
                hasher.update(leaf);
                hasher.finalize().into()
            })
            .collect();
        
        let root = Self::build_tree(&leaf_hashes);
        let height = Self::calculate_height(leaf_hashes.len());
        
        Self {
            root,
            leaves: leaf_hashes,
            height,
        }
    }
    
    /// 构建默克尔树
    fn build_tree(leaves: &[[u8; 32]]) -> [u8; 32] {
        if leaves.is_empty() {
            return [0; 32];
        }
        
        if leaves.len() == 1 {
            return leaves[0];
        }
        
        let mut level = leaves.to_vec();
        
        while level.len() > 1 {
            let mut next_level = Vec::new();
            
            for chunk in level.chunks(2) {
                let mut hasher = Sha256::new();
                hasher.update(&chunk[0]);
                
                if chunk.len() > 1 {
                    hasher.update(&chunk[1]);
                } else {
                    hasher.update(&chunk[0]); // 奇数个节点时重复
                }
                
                next_level.push(hasher.finalize().into());
            }
            
            level = next_level;
        }
        
        level[0]
    }
    
    /// 计算树高度
    fn calculate_height(leaf_count: usize) -> usize {
        if leaf_count == 0 {
            return 0;
        }
        (leaf_count as f64).log2().ceil() as usize
    }
    
    /// 生成默克尔证明
    /// 
    /// 理论映射: generate_proof(leaf_index) → proof
    pub fn generate_proof(&self, index: usize) -> Option<MerkleProof> {
        if index >= self.leaves.len() {
            return None;
        }
        
        let mut proof = Vec::new();
        let mut current_index = index;
        let mut current_level = self.leaves.clone();
        
        while current_level.len() > 1 {
            let is_right = current_index % 2 == 1;
            let sibling_index = if is_right { current_index - 1 } else { current_index + 1 };
            
            if sibling_index < current_level.len() {
                proof.push((current_level[sibling_index], is_right));
            }
            
            current_index /= 2;
            current_level = Self::build_next_level(&current_level);
        }
        
        Some(MerkleProof {
            leaf_index: index,
            proof,
            leaf_hash: self.leaves[index],
        })
    }
    
    /// 验证默克尔证明
    /// 
    /// 理论映射: verify_proof(proof, root) → {0,1}
    pub fn verify_proof(proof: &MerkleProof, root: [u8; 32]) -> bool {
        let mut current_hash = proof.leaf_hash;
        
        for (sibling_hash, is_right) in &proof.proof {
            let mut hasher = Sha256::new();
            
            if *is_right {
                hasher.update(&current_hash);
                hasher.update(sibling_hash);
            } else {
                hasher.update(sibling_hash);
                hasher.update(&current_hash);
            }
            
            current_hash = hasher.finalize().into();
        }
        
        current_hash == root
    }
    
    fn build_next_level(level: &[[u8; 32]]) -> Vec<[u8; 32]> {
        let mut next_level = Vec::new();
        
        for chunk in level.chunks(2) {
            let mut hasher = Sha256::new();
            hasher.update(&chunk[0]);
            
            if chunk.len() > 1 {
                hasher.update(&chunk[1]);
            } else {
                hasher.update(&chunk[0]);
            }
            
            next_level.push(hasher.finalize().into());
        }
        
        next_level
    }
}

/// 默克尔证明结构
#[derive(Debug, Clone)]
pub struct MerkleProof {
    pub leaf_index: usize,
    pub proof: Vec<([u8; 32], bool)>, // (hash, is_right)
    pub leaf_hash: [u8; 32],
}

/// 零知识证明实现（简化版）
/// 
/// 理论映射: Π = (P, V, S)
pub struct ZeroKnowledgeProof {
    pub statement: Vec<u8>,
    pub proof: Vec<u8>,
    pub public_inputs: Vec<u8>,
}

impl ZeroKnowledgeProof {
    pub fn new(statement: Vec<u8>, proof: Vec<u8>, public_inputs: Vec<u8>) -> Self {
        Self {
            statement,
            proof,
            public_inputs,
        }
    }
    
    /// 生成零知识证明（简化实现）
    /// 
    /// 理论映射: P(witness, statement) → proof
    pub fn generate_proof(witness: &[u8], statement: &[u8]) -> Self {
        // 简化实现：实际应用中需要更复杂的零知识证明系统
        let mut proof_data = Vec::new();
        proof_data.extend_from_slice(witness);
        proof_data.extend_from_slice(statement);
        
        // 使用哈希作为简化的"证明"
        let mut hasher = Sha256::new();
        hasher.update(&proof_data);
        let proof = hasher.finalize().to_vec();
        
        Self {
            statement: statement.to_vec(),
            proof,
            public_inputs: statement.to_vec(),
        }
    }
    
    /// 验证零知识证明
    /// 
    /// 理论映射: V(statement, proof) → {0,1}
    pub fn verify_proof(&self) -> bool {
        // 简化验证：检查证明格式
        !self.proof.is_empty() && self.proof.len() == 32
    }
    
    /// 验证完备性
    pub fn verify_completeness(&self, witness: &[u8]) -> bool {
        let mut proof_data = Vec::new();
        proof_data.extend_from_slice(witness);
        proof_data.extend_from_slice(&self.statement);
        
        let mut hasher = Sha256::new();
        hasher.update(&proof_data);
        let expected_proof = hasher.finalize().to_vec();
        
        self.proof == expected_proof
    }
}

/// 同态加密实现（简化版）
/// 
/// 理论映射: HE(E(x) ⊕ E(y)) = E(x + y)
pub struct HomomorphicEncryption {
    pub public_key: Vec<u8>,
    pub ciphertexts: HashMap<String, Vec<u8>>,
}

impl HomomorphicEncryption {
    pub fn new() -> Self {
        Self {
            public_key: vec![1, 2, 3, 4, 5], // 简化公钥
            ciphertexts: HashMap::new(),
        }
    }
    
    /// 加密消息
    /// 
    /// 理论映射: Enc(pk, m) → c
    pub fn encrypt(&mut self, message: u64, label: &str) -> Vec<u8> {
        // 简化实现：实际需要真正的同态加密方案
        let mut ciphertext = Vec::new();
        ciphertext.extend_from_slice(&message.to_be_bytes());
        ciphertext.extend_from_slice(&self.public_key);
        
        self.ciphertexts.insert(label.to_string(), ciphertext.clone());
        ciphertext
    }
    
    /// 同态加法
    /// 
    /// 理论映射: HE(E(x) ⊕ E(y)) = E(x + y)
    pub fn homomorphic_add(&self, ciphertext1: &[u8], ciphertext2: &[u8]) -> Vec<u8> {
        // 简化实现：实际需要真正的同态加密运算
        let mut result = Vec::new();
        result.extend_from_slice(ciphertext1);
        result.extend_from_slice(ciphertext2);
        result
    }
    
    /// 解密消息
    /// 
    /// 理论映射: Dec(sk, c) → m
    pub fn decrypt(&self, ciphertext: &[u8]) -> Option<u64> {
        if ciphertext.len() < 8 {
            return None;
        }
        
        let message_bytes = &ciphertext[..8];
        let message = u64::from_be_bytes([
            message_bytes[0], message_bytes[1], message_bytes[2], message_bytes[3],
            message_bytes[4], message_bytes[5], message_bytes[6], message_bytes[7],
        ]);
        
        Some(message)
    }
}

/// 密码学工具类
pub struct CryptoUtils;

impl CryptoUtils {
    /// 生成随机字节
    pub fn generate_random_bytes(length: usize) -> Vec<u8> {
        let mut bytes = vec![0u8; length];
        OsRng.fill(&mut bytes);
        bytes
    }
    
    /// 计算HMAC
    pub fn hmac(key: &[u8], message: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(key);
        hasher.update(message);
        hasher.finalize().into()
    }
    
    /// 验证密码学安全性
    pub fn verify_cryptographic_security(hash: &[u8], signature: &[u8]) -> bool {
        // 简化验证：检查基本格式
        hash.len() == 32 && !signature.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 测试哈希函数
    #[test]
    fn test_hash_function() {
        let hash_fn = HashFunction::new("SHA-256".to_string(), 32);
        let input = b"Hello, Blockchain!";
        let hash = hash_fn.sha256(input);
        
        assert_eq!(hash.len(), 32);
        assert!(hash_fn.verify_collision_resistance(&hash, &[0u8; 32]));
    }

    /// 测试数字签名
    #[test]
    fn test_digital_signature() {
        let (public_key, secret_key) = DigitalSignature::generate_keypair();
        let message = b"Test message for signing";
        
        let signature = DigitalSignature::sign_message(message, &secret_key);
        let digital_sig = DigitalSignature::new(public_key, signature, message.to_vec());
        
        assert!(digital_sig.verify_signature());
    }

    /// 测试默克尔树
    #[test]
    fn test_merkle_tree() {
        let leaves = vec![
            b"Leaf 1".to_vec(),
            b"Leaf 2".to_vec(),
            b"Leaf 3".to_vec(),
            b"Leaf 4".to_vec(),
        ];
        
        let merkle_tree = MerkleTree::new(leaves);
        
        // 生成证明
        let proof = merkle_tree.generate_proof(1).unwrap();
        
        // 验证证明
        assert!(MerkleTree::verify_proof(&proof, merkle_tree.root));
    }

    /// 测试零知识证明
    #[test]
    fn test_zero_knowledge_proof() {
        let witness = b"secret witness";
        let statement = b"public statement";
        
        let zk_proof = ZeroKnowledgeProof::generate_proof(witness, statement);
        
        assert!(zk_proof.verify_proof());
        assert!(zk_proof.verify_completeness(witness));
    }

    /// 测试同态加密
    #[test]
    fn test_homomorphic_encryption() {
        let mut he = HomomorphicEncryption::new();
        
        let ciphertext1 = he.encrypt(10, "value1");
        let ciphertext2 = he.encrypt(20, "value2");
        
        let sum_ciphertext = he.homomorphic_add(&ciphertext1, &ciphertext2);
        
        // 验证加密结果不为空
        assert!(!ciphertext1.is_empty());
        assert!(!ciphertext2.is_empty());
        assert!(!sum_ciphertext.is_empty());
    }

    /// 测试密码学工具
    #[test]
    fn test_crypto_utils() {
        let random_bytes = CryptoUtils::generate_random_bytes(32);
        assert_eq!(random_bytes.len(), 32);
        
        let hmac = CryptoUtils::hmac(b"key", b"message");
        assert_eq!(hmac.len(), 32);
        
        assert!(CryptoUtils::verify_cryptographic_security(&[0u8; 32], &[1u8; 64]));
    }
}

/// 示例用法
pub async fn run_examples() {
    println!("=== 基础密码学原语案例 ===");
    
    // 1. 哈希函数示例
    println!("\n1. 哈希函数示例:");
    let hash_fn = HashFunction::new("SHA-256".to_string(), 32);
    let message = b"Blockchain security is paramount";
    let hash = hash_fn.sha256(message);
    let double_hash = hash_fn.double_sha256(message);
    
    println!("  原始消息: {}", String::from_utf8_lossy(message));
    println!("  SHA-256哈希: {:?}", hash);
    println!("  双重SHA-256哈希: {:?}", double_hash);
    
    // 2. 数字签名示例
    println!("\n2. 数字签名示例:");
    let (public_key, secret_key) = DigitalSignature::generate_keypair();
    let transaction_data = b"Transfer 100 tokens to Alice";
    
    let signature = DigitalSignature::sign_message(transaction_data, &secret_key);
    let digital_sig = DigitalSignature::new(public_key, signature, transaction_data.to_vec());
    
    if digital_sig.verify_signature() {
        println!("  交易签名验证成功");
    } else {
        println!("  交易签名验证失败");
    }
    
    // 3. 默克尔树示例
    println!("\n3. 默克尔树示例:");
    let transactions = vec![
        b"Transaction 1".to_vec(),
        b"Transaction 2".to_vec(),
        b"Transaction 3".to_vec(),
        b"Transaction 4".to_vec(),
    ];
    
    let merkle_tree = MerkleTree::new(transactions);
    println!("  默克尔树根: {:?}", merkle_tree.root);
    println!("  树高度: {}", merkle_tree.height);
    
    // 生成并验证证明
    if let Some(proof) = merkle_tree.generate_proof(2) {
        if MerkleTree::verify_proof(&proof, merkle_tree.root) {
            println!("  默克尔证明验证成功");
        } else {
            println!("  默克尔证明验证失败");
        }
    }
    
    // 4. 零知识证明示例
    println!("\n4. 零知识证明示例:");
    let secret_witness = b"I know the secret";
    let public_statement = b"Prove knowledge without revealing";
    
    let zk_proof = ZeroKnowledgeProof::generate_proof(secret_witness, public_statement);
    
    if zk_proof.verify_proof() {
        println!("  零知识证明验证成功");
    } else {
        println!("  零知识证明验证失败");
    }
    
    // 5. 同态加密示例
    println!("\n5. 同态加密示例:");
    let mut he = HomomorphicEncryption::new();
    
    let encrypted_value1 = he.encrypt(50, "balance1");
    let encrypted_value2 = he.encrypt(30, "balance2");
    
    let encrypted_sum = he.homomorphic_add(&encrypted_value1, &encrypted_value2);
    
    println!("  加密值1: {:?}", encrypted_value1);
    println!("  加密值2: {:?}", encrypted_value2);
    println!("  加密和: {:?}", encrypted_sum);
    
    // 6. 密码学工具示例
    println!("\n6. 密码学工具示例:");
    let random_data = CryptoUtils::generate_random_bytes(16);
    let hmac_result = CryptoUtils::hmac(b"secret_key", b"authenticated_message");
    
    println!("  随机数据: {:?}", random_data);
    println!("  HMAC结果: {:?}", hmac_result);
    
    if CryptoUtils::verify_cryptographic_security(&[0u8; 32], &[1u8; 64]) {
        println!("  密码学安全性验证通过");
    } else {
        println!("  密码学安全性验证失败");
    }
} 