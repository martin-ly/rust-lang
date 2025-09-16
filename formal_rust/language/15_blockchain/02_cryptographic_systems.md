# 15.2 密码学系统设计

## 目录

- [15.2.1 哈希函数理论](#1521-哈希函数理论)
- [15.2.2 数字签名理论](#1522-数字签名理论)
- [15.2.3 零知识证明理论](#1523-零知识证明理论)
- [15.2.4 同态加密理论](#1524-同态加密理论)
- [15.2.5 多方计算理论](#1525-多方计算理论)

## 15.2.1 哈希函数理论

**定义 15.2.1** (密码学哈希函数)
密码学哈希函数 H: {0,1}* → {0,1}^n 满足：

- 单向性：给定 y = H(x)，计算 x 在计算上不可行
- 抗碰撞性：找到 x₁ ≠ x₂ 使得 H(x₁) = H(x₂) 在计算上不可行
- 雪崩效应：输入的微小变化导致输出的巨大变化

**定理 15.2.1** (哈希函数安全性)
如果哈希函数 H 是抗碰撞的，则它是单向的。

**Rust实现**：

```rust
use sha2::{Sha256, Digest};
use blake2::{Blake2b, Blake2s};

pub struct CryptographicHash {
    algorithm: HashAlgorithm,
}

pub enum HashAlgorithm {
    SHA256,
    SHA3,
    Blake2b,
    Blake2s,
}

impl CryptographicHash {
    pub fn hash(&self, data: &[u8]) -> Vec<u8> {
        match self.algorithm {
            HashAlgorithm::SHA256 => {
                let mut hasher = Sha256::new();
                hasher.update(data);
                hasher.finalize().to_vec()
            }
            HashAlgorithm::Blake2b => {
                let mut hasher = Blake2b::new();
                hasher.update(data);
                hasher.finalize().to_vec()
            }
            _ => unimplemented!()
        }
    }
}
```

## 15.2.2 数字签名理论

**定义 15.2.2** (数字签名方案)
数字签名方案是一个三元组 (Gen, Sign, Verify)：

- Gen: 生成密钥对 (pk, sk)
- Sign: 使用私钥 sk 对消息 m 签名 σ = Sign(sk, m)
- Verify: 使用公钥 pk 验证签名 Verify(pk, m, σ) ∈ {0,1}

**定理 15.2.2** (数字签名安全性)
数字签名方案在存在性不可伪造攻击下是安全的，当且仅当：
∀ PPT adversary A: Pr[Verify(pk, m*, σ*) = 1 ∧ m* ∉ Q] ≤ negl(λ)

**Rust实现**：

```rust
use ed25519_dalek::{Keypair, Signer, Verifier, Signature};

pub struct DigitalSignature {
    keypair: Keypair,
}

impl DigitalSignature {
    pub fn new() -> Self {
        let keypair = Keypair::generate(&mut rand::rngs::OsRng);
        Self { keypair }
    }
    
    pub fn sign(&self, message: &[u8]) -> Signature {
        self.keypair.sign(message)
    }
    
    pub fn verify(&self, message: &[u8], signature: &Signature) -> bool {
        self.keypair.verify(message, signature).is_ok()
    }
}
```

## 15.2.3 零知识证明理论

**定义 15.2.3** (零知识证明)
零知识证明系统是一个交互式协议 (P, V)，满足：

- 完备性：如果 x ∈ L，则 Pr[⟨P, V⟩(x) = 1] ≥ c
- 可靠性：如果 x ∉ L，则 Pr[⟨P, V⟩(x) = 1] ≤ s
- 零知识性：验证者无法获得除 x ∈ L 外的任何信息

**定理 15.2.3** (零知识证明存在性)
对于任何 NP 语言 L，都存在零知识证明系统。

**Rust实现**：

```rust
pub struct ZeroKnowledgeProof {
    statement: Statement,
    witness: Witness,
}

pub struct Statement {
    public_input: Vec<u8>,
}

pub struct Witness {
    private_input: Vec<u8>,
}

impl ZeroKnowledgeProof {
    pub fn prove(&self) -> Proof {
        // 实现零知识证明生成
        Proof::new()
    }
    
    pub fn verify(&self, proof: &Proof) -> bool {
        // 实现零知识证明验证
        true
    }
}
```

## 15.2.4 同态加密理论

**定义 15.2.4** (同态加密)
同态加密方案允许在密文上直接计算，满足：
Dec(sk, Eval(pk, f, c₁, ..., cₙ)) = f(Dec(sk, c₁), ..., Dec(sk, cₙ))

**同态类型**：

- 部分同态：支持有限运算
- 全同态：支持任意运算
- 近似同态：支持近似运算

**Rust实现**：

```rust
pub struct HomomorphicEncryption {
    public_key: PublicKey,
    private_key: PrivateKey,
}

impl HomomorphicEncryption {
    pub fn encrypt(&self, plaintext: u64) -> Ciphertext {
        // 实现同态加密
        Ciphertext::new(plaintext)
    }
    
    pub fn decrypt(&self, ciphertext: &Ciphertext) -> u64 {
        // 实现同态解密
        ciphertext.decrypt(&self.private_key)
    }
    
    pub fn add(&self, c1: &Ciphertext, c2: &Ciphertext) -> Ciphertext {
        // 实现同态加法
        Ciphertext::add(c1, c2)
    }
}
```

## 15.2.5 多方计算理论

**定义 15.2.5** (安全多方计算)
安全多方计算允许 n 个参与方在不泄露私有输入的情况下计算函数 f(x₁, ..., xₙ)。

**安全模型**：

- 半诚实模型：参与方遵循协议但可能泄露信息
- 恶意模型：参与方可能偏离协议
- 诚实多数：假设多数参与方是诚实的

**Rust实现**：

```rust
pub struct MultiPartyComputation {
    participants: Vec<Participant>,
    threshold: usize,
}

pub struct Participant {
    id: ParticipantId,
    secret_share: SecretShare,
}

impl MultiPartyComputation {
    pub fn compute(&self, function: Function) -> Result<Output, MPCError> {
        // 实现多方计算协议
        Ok(Output::new())
    }
    
    pub fn share_secret(&self, secret: u64) -> Vec<SecretShare> {
        // 实现秘密分享
        vec![]
    }
}
```

---

**结论**：密码学系统为区块链提供了安全基础，确保数据的机密性、完整性和可用性。
