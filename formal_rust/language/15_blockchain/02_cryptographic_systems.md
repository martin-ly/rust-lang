# 密码学系统设计

## 概述

密码学系统是区块链技术的核心基础，提供了数据完整性、身份认证和隐私保护等关键功能。本章介绍区块链中使用的各种密码学原语和系统设计。

### 读者指引与快速导航

- 模型理论与形式化验证对接：`../../18_model/01_model_theory.md`
- 智能合约与安全工程：`05_smart_contract_engine.md`
- 共识机制中的密码学应用：`03_consensus_mechanisms.md`

## 哈希函数理论

### 密码学哈希函数

**定义 2.1** (密码学哈希函数)
一个密码学哈希函数 $H: \{0,1\}^* \to \{0,1\}^n$ 必须满足以下性质：

1. **抗原像性**：给定 $y = H(x)$，计算上难以找到 $x'$ 使得 $H(x') = y$
2. **抗第二原像性**：给定 $x$，计算上难以找到 $x' \neq x$ 使得 $H(x') = H(x)$
3. **抗碰撞性**：计算上难以找到 $x_1 \neq x_2$ 使得 $H(x_1) = H(x_2)$

### SHA-256

**算法 2.1** (SHA-256)

```text
输入: 消息 M
输出: 256位哈希值

1. 预处理消息
2. 初始化哈希值
3. 对每个512位块执行压缩函数
4. 返回最终哈希值
```

### 默克尔树

**定义 2.2** (默克尔树)
默克尔树是一个二叉树，其中：

- 叶子节点包含数据的哈希值
- 内部节点包含其子节点哈希值的哈希
- 根节点包含整个数据集的哈希值

**性质 2.A**（抗篡改与高效证明）

- 若底层哈希满足抗碰撞与抗第二原像，则默克尔根对数据集具有抗篡改性。
- 单个元素成员性证明长度为 O(log N)，验证时间 O(log N)。

## 数字签名理论

### 数字签名方案

**定义 2.3** (数字签名方案)
一个数字签名方案由三个算法组成：

- $\text{KeyGen}() \to (sk, pk)$：密钥生成
- $\text{Sign}(sk, m) \to \sigma$：签名生成
- $\text{Verify}(pk, m, \sigma) \to \{0,1\}$：签名验证

### ECDSA

**算法 2.2** (ECDSA签名)

```text
输入: 私钥 d, 消息 m
输出: 签名 (r, s)

1. 计算 h = Hash(m)
2. 选择随机数 k
3. 计算 (x, y) = k * G
4. 计算 r = x mod n
5. 计算 s = k^(-1) * (h + r * d) mod n
6. 返回 (r, s)
```

**安全性质 3.A**（UF-CMA）

在选择安全曲线、实现恒定时间算子并保证随机数 k 唯一与保密的条件下，ECDSA 达到抗选择消息伪造（UF-CMA）。

## 零知识证明理论

### 零知识证明系统

**定义 2.4** (零知识证明系统)
一个零知识证明系统是一个三元组 $(P, V, S)$，其中：

- $P$ 是证明者
- $V$ 是验证者  
- $S$ 是模拟器

满足完整性、可靠性和零知识性。

### zk-SNARKs

**定义 2.5** (zk-SNARKs)
zk-SNARKs (零知识简洁非交互式知识论证) 是一种零知识证明系统，具有：

- 简洁性：证明大小固定
- 非交互性：不需要证明者和验证者之间的交互
- 可验证性：验证时间与电路大小无关

**形式定义 4.A**（知识健全性与零知识性）

zk-SNARK 证明系统满足：存在模拟器 S，使验证者在无证据情况下无法区分真实证明与模拟证明；且任意能产生有效证明的多项式时间证明者必须“知道”相应见证。

## 同态加密理论

### 同态加密方案

**定义 2.6** (同态加密方案)
一个同态加密方案允许在加密数据上直接进行计算，而不需要先解密。

**定义 2.7** (全同态加密)
如果加密方案支持任意电路的计算，则称为全同态加密。

#### 应用注记 5.A

在区块链隐私应用（例如统计或混合链下处理）中，常以部分同态（仅加法或仅乘法）满足算子需求，以降低性能与带宽开销。

## 多方计算理论

### 安全多方计算

**定义 2.8** (安全多方计算)
安全多方计算允许多个参与方在不泄露各自私有输入的情况下，共同计算一个函数。

### 门限签名

**定义 2.9** (门限签名)
门限签名允许 $n$ 个参与方中的任意 $t$ 个参与方共同生成有效签名。

#### 工程权衡 6.A

参数 t 的选取需在安全性（更高 t 抵御合谋）与可用性（更低 t 提升容错）间平衡，并结合网络延迟、委员会规模和密钥托管策略。

## 区块链密码学应用

### 工作量证明

**定义 2.10** (工作量证明)
工作量证明要求找到一个随机数 $nonce$，使得：
$$H(block\_header \| nonce) < target$$

### 权益证明

**定义 2.11** (权益证明)
权益证明根据验证者的权益大小来选择区块生产者。

### 智能合约安全

**定义 2.12** (智能合约安全)
智能合约安全涉及：

- 重入攻击防护
- 整数溢出检查
- 访问控制
- 状态一致性

### Rust 实现示例（节选）

```rust
// 注意：示例仅为结构示意，具体参数与实现需采用成熟库
use k256::{ecdsa::{SigningKey, Signature, signature::{Signer, Verifier}}, PublicKey};

pub fn sign_message(sk: &SigningKey, msg: &[u8]) -> Signature {
    sk.sign(msg)
}

pub fn verify_signature(pk: &PublicKey, msg: &[u8], sig: &Signature) -> bool {
    pk.verify(msg, sig).is_ok()
}
```

## 实现考虑

### 性能优化

1. **批量验证**：同时验证多个签名
2. **预计算**：预先计算常用值
3. **并行处理**：利用多核CPU
4. **硬件加速**：使用专用硬件

### 安全考虑

1. **密钥管理**：安全的密钥存储和分发
2. **随机数生成**：密码学安全的随机数
3. **侧信道攻击**：防护时序攻击和功耗分析
4. **量子抗性**：考虑量子计算威胁

## 交叉引用与进一步阅读

- 模型与性质映射：`../../18_model/01_model_theory.md`
- 共识与协议安全：`03_consensus_mechanisms.md`
- 智能合约引擎与审计：`05_smart_contract_engine.md`

### 快速导航

- IoT FAQ：`../../17_iot/FAQ.md`
- 分布式系统FAQ：`../../../crates/c20_distributed/docs/FAQ.md`
- AI系统FAQ：`../../../crates/c19_ai/docs/FAQ.md`
- WebAssembly FAQ：`../../16_webassembly/FAQ.md`

## 总结

密码学系统是区块链技术的安全基础，提供了：

1. **数据完整性**：通过哈希函数保证
2. **身份认证**：通过数字签名实现
3. **隐私保护**：通过零知识证明和同态加密
4. **分布式安全**：通过多方计算和门限签名

选择合适的密码学原语和实现方式对区块链系统的安全性和性能至关重要。

## 记号与术语约定

为保证全文一致，采用如下记号约定：

- **密码学原语**：$H$ 表示哈希函数；$E, D$ 表示加密/解密函数；$S, V$ 表示签名/验证函数
- **安全参数**：$\lambda$ 表示安全参数；$n$ 表示输出长度；$k$ 表示密钥长度
- **概率与复杂度**：$\text{negl}(\lambda)$ 表示可忽略函数；$\text{poly}(\lambda)$ 表示多项式函数
- **安全性质**：$\text{IND-CPA}$ 表示选择明文攻击下的不可区分性；$\text{EUF-CMA}$ 表示存在性不可伪造性
- **区块链相关**：$B_i$ 表示第 $i$ 个区块；$T_j$ 表示第 $j$ 个交易；$\text{MerkleRoot}$ 表示默克尔根

术语对照（区块链语境）：

- **密码学原语 (Cryptographic Primitive)**：基础密码学算法组件
- **安全模型 (Security Model)**：定义攻击者能力和安全目标的数学模型
- **零知识证明 (Zero-Knowledge Proof)**：证明者向验证者证明某个陈述为真，但不泄露任何额外信息

## Rust实现示例

### 哈希函数实现

```rust
use sha2::{Sha256, Digest};
use std::collections::HashMap;

/// 密码学哈希函数接口
pub trait CryptographicHash {
    type Output: AsRef<[u8]> + Clone + Eq + std::hash::Hash;
    
    fn hash(&self, input: &[u8]) -> Self::Output;
    fn hash_twice(&self, input: &[u8]) -> Self::Output;
}

/// SHA-256 实现
pub struct Sha256Hasher;

impl CryptographicHash for Sha256Hasher {
    type Output = [u8; 32];
    
    fn hash(&self, input: &[u8]) -> Self::Output {
        let mut hasher = Sha256::new();
        hasher.update(input);
        hasher.finalize().into()
    }
    
    fn hash_twice(&self, input: &[u8]) -> Self::Output {
        let first_hash = self.hash(input);
        self.hash(&first_hash)
    }
}

/// 默克尔树实现
#[derive(Debug, Clone)]
pub struct MerkleTree {
    root: [u8; 32],
    leaves: Vec<[u8; 32]>,
}

impl MerkleTree {
    pub fn new(data: &[Vec<u8>]) -> Self {
        let hasher = Sha256Hasher;
        let mut leaves: Vec<[u8; 32]> = data.iter()
            .map(|d| hasher.hash(d))
            .collect();
        
        // 如果叶子节点数为奇数，复制最后一个节点
        if leaves.len() % 2 == 1 {
            leaves.push(*leaves.last().unwrap());
        }
        
        let root = Self::build_tree(&leaves, &hasher);
        
        Self { root, leaves }
    }
    
    fn build_tree(leaves: &[[u8; 32]], hasher: &Sha256Hasher) -> [u8; 32] {
        if leaves.len() == 1 {
            return leaves[0];
        }
        
        let mut next_level = Vec::new();
        for chunk in leaves.chunks(2) {
            let combined = [&chunk[0][..], &chunk[1][..]].concat();
            next_level.push(hasher.hash(&combined));
        }
        
        Self::build_tree(&next_level, hasher)
    }
    
    pub fn root(&self) -> &[u8; 32] {
        &self.root
    }
    
    /// 生成成员性证明
    pub fn generate_proof(&self, index: usize) -> Option<Vec<[u8; 32]>> {
        if index >= self.leaves.len() {
            return None;
        }
        
        let mut proof = Vec::new();
        let mut current_index = index;
        let mut current_level = self.leaves.clone();
        
        while current_level.len() > 1 {
            let sibling_index = if current_index % 2 == 0 {
                current_index + 1
            } else {
                current_index - 1
            };
            
            if sibling_index < current_level.len() {
                proof.push(current_level[sibling_index]);
            }
            
            current_index /= 2;
            current_level = Self::build_next_level(&current_level, &Sha256Hasher);
        }
        
        Some(proof)
    }
    
    fn build_next_level(level: &[[u8; 32]], hasher: &Sha256Hasher) -> Vec<[u8; 32]> {
        let mut next_level = Vec::new();
        for chunk in level.chunks(2) {
            let combined = [&chunk[0][..], &chunk[1][..]].concat();
            next_level.push(hasher.hash(&combined));
        }
        next_level
    }
}

/// 验证默克尔证明
pub fn verify_merkle_proof(
    leaf: &[u8; 32],
    proof: &[[u8; 32]],
    root: &[u8; 32],
    index: usize,
) -> bool {
    let hasher = Sha256Hasher;
    let mut current = *leaf;
    let mut current_index = index;
    
    for sibling in proof {
        let combined = if current_index % 2 == 0 {
            [&current[..], &sibling[..]].concat()
        } else {
            [&sibling[..], &current[..]].concat()
        };
        current = hasher.hash(&combined);
        current_index /= 2;
    }
    
    current == *root
}
```

### 数字签名实现

```rust
use ed25519_dalek::{Keypair, Signer, Verifier, Signature, PublicKey, SecretKey};
use rand::rngs::OsRng;

/// 数字签名接口
pub trait DigitalSignature {
    type KeyPair;
    type Signature;
    type PublicKey;
    type SecretKey;
    
    fn generate_keypair() -> Self::KeyPair;
    fn sign(&self, message: &[u8]) -> Self::Signature;
    fn verify(public_key: &Self::PublicKey, message: &[u8], signature: &Self::Signature) -> bool;
}

/// Ed25519 签名实现
pub struct Ed25519Signer {
    keypair: Keypair,
}

impl DigitalSignature for Ed25519Signer {
    type KeyPair = Keypair;
    type Signature = Signature;
    type PublicKey = PublicKey;
    type SecretKey = SecretKey;
    
    fn generate_keypair() -> Self::KeyPair {
        Keypair::generate(&mut OsRng)
    }
    
    fn sign(&self, message: &[u8]) -> Self::Signature {
        self.keypair.sign(message)
    }
    
    fn verify(public_key: &Self::PublicKey, message: &[u8], signature: &Self::Signature) -> bool {
        public_key.verify(message, signature).is_ok()
    }
}

impl Ed25519Signer {
    pub fn new() -> Self {
        Self {
            keypair: Self::generate_keypair(),
        }
    }
    
    pub fn from_secret_key(secret_key: SecretKey) -> Self {
        let public_key = PublicKey::from(&secret_key);
        Self {
            keypair: Keypair { secret: secret_key, public: public_key },
        }
    }
    
    pub fn public_key(&self) -> &PublicKey {
        &self.keypair.public
    }
}
```

## 安全证明与形式化验证

### 哈希函数安全性证明

**定理 2.1** (SHA-256 抗碰撞性)
假设 SHA-256 是抗碰撞的，则基于 SHA-256 的默克尔树满足以下性质：

1. **完整性**：任何对叶子节点的修改都会导致根哈希值改变
2. **高效证明**：成员性证明的长度为 O(log n)

**证明思路**：
设 $H$ 是抗碰撞的哈希函数，$T$ 是默克尔树。若存在两个不同的数据集 $D_1, D_2$ 产生相同的根哈希，则可以通过回溯找到 $H$ 的碰撞，与假设矛盾。

### 数字签名安全性证明

**定理 2.2** (Ed25519 EUF-CMA 安全性)
在随机预言机模型下，Ed25519 签名方案满足存在性不可伪造性（EUF-CMA）。

**证明框架**：

1. 定义安全游戏：攻击者可以查询签名预言机，目标是伪造有效签名
2. 归约到离散对数问题：将伪造攻击转化为求解离散对数
3. 分析成功概率：证明攻击者成功概率可忽略

## 练习与思考题

### 基础练习

1. **哈希函数性质验证**
   - 实现一个简单的哈希函数，验证其是否满足抗原像性
   - 设计实验测试抗碰撞性（注意：仅用于教学目的）

2. **默克尔树实现**
   - 实现一个支持任意数量叶子节点的默克尔树
   - 添加批量验证功能，验证多个元素的成员性

3. **数字签名应用**
   - 实现一个简单的区块链交易签名系统
   - 添加多重签名支持

4. **门限签名与委员会**
   - 设计 t-of-n 门限签名在共识中的使用方案，给出失效与恢复策略
   - 分析网络分区下的可用性与安全权衡

5. **零知识的工程化落地**
   - 选择一个简单电路，生成并验证 zk 证明，测量证明/验证开销
   - 讨论可信设置、通用性与批量验证对工程的影响

### 进阶练习

 1. **零知识证明基础**
    - 研究 zk-SNARKs 在区块链中的应用
    - 实现一个简单的零知识证明协议

 2. **同态加密应用**
    - 探索同态加密在隐私保护区块链中的应用
    - 实现基本的同态运算

 3. **门限签名**
    - 实现 Shamir 秘密分享方案
    - 构建门限签名系统

### 安全分析练习

1. **攻击模拟**
   - 分析已知的密码学攻击（如长度扩展攻击）
   - 设计防护措施

2. **性能优化**
   - 优化哈希函数的批量计算
   - 实现并行签名验证

## 交叉引用与扩展阅读

### 相关文档

- 区块链理论：`01_blockchain_theory.md`
- 共识机制：`03_consensus_mechanisms.md`
- 智能合约：`05_smart_contract_engine.md`
- 网络协议：`06_network_protocols.md`

### 外部资源

- [RustCrypto](https://github.com/RustCrypto) - Rust 密码学库集合
- [ed25519-dalek](https://github.com/dalek-cryptography/ed25519-dalek) - Ed25519 实现
- [merkle-tree](https://crates.io/crates/merkle-tree) - 默克尔树实现

### 安全标准

- FIPS 140-2 - 密码学模块安全要求
- Common Criteria - 信息技术安全评估标准
- NIST SP 800-57 - 密钥管理建议

## 参考文献

1. Katz, J., & Lindell, Y. (2014). Introduction to modern cryptography. CRC press.
2. Menezes, A. J., Van Oorschot, P. C., & Vanstone, S. A. (2018). Handbook of applied cryptography. CRC press.
3. Goldreich, O. (2001). Foundations of cryptography: volume 1, basic tools. Cambridge university press.
4. Boneh, D., & Shoup, V. (2020). A graduate course in applied cryptography. Draft 0.5.
