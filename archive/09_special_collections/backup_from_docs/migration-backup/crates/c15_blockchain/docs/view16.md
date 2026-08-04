# 区块链的形式逻辑基础与推论

## 目录

1. **引言：为何需要形式逻辑？**
2. **核心概念的形式化定义**
    * 2.1 分布式账本 (Distributed Ledger)
    * 2.2 状态机模型 (State Machine Model)
    * 2.3 密码学原语 (Cryptographic Primitives)
        * 2.3.1 哈希函数 (Hash Functions)
        * 2.3.2 数字签名 (Digital Signatures)
    * 2.4 交易 (Transaction)
    * 2.5 区块 (Block)
    * 2.6 共识机制 (Consensus Mechanisms)
3. **关键属性的形式化定理**
    * 3.1 不可篡改性 (Immutability)
    * 3.2 一致性 (Consistency)
    * 3.3 可用性/活性 (Availability/Liveness)
    * 3.4 拜占庭容错 (Byzantine Fault Tolerance - BFT)
4. **形式推理与证明（思路）**
    * 4.1 不可篡改性的证明思路
    * 4.2 一致性的证明思路
5. **Rust 代码示例**
    * 5.1 基本数据结构 (Block, Transaction)
    * 5.2 哈希计算
    * 5.3 (简化的) 签名与验证
6. **扩展视角与关联概念**
    * 6.1 智能合约的形式化
    * 6.2 零知识证明 (ZKP)
    * 6.3 形式化验证 (Formal Verification)
    * 6.4 不同共识的逻辑基础 (PoW vs PoS vs PBFT)
7. **总结**
8. **思维导图 (文本)**

---

## 1. 引言：为何需要形式逻辑？

区块链本质上是一个复杂的分布式系统，其核心价值在于提供无需信任第三方的数据一致性、不可篡改性和可用性。要严格地理解和保证这些特性，就需要借助形式逻辑的工具：

* **精确定义**: 形式化语言可以消除自然语言的歧义，精确描述系统组件、状态和行为。
* **严格证明**: 可以通过逻辑推导来证明系统在特定假设下（如密码学假设、网络假设）满足期望的属性（如安全性、一致性）。
* **系统设计与分析**: 形式化模型有助于发现设计中的潜在缺陷和漏洞。
* **自动化验证**: 形式化规约可用于自动化工具进行模型检测或定理证明。

将区块链视为一个**分布式状态机**，其状态转换由经过验证和共识的交易驱动，是进行形式化分析的常用切入点。

## 2. 核心概念的形式化定义

* **2.1 分布式账本 (Distributed Ledger)**
  * **定义**: 一个在多个网络节点 \(P = \{p_1, p_2, ..., p_n\}\) 之间复制、共享和同步的仅追加 (Append-only) 数据记录 \(L\)。
  * **形式化**: 可以看作是一个序列（或有向无环图 DAG）的记录 \(L = \langle r_1, r_2, ... \rangle\)。每个节点 \(p_i\) 维护一个本地副本 \(L_i\)。目标是确保所有（诚实的）节点的副本最终趋于一致。

* **2.2 状态机模型 (State Machine Model)**
  * **定义**: 区块链可以建模为一个确定性状态机 \(SM = (S, T, \delta)\)，其中：
    * \(S\) 是所有可能状态的集合（例如，所有账户余额的集合）。
    * \(T\) 是所有可能交易（输入）的集合。
    * \(\delta: S \times T \rightarrow S\) 是状态转换函数。给定当前状态 \(s \in S\) 和一个交易 \(t \in T\)，\(\delta(s, t)\) 计算出新的状态 \(s'\)。
  * **关键**: \(\delta\) 必须是确定性的，即对于相同的状态和交易，结果永远相同。所有节点必须就交易的顺序达成共识，以保证它们应用 \(\delta\) 后达到相同的最终状态。

* **2.3 密码学原语 (Cryptographic Primitives)**
  * **2.3.1 哈希函数 (Hash Functions)**
    * **定义**: 一个函数 \(H: \{0,1\}^* \rightarrow \{0,1\}^k\)，将任意长度的输入映射到固定长度 \(k\) 的输出。
    * **形式属性 (假设)**:
      * **抗碰撞性 (Collision Resistance)**: 找到不同的输入 \(x, y\) 使得 \(H(x) = H(y)\) 在计算上是不可行的。
      * **抗原像性 (Preimage Resistance)**: 给定 \(h\)，找到 \(x\) 使得 \(H(x) = h\) 在计算上是不可行的。
      * **抗第二原像性 (Second Preimage Resistance)**: 给定 \(x\)，找到 \(y \neq x\) 使得 \(H(x) = H(y)\) 在计算上是不可行的。
  * **2.3.2 数字签名 (Digital Signatures)**
    * **定义**: 一个方案 \(DS = (Gen, Sign, Verify)\)。
      * \(Gen()\): 生成一对密钥（公钥 \(pk\)，私钥 \(sk\)）。
      * \(Sign(sk, m)\): 使用私钥 \(sk\) 对消息 \(m\) 生成签名 \(\sigma\)。
      * \(Verify(pk, m, \sigma)\): 使用公钥 \(pk\) 验证签名 \(\sigma\) 对于消息 \(m\) 是否有效，输出 True/False。
    * **形式属性 (假设)**: **不可伪造性 (Unforgeability)**: 攻击者在不知道 \(sk\) 的情况下，即使能让签名者对选择的消息进行签名（选择消息攻击），也无法伪造出任何新消息 \(m'\) 的有效签名 \(\sigma'\)。即 \(Verify(pk, m', \sigma')\) 为 True。

* **2.4 交易 (Transaction)**
  * **定义**: 表示状态转换请求的数据结构。通常包含发送者、接收者、值/数据、签名等。
  * **形式化**: \(t = (sender, recipient, data, signature)\)，其中 \(signature = Sign(sk_{sender}, H(sender, recipient, data))\)。验证交易需要 \(Verify(pk_{sender}, H(sender, recipient, data), signature)\)。

* **2.5 区块 (Block)**
  * **定义**: 一组有序交易的集合，通常还包含元数据，如上一个区块的哈希、时间戳、Nonce（用于PoW）等。
  * **形式化**: \(B = (prev\_hash, timestamp, nonce, transactions, merkleroot)\)。\(transactions = \langle t_1, t_2, ..., t_k \rangle\)。\(merkleroot\) 是交易列表的默克尔树根哈希。区块头 \(Header = (prev\_hash, timestamp, nonce, merkleroot)\)。区块哈希 \(H(B) = H(Header)\)。
  * **链**: 区块通过 \(prev\_hash\) 指针连接起来，形成链 \(C = \langle B_0, B_1, B_2, ... \rangle\)，其中 \(B_i.prev\_hash = H(B_{i-1})\)。

* **2.6 共识机制 (Consensus Mechanisms)**
  * **定义**: 一组规则和协议，使得分布式网络中的节点能够就下一个要添加到链上的区块（即交易的顺序和有效性）达成一致。
  * **形式化目标**: 确保所有诚实节点最终会接受相同的、有效的区块序列。例如，对于任何两个诚实节点 \(p_i, p_j\) 和它们接受的链 \(C_i, C_j\)，在某个时间点之后，\(C_i\) 是 \(C_j\) 的前缀，或者 \(C_j\) 是 \(C_i\) 的前缀（最终收敛到同一条主链）。

## 3. 关键属性的形式化定理

* **3.1 不可篡改性 (Immutability)**
  * **定理 (非形式化)**: 一旦一个区块 \(B_k\) 被添加到链中并被足够多的后续区块确认（例如，在比特币中是6个区块），那么修改 \(B_k\) 或其之前的任何区块 \(B_j (j \le k)\) 中的任何信息（如交易）在计算上是不可行的，除非攻击者控制了网络的大部分算力（或权益等）。
  * **逻辑基础**:
    * 哈希函数的抗碰撞性：修改区块内容会导致哈希改变。
    * 链式结构：修改 \(B_k\) 的哈希 \(H(B_k)\) 会使其与 \(B_{k+1}.prev\_hash\) 不匹配，要使链重新有效，必须重新计算 \(B_{k+1}\) 及之后所有区块的哈希。
    * 共识机制（如PoW）的难度：重新计算大量区块需要巨大的、通常是不可行的计算资源。

* **3.2 一致性 (Consistency)**
  * **定理 (最终一致性)**: 对于任何两个诚实的节点 \(p_i\) 和 \(p_j\)，它们各自维护的账本状态 \(S_i\) 和 \(S_j\)，随着时间的推移，它们对于账本历史（已确认区块序列）的认知将趋于一致。对于某个足够深度的区块 \(k\) 之后，它们都会认可相同的主链 \(C = \langle B_0, ..., B_k, ... \rangle\)。
  * **逻辑基础**: 共识协议的设计目标就是收敛到单一的全局认可的交易历史。例如，Nakamoto共识（最长链规则）确保节点倾向于在增长最快的链上工作。

* **3.3 可用性/活性 (Availability/Liveness)**
  * **定理 (非形式化)**: 如果一个有效的交易被广播到网络中足够多的诚实节点，那么它最终会被包含在某个区块中，并被添加到链上。
  * **逻辑基础**: 共识协议通常包含激励机制（如交易费、区块奖励）和规则（如诚实节点会打包待处理的有效交易），以确保系统持续运行并处理新的交易。但活性在异步网络和面临特定攻击（如审查）时可能更难保证。

* **3.4 拜占庭容错 (Byzantine Fault Tolerance - BFT)**
  * **定理 (对于BFT类共识)**: 如果网络中恶意或故障的节点数量不超过某个阈值 \(f\)（例如，对于经典的PBFT，\(f < n/3\)，其中 \(n\) 是总节点数），那么系统仍能保证一致性（Safety）和活性（Liveness）。
  * **逻辑基础**: BFT协议通过多轮投票、确认和锁定机制来设计，即使存在部分节点发送错误或矛盾的信息，诚实节点也能通过协议规则识别并达成正确的共识。

## 4. 形式推理与证明（思路）

* **4.1 不可篡改性的证明思路 (基于PoW)**
  * **假设**:
        1. 哈希函数 \(H\) 是抗碰撞和抗原像的。
        2. 攻击者 \(\mathcal{A}\) 控制的算力比例 \(q\) 小于诚实节点控制的算力比例 \(p\) (\(q < p\)，通常假设 \(q < 0.5\))。
  * **目标**: 证明修改 \(k\) 个区块之前的区块 \(B_{i-k}\) 的成本随 \(k\) 指数级增长且极高。
  * **推理**:
        1. 要修改 \(B_{i-k}\)，必须改变其内容，导致 \(H(B_{i-k})\) 改变。
        2. 这使得 \(B_{i-k+1}.prev\_hash\) 失效。必须重新找到 \(B'_{i-k+1}\) (找到新的Nonce) 使得 \(H(B'_{i-k+1})\) 满足难度要求，且 \(B'_{i-k+1}.prev\_hash = H'(B_{i-k})\)。
        3. 此过程必须一直持续到当前最新区块 \(B_i\)，生成一条新的分叉链 \(C' = \langle ..., B'_{i-k}, ..., B'_i \rangle\)。
        4. 根据PoW，找到一个有效区块的概率与算力成正比。诚实网络产生新区块的速率期望为 \(p \lambda\)，攻击者为 \(q \lambda\) (\(\lambda\) 是总速率)。
        5. 攻击者需要生成一条比诚实链增长更快的链（至少赶上并超过 \(k\) 个区块）。这类似于一个随机游走问题（Gambler's Ruin）。当 \(q < p\) 时，攻击者成功追上并超过 \(k\) 个区块的概率随 \(k\) 的增加呈指数级下降 \( (q/p)^k \)。
        6. 因此，当 \(k\) 足够大时（如 \(k=6\)），成功的概率在计算上可以忽略不计。

* **4.2 一致性的证明思路 (基于最长链规则)**
  * **假设**:
        1. 网络延迟有界（或者消息最终能送达）。
        2. 诚实节点遵循协议（选择最长的有效链）。
        3. 攻击者算力 \(q < 0.5\)。
  * **目标**: 证明两个诚实节点最终会收敛到同一条主链。
  * **推理**:
        1. 由于诚实算力占优，诚实链（由诚实节点挖掘区块构成的链）预期增长速度更快。
        2. 即使暂时出现分叉（例如，两个节点几乎同时挖到区块），诚实节点会继续在它们看到的最长链上扩展。
        3. 随着时间推移，其中一条分叉链会因为获得更多（诚实的）算力支持而变得更长。
        4. 根据最长链规则，原来在较短分叉上的诚实节点最终会切换到这条更长的链上。
        5. 因此，对于足够深的区块，它们被推翻的可能性指数级下降，所有诚实节点最终会就包含这些区块的主链达成一致。

## 5. Rust 代码示例

这里提供一些概念性的 Rust 代码片段，用于说明核心逻辑，并非完整实现。

```rust
use sha2::{Sha256, Digest}; // 需要添加 sha2 crate
use std::time::{SystemTime, UNIX_EPOCH};

// 简化交易结构
#[derive(Debug, Clone)] // 添加 Clone trait
struct Transaction {
    sender: String,
    recipient: String,
    amount: u64,
    // 在实际应用中，这里应该是数字签名
    // signature: Vec<u8>, 
    // 为了简化，我们省略签名部分或用一个简单标识
    timestamp: u64,
}

impl Transaction {
    // 交易数据序列化，用于哈希
    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(self.sender.as_bytes());
        bytes.extend_from_slice(self.recipient.as_bytes());
        bytes.extend_from_slice(&self.amount.to_be_bytes());
        bytes.extend_from_slice(&self.timestamp.to_be_bytes());
        bytes
    }

    // 计算交易哈希（简化）
    fn calculate_hash(&self) -> Vec<u8> {
        let mut hasher = Sha256::new();
        hasher.update(self.to_bytes());
        hasher.finalize().to_vec()
    }
}


// 简化区块结构
#[derive(Debug, Clone)] // 添加 Clone trait
struct Block {
    index: u64,
    timestamp: u64,
    transactions: Vec<Transaction>, // 区块包含的交易列表
    previous_hash: Vec<u8>,        // 上一个区块的哈希
    hash: Vec<u8>,                // 当前区块的哈希
    nonce: u64,                   // 用于 PoW
}

impl Block {
    // 创建创世区块
    fn genesis() -> Self {
         let genesis_tx = Transaction {
            sender: String::from("Genesis"),
            recipient: String::from("Genesis"),
            amount: 0,
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
        };
        let mut block = Block {
            index: 0,
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
            transactions: vec![genesis_tx],
            previous_hash: vec![0; 32], // 创世区块的前哈希通常为0
            hash: vec![], // 先置空，稍后计算
            nonce: 0,
        };
        // 在实际PoW中，需要挖矿找到合适的nonce才计算最终hash
        block.hash = block.calculate_hash();
        block
    }

    // 计算区块哈希 (简化，未包含 PoW 逻辑)
    // 实际哈希计算通常只针对区块头
    fn calculate_hash(&self) -> Vec<u8> {
        let mut hasher = Sha256::new();
        hasher.update(&self.index.to_be_bytes());
        hasher.update(&self.timestamp.to_be_bytes());
        // 实际应用中可能使用 Merkle Root
        for tx in &self.transactions {
             hasher.update(tx.calculate_hash()); // 使用交易哈希
        }
        hasher.update(&self.previous_hash);
        hasher.update(&self.nonce.to_be_bytes());
        hasher.finalize().to_vec()
    }
    
    // 演示区块创建（非挖矿）
    fn new(index: u64, transactions: Vec<Transaction>, previous_hash: Vec<u8>) -> Self {
         let mut block = Block {
            index,
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
            transactions,
            previous_hash,
            hash: vec![], // 先置空
            nonce: 0,     // PoW 需要找到合适的 nonce
        };
        // 假设我们找到了 nonce (简化)
        // block.mine_block(difficulty); // 实际需要挖矿逻辑
        block.hash = block.calculate_hash(); // 计算最终哈希
        block
    }
}

// 简化区块链结构
struct Blockchain {
    chain: Vec<Block>,
    // pending_transactions: Vec<Transaction>, // 未打包交易
    // difficulty: usize, // PoW 难度
}

impl Blockchain {
    fn new() -> Self {
        Blockchain {
            chain: vec![Block::genesis()],
            // pending_transactions: vec![],
            // difficulty: 2, // 示例难度
        }
    }

    fn get_latest_block(&self) -> &Block {
        self.chain.last().unwrap()
    }

    // 添加新区块（简化，未包含完整验证和共识）
    fn add_block(&mut self, transactions: Vec<Transaction>) {
        let previous_block = self.get_latest_block();
        let new_block = Block::new(
            previous_block.index + 1,
            transactions,
            previous_block.hash.clone(),
        );
        
        // 基础验证（简化）
        if new_block.previous_hash == previous_block.hash {
           // 在实际应用中还需要验证区块哈希是否满足难度要求、交易有效性等
           println!("Adding block: {:?}", new_block.index);
           self.chain.push(new_block);
        } else {
            println!("Invalid block: Previous hash mismatch");
        }
    }
    
     // 链的有效性验证（简化）
    fn is_chain_valid(&self) -> bool {
        for i in 1..self.chain.len() {
            let current_block = &self.chain[i];
            let previous_block = &self.chain[i - 1];

            // 检查当前区块存储的哈希是否与其内容的计算哈希一致
            if current_block.hash != current_block.calculate_hash() {
                println!("Validation failed: Block {} hash mismatch.", current_block.index);
                return false;
            }

            // 检查 previous_hash 是否指向前一个区块的哈希
            if current_block.previous_hash != previous_block.hash {
                 println!("Validation failed: Block {} previous_hash mismatch.", current_block.index);
                return false;
            }
            // 实际应用中还需要验证 PoW, 交易签名等
        }
        // 创世区块验证（可选）
        let genesis = &self.chain[0];
        if genesis.hash != genesis.calculate_hash() {
             println!("Validation failed: Genesis block hash mismatch.");
             return false;
        }
        
        println!("Chain validation successful.");
        true
    }
}

fn main() {
    // 创建一个新的区块链实例
    let mut my_chain = Blockchain::new();
    println!("Genesis block: {:?}", my_chain.get_latest_block());

    // 创建一些交易
    let tx1 = Transaction {
        sender: String::from("Alice"),
        recipient: String::from("Bob"),
        amount: 10,
         timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
    };
     let tx2 = Transaction {
        sender: String::from("Bob"),
        recipient: String::from("Charlie"),
        amount: 5,
         timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
    };
    
    // 将交易打包进新区块并添加到链上
    println!("Mining block 1...");
    my_chain.add_block(vec![tx1]);

    println!("Mining block 2...");
    my_chain.add_block(vec![tx2]);

    // 打印区块链信息
    println!("\nCurrent blockchain:");
    for block in &my_chain.chain {
        println!("  Index: {}", block.index);
        println!("  Timestamp: {}", block.timestamp);
        // println!("  Transactions: {:?}", block.transactions); // 打印交易可能很长
        println!("  Prev Hash: {}", hex::encode(&block.previous_hash)); // 需要添加 hex crate
        println!("  Hash: {}", hex::encode(&block.hash));
        println!("  Nonce: {}", block.nonce);
        println!("---");
    }
    
    // 验证链的有效性
    println!("Validating chain...");
    my_chain.is_chain_valid();
    
    // 尝试篡改 (仅为演示逻辑)
    // my_chain.chain[1].transactions[0].amount = 1000; // 直接修改数据
    // my_chain.chain[1].hash = my_chain.chain[1].calculate_hash(); // 尝试重新计算哈希 (但未重新挖矿且未更新后续区块)
    
    // 再次验证，会失败，因为后续区块的 previous_hash 不匹配了
    // println!("\nValidating chain after tampering attempt...");
    // my_chain.is_chain_valid(); // 应该输出 false
}

// 注意: 
// 1. 运行此代码需要添加依赖到 Cargo.toml:
//    sha2 = "0.10"
//    hex = "0.4" 
// 2. 省略了网络、P2P、实际的签名验证、复杂的 PoW/PoS 挖矿/验证逻辑、交易池管理、Merkle Tree 实现等。
// 3. 错误处理简化。
// 4. 签名部分未实现，实际应用中极其重要。
```

**代码说明**:

* `Transaction` 和 `Block` 结构体定义了基本的数据单元。
* `calculate_hash` 方法演示了如何利用哈希函数（这里是 SHA-256）为数据创建摘要。区块的哈希依赖于其内容（包括交易列表、时间戳、Nonce）和上一个区块的哈希，形成了链式依赖。
* `Blockchain` 结构体维护了区块列表 `chain`。
* `add_block` 模拟了添加新区块的过程（简化了共识）。
* `is_chain_valid` 展示了验证链完整性的基本逻辑：检查每个区块自身的哈希是否正确，以及 `previous_hash` 是否正确连接。任何对历史区块的篡改都会破坏这种连接性，除非重新计算后续所有区块的哈希（这在 PoW 中成本极高）。

## 6. 扩展视角与关联概念

* **6.1 智能合约的形式化**:
  * 智能合约是部署在区块链上的代码，可视为扩展的状态转换逻辑。
  * 形式化方法可以用来：
    * **规约 (Specification)**: 使用逻辑语言（如 LTL, CTL, Hoare Logic）精确描述合约的预期行为和属性（如不变量、前置/后置条件）。
    * **验证 (Verification)**: 证明代码实现符合其规约，防止漏洞（如重入攻击、整数溢出）。常用技术包括模型检测、定理证明。
  * **视角转换**: 将智能合约视为具有明确输入、输出和状态转换规则的数学函数或逻辑程序。

* **6.2 零知识证明 (ZKP)**:
  * **定义**: 允许一方（证明者）向另一方（验证者）证明某个陈述为真，而无需透露除了该陈述为真之外的任何信息。
  * **关联**:
    * **隐私**: 隐藏交易细节（发送方、接收方、金额），只证明交易的有效性。
    * **可扩展性**: 将复杂的计算移到链下执行，然后在链上提交一个简短的 ZKP 来证明计算的正确性，验证 ZKP 比直接执行计算快得多（如 ZK-Rollups）。
  * **形式逻辑**: ZKP 本身基于复杂的数学和密码学理论，其安全性依赖于严格的证明和计算困难性假设。

* **6.3 形式化验证 (Formal Verification)**:
  * 将形式逻辑方法应用于区块链协议、客户端软件和智能合约，以数学方式证明其正确性或发现错误。
  * **深度扩展**: 这是确保高风险、高价值区块链应用（如 DeFi）安全性的重要手段。需要专门的工具（如 Coq, Isabelle/HOL, TLA+, Dafny）和专业知识。

* **6.4 不同共识的逻辑基础**:
  * **PoW (Proof-of-Work)**:
    * **逻辑**: 通过计算难题（哈希计算）来竞争记账权。安全性依赖于算力优势和经济激励。"最长链"是主要规则。其形式化分析常涉及概率论和随机过程。
  * **PoS (Proof-of-Stake)**:
    * **逻辑**: 记账权根据持有的代币数量（权益）来分配。安全性依赖于经济惩罚（罚没机制 Slashing）和权益集中度假设。其形式化分析更侧重于博弈论和分布式系统模型。
  * **PBFT (Practical Byzantine Fault Tolerance)**:
    * **逻辑**: 基于经典 BFT 理论，使用多轮消息传递和投票来达成确定性共识。只要少于 1/3 节点是拜占庭节点，就能保证安全性和活性。其形式化模型通常基于状态机复制和消息传递系统。

## 7. 总结

区块链的形式逻辑基础在于将系统建模为分布式状态机，并利用密码学原语（哈希、签名）构建其核心机制。
关键属性如不可篡改性和一致性可以通过形式化的定理进行描述，
其保证依赖于底层的密码学假设和共识协议的设计。
形式推理和证明（即使是思路层面）有助于深入理解这些保证是如何实现的。
Rust 等语言可以用来实现这些逻辑概念，
而形式化验证、ZKP 等扩展技术则进一步增强了区块链的安全性、隐私性和可扩展性。
理解这些形式化的基础对于设计、分析和信任区块链系统至关重要。

## 8. 思维导图 (文本)

```text
区块链形式逻辑基础与推论
│
├── 1. 引言：为何需要形式逻辑
│   ├── 精确定义
│   ├── 严格证明
│   ├── 系统设计与分析
│   └── 自动化验证
│
├── 2. 核心概念的形式化定义
│   ├── 分布式账本 (L = <r1, r2, ...>, 节点副本 Li)
│   ├── 状态机模型 (SM = (S, T, δ), 确定性 δ)
│   ├── 密码学原语
│   │   ├── 哈希函数 (H: {0,1}* -> {0,1}^k, 抗碰撞, 抗原像)
│   │   └── 数字签名 (DS = (Gen, Sign, Verify), 不可伪造性)
│   ├── 交易 (t = (sender, recipient, data, signature))
│   ├── 区块 (B = (prev_hash, ..., transactions), H(B), 链式结构)
│   └── 共识机制 (达成一致的规则/协议)
│
├── 3. 关键属性的形式化定理
│   ├── 不可篡改性 (基于 H, 链, 共识难度)
│   ├── 一致性 (最终一致性, 基于共识收敛)
│   ├── 可用性/活性 (有效交易最终被打包)
│   └── 拜占庭容错 (BFT, < f 故障节点仍可工作)
│
├── 4. 形式推理与证明（思路）
│   ├── 不可篡改性证明 (PoW: 算力 < 0.5, 修改成本指数增长)
│   └── 一致性证明 (最长链: 诚实节点收敛)
│
├── 5. Rust 代码示例
│   ├── 数据结构 (struct Transaction, struct Block)
│   ├── 哈希计算 (Sha256, block.calculate_hash())
│   ├── 链式结构 (struct Blockchain, add_block, is_chain_valid)
│   └── (简化了签名、PoW/PoS、网络等)
│
├── 6. 扩展视角与关联概念
│   ├── 智能合约形式化 (规约, 验证, 防漏洞)
│   ├── 零知识证明 (ZKP) (隐私, 扩展性 - ZK-Rollups)
│   ├── 形式化验证 (FV) (协议, 软件, 合约的数学证明)
│   └── 不同共识逻辑 (PoW: 算力+概率, PoS: 权益+经济惩罚, PBFT: 投票+确定性)
│
└── 7. 总结
    ├── 状态机 + 密码学 + 共识 = 区块链核心逻辑
    └── 形式化是理解、设计、信任的关键
```
