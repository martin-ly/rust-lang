# Rust 区块链/Web3 开发完整指南

> 一份全面的Rust区块链开发指南，涵盖从智能合约到核心协议的完整技术栈。

---

## 目录

- [Rust 区块链/Web3 开发完整指南](#rust-区块链web3-开发完整指南)
  - [目录](#目录)
  - [1. 区块链开发概述](#1-区块链开发概述)
    - [1.1 为什么Rust适合区块链](#11-为什么rust适合区块链)
    - [1.2 内存安全与共识算法](#12-内存安全与共识算法)
    - [1.3 性能要求](#13-性能要求)
  - [2. 智能合约开发](#2-智能合约开发)
    - [2.1 ink!框架介绍](#21-ink框架介绍)
    - [2.2 Substrate链开发](#22-substrate链开发)
    - [2.3 Solana Rust程序](#23-solana-rust程序)
    - [2.4 NEAR合约](#24-near合约)
  - [3. 区块链核心组件](#3-区块链核心组件)
    - [3.1 共识算法实现](#31-共识算法实现)
      - [工作量证明 (PoW)](#工作量证明-pow)
      - [权益证明 (PoS)](#权益证明-pos)
      - [拜占庭容错 (BFT)](#拜占庭容错-bft)
    - [3.2 交易池管理](#32-交易池管理)
  - [6. 存储层](#6-存储层)
    - [6.1 LevelDB/RocksDB集成](#61-leveldbrocksdb集成)
    - [6.2 状态数据库](#62-状态数据库)
    - [6.3 归档节点](#63-归档节点)
  - [7. 完整示例：简化的区块链实现](#7-完整示例简化的区块链实现)
    - [7.1 区块结构](#71-区块结构)
    - [7.2 挖矿算法](#72-挖矿算法)
    - [7.3 交易验证](#73-交易验证)
    - [7.4 网络同步](#74-网络同步)
  - [8. DeFi开发](#8-defi开发)
    - [8.1 DEX核心逻辑](#81-dex核心逻辑)
    - [8.2 借贷协议](#82-借贷协议)
    - [8.3 流动性池](#83-流动性池)
  - [9. 安全最佳实践](#9-安全最佳实践)
    - [9.1 重入攻击防护](#91-重入攻击防护)
    - [9.2 整数溢出防护](#92-整数溢出防护)
    - [9.3 访问控制](#93-访问控制)
  - [10. 测试与部署](#10-测试与部署)
    - [10.1 本地测试网](#101-本地测试网)
    - [10.2 单元测试](#102-单元测试)
    - [10.3 审计工具](#103-审计工具)
  - [附录：资源推荐](#附录资源推荐)
    - [学习资源](#学习资源)
    - [常用Crates](#常用crates)

---

## 1. 区块链开发概述

### 1.1 为什么Rust适合区块链

Rust在区块链领域迅速崛起成为首选语言，主要基于以下核心优势：

```text
┌─────────────────────────────────────────────────────────────────┐
│                     Rust 区块链优势矩阵                          │
├─────────────────┬─────────────────┬─────────────────────────────┤
│    内存安全      │    零成本抽象    │       高性能并发             │
│  编译期所有权    │   无运行时开销   │     fearless concurrency     │
│  消除数据竞争    │   底层控制       │      async/await            │
├─────────────────┼─────────────────┼─────────────────────────────┤
│    确定性执行    │    跨平台       │       丰富生态               │
│  可预测的gas    │   可移植性强     │    WebAssembly支持          │
│  无垃圾回收暂停  │   嵌入式支持     │      密码学库成熟            │
└─────────────────┴─────────────────┴─────────────────────────────┘
```

**核心优势详解：**

| 特性 | 区块链应用价值 |
|------|---------------|
| **内存安全** | 杜绝缓冲区溢出、use-after-free等安全漏洞 |
| **无GC** | 避免垃圾回收导致的共识延迟和性能抖动 |
| **确定性** | 确保所有节点执行结果一致，这对共识至关重要 |
| **WASM** | 天然支持WebAssembly，是智能合约的标准执行环境 |
| **零成本抽象** | 高级语言特性不牺牲性能 |

### 1.2 内存安全与共识算法

区块链系统的共识算法对执行确定性有严格要求。Rust的所有权系统从根本上保障了这一点：

```rust
// 示例：Rust所有权确保共识状态的一致性
pub struct ConsensusState {
    view_number: u64,
    validators: Vec<Validator>,
    // 所有权明确，没有隐藏的共享可变状态
}

impl ConsensusState {
    // &self 确保只读访问，不会意外修改状态
    pub fn is_valid_proposer(&self, proposer: &Address) -> bool {
        self.validators
            .get(self.view_number as usize % self.validators.len())
            .map(|v| v.address == *proposer)
            .unwrap_or(false)
    }

    // &mut self 明确表示状态变更，需要可变所有权
    pub fn advance_view(&mut self) {
        self.view_number += 1;
    }
}
```

**关键原则：**

- 编译期检查消除数据竞争
- 显式生命周期管理避免悬垂指针
- `Send` 和 `Sync` trait 保证线程安全

### 1.3 性能要求

区块链系统面临的性能挑战：

```text
TPS (每秒交易数) 优化目标
├── 比特币: ~7 TPS
├── 以太坊1.0: ~15 TPS
├── 现代Layer1目标: 1,000-10,000 TPS
└── Layer2/Rollup目标: 10,000-100,000 TPS

延迟要求
├── 区块确认: 秒级
├── 最终确定性: 分钟级
└── 查询响应: 毫秒级
```

Rust的高性能特性：

- 媲美C/C++的运行时性能
- 无运行时开销的并发模型
- SIMD指令支持（用于密码学运算）
- 内联汇编支持（关键路径优化）

---

## 2. 智能合约开发

### 2.1 ink!框架介绍

ink! 是 Parity Technologies 开发的基于Rust的智能合约语言，编译为WASM在Substrate链上运行。

```rust
#![cfg_attr(not(feature = "std"), no_std, no_main)]

#[ink::contract]
mod token {
    use ink::storage::Mapping;

    /// 事件定义
    #[ink(event)]
    pub struct Transfer {
        #[ink(topic)]
        from: Option<AccountId>,
        #[ink(topic)]
        to: Option<AccountId>,
        value: Balance,
    }

    #[ink(storage)]
    pub struct Erc20 {
        /// 总供应量
        total_supply: Balance,
        /// 余额映射
        balances: Mapping<AccountId, Balance>,
        /// 授权额度
        allowances: Mapping<(AccountId, AccountId), Balance>,
    }

    impl Erc20 {
        #[ink(constructor)]
        pub fn new(initial_supply: Balance) -> Self {
            let caller = Self::env().caller();
            let mut balances = Mapping::default();
            balances.insert(caller, &initial_supply);

            Self::env().emit_event(Transfer {
                from: None,
                to: Some(caller),
                value: initial_supply,
            });

            Self {
                total_supply: initial_supply,
                balances,
                allowances: Mapping::default(),
            }
        }

        #[ink(message)]
        pub fn total_supply(&self) -> Balance {
            self.total_supply
        }

        #[ink(message)]
        pub fn balance_of(&self, owner: AccountId) -> Balance {
            self.balances.get(owner).unwrap_or_default()
        }

        #[ink(message)]
        pub fn transfer(&mut self, to: AccountId, value: Balance) -> Result<(), Error> {
            let from = self.env().caller();
            self.transfer_from_to(from, to, value)
        }

        fn transfer_from_to(
            &mut self,
            from: AccountId,
            to: AccountId,
            value: Balance,
        ) -> Result<(), Error> {
            let from_balance = self.balance_of(from);
            if from_balance < value {
                return Err(Error::InsufficientBalance);
            }

            self.balances.insert(from, &(from_balance - value));
            let to_balance = self.balance_of(to);
            self.balances.insert(to, &(to_balance + value));

            self.env().emit_event(Transfer {
                from: Some(from),
                to: Some(to),
                value,
            });

            Ok(())
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        InsufficientBalance,
        InsufficientAllowance,
    }
}
```

**ink! 架构：**

```text
┌─────────────────────────────────────────┐
│           ink! Contract                 │
├─────────────────────────────────────────┤
│  #[ink::contract]                       │
│  ├── #[ink(storage)]     - 状态定义      │
│  ├── #[ink(event)]       - 事件定义      │
│  ├── #[ink(constructor)] - 构造函数      │
│  ├── #[ink(message)]     - 可调函数      │
│  └── #[ink(impl)]        - 内部实现      │
├─────────────────────────────────────────┤
│         WASM Compilation                │
├─────────────────────────────────────────┤
│    pallet-contracts (Substrate)         │
│    ├── wasmi (解释器)                    │
│    └── wasmtime (JIT)                   │
└─────────────────────────────────────────┘
```

### 2.2 Substrate链开发

Substrate是Parity开发的模块化区块链框架：

```rust
// FRAME Pallet 示例：自定义链上逻辑
#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
        type MaxLength: Get<u32>;
    }

    #[pallet::storage]
    #[pallet::getter(fn value)]
    pub type Value<T: Config> = StorageValue<_, u32, ValueQuery>;

    #[pallet::storage]
    #[pallet::unbounded]
    pub type Documents<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BoundedVec<u8, T::MaxLength>,
        ValueQuery,
    >;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        ValueStored { value: u32, who: T::AccountId },
        DocumentStored { who: T::AccountId, doc_id: u32 },
    }

    #[pallet::error]
    pub enum Error<T> {
        StorageOverflow,
        DocumentTooLong,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        pub fn store_value(
            origin: OriginFor<T>,
            value: u32,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            <Value<T>>::put(value);

            Self::deposit_event(Event::ValueStored { value, who });
            Ok(())
        }
    }
}
```

### 2.3 Solana Rust程序

Solana使用Rust编写原生程序，基于BPF（Berkeley Packet Filter）字节码：

```rust
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint,
    entrypoint::ProgramResult,
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
    sysvar::{rent::Rent, Sysvar},
};

entrypoint!(process_instruction);

pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    msg!("Solana program entrypoint");

    let accounts_iter = &mut accounts.iter();
    let account = next_account_info(accounts_iter)?;

    if account.owner != program_id {
        msg!("Invalid program id");
        return Err(ProgramError::IncorrectProgramId);
    }

    let mut data = account.try_borrow_mut_data()?;
    data[..instruction_data.len()].copy_from_slice(instruction_data);

    msg!("Success");
    Ok(())
}
```

### 2.4 NEAR合约

NEAR Protocol的智能合约开发：

```rust
use near_sdk::borsh::{self, BorshDeserialize, BorshSerialize};
use near_sdk::{env, near_bindgen, AccountId, Balance};

#[near_bindgen]
#[derive(BorshDeserialize, BorshSerialize, Default)]
pub struct Contract {
    owner: AccountId,
    balances: near_sdk::collections::LookupMap<AccountId, Balance>,
}

#[near_bindgen]
impl Contract {
    #[init]
    pub fn new(owner: AccountId) -> Self {
        assert!(!env::state_exists(), "Already initialized");
        Self {
            owner,
            balances: near_sdk::collections::LookupMap::new(b"b"),
        }
    }

    pub fn ft_balance_of(&self, account_id: AccountId) -> Balance {
        self.balances.get(&account_id).unwrap_or(0)
    }
}
```

---

## 3. 区块链核心组件

### 3.1 共识算法实现

#### 工作量证明 (PoW)

```rust
use sha2::{Sha256, Digest};
use std::time::{SystemTime, UNIX_EPOCH};

pub struct ProofOfWork {
    difficulty: usize,
}

impl ProofOfWork {
    pub fn new(difficulty: usize) -> Self {
        Self { difficulty }
    }

    /// 计算区块哈希
    pub fn calculate_hash(
        index: u64,
        timestamp: u64,
        prev_hash: &[u8],
        data: &str,
        nonce: u64,
    ) -> Vec<u8> {
        let mut hasher = Sha256::new();
        hasher.update(index.to_le_bytes());
        hasher.update(timestamp.to_le_bytes());
        hasher.update(prev_hash);
        hasher.update(data.as_bytes());
        hasher.update(nonce.to_le_bytes());
        hasher.finalize().to_vec()
    }

    /// 验证哈希是否满足难度要求
    fn validate_hash(hash: &[u8], difficulty: usize) -> bool {
        hash.iter().take(difficulty / 2).all(|&b| b == 0)
    }

    /// 挖矿：寻找满足条件的nonce
    pub fn mine(
        &self,
        index: u64,
        timestamp: u64,
        prev_hash: &[u8],
        data: &str,
    ) -> (u64, Vec<u8>) {
        let mut nonce = 0u64;
        loop {
            let hash = Self::calculate_hash(index, timestamp, prev_hash, data, nonce);
            if Self::validate_hash(&hash, self.difficulty) {
                return (nonce, hash);
            }
            nonce += 1;
        }
    }
}

pub struct Block {
    pub index: u64,
    pub timestamp: u64,
    pub prev_hash: Vec<u8>,
    pub hash: Vec<u8>,
    pub data: String,
    pub nonce: u64,
}
```

#### 权益证明 (PoS)

```rust
use rand::Rng;
use std::collections::HashMap;

pub struct ProofOfStake {
    stakes: HashMap<ValidatorId, u64>,
    min_stake: u64,
    total_stake: u64,
}

pub type ValidatorId = [u8; 32];

impl ProofOfStake {
    pub fn new(min_stake: u64) -> Self {
        Self {
            stakes: HashMap::new(),
            min_stake,
            total_stake: 0,
        }
    }

    /// 质押成为验证者
    pub fn stake(&mut self, validator: ValidatorId, amount: u64) -> Result<(), StakeError> {
        if amount < self.min_stake {
            return Err(StakeError::InsufficientStake);
        }

        *self.stakes.entry(validator).or_insert(0) += amount;
        self.total_stake += amount;
        Ok(())
    }

    /// 选择区块提议者（基于质押权重的随机选择）
    pub fn select_proposer(&self, seed: [u8; 32]) -> Option<ValidatorId> {
        if self.stakes.is_empty() {
            return None;
        }

        let mut rng = rand::SeedableRng::from_seed(seed);
        let threshold = rng.gen::<u64>() % self.total_stake;

        let mut cumulative = 0u64;
        for (validator, stake) in &self.stakes {
            cumulative += stake;
            if cumulative > threshold {
                return Some(*validator);
            }
        }

        None
    }
}

#[derive(Debug)]
pub enum StakeError {
    InsufficientStake,
}
```

#### 拜占庭容错 (BFT)

```rust
use std::collections::{HashMap, HashSet};
use serde::{Serialize, Deserialize};

/// Hotstuff风格的BFT共识
pub struct BftConsensus {
    validators: HashSet<ValidatorId>,
    view: u64,
    quorum: usize,
    proposals: HashMap<Hash, ProposalState>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Proposal {
    pub view: u64,
    pub height: u64,
    pub block_hash: Hash,
    pub proposer: ValidatorId,
}

pub enum ProposalState {
    PrePrepare,
    Prepare { votes: HashSet<ValidatorId> },
    Commit { votes: HashSet<ValidatorId> },
    Finalized,
}

impl BftConsensus {
    pub fn new(validators: Vec<ValidatorId>) -> Self {
        let n = validators.len();
        let quorum = 2 * n / 3 + 1;

        Self {
            validators: validators.into_iter().collect(),
            view: 0,
            quorum,
            proposals: HashMap::new(),
        }
    }

    /// 处理投票
    pub fn on_vote(&mut self, voter: ValidatorId, block_hash: Hash) -> Option<ConsensusEvent> {
        let state = self.proposals.entry(block_hash).or_insert(
            ProposalState::Prepare { votes: HashSet::new() }
        );

        match state {
            ProposalState::Prepare { votes } => {
                votes.insert(voter);
                if votes.len() >= self.quorum {
                    *state = ProposalState::Commit { votes: votes.clone() };
                    return Some(ConsensusEvent::Prepared(block_hash));
                }
            }
            ProposalState::Commit { votes } => {
                votes.insert(voter);
                if votes.len() >= self.quorum {
                    *state = ProposalState::Finalized;
                    return Some(ConsensusEvent::Finalized(block_hash));
                }
            }
            _ => {}
        }

        None
    }
}

pub enum ConsensusEvent {
    Prepared(Hash),
    Finalized(Hash),
}
```

### 3.2 交易池管理

```rust
use std::collections::{BTreeMap, HashMap, HashSet};
use std::time::{Duration, Instant};

pub struct TxPoolConfig {
    pub max_size: usize,
    pub max_per_account: usize,
    pub ttl: Duration,
    pub min_gas_price: u64,
}

pub struct TransactionPool {
    config: TxPoolConfig,
    pending: BTreeMap<Address, BTreeMap<u64, PoolTransaction>>,
    by_gas_price: BTreeMap<u64, HashSet<TransactionHash>>,
    by_hash: HashMap<TransactionHash, PoolTransaction>,
    known: HashSet<TransactionHash>,
}

#[derive(Clone)]
pub struct PoolTransaction {
    pub hash: TransactionHash,
    pub from: Address,
    pub nonce: u64,
    pub gas_price: u64,
    pub data: Vec<u8>,
    pub received_at: Instant,
}

impl TransactionPool {
    pub fn new(config: TxPoolConfig) -> Self {
        Self {
            config,
            pending: BTreeMap::new(),
            by_gas_price: BTreeMap::new(),
            by_hash: HashMap::new(),
            known: HashSet::new(),
        }
    }

    /// 添加交易到池
    pub fn add(&mut self, tx: PoolTransaction) -> Result<(), PoolError> {
        if tx.gas_price < self.config.min_gas_price {
            return Err(PoolError::Underpriced);
        }

        if !self.seen_messages.insert(id) {
            return id;
        }

        // 缓存消息
        self.message_cache.insert(id, CachedMessage {
            data: data.clone(),
            topic: topic.to_string(),
            received_at: Instant::now(),
            hops: 0,
        });

        // 清理过期消息
        self.prune_cache();

        // 选择fanout个随机邻居传播
        let targets: Vec<_> = self.select_random_neighbors(self.config.fanout);
        for target in targets {
            self.send_to_peer(target, &data);
        }

        id
    }

    /// 接收 gossip 消息
    pub fn on_message(&mut self, from: NodeId, data: Vec<u8>, hops: u8) -> Option<Vec<u8>> {
        let id = self.compute_message_id(&data);

        // 检查是否已见
        if !self.seen_messages.insert(id) {
            return None; // 重复消息
        }

        // 缓存
        self.message_cache.insert(id, CachedMessage {
            data: data.clone(),
            topic: String::new(),
            received_at: Instant::now(),
            hops,
        });

        // 继续传播（除了发送者）
        if hops < 10 { // 最大跳数限制
            let targets: Vec<_> = self.neighbors
                .iter()
                .filter(|&&n| n != from)
                .take(self.config.fanout)
                .cloned()
                .collect();

            for target in targets {
                self.send_to_peer(target, &data);
            }
        }

        Some(data)
    }

    /// 周期性心跳
    pub fn heartbeat(&mut self) {
        // 向随机邻居请求新消息
        let targets = self.select_random_neighbors(3);
        for target in targets {
            self.send_ihave(target);
        }
    }

    /// 处理邻居的ihave消息
    pub fn on_ihave(&mut self, from: NodeId, message_ids: Vec<MessageId>) {
        let missing: Vec<_> = message_ids
            .into_iter()
            .filter(|id| !self.seen_messages.contains(id))
            .collect();

        if !missing.is_empty() {
            self.request_messages(from, missing);
        }
    }

    fn compute_message_id(&self, data: &[u8]) -> MessageId {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(data);
        let result = hasher.finalize();
        let mut id = [0u8; 32];
        id.copy_from_slice(&result);
        id
    }

    fn select_random_neighbors(&self, count: usize) -> Vec<NodeId> {
        use rand::seq::IteratorRandom;
        let mut rng = rand::thread_rng();
        self.neighbors.iter()
            .cloned()
            .choose_multiple(&mut rng, count)
    }

    fn prune_cache(&mut self) {
        let now = Instant::now();
        let expired: Vec<_> = self.message_cache
            .iter()
            .filter(|(_, msg)| now.duration_since(msg.received_at) > self.config.ttl)
            .map(|(id, _)| *id)
            .collect();

        for id in expired {
            self.message_cache.remove(&id);
            self.seen_messages.remove(&id);
        }
    }

    fn send_to_peer(&self, _target: NodeId, _data: &[u8]) {
        // 实际网络发送
    }

    fn send_ihave(&self, _target: NodeId) {
        // 发送消息ID列表
    }

    fn request_messages(&self, _target: NodeId, _ids: Vec<MessageId>) {
        // 请求缺失的消息
    }
}

/// Plumtree - 优化的gossip协议
pub struct Plumtree {
    eager_push_peers: HashSet<NodeId>,
    lazy_push_peers: HashSet<NodeId>,
    pending_acks: HashMap<MessageId, HashSet<NodeId>>,
}

impl Plumtree {
    /// 优化的广播：优先使用eager push，失败后转为lazy push
    pub fn optimized_broadcast(&mut self, data: Vec<u8>) {
        let id = self.compute_message_id(&data);

        // 向所有eager peers发送
        for peer in &self.eager_push_peers {
            self.send_eager(*peer, data.clone());
        }

        // 记录待确认
        self.pending_acks.insert(id, self.eager_push_peers.clone());
    }

    fn compute_message_id(&self, data: &[u8]) -> MessageId {
        // 实现...
        [0; 32]
    }

    fn send_eager(&self, _peer: NodeId, _data: Vec<u8>) {
        // 发送数据
    }
}
```

---

## 6. 存储层

### 6.1 LevelDB/RocksDB集成

```rust
use rocksdb::{DB, Options, ColumnFamilyDescriptor, WriteBatch};
use std::sync::Arc;

/// 区块链数据库
pub struct BlockchainDB {
    db: Arc<DB>,
}

/// 列族定义
pub mod columns {
    pub const BLOCKS: &str = "blocks";
    pub const HEADERS: &str = "headers";
    pub const TRANSACTIONS: &str = "transactions";
    pub const STATE: &str = "state";
    pub const RECEIPTS: &str = "receipts";
    pub const METADATA: &str = "metadata";
    pub const TX_INDEX: &str = "tx_index";
}

impl BlockchainDB {
    pub fn open(path: &str) -> Result<Self, DatabaseError> {
        let mut opts = Options::default();
        opts.create_if_missing(true);
        opts.create_missing_column_families(true);

        // 性能优化配置
        opts.set_write_buffer_size(64 * 1024 * 1024); // 64MB
        opts.set_max_write_buffer_number(3);
        opts.set_target_file_size_base(64 * 1024 * 1024);
        opts.set_level_zero_file_num_compaction_trigger(4);
        opts.set_compression_type(rocksdb::DBCompressionType::Lz4);

        let cf_names = vec![
            columns::BLOCKS,
            columns::HEADERS,
            columns::TRANSACTIONS,
            columns::STATE,
            columns::RECEIPTS,
            columns::METADATA,
            columns::TX_INDEX,
        ];

        let cf_descriptors: Vec<_> = cf_names
            .iter()
            .map(|name| ColumnFamilyDescriptor::new(*name, Options::default()))
            .collect();

        let db = DB::open_cf_descriptors(&opts, path, cf_descriptors)
            .map_err(|e| DatabaseError::OpenFailed(e.to_string()))?;

        Ok(Self { db: Arc::new(db) })
    }

    /// 存储区块
    pub fn put_block(&self, block: &Block) -> Result<(), DatabaseError> {
        let hash = block.hash();
        let number = block.number();

        // 序列化区块
        let block_data = bincode::serialize(block)
            .map_err(|e| DatabaseError::SerializationError(e.to_string()))?;

        // 存储到 blocks CF
        let blocks_cf = self.db.cf_handle(columns::BLOCKS)
            .ok_or(DatabaseError::ColumnFamilyNotFound)?;
        self.db.put_cf(&blocks_cf, hash, &block_data)
            .map_err(|e| DatabaseError::WriteError(e.to_string()))?;

        // 存储区块号到哈希的映射
        let metadata_cf = self.db.cf_handle(columns::METADATA)
            .ok_or(DatabaseError::ColumnFamilyNotFound)?;
        self.db.put_cf(&metadata_cf,
            format!("block_number:{}", number),
            hash
        ).map_err(|e| DatabaseError::WriteError(e.to_string()))?;

        Ok(())
    }

    /// 获取区块
    pub fn get_block(&self, hash: &[u8; 32]) -> Result<Option<Block>, DatabaseError> {
        let cf = self.db.cf_handle(columns::BLOCKS)
            .ok_or(DatabaseError::ColumnFamilyNotFound)?;

        match self.db.get_cf(&cf, hash) {
            Ok(Some(data)) => {
                let block: Block = bincode::deserialize(&data)
                    .map_err(|e| DatabaseError::DeserializationError(e.to_string()))?;
                Ok(Some(block))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(DatabaseError::ReadError(e.to_string())),
        }
    }
}

#[derive(Debug)]
pub enum DatabaseError {
    OpenFailed(String),
    ColumnFamilyNotFound,
    WriteError(String),
    ReadError(String),
    SerializationError(String),
    DeserializationError(String),
}

#[derive(Serialize, Deserialize)]
pub struct Block {
    pub header: Header,
    pub transactions: Vec<Transaction>,
}

impl Block {
    pub fn hash(&self) -> [u8; 32] {
        // 实现...
        [0; 32]
    }

    pub fn number(&self) -> u64 {
        self.header.number
    }
}

#[derive(Serialize, Deserialize)]
pub struct Header {
    pub number: u64,
    pub parent_hash: [u8; 32],
    pub state_root: [u8; 32],
    pub timestamp: u64,
}
```

### 6.2 状态数据库

```rust
/// 状态数据库 - 维护账户状态
pub struct StateDB {
    /// 底层KV存储
    db: Arc<BlockchainDB>,
    /// 状态缓存
    cache: StateCache,
    /// 当前state root
    state_root: [u8; 32],
}

/// 状态缓存
pub struct StateCache {
    accounts: lru::LruCache<Address, Account>,
    storage: lru::LruCache<(Address, H256), H256>,
}

impl StateDB {
    pub fn new(db: Arc<BlockchainDB>, state_root: [u8; 32]) -> Self {
        Self {
            db,
            cache: StateCache {
                accounts: lru::LruCache::new(10000),
                storage: lru::LruCache::new(100000),
            },
            state_root,
        }
    }

    /// 获取账户
    pub fn get_account(&mut self, address: &Address) -> Result<Account, StateError> {
        // 先查缓存
        if let Some(acc) = self.cache.accounts.get(address) {
            return Ok(acc.clone());
        }

        // 从数据库加载
        let key = self.account_key(address);
        match self.db.get_state(&key)? {
            Some(data) => {
                let account: Account = bincode::deserialize(&data)?;
                self.cache.accounts.put(*address, account.clone());
                Ok(account)
            }
            None => Ok(Account::default()),
        }
    }

    /// 更新账户
    pub fn set_account(&mut self, address: &Address, account: &Account) -> Result<(), StateError> {
        let key = self.account_key(address);
        let data = bincode::serialize(account)?;
        self.db.put_state(&key, &data)?;
        self.cache.accounts.put(*address, account.clone());
        Ok(())
    }
}

/// 快照管理
pub struct SnapshotManager {
    db: Arc<BlockchainDB>,
    snapshot_dir: String,
}

impl SnapshotManager {
    /// 创建状态快照
    pub fn create_snapshot(&self, at_block: u64) -> Result<String, StateError> {
        let snapshot_path = format!("{}/snapshot_{}", self.snapshot_dir, at_block);

        // 复制状态数据
        let checkpoint = rocksdb::checkpoint::Checkpoint::new(&self.db.db)?;
        checkpoint.create_checkpoint(&snapshot_path)?;

        // 创建元数据文件
        let meta = SnapshotMeta {
            block_number: at_block,
            state_root: self.compute_root_at(at_block)?,
            timestamp: std::time::SystemTime::now(),
        };

        let meta_path = format!("{}/meta.json", snapshot_path);
        std::fs::write(&meta_path, serde_json::to_string(&meta)?)?;

        Ok(snapshot_path)
    }

    fn compute_root_at(&self, _block: u64) -> Result<[u8; 32], StateError> {
        Ok([0; 32])
    }
}

#[derive(Serialize, Deserialize)]
struct SnapshotMeta {
    block_number: u64,
    state_root: [u8; 32],
    timestamp: std::time::SystemTime,
}
```

### 6.3 归档节点

```rust
/// 归档节点配置
pub struct ArchiveConfig {
    /// 保留完整历史
    pub keep_full_history: bool,
    /// 状态修剪间隔
    pub prune_interval: u64,
    /// 冷存储阈值（区块数）
    pub cold_storage_threshold: u64,
    /// 冷存储路径
    pub cold_storage_path: String,
}

/// 归档节点管理器
pub struct ArchiveManager {
    hot_db: Arc<BlockchainDB>,
    cold_db: Option<Arc<BlockchainDB>>,
    config: ArchiveConfig,
    current_height: u64,
}

impl ArchiveManager {
    pub fn new(
        hot_db: Arc<BlockchainDB>,
        cold_db: Option<Arc<BlockchainDB>>,
        config: ArchiveConfig,
    ) -> Self {
        Self {
            hot_db,
            cold_db,
            config,
            current_height: 0,
        }
    }

    /// 存储新区块
    pub fn store_block(&mut self, block: &Block) -> Result<(), ArchiveError> {
        let height = block.number();

        // 总是存入热存储
        self.hot_db.put_block(block)?;

        // 归档策略
        if !self.config.keep_full_history {
            self.apply_pruning_strategy(height)?;
        }

        // 冷存储归档
        if let Some(ref cold) = self.cold_db {
            if height >= self.config.cold_storage_threshold {
                if height % self.config.cold_storage_threshold == 0 {
                    self.archive_to_cold_storage(block, cold)?;
                }
            }
        }

        self.current_height = height;
        Ok(())
    }

    /// 获取历史区块
    pub fn get_historical_block(&self, height: u64) -> Result<Option<Block>, ArchiveError> {
        // 先查热存储
        if let Some(block) = self.hot_db.get_block_by_number(height)? {
            return Ok(Some(block));
        }

        // 查冷存储
        if let Some(ref cold) = self.cold_db {
            return cold.get_block_by_number(height).map_err(|e| e.into());
        }

        Ok(None)
    }

    /// 应用修剪策略
    fn apply_pruning_strategy(&self, current_height: u64) -> Result<(), ArchiveError> {
        // 修剪老状态
        if current_height % self.config.prune_interval == 0 {
            let prune_height = current_height.saturating_sub(10000);
            self.prune_old_states(prune_height)?;
        }

        Ok(())
    }

    fn prune_old_states(&self, _before_height: u64) -> Result<(), ArchiveError> {
        // 实现状态修剪逻辑
        Ok(())
    }

    /// 归档到冷存储
    fn archive_to_cold_storage(
        &self,
        block: &Block,
        cold: &Arc<BlockchainDB>,
    ) -> Result<(), ArchiveError> {
        cold.put_block(block)?;
        Ok(())
    }

    /// 导出历史数据
    pub fn export_range(&self, start: u64, end: u64, output_path: &str) -> Result<(), ArchiveError> {
        let file = std::fs::File::create(output_path)?;
        let mut writer = std::io::BufWriter::new(file);

        for height in start..=end {
            if let Some(block) = self.get_historical_block(height)? {
                let json = serde_json::to_string(&block)?;
                writeln!(writer, "{}", json)?;
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
pub enum ArchiveError {
    DatabaseError(DatabaseError),
    IOError(std::io::Error),
    SerializationError(serde_json::Error),
}

impl From<DatabaseError> for ArchiveError {
    fn from(e: DatabaseError) -> Self {
        ArchiveError::DatabaseError(e)
    }
}

impl From<std::io::Error> for ArchiveError {
    fn from(e: std::io::Error) -> Self {
        ArchiveError::IOError(e)
    }
}

impl From<serde_json::Error> for ArchiveError {
    fn from(e: serde_json::Error) -> Self {
        ArchiveError::SerializationError(e)
    }
}
```

---

## 7. 完整示例：简化的区块链实现

### 7.1 区块结构

```rust
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};
use std::time::{SystemTime, UNIX_EPOCH};

/// 完整区块
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SimpleBlock {
    pub header: BlockHeader,
    pub transactions: Vec<SimpleTransaction>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BlockHeader {
    pub version: u32,
    pub prev_hash: [u8; 32],
    pub merkle_root: [u8; 32],
    pub timestamp: u64,
    pub difficulty: u32,
    pub nonce: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SimpleTransaction {
    pub from: [u8; 20],
    pub to: [u8; 20],
    pub amount: u64,
    pub fee: u64,
    pub nonce: u64,
    pub signature: Vec<u8>,
}

impl SimpleBlock {
    /// 创建创世区块
    pub fn genesis() -> Self {
        let header = BlockHeader {
            version: 1,
            prev_hash: [0; 32],
            merkle_root: [0; 32],
            timestamp: 0,
            difficulty: 0x1d00ffff,
            nonce: 0,
        };

        Self {
            header,
            transactions: vec![],
        }
    }

    /// 计算区块哈希
    pub fn hash(&self) -> [u8; 32] {
        let header_bytes = bincode::serialize(&self.header).unwrap();
        let mut hasher = Sha256::new();
        hasher.update(&header_bytes);
        let first = hasher.finalize();

        let mut hasher = Sha256::new();
        hasher.update(&first);
        hasher.finalize().into()
    }

    /// 计算Merkle根
    fn calculate_merkle_root(transactions: &[SimpleTransaction]) -> [u8; 32] {
        if transactions.is_empty() {
            return [0; 32];
        }

        let mut hashes: Vec<[u8; 32]> = transactions
            .iter()
            .map(|tx| {
                let tx_bytes = bincode::serialize(tx).unwrap();
                let mut hasher = Sha256::new();
                hasher.update(&tx_bytes);
                hasher.finalize().into()
            })
            .collect();

        while hashes.len() > 1 {
            let mut next_level = Vec::new();

            for i in (0..hashes.len()).step_by(2) {
                let left = hashes[i];
                let right = if i + 1 < hashes.len() { hashes[i + 1] } else { left };

                let mut hasher = Sha256::new();
                hasher.update(&left);
                hasher.update(&right);
                next_level.push(hasher.finalize().into());
            }

            hashes = next_level;
        }

        hashes[0]
    }

    /// 创建新区块
    pub fn new(
        prev_hash: [u8; 32],
        transactions: Vec<SimpleTransaction>,
        difficulty: u32,
    ) -> Self {
        let merkle_root = Self::calculate_merkle_root(&transactions);

        Self {
            header: BlockHeader {
                version: 1,
                prev_hash,
                merkle_root,
                timestamp: current_timestamp(),
                difficulty,
                nonce: 0,
            },
            transactions,
        }
    }

    /// 设置nonce（挖矿用）
    pub fn set_nonce(&mut self, nonce: u64) {
        self.header.nonce = nonce;
    }
}

fn current_timestamp() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}
```

### 7.2 挖矿算法

```rust
use rayon::prelude::*;

/// 挖矿管理器
pub struct Miner {
    target: [u8; 32],
}

impl Miner {
    /// 从难度值计算目标哈希
    pub fn new(difficulty: u32) -> Self {
        let target = Self::difficulty_to_target(difficulty);
        Self { target }
    }

    /// 难度压缩格式转目标
    fn difficulty_to_target(difficulty: u32) -> [u8; 32] {
        let exp = (difficulty >> 24) as usize;
        let mantissa = difficulty & 0x007fffff;

        let mut target = [0u8; 32];
        target[exp - 3] = (mantissa >> 16) as u8;
        target[exp - 2] = ((mantissa >> 8) & 0xff) as u8;
        target[exp - 1] = (mantissa & 0xff) as u8;

        target
    }

    /// 验证哈希是否满足难度
    fn hash_meets_target(hash: &[u8; 32], target: &[u8; 32]) -> bool {
        // 大端比较
        for i in 0..32 {
            if hash[31 - i] < target[31 - i] {
                return true;
            }
            if hash[31 - i] > target[31 - i] {
                return false;
            }
        }
        true
    }

    /// 串行挖矿
    pub fn mine_serial(&self, block: &mut SimpleBlock) -> bool {
        let mut nonce: u64 = 0;

        loop {
            block.set_nonce(nonce);
            let hash = block.hash();

            if Self::hash_meets_target(&hash, &self.target) {
                return true;
            }

            nonce += 1;

            // 定期更新timestamp
            if nonce % 1000000 == 0 {
                block.header.timestamp = current_timestamp();
            }
        }
    }

    /// 并行挖矿（使用多核）
    pub fn mine_parallel(&self, block: &SimpleBlock, threads: usize) -> Option<u64> {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Arc;

        let found = Arc::new(AtomicBool::new(false));
        let batch_size = 100000u64;

        // 为每个线程分配搜索范围
        let result: Option<u64> = (0..threads)
            .into_par_iter()
            .find_map_any(|thread_id| {
                let mut local_block = block.clone();
                let found = Arc::clone(&found);
                let target = self.target;

                let start_nonce = thread_id as u64 * batch_size;

                for batch in 0.. {
                    if found.load(Ordering::Relaxed) {
                        return None;
                    }

                    let batch_start = start_nonce + batch * batch_size * threads as u64;

                    for offset in 0..batch_size {
                        let nonce = batch_start + offset;
                        local_block.set_nonce(nonce);
                        let hash = local_block.hash();

                        if Self::hash_meets_target(&hash, &target) {
                            found.store(true, Ordering::Relaxed);
                            return Some(nonce);
                        }
                    }
                }

                None
            });

        result
    }

    /// 验证区块
    pub fn verify(&self, block: &SimpleBlock) -> bool {
        // 验证难度
        let expected_target = Self::difficulty_to_target(block.header.difficulty);

        // 验证Merkle根
        if block.header.merkle_root != SimpleBlock::calculate_merkle_root(&block.transactions) {
            return false;
        }

        // 验证哈希
        let hash = block.hash();
        Self::hash_meets_target(&hash, &expected_target)
    }
}
```

### 7.3 交易验证

```rust
use secp256k1::{Secp256k1, Message, PublicKey, ecdsa::Signature};
use std::collections::HashMap;

/// 交易验证器
pub struct TransactionValidator {
    secp: Secp256k1<secp256k1::All>,
    /// 已知的账户nonce
    account_nonces: HashMap<[u8; 20], u64>,
    /// 账户余额
    balances: HashMap<[u8; 20], u64>,
}

impl TransactionValidator {
    pub fn new() -> Self {
        Self {
            secp: Secp256k1::new(),
            account_nonces: HashMap::new(),
            balances: HashMap::new(),
        }
    }

    /// 完整验证交易
    pub fn validate(&self, tx: &SimpleTransaction) -> Result<(), ValidationError> {
        // 1. 验证格式
        self.validate_format(tx)?;

        // 2. 验证签名
        self.validate_signature(tx)?;

        // 3. 验证nonce
        self.validate_nonce(tx)?;

        // 4. 验证余额
        self.validate_balance(tx)?;

        Ok(())
    }

    fn validate_format(&self, tx: &SimpleTransaction) -> Result<(), ValidationError> {
        // 地址长度检查
        if tx.from.len() != 20 || tx.to.len() != 20 {
            return Err(ValidationError::InvalidAddress);
        }

        // 金额检查
        if tx.amount == 0 {
            return Err(ValidationError::ZeroAmount);
        }

        // 签名存在性检查
        if tx.signature.is_empty() {
            return Err(ValidationError::MissingSignature);
        }

        Ok(())
    }

    fn validate_signature(&self, tx: &SimpleTransaction) -> Result<(), ValidationError> {
        // 构造签名消息
        let message = self.tx_hash_for_sign(tx);
        let msg = Message::from_slice(&message)
            .map_err(|_| ValidationError::InvalidMessage)?;

        // 解析签名
        let _sig = Signature::from_compact(&tx.signature)
            .map_err(|_| ValidationError::InvalidSignature)?;

        // 实际实现需要存储公钥或使用恢复ID
        Ok(())
    }

    fn validate_nonce(&self, tx: &SimpleTransaction) -> Result<(), ValidationError> {
        let expected_nonce = self.account_nonces.get(&tx.from).copied().unwrap_or(0);

        if tx.nonce < expected_nonce {
            return Err(ValidationError::NonceTooLow);
        }

        if tx.nonce > expected_nonce {
            return Err(ValidationError::NonceTooHigh);
        }

        Ok(())
    }

    fn validate_balance(&self, tx: &SimpleTransaction) -> Result<(), ValidationError> {
        let balance = self.balances.get(&tx.from).copied().unwrap_or(0);
        let required = tx.amount + tx.fee;

        if balance < required {
            return Err(ValidationError::InsufficientBalance);
        }

        Ok(())
    }

    /// 用于签名的交易哈希
    fn tx_hash_for_sign(&self, tx: &SimpleTransaction) -> [u8; 32] {
        let mut data = Vec::new();
        data.extend_from_slice(&tx.from);
        data.extend_from_slice(&tx.to);
        data.extend_from_slice(&tx.amount.to_le_bytes());
        data.extend_from_slice(&tx.fee.to_le_bytes());
        data.extend_from_slice(&tx.nonce.to_le_bytes());

        let mut hasher = Sha256::new();
        hasher.update(&data);
        hasher.finalize().into()
    }

    /// 执行交易并更新状态
    pub fn execute(&mut self, tx: &SimpleTransaction) -> Result<Receipt, ValidationError> {
        self.validate(tx)?;

        // 扣除发送方余额
        let from_balance = self.balances.entry(tx.from).or_insert(0);
        *from_balance -= tx.amount + tx.fee;

        // 增加接收方余额
        let to_balance = self.balances.entry(tx.to).or_insert(0);
        *to_balance += tx.amount;

        // 增加nonce
        let nonce = self.account_nonces.entry(tx.from).or_insert(0);
        *nonce += 1;

        Ok(Receipt {
            success: true,
            gas_used: tx.fee,
        })
    }
}

#[derive(Debug)]
pub enum ValidationError {
    InvalidAddress,
    ZeroAmount,
    MissingSignature,
    InvalidSignature,
    InvalidMessage,
    NonceTooLow,
    NonceTooHigh,
    InsufficientBalance,
}

pub struct Receipt {
    pub success: bool,
    pub gas_used: u64,
}
```

### 7.4 网络同步

```rust
use tokio::sync::{mpsc, RwLock};
use std::sync::Arc;

/// 区块链节点
pub struct BlockchainNode {
    /// 本地区块链
    chain: Arc<RwLock<Vec<SimpleBlock>>>,
    /// 交易池
    tx_pool: Arc<RwLock<Vec<SimpleTransaction>>>,
    /// 网络层
    network: BlockchainNetwork,
    /// 是否正在同步
    syncing: Arc<RwLock<bool>>,
    /// 事件通道
    event_sender: mpsc::Sender<NodeEvent>,
}

#[derive(Debug, Clone)]
pub enum NodeEvent {
    BlockMined(u64),
    NewTransaction([u8; 32]),
    SyncProgress(u64, u64),
    PeerConnected(String),
}

impl BlockchainNode {
    pub async fn new(
        network: BlockchainNetwork,
        event_sender: mpsc::Sender<NodeEvent>,
    ) -> Self {
        let genesis = SimpleBlock::genesis();

        Self {
            chain: Arc::new(RwLock::new(vec![genesis])),
            tx_pool: Arc::new(RwLock::new(vec![])),
            network,
            syncing: Arc::new(RwLock::new(false)),
            event_sender,
        }
    }

    /// 开始运行节点
    pub async fn run(&self) {
        // 1. 首先同步区块链
        self.sync_chain().await;

        // 2. 启动矿工（如果需要）
        tokio::spawn(self.miner_loop());

        // 3. 处理网络事件
        self.network_event_loop().await;
    }

    /// 区块链同步
    async fn sync_chain(&self) {
        let mut syncing = self.syncing.write().await;
        *syncing = true;
        drop(syncing);

        // 获取最佳peer的高度
        let best_height = self.get_best_peer_height().await;
        let current_height = self.get_local_height().await;

        if best_height > current_height {
            // 批量请求缺失的区块
            for height in (current_height + 1)..=best_height {
                self.request_block(height).await;

                self.event_sender
                    .send(NodeEvent::SyncProgress(height, best_height))
                    .await
                    .unwrap();
            }
        }

        let mut syncing = self.syncing.write().await;
        *syncing = false;
    }

    /// 处理网络事件循环
    async fn network_event_loop(&self) {
        loop {
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            // 处理新交易、新区块等
        }
    }

    /// 矿工循环
    async fn miner_loop(&self) {
        let miner = Miner::new(0x1d00ffff);

        loop {
            // 收集待打包交易
            let txs = {
                let pool = self.tx_pool.read().await;
                pool.clone()
            };

            // 获取前一个区块哈希
            let prev_hash = {
                let chain = self.chain.read().await;
                chain.last().unwrap().hash()
            };

            // 创建新区块
            let mut block = SimpleBlock::new(prev_hash, txs, 0x1d00ffff);

            // 挖矿
            println!("Mining block...");
            if miner.mine_serial(&mut block) {
                println!("Block mined! Nonce: {}", block.header.nonce);

                // 验证并添加区块
                self.add_block(block.clone()).await;

                // 广播区块
                self.broadcast_block(&block).await;

                // 清空交易池
                {
                    let mut pool = self.tx_pool.write().await;
                    pool.clear();
                }

                self.event_sender
                    .send(NodeEvent::BlockMined(block.hash().into()))
                    .await
                    .unwrap();
            }
        }
    }

    /// 添加新区块
    async fn add_block(&self, block: SimpleBlock) -> Result<(), BlockError> {
        let mut chain = self.chain.write().await;

        // 验证区块连接
        let last_block = chain.last().ok_or(BlockError::EmptyChain)?;
        if block.header.prev_hash != last_block.hash() {
            return Err(BlockError::InvalidPrevHash);
        }

        // 验证工作量证明
        let miner = Miner::new(block.header.difficulty);
        if !miner.verify(&block) {
            return Err(BlockError::InvalidProof);
        }

        // 添加区块
        chain.push(block);

        Ok(())
    }

    /// 广播区块
    async fn broadcast_block(&self, block: &SimpleBlock) {
        let data = bincode::serialize(block).unwrap();
        // 通过network广播
    }

    /// 处理收到的交易
    pub async fn on_new_transaction(&self, tx: SimpleTransaction) {
        // 验证交易
        let validator = TransactionValidator::new();
        if validator.validate(&tx).is_ok() {
            let mut pool = self.tx_pool.write().await;
            pool.push(tx);
        }
    }

    /// 处理收到的区块
    pub async fn on_new_block(&self, block: SimpleBlock) -> Result<(), BlockError> {
        // 检查是否需要同步
        let is_syncing = *self.syncing.read().await;

        if is_syncing {
            // 简单添加，假设顺序正确
            let mut chain = self.chain.write().await;
            chain.push(block);
        } else {
            // 正常验证流程
            self.add_block(block).await?;
        }

        Ok(())
    }

    async fn get_best_peer_height(&self) -> u64 {
        // 查询所有peer获取最高高度
        0
    }

    async fn get_local_height(&self) -> u64 {
        let chain = self.chain.read().await;
        (chain.len() as u64).saturating_sub(1)
    }

    async fn request_block(&self, _height: u64) {
        // 向peer请求特定区块
    }
}

#[derive(Debug)]
pub enum BlockError {
    EmptyChain,
    InvalidPrevHash,
    InvalidProof,
}
```

---

## 8. DeFi开发

### 8.1 DEX核心逻辑

```rust
/// 自动做市商(AMM) - Uniswap V2风格
pub struct AMM {
    /// 储备金
    reserves: HashMap<TokenId, u128>,
    /// LP代币总供应量
    total_lp_supply: u128,
    /// 用户LP余额
    lp_balances: HashMap<Address, u128>,
    /// 交易费率 (0.3% = 30)
    fee_rate: u16,
    /// 精度基数 (10000 = 1%)
    fee_precision: u16,
}

pub type TokenId = [u8; 20];

impl AMM {
    const MINIMUM_LIQUIDITY: u128 = 1000;

    /// 添加流动性
    pub fn add_liquidity(
        &mut self,
        token_a: TokenId,
        amount_a: u128,
        token_b: TokenId,
        amount_b: u128,
        provider: Address,
    ) -> Result<u128, DeFiError> {
        // 计算LP代币数量
        let lp_tokens = if self.total_lp_supply == 0 {
            // 首次添加
            let liquidity = (amount_a * amount_b).sqrt() - Self::MINIMUM_LIQUIDITY;
            // 锁定最小流动性
            self.total_lp_supply = Self::MINIMUM_LIQUIDITY;
            liquidity
        } else {
            // 按比例计算
            let reserve_a = *self.reserves.get(&token_a).unwrap_or(&0);
            let reserve_b = *self.reserves.get(&token_b).unwrap_or(&0);

            let liquidity_a = amount_a * self.total_lp_supply / reserve_a;
            let liquidity_b = amount_b * self.total_lp_supply / reserve_b;

            liquidity_a.min(liquidity_b)
        };

        if lp_tokens == 0 {
            return Err(DeFiError::InsufficientLiquidityMinted);
        }

        // 更新储备金
        *self.reserves.entry(token_a).or_insert(0) += amount_a;
        *self.reserves.entry(token_b).or_insert(0) += amount_b;

        // 铸造LP代币
        self.total_lp_supply += lp_tokens;
        *self.lp_balances.entry(provider).or_insert(0) += lp_tokens;

        Ok(lp_tokens)
    }

    /// 移除流动性
    pub fn remove_liquidity(
        &mut self,
        lp_amount: u128,
        provider: Address,
    ) -> Result<(u128, u128), DeFiError> {
        let provider_balance = *self.lp_balances.get(&provider).unwrap_or(&0);
        if provider_balance < lp_amount {
            return Err(DeFiError::InsufficientBalance);
        }

        // 计算应得的代币数量
        let reserve_a = *self.reserves.values().nth(0).unwrap_or(&0);
        let reserve_b = *self.reserves.values().nth(1).unwrap_or(&0);

        let amount_a = lp_amount * reserve_a / self.total_lp_supply;
        let amount_b = lp_amount * reserve_b / self.total_lp_supply;

        // 销毁LP代币
        *self.lp_balances.get_mut(&provider).unwrap() -= lp_amount;
        self.total_lp_supply -= lp_amount;

        // 更新储备金
        let token_a = *self.reserves.keys().nth(0).unwrap();
        let token_b = *self.reserves.keys().nth(1).unwrap();
        *self.reserves.get_mut(&token_a).unwrap() -= amount_a;
        *self.reserves.get_mut(&token_b).unwrap() -= amount_b;

        Ok((amount_a, amount_b))
    }

    /// 交换代币（token_in -> token_out）
    pub fn swap(
        &mut self,
        token_in: TokenId,
        token_out: TokenId,
        amount_in: u128,
        min_amount_out: u128,
    ) -> Result<u128, DeFiError> {
        let reserve_in = *self.reserves.get(&token_in).ok_or(DeFiError::InvalidToken)?;
        let reserve_out = *self.reserves.get(&token_out).ok_or(DeFiError::InvalidToken)?;

        if reserve_in == 0 || reserve_out == 0 {
            return Err(DeFiError::InsufficientLiquidity);
        }

        // 计算输出数量（含手续费）
        let amount_in_with_fee = amount_in * (self.fee_precision - self.fee_rate) as u128;
        let numerator = amount_in_with_fee * reserve_out;
        let denominator = reserve_in * self.fee_precision as u128 + amount_in_with_fee;
        let amount_out = numerator / denominator;

        if amount_out < min_amount_out {
            return Err(DeFiError::SlippageExceeded);
        }

        // 更新储备金
        *self.reserves.get_mut(&token_in).unwrap() += amount_in;
        *self.reserves.get_mut(&token_out).unwrap() -= amount_out;

        // 维护k = x * y 不变量检查
        let new_reserve_in = *self.reserves.get(&token_in).unwrap();
        let new_reserve_out = *self.reserves.get(&token_out).unwrap();
        assert!(new_reserve_in * new_reserve_out >= reserve_in * reserve_out);

        Ok(amount_out)
    }

    /// 获取当前价格
    pub fn get_price(&self, base: TokenId, quote: TokenId) -> Option<u128> {
        let reserve_base = *self.reserves.get(&base)?;
        let reserve_quote = *self.reserves.get(&quote)?;

        if reserve_base == 0 {
            return None;
        }

        // price = reserve_quote / reserve_base
        Some(reserve_quote * 1e18 as u128 / reserve_base)
    }
}

/// 限价订单簿
pub struct OrderBook {
    /// 买单 (价格 -> 订单列表)
    bids: BTreeMap<u128, Vec<Order>>,
    /// 卖单 (价格 -> 订单列表)
    asks: BTreeMap<u128, Vec<Order>>,
    /// 用户订单
    user_orders: HashMap<Address, Vec<OrderId>>,
}

pub type OrderId = u64;

#[derive(Clone)]
pub struct Order {
    pub id: OrderId,
    pub trader: Address,
    pub side: Side,
    pub price: u128,
    pub amount: u128,
    pub filled: u128,
}

pub enum Side {
    Buy,
    Sell,
}

impl OrderBook {
    /// 提交订单
    pub fn place_order(&mut self, order: Order) -> Vec<Fill> {
        let mut fills = Vec::new();

        match order.side {
            Side::Buy => self.match_buy_order(&order, &mut fills),
            Side::Sell => self.match_sell_order(&order, &mut fills),
        }

        // 如果有剩余，加入订单簿
        if order.filled < order.amount {
            self.add_to_book(order);
        }

        fills
    }

    fn match_buy_order(&mut self, order: &Order, fills: &mut Vec<Fill>) {
        // 从最低卖价开始匹配
        for (price, asks) in self.asks.iter_mut() {
            if *price > order.price {
                break; // 价格不满足
            }

            // 匹配此价格的所有订单
            while let Some(mut ask) = asks.pop() {
                let fill_amount = (order.amount - order.filled).min(ask.amount - ask.filled);

                // 记录成交
                fills.push(Fill {
                    maker: ask.trader,
                    taker: order.trader,
                    price: *price,
                    amount: fill_amount,
                });

                ask.filled += fill_amount;

                if ask.filled < ask.amount {
                    asks.push(ask); // 未完全成交，放回
                    break;
                }
            }
        }
    }

    fn match_sell_order(&mut self, order: &Order, fills: &mut Vec<Fill>) {
        // 从最高买价开始匹配
        for (price, bids) in self.bids.iter_mut().rev() {
            if *price < order.price {
                break;
            }
            // 类似匹配逻辑...
        }
    }

    fn add_to_book(&mut self, order: Order) {
        match order.side {
            Side::Buy => {
                self.bids.entry(order.price).or_insert_with(Vec::new).push(order);
            }
            Side::Sell => {
                self.asks.entry(order.price).or_insert_with(Vec::new).push(order);
            }
        }
    }
}

pub struct Fill {
    pub maker: Address,
    pub taker: Address,
    pub price: u128,
    pub amount: u128,
}

#[derive(Debug)]
pub enum DeFiError {
    InsufficientLiquidity,
    InsufficientLiquidityMinted,
    InsufficientBalance,
    InvalidToken,
    SlippageExceeded,
}
```

### 8.2 借贷协议

```rust
/// 超额抵押借贷协议（Compound/Aave风格）
pub struct LendingProtocol {
    /// 支持的代币市场
    markets: HashMap<TokenId, Market>,
    /// 用户账户流动性
    accounts: HashMap<Address, Account>,
    /// 价格预言机
    oracle: Box<dyn PriceOracle>,
    /// 清算激励
    liquidation_incentive: u16,
    /// 清算阈值
    liquidation_threshold: u16,
}

pub struct Market {
    /// 代币地址
    pub token: TokenId,
    /// cToken总供应
    pub total_supply: u128,
    /// 总借款
    pub total_borrows: u128,
    /// 储备金
    pub reserves: u128,
    /// 供应指数
    pub supply_index: u128,
    /// 借款指数
    pub borrow_index: u128,
    /// 利率模型参数
    pub base_rate: u128,
    pub multiplier: u128,
}

pub struct Account {
    /// 存款余额（以cToken计）
    pub deposits: HashMap<TokenId, u128>,
    /// 借款余额（以本金计）
    pub borrows: HashMap<TokenId, u128>,
    /// 累计借款利息
    pub borrow_interest: HashMap<TokenId, u128>,
}

pub trait PriceOracle: Send + Sync {
    fn get_price(&self, token: &TokenId) -> Option<u128>;
}

impl LendingProtocol {
    /// 存款
    pub fn mint(&mut self, token: TokenId, amount: u128, user: Address) -> Result<u128, DeFiError> {
        let market = self.markets.get_mut(&token).ok_or(DeFiError::InvalidMarket)?;

        // 计算cToken数量
        let exchange_rate = self.exchange_rate(market);
        let ctoken_amount = amount * 1e18 as u128 / exchange_rate;

        // 更新市场
        market.total_supply += ctoken_amount;

        // 更新用户账户
        let account = self.accounts.entry(user).or_insert_with(Account::default);
        *account.deposits.entry(token).or_insert(0) += ctoken_amount;

        Ok(ctoken_amount)
    }

    /// 取款
    pub fn redeem(&mut self, token: TokenId, ctoken_amount: u128, user: Address) -> Result<u128, DeFiError> {
        let market = self.markets.get_mut(&token).ok_or(DeFiError::InvalidMarket)?;
        let account = self.accounts.get_mut(&user).ok_or(DeFiError::NoAccount)?;

        let deposit = account.deposits.get(&token).copied().unwrap_or(0);
        if deposit < ctoken_amount {
            return Err(DeFiError::InsufficientDeposit);
        }

        // 计算可取回的代币数量
        let exchange_rate = self.exchange_rate(market);
        let underlying_amount = ctoken_amount * exchange_rate / 1e18 as u128;

        // 检查流动性
        if !self.has_sufficient_liquidity(&user, token, underlying_amount)? {
            return Err(DeFiError::InsufficientLiquidity);
        }

        // 更新状态
        *account.deposits.get_mut(&token).unwrap() -= ctoken_amount;
        market.total_supply -= ctoken_amount;

        Ok(underlying_amount)
    }

    /// 借款
    pub fn borrow(&mut self, token: TokenId, amount: u128, user: Address) -> Result<(), DeFiError> {
        let market = self.markets.get_mut(&token).ok_or(DeFiError::InvalidMarket)?;

        // 检查流动性
        if !self.has_sufficient_liquidity(&user, token, 0)? {
            return Err(DeFiError::InsufficientCollateral);
        }

        // 计算可借额度
        let borrow_cap = self.calculate_borrow_cap(&user)?;
        let price = self.oracle.get_price(&token).ok_or(DeFiError::PriceUnavailable)?;
        let borrow_value = amount * price / 1e18 as u128;

        if borrow_value > borrow_cap {
            return Err(DeFiError::BorrowCapExceeded);
        }

        // 更新状态
        let account = self.accounts.entry(user).or_insert_with(Account::default);
        *account.borrows.entry(token).or_insert(0) += amount;
        market.total_borrows += amount;

        Ok(())
    }

    /// 还款
    pub fn repay(&mut self, token: TokenId, amount: u128, user: Address) -> Result<u128, DeFiError> {
        let market = self.markets.get_mut(&token).ok_or(DeFiError::InvalidMarket)?;
        let account = self.accounts.get_mut(&user).ok_or(DeFiError::NoAccount)?;

        let borrow_balance = self.borrow_balance(&token, account)?;
        let repay_amount = amount.min(borrow_balance);

        // 更新状态
        *account.borrows.get_mut(&token).unwrap() -= repay_amount;
        market.total_borrows -= repay_amount;

        Ok(repay_amount)
    }

    /// 清算
    pub fn liquidate(
        &mut self,
        borrower: Address,
        collateral_token: TokenId,
        debt_token: TokenId,
        repay_amount: u128,
        liquidator: Address,
    ) -> Result<u128, DeFiError> {
        // 检查借款人是否可清算
        if !self.is_liquidatable(&borrower)? {
            return Err(DeFiError::NotLiquidatable);
        }

        // 计算可获得的抵押品
        let collateral_amount = self.calculate_liquidation_reward(
            debt_token,
            collateral_token,
            repay_amount,
        )?;

        // 执行清算逻辑...

        Ok(collateral_amount)
    }

    /// 计算兑换率
    fn exchange_rate(&self, market: &Market) -> u128 {
        if market.total_supply == 0 {
            return 1e18 as u128; // 初始兑换率
        }

        let cash = self.get_cash(market);
        let borrows = market.total_borrows;
        let reserves = market.reserves;

        (cash + borrows - reserves) * 1e18 as u128 / market.total_supply
    }

    /// 检查账户流动性
    fn has_sufficient_liquidity(
        &self,
        user: &Address,
        _exclude_token: TokenId,
        _exclude_amount: u128,
    ) -> Result<bool, DeFiError> {
        let account = self.accounts.get(user).ok_or(DeFiError::NoAccount)?;

        let mut collateral_value = 0u128;
        let mut borrow_value = 0u128;

        // 计算抵押品价值
        for (token, deposit) in &account.deposits {
            let price = self.oracle.get_price(token).unwrap_or(0);
            let market = self.markets.get(token).ok_or(DeFiError::InvalidMarket)?;
            let exchange_rate = self.exchange_rate(market);
            collateral_value += *deposit * exchange_rate / 1e18 as u128 * price / 1e18 as u128;
        }

        // 计算借款价值
        for (token, borrow) in &account.borrows {
            let price = self.oracle.get_price(token).unwrap_or(0);
            borrow_value += *borrow * price / 1e18 as u128;
        }

        // 检查是否超额抵押
        Ok(collateral_value * self.liquidation_threshold as u128 / 100 >= borrow_value)
    }

    /// 检查是否可清算
    fn is_liquidatable(&self, user: &Address) -> Result<bool, DeFiError> {
        // 类似流动性检查，使用更低的阈值
        Ok(false)
    }

    fn get_cash(&self, _market: &Market) -> u128 {
        // 返回市场可用现金
        0
    }

    fn calculate_borrow_cap(&self, _user: &Address) -> Result<u128, DeFiError> {
        Ok(0)
    }

    fn borrow_balance(&self, _token: &TokenId, _account: &Account) -> Result<u128, DeFiError> {
        Ok(0)
    }

    fn calculate_liquidation_reward(
        &self,
        _debt_token: TokenId,
        _collateral_token: TokenId,
        _repay_amount: u128,
    ) -> Result<u128, DeFiError> {
        Ok(0)
    }
}

impl Default for Account {
    fn default() -> Self {
        Self {
            deposits: HashMap::new(),
            borrows: HashMap::new(),
            borrow_interest: HashMap::new(),
        }
    }
}

#[derive(Debug)]
pub enum LendingError {
    InvalidMarket,
    NoAccount,
    InsufficientDeposit,
    InsufficientLiquidity,
    InsufficientCollateral,
    BorrowCapExceeded,
    NotLiquidatable,
    PriceUnavailable,
}
```

### 8.3 流动性池

```rust
/// 多代币流动性池 - Balancer风格
pub struct WeightedPool {
    /// 池中的代币
    tokens: Vec<TokenId>,
    /// 各代币权重（总和为1）
    weights: Vec<u128>,
    /// 各代币余额
    balances: Vec<u128>,
    /// 兑换费率
    swap_fee: u128,
    /// 总供应量
    total_supply: u128,
    /// 用户余额
    balances_of: HashMap<Address, u128>,
}

impl WeightedPool {
    /// 初始化池
    pub fn new(
        tokens: Vec<TokenId>,
        weights: Vec<u128>,
        initial_balances: Vec<u128>,
    ) -> Result<Self, DeFiError> {
        if tokens.len() != weights.len() || tokens.len() != initial_balances.len() {
            return Err(DeFiError::InvalidParameters);
        }

        // 验证权重总和
        let total_weight: u128 = weights.iter().sum();
        if total_weight != 1e18 as u128 {
            return Err(DeFiError::InvalidWeights);
        }

        Ok(Self {
            tokens,
            weights,
            balances: initial_balances,
            swap_fee: 0, // 0.1% = 1e15
            total_supply: 0,
            balances_of: HashMap::new(),
        })
    }

    /// 恒定乘积公式：计算输出数量
    /// 公式: out = balance_out * (1 - (balance_in / (balance_in + amount_in))^(weight_in/weight_out))
    pub fn out_given_in(
        &self,
        token_in: usize,
        token_out: usize,
        amount_in: u128,
    ) -> Result<u128, DeFiError> {
        let balance_in = self.balances[token_in];
        let balance_out = self.balances[token_out];
        let weight_in = self.weights[token_in];
        let weight_out = self.weights[token_out];

        // 扣除手续费
        let amount_in_after_fee = amount_in * (1e18 as u128 - self.swap_fee) / 1e18 as u128;

        // 计算幂
        let power = weight_in * 1e18 as u128 / weight_out;
        let base = balance_in * 1e18 as u128 / (balance_in + amount_in_after_fee);

        // pow(base, power)
        let ratio = self.pow(base, power);

        let amount_out = balance_out * (1e18 as u128 - ratio) / 1e18 as u128;

        Ok(amount_out)
    }

    /// 简化幂运算（实际使用更精确的数学库）
    fn pow(&self, base: u128, exp: u128) -> u128 {
        // 使用泰勒展开或查找表
        // 简化实现
        base
    }

    /// 计算提供流动性可获得的池代币
    pub fn pool_tokens_out(
        &self,
        amounts_in: &[u128],
    ) -> Result<u128, DeFiError> {
        if self.total_supply == 0 {
            // 首次添加，使用几何平均
            let product: u128 = amounts_in.iter().product();
            let root = self.nth_root(product, amounts_in.len() as u32);
            return Ok(root);
        }

        // 按比例计算
        let mut pool_tokens = u128::MAX;
        for (i, amount) in amounts_in.iter().enumerate() {
            let token_amount = *amount * self.total_supply / self.balances[i];
            pool_tokens = pool_tokens.min(token_amount);
        }

        Ok(pool_tokens)
    }

    fn nth_root(&self, value: u128, n: u32) -> u128 {
        // 简化实现
        value
    }
}
```

---

## 9. 安全最佳实践

### 9.1 重入攻击防护

```rust
/// 重入攻击防护模式
pub struct ReentrancyGuard {
    locked: std::cell::RefCell<bool>,
}

impl ReentrancyGuard {
    pub fn new() -> Self {
        Self {
            locked: std::cell::RefCell::new(false),
        }
    }

    /// 检查锁状态
    fn non_reentrant<F, R>(&self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        if *self.locked.borrow() {
            panic!("ReentrancyGuard: reentrant call");
        }

        *self.locked.borrow_mut() = true;
        let result = f();
        *self.locked.borrow_mut() = false;

        result
    }
}

/// 安全的提款模式 - Checks-Effects-Interactions
pub struct SecureVault {
    balances: HashMap<Address, u128>,
    guard: ReentrancyGuard,
}

impl SecureVault {
    /// 安全提款实现
    pub fn withdraw(&mut self, user: Address, amount: u128) -> Result<(), SecurityError> {
        self.guard.non_reentrant(|| {
            // 1. CHECKS: 验证条件
            let balance = self.balances.get(&user).copied().unwrap_or(0);
            if balance < amount {
                return Err(SecurityError::InsufficientBalance);
            }

            // 2. EFFECTS: 先更新状态
            *self.balances.get_mut(&user).unwrap() -= amount;

            // 3. INTERACTIONS: 最后进行外部调用
            self.transfer_tokens(&user, amount)?;

            Ok(())
        })
    }

    fn transfer_tokens(&self, _to: &Address, _amount: u128) -> Result<(), SecurityError> {
        // 执行转账
        Ok(())
    }
}

/// 另一种防护：Pull over Push 模式
pub struct PullPayment {
    /// 待领取的支付
    pending_payments: HashMap<Address, u128>,
}

impl PullPayment {
    /// 存入待领取资金（不直接发送）
    pub fn deposit(&mut self, recipient: Address, amount: u128) {
        *self.pending_payments.entry(recipient).or_insert(0) += amount;
    }

    /// 用户主动提款
    pub fn withdraw(&mut self) -> Result<u128, SecurityError> {
        let caller = self.get_caller();
        let amount = self.pending_payments.get(&caller).copied().unwrap_or(0);

        if amount == 0 {
            return Err(SecurityError::NoPendingPayment);
        }

        // 先清零
        self.pending_payments.insert(caller, 0);

        // 再转账
        self.transfer(&caller, amount)?;

        Ok(amount)
    }

    fn get_caller(&self) -> Address {
        [0; 20]
    }

    fn transfer(&self, _to: &Address, _amount: u128) -> Result<(), SecurityError> {
        Ok(())
    }
}

#[derive(Debug)]
pub enum SecurityError {
    InsufficientBalance,
    ReentrantCall,
    NoPendingPayment,
}
```

### 9.2 整数溢出防护

```rust
use num_traits::{CheckedAdd, CheckedSub, CheckedMul, CheckedDiv};

/// 安全数学运算trait
pub trait SafeMath {
    fn safe_add(&self, other: Self) -> Option<Self> where Self: Sized;
    fn safe_sub(&self, other: Self) -> Option<Self> where Self: Sized;
    fn safe_mul(&self, other: Self) -> Option<Self> where Self: Sized;
    fn safe_div(&self, other: Self) -> Option<Self> where Self: Sized;
}

impl SafeMath for u128 {
    fn safe_add(&self, other: Self) -> Option<Self> {
        self.checked_add(other)
    }

    fn safe_sub(&self, other: Self) -> Option<Self> {
        self.checked_sub(other)
    }

    fn safe_mul(&self, other: Self) -> Option<Self> {
        self.checked_mul(other)
    }

    fn safe_div(&self, other: Self) -> Option<Self> {
        self.checked_div(other)
    }
}

/// 安全数学宏
#[macro_export]
macro_rules! safe_add {
    ($a:expr, $b:expr) => {
        $a.checked_add($b).ok_or(MathError::Overflow)
    };
}

#[macro_export]
macro_rules! safe_sub {
    ($a:expr, $b:expr) => {
        $a.checked_sub($b).ok_or(MathError::Underflow)
    };
}

/// 安全计算示例
pub struct SafeToken {
    total_supply: u128,
    balances: HashMap<Address, u128>,
}

impl SafeToken {
    /// 安全转账
    pub fn transfer(
        &mut self,
        from: Address,
        to: Address,
        amount: u128,
    ) -> Result<(), MathError> {
        let from_balance = self.balances.get(&from).copied().unwrap_or(0);
        let to_balance = self.balances.get(&to).copied().unwrap_or(0);

        // 使用checked运算
        let new_from_balance = from_balance
            .checked_sub(amount)
            .ok_or(MathError::InsufficientBalance)?;

        let new_to_balance = to_balance
            .checked_add(amount)
            .ok_or(MathError::Overflow)?;

        // 验证结果
        assert!(new_from_balance <= from_balance);
        assert!(new_to_balance >= to_balance);

        self.balances.insert(from, new_from_balance);
        self.balances.insert(to, new_to_balance);

        Ok(())
    }

    /// 安全铸造
    pub fn mint(&mut self, to: Address, amount: u128) -> Result<(), MathError> {
        let new_supply = self.total_supply
            .checked_add(amount)
            .ok_or(MathError::Overflow)?;

        let new_balance = self.balances
            .get(&to)
            .copied()
            .unwrap_or(0)
            .checked_add(amount)
            .ok_or(MathError::Overflow)?;

        self.total_supply = new_supply;
        self.balances.insert(to, new_balance);

        Ok(())
    }

    /// 安全销毁
    pub fn burn(&mut self, from: Address, amount: u128) -> Result<(), MathError> {
        let balance = self.balances.get(&from).copied().unwrap_or(0);

        let new_balance = balance
            .checked_sub(amount)
            .ok_or(MathError::InsufficientBalance)?;

        let new_supply = self.total_supply
            .checked_sub(amount)
            .ok_or(MathError::Underflow)?;

        self.balances.insert(from, new_balance);
        self.total_supply = new_supply;

        Ok(())
    }
}

#[derive(Debug)]
pub enum MathError {
    Overflow,
    Underflow,
    DivisionByZero,
    InsufficientBalance,
}
```

### 9.3 访问控制

```rust
use std::collections::HashSet;

/// 基于角色的访问控制
pub struct AccessControl {
    /// 超级管理员
    admin: Address,
    /// 角色到账户的映射
    roles: HashMap<Role, HashSet<Address>>,
    /// 账户到角色的映射
    member_roles: HashMap<Address, HashSet<Role>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Role {
    Admin,
    Minter,
    Burner,
    Pauser,
    Upgrader,
}

impl AccessControl {
    pub fn new(admin: Address) -> Self {
        let mut roles = HashMap::new();
        let mut admins = HashSet::new();
        admins.insert(admin);
        roles.insert(Role::Admin, admins);

        let mut member_roles = HashMap::new();
        let mut admin_roles = HashSet::new();
        admin_roles.insert(Role::Admin);
        member_roles.insert(admin, admin_roles);

        Self {
            admin,
            roles,
            member_roles,
        }
    }

    /// 检查是否有角色
    pub fn has_role(&self, role: Role, account: Address) -> bool {
        self.roles
            .get(&role)
            .map(|members| members.contains(&account))
            .unwrap_or(false)
    }

    /// 授予角色（仅admin可调用）
    pub fn grant_role(
        &mut self,
        caller: Address,
        role: Role,
        account: Address,
    ) -> Result<(), AccessError> {
        self.require_role(caller, Role::Admin)?;

        self.roles
            .entry(role)
            .or_insert_with(HashSet::new)
            .insert(account);

        self.member_roles
            .entry(account)
            .or_insert_with(HashSet::new)
            .insert(role);

        Ok(())
    }

    /// 撤销角色
    pub fn revoke_role(
        &mut self,
        caller: Address,
        role: Role,
        account: Address,
    ) -> Result<(), AccessError> {
        self.require_role(caller, Role::Admin)?;

        if let Some(members) = self.roles.get_mut(&role) {
            members.remove(&account);
        }

        if let Some(roles) = self.member_roles.get_mut(&account) {
            roles.remove(&role);
        }

        Ok(())
    }

    /// 放弃角色（自己放弃）
    pub fn renounce_role(&mut self, caller: Address, role: Role) -> Result<(), AccessError> {
        // 不能放弃最后一个admin角色
        if role == Role::Admin {
            let admin_count = self.roles.get(&Role::Admin).map(|s| s.len()).unwrap_or(0);
            if admin_count <= 1 && self.has_role(Role::Admin, caller) {
                return Err(AccessError::CannotRenounceAdmin);
            }
        }

        if let Some(members) = self.roles.get_mut(&role) {
            members.remove(&caller);
        }

        if let Some(roles) = self.member_roles.get_mut(&caller) {
            roles.remove(&role);
        }

        Ok(())
    }

    /// 要求调用者拥有特定角色
    pub fn require_role(&self, caller: Address, role: Role) -> Result<(), AccessError> {
        if !self.has_role(role, caller) {
            return Err(AccessError::MissingRole(role));
        }
        Ok(())
    }

    /// 获取账户的所有角色
    pub fn get_roles(&self, account: Address) -> Vec<Role> {
        self.member_roles
            .get(&account)
            .map(|roles| roles.iter().cloned().collect())
            .unwrap_or_default()
    }
}

/// 双阶段所有权转移
pub struct TwoStepOwnership {
    owner: Address,
    pending_owner: Option<Address>,
}

impl TwoStepOwnership {
    pub fn new(owner: Address) -> Self {
        Self {
            owner,
            pending_owner: None,
        }
    }

    /// 当前所有者发起转移
    pub fn transfer_ownership(&mut self, caller: Address, new_owner: Address) -> Result<(), AccessError> {
        if caller != self.owner {
            return Err(AccessError::NotOwner);
        }

        self.pending_owner = Some(new_owner);
        Ok(())
    }

    /// 新所有者接受转移
    pub fn accept_ownership(&mut self, caller: Address) -> Result<(), AccessError> {
        match self.pending_owner {
            Some(pending) if pending == caller => {
                self.owner = caller;
                self.pending_owner = None;
                Ok(())
            }
            _ => Err(AccessError::NotPendingOwner),
        }
    }

    /// 取消待处理的转移
    pub fn cancel_transfer(&mut self, caller: Address) -> Result<(), AccessError> {
        if caller != self.owner {
            return Err(AccessError::NotOwner);
        }

        self.pending_owner = None;
        Ok(())
    }
}

#[derive(Debug)]
pub enum AccessError {
    MissingRole(Role),
    NotOwner,
    NotPendingOwner,
    CannotRenounceAdmin,
}
```

---

## 10. 测试与部署

### 10.1 本地测试网

```rust
use std::process::{Command, Child};
use std::time::Duration;

/// 本地测试网管理器
pub struct TestnetManager {
    /// 节点进程
    nodes: Vec<Child>,
    /// 链配置
    config: ChainConfig,
}

pub struct ChainConfig {
    pub chain_id: u64,
    pub block_time: u64,
    pub accounts: Vec<TestAccount>,
    pub prefunded_balance: u128,
}

pub struct TestAccount {
    pub address: Address,
    pub private_key: Vec<u8>,
}

impl TestnetManager {
    /// 启动本地测试网
    pub fn start(config: ChainConfig, node_count: usize) -> Result<Self, TestError> {
        let mut nodes = Vec::with_capacity(node_count);

        for i in 0..node_count {
            let port = 8545 + i;
            let child = Command::new("node")
                .args(&[
                    "--chain-id", &config.chain_id.to_string(),
                    "--port", &port.to_string(),
                    "--dev",
                ])
                .spawn()
                .map_err(|e| TestError::SpawnFailed(e.to_string()))?;

            nodes.push(child);
        }

        // 等待节点启动
        std::thread::sleep(Duration::from_secs(2));

        Ok(Self { nodes, config })
    }

    /// 创建测试账户并预充值
    pub fn create_test_account(&mut self) -> TestAccount {
        use rand::Rng;
        let mut rng = rand::thread_rng();

        let private_key: Vec<u8> = (0..32).map(|_| rng.gen()).collect();
        let address = self.derive_address(&private_key);

        TestAccount { address, private_key }
    }

    fn derive_address(&self, _private_key: &[u8]) -> Address {
        // 从私钥派生地址
        [0; 20]
    }

    /// 部署合约
    pub fn deploy_contract(
        &self,
        _deployer: &TestAccount,
        bytecode: Vec<u8>,
    ) -> Result<Address, TestError> {
        // 发送部署交易
        println!("Deploying contract with {} bytes", bytecode.len());
        Ok([0; 20])
    }

    /// 发送交易
    pub fn send_transaction(
        &self,
        _from: &TestAccount,
        _to: Address,
        _value: u128,
        _data: Vec<u8>,
    ) -> Result<[u8; 32], TestError> {
        // 构造并发送交易
        Ok([0; 32])
    }

    /// 调用合约（只读）
    pub fn call(&self, _contract: Address, _data: Vec<u8>) -> Result<Vec<u8>, TestError> {
        // 执行eth_call
        Ok(vec![])
    }

    /// 挖一个新块
    pub fn mine_block(&self) -> Result<(), TestError> {
        // 触发挖矿
        Ok(())
    }

    /// 增加时间
    pub fn increase_time(&self, seconds: u64) -> Result<(), TestError> {
        println!("Advancing time by {} seconds", seconds);
        Ok(())
    }

    /// 快照当前状态
    pub fn snapshot(&self) -> Result<u64, TestError> {
        // 返回快照ID
        Ok(1)
    }

    /// 恢复到快照
    pub fn revert(&self, snapshot_id: u64) -> Result<(), TestError> {
        println!("Reverting to snapshot {}", snapshot_id);
        Ok(())
    }
}

impl Drop for TestnetManager {
    fn drop(&mut self) {
        // 清理节点进程
        for node in &mut self.nodes {
            let _ = node.kill();
        }
    }
}

#[derive(Debug)]
pub enum TestError {
    SpawnFailed(String),
    DeploymentFailed(String),
    TransactionFailed(String),
}
```

### 10.2 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    /// ERC20合约测试示例
    mod erc20_tests {
        use super::*;

        fn setup() -> (TestnetManager, TestAccount, Address) {
            let config = ChainConfig {
                chain_id: 1337,
                block_time: 1,
                accounts: vec![],
                prefunded_balance: 1_000_000_000_000_000_000u128, // 1 ETH
            };

            let mut testnet = TestnetManager::start(config, 1).unwrap();
            let deployer = testnet.create_test_account();

            // 部署测试合约
            let bytecode = vec![/* ERC20 bytecode */];
            let contract = testnet.deploy_contract(&deployer, bytecode).unwrap();

            (testnet, deployer, contract)
        }

        #[test]
        fn test_initial_supply() {
            let (testnet, _deployer, contract) = setup();

            // 调用totalSupply
            let result = testnet.call(contract, vec![0x18, 0x16, 0x0d, 0xdd]).unwrap();
            let supply = u128::from_be_bytes(result.try_into().unwrap());

            assert_eq!(supply, 1_000_000_000_000_000_000_000u128);
        }

        #[test]
        fn test_transfer() {
            let (mut testnet, sender, contract) = setup();
            let recipient = testnet.create_test_account();

            // 构造transfer调用
            let mut data = vec![0xa9, 0x05, 0x9c, 0xbb]; // transfer selector
            data.extend_from_slice(&recipient.address);
            data.extend_from_slice(&100u128.to_be_bytes());

            // 发送交易
            let tx_hash = testnet.send_transaction(&sender, contract, 0, data).unwrap();

            // 挖块确认
            testnet.mine_block().unwrap();

            // 验证余额
            let mut balance_data = vec![0x70, 0xa0, 0x82, 0x31]; // balanceOf selector
            balance_data.extend_from_slice(&recipient.address);
            let result = testnet.call(contract, balance_data).unwrap();
            let balance = u128::from_be_bytes(result.try_into().unwrap());

            assert_eq!(balance, 100);
        }

        #[test]
        fn test_insufficient_balance() {
            let (mut testnet, sender, contract) = setup();
            let recipient = testnet.create_test_account();

            // 尝试转移超过余额
            let mut data = vec![0xa9, 0x05, 0x9c, 0xbb];
            data.extend_from_slice(&recipient.address);
            data.extend_from_slice(&u128::MAX.to_be_bytes());

            let result = testnet.send_transaction(&sender, contract, 0, data);

            assert!(result.is_err());
        }
    }

    /// 模糊测试示例
    mod fuzz_tests {
        use super::*;

        #[test]
        fn test_math_operations() {
            use proptest::prelude::*;

            proptest! {
                #[test]
                fn test_safe_add(a: u128, b: u128) {
                    let result = a.checked_add(b);

                    if let Some(sum) = result {
                        assert!(sum >= a);
                        assert!(sum >= b);
                    }
                    // 如果返回None，说明溢出
                }

                #[test]
                fn test_safe_mul(a: u128, b: u128) {
                    if let Some(product) = a.checked_mul(b) {
                        if a > 0 {
                            assert_eq!(product / a, b);
                        }
                    }
                }
            }
        }
    }

    /// 集成测试示例
    mod integration_tests {
        use super::*;

        #[tokio::test]
        async fn test_full_lifecycle() {
            // 启动测试网
            let config = ChainConfig {
                chain_id: 1337,
                block_time: 1,
                accounts: vec![],
                prefunded_balance: 1_000_000_000_000_000_000u128,
            };

            let mut testnet = TestnetManager::start(config, 3).unwrap();

            // 创建用户
            let alice = testnet.create_test_account();
            let bob = testnet.create_test_account();

            // 部署代币合约
            let token = testnet.deploy_contract(&alice, vec![]).unwrap();

            // 铸造代币
            let mut mint_data = vec![0x40, 0xc1, 0x0f, 0x19]; // mint selector
            mint_data.extend_from_slice(&alice.address);
            mint_data.extend_from_slice(&1_000_000u128.to_be_bytes());
            testnet.send_transaction(&alice, token, 0, mint_data).unwrap();

            testnet.mine_block().unwrap();

            // 转账
            let mut transfer_data = vec![0xa9, 0x05, 0x9c, 0xbb];
            transfer_data.extend_from_slice(&bob.address);
            transfer_data.extend_from_slice(&100_000u128.to_be_bytes());
            testnet.send_transaction(&alice, token, 0, transfer_data).unwrap();

            testnet.mine_block().unwrap();

            // 验证最终状态
            // ...
        }
    }
}
```

### 10.3 审计工具

```rust
/// 安全审计检查器
pub struct SecurityAuditor;

impl SecurityAuditor {
    /// 检查常见的安全问题
    pub fn audit_contract(bytecode: &[u8]) -> AuditReport {
        let mut findings = Vec::new();

        // 1. 检查SELFDESTRUCT
        if Self::contains_opcode(bytecode, 0xFF) {
            findings.push(Finding {
                severity: Severity::High,
                category: Category::AccessControl,
                description: "Contract contains SELFDESTRUCT opcode".to_string(),
            });
        }

        // 2. 检查未检查的call返回值
        if Self::has_unchecked_calls(bytecode) {
            findings.push(Finding {
                severity: Severity::Medium,
                category: Category::ErrorHandling,
                description: "Unchecked external call return values".to_string(),
            });
        }

        // 3. 检查可能的重入模式
        if Self::has_potential_reentrancy(bytecode) {
            findings.push(Finding {
                severity: Severity::High,
                category: Category::Reentrancy,
                description: "Potential reentrancy vulnerability".to_string(),
            });
        }

        // 4. 检查时间依赖
        if Self::uses_timestamp(bytecode) {
            findings.push(Finding {
                severity: Severity::Low,
                category: Category::Timestamp,
                description: "Contract uses block.timestamp".to_string(),
            });
        }

        // 5. 检查硬编码地址
        if Self::has_hardcoded_addresses(bytecode) {
            findings.push(Finding {
                severity: Severity::Info,
                category: Category::Configurability,
                description: "Hardcoded addresses found".to_string(),
            });
        }

        AuditReport { findings }
    }

    fn contains_opcode(bytecode: &[u8], opcode: u8) -> bool {
        bytecode.contains(&opcode)
    }

    fn has_unchecked_calls(_bytecode: &[u8]) -> bool {
        // 实现分析逻辑
        false
    }

    fn has_potential_reentrancy(_bytecode: &[u8]) -> bool {
        // 实现分析逻辑
        false
    }

    fn uses_timestamp(bytecode: &[u8]) -> bool {
        bytecode.contains(&0x42) // TIMESTAMP opcode
    }

    fn has_hardcoded_addresses(_bytecode: &[u8]) -> bool {
        false
    }
}

pub struct AuditReport {
    pub findings: Vec<Finding>,
}

pub struct Finding {
    pub severity: Severity,
    pub category: Category,
    pub description: String,
}

pub enum Severity {
    Critical,
    High,
    Medium,
    Low,
    Info,
}

pub enum Category {
    AccessControl,
    Reentrancy,
    ErrorHandling,
    Timestamp,
    Configurability,
}

/// 静态分析工具集成
pub mod static_analysis {
    use std::process::Command;

    /// 运行Slither分析
    pub fn run_slither(contract_path: &str) -> Result<String, String> {
        let output = Command::new("slither")
            .args(&[contract_path, "--json", "-"])
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).to_string())
        }
    }

    /// 运行Mythril符号执行
    pub fn run_mythril(contract_path: &str) -> Result<String, String> {
        let output = Command::new("myth")
            .args(&["analyze", contract_path, "-o", "json"])
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).to_string())
        }
    }
}
```

---

## 附录：资源推荐

### 学习资源

| 资源 | 链接 | 描述 |
|------|------|------|
| Rust区块链开发 | <https://github.com/parasyte/pixels> | Rust区块链项目集合 |
| Substrate教程 | <https://docs.substrate.io/> | Substrate官方文档 |
| ink!文档 | <https://ink.substrate.io/> | ink!智能合约 |
| Solana开发 | <https://solana.com/developers> | Solana开发者资源 |
| Rust密码学 | <https://github.com/RustCrypto> | Rust密码学库 |

### 常用Crates

```toml
[dependencies]
# 密码学
sha2 = "0.10"
sha3 = "0.10"
secp256k1 = "0.28"
ed25519-dalek = "2.0"
blake2 = "0.10"

# 区块链相关
primitive-types = "0.12"
ethereum-types = "0.14"
rlp = "0.5"

# 网络
libp2p = "0.52"
tokio = { version = "1.0", features = ["full"] }

# 存储
rocksdb = "0.21"
leveldb = "0.8"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
parity-scale-codec = "3.0"

# 测试
proptest = "1.0"
tokio-test = "0.4"
```

---

> **提示**: 本文档涵盖了Rust区块链开发的核心概念和实践。实际项目开发中，请参考各项目的官方文档和最新的安全建议。
