# Blockchain - 区块链开发

## 📋 目录

- [Blockchain - 区块链开发](#blockchain---区块链开发)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [核心库](#核心库)
    - [密码学基础](#密码学基础)
  - [以太坊开发](#以太坊开发)
    - [Ethers-rs](#ethers-rs)
    - [智能合约交互](#智能合约交互)
  - [Substrate](#substrate)
    - [Pallet 开发](#pallet-开发)
  - [实战示例](#实战示例)
    - [简单区块链实现](#简单区块链实现)
  - [参考资源](#参考资源)

---

## 概述

Rust 在区块链领域被广泛应用，提供高性能和安全性保证。

### 核心依赖

```toml
[dependencies]
# 以太坊
ethers = "2.0"
alloy = "0.1"

# Substrate
substrate = "3.0"
sp-core = "28.0"

# 密码学
sha2 = "0.10"
secp256k1 = "0.28"
```

---

## 核心库

### 密码学基础

```rust
use sha2::{Sha256, Digest};
use secp256k1::{Secp256k1, Message, SecretKey};

fn hash_example() {
    let mut hasher = Sha256::new();
    hasher.update(b"Hello, Blockchain!");
    let result = hasher.finalize();
    
    println!("SHA256: {:x}", result);
}

fn sign_example() {
    let secp = Secp256k1::new();
    let secret_key = SecretKey::from_slice(&[0x01; 32]).unwrap();
    let message = Message::from_digest_slice(&[0x02; 32]).unwrap();
    
    let sig = secp.sign_ecdsa(&message, &secret_key);
    println!("签名: {:?}", sig);
}
```

---

## 以太坊开发

### Ethers-rs

```rust
use ethers::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 连接到以太坊节点
    let provider = Provider::<Http>::try_from("https://eth.llamarpc.com")?;
    
    // 获取最新区块号
    let block_number = provider.get_block_number().await?;
    println!("最新区块: {}", block_number);
    
    // 获取余额
    let address = "0x0000000000000000000000000000000000000000".parse::<Address>()?;
    let balance = provider.get_balance(address, None).await?;
    println!("余额: {} ETH", ethers::utils::format_ether(balance));
    
    Ok(())
}
```

### 智能合约交互

```rust
use ethers::{
    prelude::*,
    contract::abigen,
};

// 生成合约绑定
abigen!(
    ERC20,
    r#"[
        function balanceOf(address) external view returns (uint256)
        function transfer(address to, uint256 amount) external returns (bool)
    ]"#,
);

async fn interact_with_contract() -> Result<(), Box<dyn std::error::Error>> {
    let provider = Provider::<Http>::try_from("https://eth.llamarpc.com")?;
    let contract_address = "0x...".parse::<Address>()?;
    let contract = ERC20::new(contract_address, Arc::new(provider));
    
    let balance = contract
        .balance_of("0x...".parse::<Address>()?)
        .call()
        .await?;
    
    println!("余额: {}", balance);
    Ok(())
}
```

---

## Substrate

### Pallet 开发

```rust
use frame_support::{decl_module, decl_storage, decl_event, dispatch::DispatchResult};
use frame_system::ensure_signed;

pub trait Config: frame_system::Config {
    type RuntimeEvent: From<Event<Self>> + Into<<Self as frame_system::Config>::RuntimeEvent>;
}

decl_storage! {
    trait Store for Module<T: Config> as TemplateModule {
        Something get(fn something): Option<u32>;
    }
}

decl_event!(
    pub enum Event<T> where AccountId = <T as frame_system::Config>::AccountId {
        SomethingStored(u32, AccountId),
    }
);

decl_module! {
    pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin {
        fn deposit_event() = default;
        
        #[weight = 10_000]
        pub fn do_something(origin, something: u32) -> DispatchResult {
            let who = ensure_signed(origin)?;
            
            <Something>::put(something);
            
            Self::deposit_event(RawEvent::SomethingStored(something, who));
            Ok(())
        }
    }
}
```

---

## 实战示例

### 简单区块链实现

```rust
use sha2::{Sha256, Digest};
use chrono::Utc;

#[derive(Debug, Clone)]
struct Block {
    index: u64,
    timestamp: i64,
    data: String,
    previous_hash: String,
    hash: String,
    nonce: u64,
}

impl Block {
    fn new(index: u64, data: String, previous_hash: String) -> Self {
        let timestamp = Utc::now().timestamp();
        let mut block = Block {
            index,
            timestamp,
            data,
            previous_hash,
            hash: String::new(),
            nonce: 0,
        };
        block.mine(2); // 难度为2
        block
    }
    
    fn calculate_hash(&self) -> String {
        let content = format!(
            "{}{}{}{}{}",
            self.index, self.timestamp, self.data, self.previous_hash, self.nonce
        );
        
        let mut hasher = Sha256::new();
        hasher.update(content.as_bytes());
        format!("{:x}", hasher.finalize())
    }
    
    fn mine(&mut self, difficulty: usize) {
        let target = "0".repeat(difficulty);
        
        while &self.calculate_hash()[..difficulty] != target {
            self.nonce += 1;
        }
        
        self.hash = self.calculate_hash();
    }
}

struct Blockchain {
    chain: Vec<Block>,
}

impl Blockchain {
    fn new() -> Self {
        let genesis = Block::new(0, "Genesis Block".to_string(), "0".to_string());
        Blockchain {
            chain: vec![genesis],
        }
    }
    
    fn add_block(&mut self, data: String) {
        let previous_block = self.chain.last().unwrap();
        let new_block = Block::new(
            previous_block.index + 1,
            data,
            previous_block.hash.clone(),
        );
        self.chain.push(new_block);
    }
    
    fn is_valid(&self) -> bool {
        for i in 1..self.chain.len() {
            let current = &self.chain[i];
            let previous = &self.chain[i - 1];
            
            if current.hash != current.calculate_hash() {
                return false;
            }
            
            if current.previous_hash != previous.hash {
                return false;
            }
        }
        true
    }
}

fn main() {
    let mut blockchain = Blockchain::new();
    
    blockchain.add_block("第1笔交易".to_string());
    blockchain.add_block("第2笔交易".to_string());
    
    println!("区块链有效: {}", blockchain.is_valid());
    
    for block in &blockchain.chain {
        println!("{:#?}", block);
    }
}
```

---

## 参考资源

- [Ethers-rs 文档](https://docs.rs/ethers/)
- [Substrate 文档](https://docs.substrate.io/)
- [Rust Blockchain Ecosystem](https://github.com/rust-in-blockchain/awesome-blockchain-rust)
