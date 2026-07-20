# 智能合约基础（Smart Contract Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [智能合约基础（Smart Contract Basics）](#智能合约基础smart-contract-basics)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [智能合约开发](#智能合约开发)
    - [基本合约结构](#基本合约结构)
  - [状态管理](#状态管理)
    - [状态存储](#状态存储)
  - [事件和日志](#事件和日志)
    - [事件定义](#事件定义)
  - [实践示例](#实践示例)
    - [示例 1：投票合约](#示例-1投票合约)
    - [示例 2：拍卖合约](#示例-2拍卖合约)
  - [安全考虑](#安全考虑)
    - [1. 重入攻击防护](#1-重入攻击防护)
    - [2. 整数溢出防护](#2-整数溢出防护)
  - [参考资料](#参考资料)

---

## 概述

智能合约是运行在区块链上的程序，Rust 在智能合约开发中提供了类型安全和性能优势。本示例展示 Rust 智能合约开发的基础知识。

## 智能合约开发

### 基本合约结构

```rust
use near_sdk::borsh::{self, BorshDeserialize, BorshSerialize};
use near_sdk::{env, near_bindgen, AccountId, Balance};

#[near_bindgen]
#[derive(BorshDeserialize, BorshSerialize)]
pub struct SimpleContract {
    owner: AccountId,
    balance: Balance,
}

#[near_bindgen]
impl SimpleContract {
    #[init]
    pub fn new(owner: AccountId) -> Self {
        Self {
            owner,
            balance: 0,
        }
    }

    pub fn get_balance(&self) -> Balance {
        self.balance
    }

    pub fn deposit(&mut self, amount: Balance) {
        self.balance += amount;
    }

    pub fn withdraw(&mut self, amount: Balance) {
        assert_eq!(env::predecessor_account_id(), self.owner, "只有所有者可以提取");
        assert!(amount <= self.balance, "余额不足");
        self.balance -= amount;
    }
}
```

## 状态管理

### 状态存储

```rust
use near_sdk::collections::UnorderedMap;

#[near_bindgen]
#[derive(BorshDeserialize, BorshSerialize)]
pub struct TokenContract {
    balances: UnorderedMap<AccountId, Balance>,
    total_supply: Balance,
}

#[near_bindgen]
impl TokenContract {
    #[init]
    pub fn new(initial_supply: Balance) -> Self {
        let mut contract = Self {
            balances: UnorderedMap::new(b"b".to_vec()),
            total_supply: initial_supply,
        };

        let owner = env::predecessor_account_id();
        contract.balances.insert(&owner, &initial_supply);
        contract
    }

    pub fn transfer(&mut self, to: AccountId, amount: Balance) {
        let from = env::predecessor_account_id();
        let from_balance = self.balances.get(&from).unwrap_or(0);
        assert!(from_balance >= amount, "余额不足");

        let to_balance = self.balances.get(&to).unwrap_or(0);
        self.balances.insert(&from, &(from_balance - amount));
        self.balances.insert(&to, &(to_balance + amount));
    }

    pub fn get_balance(&self, account: AccountId) -> Balance {
        self.balances.get(&account).unwrap_or(0)
    }
}
```

## 事件和日志

### 事件定义

```rust
use near_sdk::serde::{Deserialize, Serialize};
use near_sdk::serde_json::json;

#[derive(Serialize, Deserialize)]
#[serde(crate = "near_sdk::serde")]
pub struct TransferEvent {
    from: AccountId,
    to: AccountId,
    amount: Balance,
}

impl TokenContract {
    pub fn transfer_with_event(&mut self, to: AccountId, amount: Balance) {
        let from = env::predecessor_account_id();
        // ... 转账逻辑 ...

        // 发出事件
        let event = TransferEvent {
            from: from.clone(),
            to: to.clone(),
            amount,
        };
        env::log_str(&json!({
            "event": "Transfer",
            "data": event
        }).to_string());
    }
}
```

## 实践示例

### 示例 1：投票合约

```rust
use near_sdk::collections::UnorderedSet;

#[near_bindgen]
#[derive(BorshDeserialize, BorshSerialize)]
pub struct VotingContract {
    candidates: UnorderedSet<String>,
    votes: UnorderedMap<String, u64>,
    voters: UnorderedSet<AccountId>,
}

#[near_bindgen]
impl VotingContract {
    #[init]
    pub fn new(candidates: Vec<String>) -> Self {
        let mut contract = Self {
            candidates: UnorderedSet::new(b"c".to_vec()),
            votes: UnorderedMap::new(b"v".to_vec()),
            voters: UnorderedSet::new(b"r".to_vec()),
        };

        for candidate in candidates {
            contract.candidates.insert(&candidate);
            contract.votes.insert(&candidate, &0);
        }
        contract
    }

    pub fn vote(&mut self, candidate: String) {
        let voter = env::predecessor_account_id();
        assert!(!self.voters.contains(&voter), "已经投票");
        assert!(self.candidates.contains(&candidate), "无效的候选人");

        self.voters.insert(&voter);
        let current_votes = self.votes.get(&candidate).unwrap_or(0);
        self.votes.insert(&candidate, &(current_votes + 1));
    }

    pub fn get_votes(&self, candidate: String) -> u64 {
        self.votes.get(&candidate).unwrap_or(0)
    }
}
```

### 示例 2：拍卖合约

```rust
#[near_bindgen]
#[derive(BorshDeserialize, BorshSerialize)]
pub struct AuctionContract {
    item: String,
    seller: AccountId,
    highest_bid: Balance,
    highest_bidder: Option<AccountId>,
    ended: bool,
}

#[near_bindgen]
impl AuctionContract {
    #[init]
    pub fn new(item: String, seller: AccountId) -> Self {
        Self {
            item,
            seller,
            highest_bid: 0,
            highest_bidder: None,
            ended: false,
        }
    }

    pub fn bid(&mut self) {
        assert!(!self.ended, "拍卖已结束");
        let bidder = env::predecessor_account_id();
        let amount = env::attached_deposit();

        assert!(amount > self.highest_bid, "出价必须高于当前最高价");

        // 退还之前的最高出价
        if let Some(prev_bidder) = &self.highest_bidder {
            env::promise_create(
                prev_bidder.clone(),
                "withdraw",
                &[],
                self.highest_bid,
                0,
            );
        }

        self.highest_bid = amount;
        self.highest_bidder = Some(bidder);
    }

    pub fn end_auction(&mut self) {
        assert_eq!(env::predecessor_account_id(), self.seller, "只有卖家可以结束拍卖");
        assert!(!self.ended, "拍卖已结束");

        self.ended = true;

        if let Some(bidder) = &self.highest_bidder {
            // 将资金转给卖家
            env::promise_create(
                self.seller.clone(),
                "transfer",
                &[],
                self.highest_bid,
                0,
            );
        }
    }
}
```

## 安全考虑

### 1. 重入攻击防护

```rust
use near_sdk::collections::LookupMap;

pub struct SecureContract {
    locked: LookupMap<AccountId, bool>,
}

impl SecureContract {
    pub fn secure_withdraw(&mut self, amount: Balance) {
        let account = env::predecessor_account_id();

        // 检查重入锁
        if self.locked.get(&account).unwrap_or(false) {
            env::panic_str("重入攻击检测");
        }

        self.locked.insert(&account, &true);

        // 执行提取
        // ...

        self.locked.insert(&account, &false);
    }
}
```

### 2. 整数溢出防护

```rust
use near_sdk::env;

pub fn safe_add(a: Balance, b: Balance) -> Balance {
    a.checked_add(b)
        .unwrap_or_else(|| env::panic_str("整数溢出"))
}
```

## 参考资料

- [区块链/Web3 索引](./00_index.md)
- [金融科技索引](../00_index.md)
- [NEAR SDK 文档](https://docs.rs/near-sdk/)
- [Solana 程序文档](https://docs.rs/solana-program/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回金融科技: [`../00_index.md`](../00_index.md)
