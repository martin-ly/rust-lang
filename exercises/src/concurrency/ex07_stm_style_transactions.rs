//! # 练习 7: STM 风格事务 / Exercise 7: STM-Style Transactions
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 乐观并发、事务语义、Mutex 粗粒度替代 STM
//!   Optimistic concurrency, transactional semantics, coarse-grained Mutex as STM substitute
//!
//! ## 题目描述 / Problem Description
//!
//! Rust 标准库没有原生 STM；用 `Mutex` + 版本号实现一个多账户转账的
//! “事务”抽象，体会原子性保证与 Haskell `stm` 的差异。
//! Rust std has no native STM; implement a multi-account transfer
//! "transaction" with `Mutex` + version counters, and compare the
//! atomicity guarantees with Haskell `stm`.
//!
//! ## 对应概念 / Related Concepts
//!
//! - `concept/04_formal/07_concurrency_semantics/05_stm_semantics.md`
//! - `concept/03_advanced/00_concurrency/03_concurrency_patterns.md`

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// 账户表：单把大锁保护（粗粒度事务）/ Account table: one coarse lock (coarse transaction)
#[derive(Debug, Default)]
pub struct Bank {
    accounts: Mutex<HashMap<String, i64>>,
    /// 全局版本号：每次事务提交递增 / Global version: incremented per commit
    version: Mutex<u64>,
}

impl Bank {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn open_account(&self, name: &str, balance: i64) {
        self.accounts
            .lock()
            .expect("accounts poisoned")
            .insert(name.to_string(), balance);
    }

    pub fn balance_of(&self, name: &str) -> Option<i64> {
        self.accounts.lock().expect("accounts poisoned").get(name).copied()
    }

    /// 事务式转账：要么全部生效，要么全部回滚 / Transactional transfer: all-or-nothing
    ///
    /// 关键：两把锁的获取顺序固定（先 accounts 后 version），避免死锁。
    /// Key: fixed lock acquisition order (accounts then version) to avoid deadlock.
    pub fn transfer(&self, from: &str, to: &str, amount: i64) -> Result<(), String> {
        if amount < 0 {
            return Err("amount must be non-negative".into());
        }
        let mut accounts = self.accounts.lock().expect("accounts poisoned");
        let from_balance = accounts
            .get(from)
            .copied()
            .ok_or_else(|| format!("no such account: {from}"))?;
        let to_balance = accounts
            .get(to)
            .copied()
            .ok_or_else(|| format!("no such account: {to}"))?;
        if from_balance < amount {
            // 回滚：未做任何修改即返回 / Rollback: return before any mutation
            return Err("insufficient funds".into());
        }
        accounts.insert(from.to_string(), from_balance - amount);
        accounts.insert(to.to_string(), to_balance + amount);
        drop(accounts);
        *self.version.lock().expect("version poisoned") += 1;
        Ok(())
    }

    pub fn version(&self) -> u64 {
        *self.version.lock().expect("version poisoned")
    }

    /// 总存款守恒检查 / Conservation invariant check
    pub fn total(&self) -> i64 {
        self.accounts.lock().expect("accounts poisoned").values().sum()
    }
}

/// 并发转账驱动：多线程对同一 Bank 并发执行事务 / Concurrent transfer driver
pub fn run_concurrent_transfers(bank: &Arc<Bank>, rounds: usize) {
    std::thread::scope(|s| {
        for i in 0..rounds {
            let bank = Arc::clone(bank);
            s.spawn(move || {
                let _ = bank.transfer("alice", "bob", 1);
                let _ = bank.transfer("bob", "alice", 1);
                let _ = i; // silence unused
            });
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transfer_success() {
        let bank = Bank::new();
        bank.open_account("alice", 100);
        bank.open_account("bob", 50);
        assert!(bank.transfer("alice", "bob", 30).is_ok());
        assert_eq!(bank.balance_of("alice"), Some(70));
        assert_eq!(bank.balance_of("bob"), Some(80));
        assert_eq!(bank.version(), 1);
    }

    #[test]
    fn test_transfer_rollback_on_insufficient_funds() {
        let bank = Bank::new();
        bank.open_account("alice", 10);
        bank.open_account("bob", 50);
        assert!(bank.transfer("alice", "bob", 30).is_err());
        // 回滚：余额不变，版本号不递增 / Rolled back: balances and version unchanged
        assert_eq!(bank.balance_of("alice"), Some(10));
        assert_eq!(bank.balance_of("bob"), Some(50));
        assert_eq!(bank.version(), 0);
    }

    #[test]
    fn test_transfer_unknown_account() {
        let bank = Bank::new();
        bank.open_account("alice", 10);
        assert!(bank.transfer("alice", "ghost", 1).is_err());
        assert!(bank.transfer("ghost", "alice", 1).is_err());
    }

    #[test]
    fn test_negative_amount_rejected() {
        let bank = Bank::new();
        bank.open_account("alice", 10);
        bank.open_account("bob", 10);
        assert!(bank.transfer("alice", "bob", -5).is_err());
    }

    #[test]
    fn test_concurrent_transfers_conserve_total() {
        let bank = Arc::new(Bank::new());
        bank.open_account("alice", 1000);
        bank.open_account("bob", 1000);
        let before = bank.total();
        run_concurrent_transfers(&bank, 8);
        assert_eq!(bank.total(), before, "total must be conserved");
    }
}
