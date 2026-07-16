//! STM 风格事务示例 / STM-style transaction demo
//!
//! 用 `Mutex` + 版本号实现多账户转账事务，演示 Rust 无原生 STM 时的
//! 粗粒度事务替代模式，并与 Haskell `stm` 的细粒度组合性对比。
//!
//! 权威概念页（concept prose lives there, not here）：
//! - `concept/04_formal/07_concurrency_semantics/05_stm_semantics.md`
//!
//! 运行方式 / Run:
//!
//! ```bash
//! cargo run -p c05_threads --example stm_style_transaction_demo
//! ```

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// 粗粒度事务银行：单锁保护全部账户 / Coarse-grained transactional bank
struct Bank {
    accounts: Mutex<HashMap<String, i64>>,
    version: Mutex<u64>,
}

impl Bank {
    fn new() -> Self {
        Self {
            accounts: Mutex::new(HashMap::new()),
            version: Mutex::new(0),
        }
    }

    fn open(&self, name: &str, balance: i64) {
        self.accounts
            .lock()
            .expect("accounts poisoned")
            .insert(name.to_string(), balance);
    }

    /// 事务式转账：要么全部生效，要么全部回滚 / All-or-nothing transfer
    fn transfer(&self, from: &str, to: &str, amount: i64) -> Result<(), String> {
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
            return Err("insufficient funds: rolled back".into());
        }
        accounts.insert(from.to_string(), from_balance - amount);
        accounts.insert(to.to_string(), to_balance + amount);
        drop(accounts);
        *self.version.lock().expect("version poisoned") += 1;
        Ok(())
    }

    fn total(&self) -> i64 {
        self.accounts.lock().expect("accounts poisoned").values().sum()
    }
}

fn main() {
    let bank = Arc::new(Bank::new());
    bank.open("alice", 1000);
    bank.open("bob", 1000);
    println!("初始总存款 / initial total: {}", bank.total());

    // 单线程事务 / single-threaded transaction
    match bank.transfer("alice", "bob", 200) {
        Ok(()) => println!("transfer 200 alice->bob: OK"),
        Err(e) => println!("transfer failed: {e}"),
    }
    // 触发回滚 / trigger rollback
    match bank.transfer("alice", "bob", 10_000) {
        Ok(()) => println!("unexpected success"),
        Err(e) => println!("transfer 10000 alice->bob: {e}"),
    }

    // 并发事务：总存款守恒 / concurrent transactions: conservation invariant
    std::thread::scope(|s| {
        for _ in 0..8 {
            let bank = Arc::clone(&bank);
            s.spawn(move || {
                let _ = bank.transfer("alice", "bob", 1);
                let _ = bank.transfer("bob", "alice", 1);
            });
        }
    });

    println!("并发转账后总存款 / total after concurrent transfers: {}", bank.total());
    println!(
        "要点 / takeaway: Rust 用所有权+锁实现事务语义；细粒度可组合 STM 见 concept/04_formal/07_concurrency_semantics/05_stm_semantics.md"
    );
}
