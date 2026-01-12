//! 形式化验证与证明 - Formal Verification and Proofs
//!
//! # 概述 (Overview)
//!
//! 本模块提供异步编程的形式化验证技术，包括：
//! - 不变式证明 (Invariant Proofs)
//! - 活性证明 (Liveness Proofs)
//! - 安全性证明 (Safety Proofs)
//! - 终止性证明 (Termination Proofs)
//! - 死锁检测 (Deadlock Detection)
//!
//! # 理论基础
//!
//! ## 1. Hoare 逻辑 (Hoare Logic)
//!
//! ```text
//! {P} C {Q}
//!
//! 其中:
//! - P: 前置条件 (Precondition)
//! - C: 命令/程序 (Command/Program)
//! - Q: 后置条件 (Postcondition)
//!
//! 推理规则:
//!
//! 1. 空命令:
//!    ─────────────
//!    {P} skip {P}
//!
//! 2. 赋值:
//!    ────────────────────────────
//!    {P[E/x]} x := E {P}
//!
//! 3. 顺序组合:
//!    {P} C1 {Q}    {Q} C2 {R}
//!    ──────────────────────────
//!    {P} C1; C2 {R}
//!
//! 4. 条件:
//!    {P ∧ B} C1 {Q}    {P ∧ ¬B} C2 {Q}
//!    ─────────────────────────────────
//!    {P} if B then C1 else C2 {Q}
//!
//! 5. 循环:
//!    {I ∧ B} C {I}
//!    ───────────────────────────
//!    {I} while B do C {I ∧ ¬B}
//!
//!    其中 I 是循环不变式
//! ```
//!
//! ## 2. 时序逻辑 (Temporal Logic)
//!
//! ### 线性时序逻辑 (LTL - Linear Temporal Logic)
//!
//! ```text
//! 算子:
//! - □P (Always): P 在所有未来状态都成立
//! - ◇P (Eventually): P 在某个未来状态成立
//! - ○P (Next): P 在下一个状态成立
//! - P U Q (Until): P 一直成立直到 Q 成立
//!
//! 性质:
//! - 安全性 (Safety): □¬Bad (永远不会到达坏状态)
//! - 活性 (Liveness): □◇Good (无限次到达好状态)
//! ```
//!
//! ## 3. 并发验证
//!
//! ```text
//! 并发程序 P || Q 的验证:
//!
//! 1. 不干扰原则 (Non-interference):
//!    如果 {P} C {Q}，则 C 不修改 P 和 Q 中的共享变量
//!
//! 2. 资源不变式 (Resource Invariant):
//!    对于共享资源 R，定义不变式 I(R)
//!    每个访问 R 的线程必须维护 I(R)
//!
//! 3. 所有权 (Ownership):
//!    每个资源有唯一所有者
//!    访问资源需要获取所有权
//! ```

use std::sync::Arc;
use std::time::Duration;
use tokio::sync::Mutex;
use tokio::time::sleep;

/// # 示例 1: 不变式验证
///
/// 验证程序在执行过程中保持特定不变式
pub mod invariant_verification {
    use super::*;

    /// 银行账户 - 演示不变式维护
    ///
    /// ## 不变式
    /// ```text
    /// I: balance ≥ 0  (账户余额始终非负)
    /// ```
    pub struct BankAccount {
        balance: Arc<Mutex<i64>>,
    }

    impl BankAccount {
        /// 创建账户
        ///
        /// ## 前置条件
        /// ```text
        /// P: initial_balance ≥ 0
        /// ```
        ///
        /// ## 后置条件
        /// ```text
        /// Q: balance = initial_balance ∧ balance ≥ 0
        /// ```
        pub fn new(initial_balance: i64) -> Self {
            assert!(initial_balance >= 0, "违反前置条件: 初始余额必须非负");
            Self {
                balance: Arc::new(Mutex::new(initial_balance)),
            }
        }

        /// 存款操作
        ///
        /// ## Hoare 三元组
        /// ```text
        /// {balance = old_balance ∧ amount > 0}
        ///   deposit(amount)
        /// {balance = old_balance + amount ∧ balance ≥ 0}
        /// ```
        pub async fn deposit(&self, amount: i64) -> Result<i64, &'static str> {
            if amount <= 0 {
                return Err("存款金额必须为正");
            }

            let mut balance = self.balance.lock().await;
            let old_balance = *balance;

            // 执行操作
            *balance += amount;
            let new_balance = *balance;

            // 验证后置条件
            assert_eq!(new_balance, old_balance + amount);
            assert!(new_balance >= 0, "违反不变式: 余额为负");

            println!("  [Deposit] {} + {} = {}", old_balance, amount, new_balance);
            Ok(new_balance)
        }

        /// 取款操作
        ///
        /// ## Hoare 三元组
        /// ```text
        /// {balance = old_balance ∧ amount > 0 ∧ amount ≤ old_balance}
        ///   withdraw(amount)
        /// {balance = old_balance - amount ∧ balance ≥ 0}
        /// ```
        pub async fn withdraw(&self, amount: i64) -> Result<i64, &'static str> {
            if amount <= 0 {
                return Err("取款金额必须为正");
            }

            let mut balance = self.balance.lock().await;
            let old_balance = *balance;

            // 检查前置条件
            if amount > old_balance {
                return Err("余额不足");
            }

            // 执行操作
            *balance -= amount;
            let new_balance = *balance;

            // 验证后置条件
            assert_eq!(new_balance, old_balance - amount);
            assert!(new_balance >= 0, "违反不变式: 余额为负");

            println!("  [Withdraw] {} - {} = {}", old_balance, amount, new_balance);
            Ok(new_balance)
        }

        /// 获取余额
        pub async fn get_balance(&self) -> i64 {
            let balance = self.balance.lock().await;
            *balance
        }
    }

    /// 演示并发转账的不变式维护
    ///
    /// ## 全局不变式
    /// ```text
    /// I: sum(all_balances) = constant
    /// ```
    pub async fn demo_concurrent_transfers() {
        println!("\n=== 不变式验证: 并发转账 ===");

        let account1 = Arc::new(BankAccount::new(1000));
        let account2 = Arc::new(BankAccount::new(2000));
        let account3 = Arc::new(BankAccount::new(3000));

        // 初始总额
        let initial_total = 1000 + 2000 + 3000;
        println!("初始总额: {}", initial_total);

        // 并发转账
        let acc1 = account1.clone();
        let acc2 = account2.clone();
        let t1 = tokio::spawn(async move {
            // Account1 -> Account2: 100
            acc1.withdraw(100).await.unwrap();
            acc2.deposit(100).await.unwrap();
        });

        let acc2 = account2.clone();
        let acc3 = account3.clone();
        let t2 = tokio::spawn(async move {
            // Account2 -> Account3: 200
            acc2.withdraw(200).await.unwrap();
            acc3.deposit(200).await.unwrap();
        });

        let acc3 = account3.clone();
        let acc1 = account1.clone();
        let t3 = tokio::spawn(async move {
            // Account3 -> Account1: 150
            acc3.withdraw(150).await.unwrap();
            acc1.deposit(150).await.unwrap();
        });

        // 等待所有转账完成
        let _ = tokio::join!(t1, t2, t3);

        // 验证全局不变式
        let final_total = account1.get_balance().await
            + account2.get_balance().await
            + account3.get_balance().await;

        println!("最终总额: {}", final_total);
        assert_eq!(
            initial_total, final_total,
            "违反全局不变式: 总额发生变化"
        );
        println!("✓ 全局不变式验证通过");
    }
}

/// # 示例 2: 终止性证明
///
/// 使用度量函数证明程序终止
pub mod termination_proofs {
    use super::*;

    /// 证明异步循环的终止性
    ///
    /// ## 度量函数 (Ranking Function)
    /// ```text
    /// φ(n) = n
    ///
    /// 性质:
    /// 1. φ(n) ≥ 0  (非负)
    /// 2. 每次迭代 φ 严格递减
    /// 3. φ = 0 时循环终止
    /// ```
    pub async fn countdown_with_proof(mut n: u64) {
        println!("\n=== 终止性证明: 倒计时 ===");
        println!("初始度量: φ({}) = {}", n, n);

        while n > 0 {
            println!("  当前度量: φ({}) = {}", n, n);
            sleep(Duration::from_millis(100)).await;

            let old_n = n;
            n -= 1; // 度量严格递减

            println!("  度量递减: {} → {}", old_n, n);
            assert!(n < old_n, "度量函数必须严格递减");
        }

        println!("度量为 0，循环终止");
        println!("✓ 终止性证明完成");
    }

    /// 更复杂的终止性证明：二分查找
    ///
    /// ## 度量函数
    /// ```text
    /// φ(left, right) = right - left
    /// ```
    pub async fn binary_search_with_proof(arr: Vec<i32>, target: i32) -> Option<usize> {
        println!("\n=== 终止性证明: 二分查找 ===");

        let mut left = 0;
        let mut right = arr.len();

        println!("初始度量: φ({}, {}) = {}", left, right, right - left);

        while left < right {
            let old_metric = right - left;
            println!("  当前度量: φ({}, {}) = {}", left, right, old_metric);

            let mid = left + (right - left) / 2;

            if arr[mid] == target {
                println!("找到目标，返回");
                return Some(mid);
            } else if arr[mid] < target {
                left = mid + 1;
            } else {
                right = mid;
            }

            let new_metric = right - left;
            println!("  度量递减: {} → {}", old_metric, new_metric);
            assert!(new_metric < old_metric, "度量函数必须严格递减");

            sleep(Duration::from_millis(50)).await;
        }

        println!("度量为 0，查找终止");
        println!("✓ 终止性证明完成");
        None
    }
}

/// # 示例 3: 死锁检测
///
/// 检测和预防死锁
pub mod deadlock_detection {
    use super::*;

    /// 资源分配图
    ///
    /// 用于死锁检测的数据结构
    pub struct ResourceGraph {
        /// 资源 -> 等待该资源的任务
        resource_holders: Arc<Mutex<std::collections::HashMap<String, String>>>,
    }

    impl Default for ResourceGraph {
        fn default() -> Self {
            Self {
                resource_holders: Arc::new(Mutex::new(std::collections::HashMap::new())),
            }
        }
    }

    impl ResourceGraph {
        pub fn new() -> Self {
            Self::default()
        }

        /// 请求资源
        pub async fn acquire(&self, task: &str, resource: &str) -> Result<(), &'static str> {
            let mut holders = self.resource_holders.lock().await;

            if let Some(holder) = holders.get(resource) {
                if holder != task {
                    println!("  [Warning] {} 等待资源 {}，当前持有者: {}", task, resource, holder);
                    return Err("资源被占用");
                }
            }

            holders.insert(resource.to_string(), task.to_string());
            println!("  [Acquire] {} 获取资源 {}", task, resource);
            Ok(())
        }

        /// 释放资源
        pub async fn release(&self, task: &str, resource: &str) {
            let mut holders = self.resource_holders.lock().await;
            holders.remove(resource);
            println!("  [Release] {} 释放资源 {}", task, resource);
        }
    }

    /// 演示死锁场景
    pub async fn demo_deadlock_scenario() {
        println!("\n=== 死锁检测演示 ===");

        let graph = Arc::new(ResourceGraph::new());

        let res_a = Arc::new(Mutex::new(()));
        let res_b = Arc::new(Mutex::new(()));

        let g1 = graph.clone();
        let a1 = res_a.clone();
        let b1 = res_b.clone();
        let task1 = tokio::spawn(async move {
            println!("Task1: 尝试获取资源 A");
            let _lock_a = a1.lock().await;
            g1.acquire("Task1", "ResourceA").await.ok();

            sleep(Duration::from_millis(50)).await;

            println!("Task1: 尝试获取资源 B");
            let _lock_b = b1.lock().await;
            g1.acquire("Task1", "ResourceB").await.ok();

            println!("Task1: 完成工作");
            g1.release("Task1", "ResourceA").await;
            g1.release("Task1", "ResourceB").await;
        });

        let g2 = graph.clone();
        let a2 = res_a.clone();
        let b2 = res_b.clone();
        let task2 = tokio::spawn(async move {
            println!("Task2: 尝试获取资源 B");
            let _lock_b = b2.lock().await;
            g2.acquire("Task2", "ResourceB").await.ok();

            sleep(Duration::from_millis(50)).await;

            println!("Task2: 尝试获取资源 A");
            let _lock_a = a2.lock().await;
            g2.acquire("Task2", "ResourceA").await.ok();

            println!("Task2: 完成工作");
            g2.release("Task2", "ResourceB").await;
            g2.release("Task2", "ResourceA").await;
        });

        // 添加超时以避免真正的死锁
        tokio::select! {
            _ = task1 => println!("Task1 完成"),
            _ = task2 => println!("Task2 完成"),
            _ = sleep(Duration::from_secs(2)) => {
                println!("⚠️  检测到潜在死锁（超时）");
            }
        }

        println!("✓ 死锁检测完成");
    }
}

/// # 综合示例: 运行所有验证
pub async fn run_all_verifications() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║       形式化验证与证明                                   ║");
    println!("║       Formal Verification and Proofs                     ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    // 1. 不变式验证
    invariant_verification::demo_concurrent_transfers().await;

    // 2. 终止性证明
    termination_proofs::countdown_with_proof(5).await;

    let arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
    termination_proofs::binary_search_with_proof(arr, 7).await;

    // 3. 死锁检测
    deadlock_detection::demo_deadlock_scenario().await;

    println!("\n════════════════════════════════════════════════════════════");
    println!("所有验证完成！");
    println!("════════════════════════════════════════════════════════════\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_invariant() {
        invariant_verification::demo_concurrent_transfers().await;
    }

    #[tokio::test]
    async fn test_termination() {
        termination_proofs::countdown_with_proof(3).await;
    }

    #[tokio::test]
    async fn test_deadlock() {
        deadlock_detection::demo_deadlock_scenario().await;
    }
}
