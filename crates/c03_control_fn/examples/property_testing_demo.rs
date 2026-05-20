//! 属性测试 (Property-Based Testing) 演示
//!
//! 使用 `proptest` 展示基于属性的测试方法：
//! - 基础属性：交换律、结合律、分配律
//! - 自定义策略：生成有效输入数据
//! - 状态机测试：模拟银行账户状态转换
//! - 回归测试：proptest 自动发现反例并持久化
//!
//! 运行: cargo test --example property_testing_demo -p c03_control_fn
//! 运行示例: cargo run --example property_testing_demo -p c03_control_fn

use proptest::prelude::*;
use std::collections::HashMap;

// ============================================================
// 1. 基础属性测试：数学定律
// ============================================================

/// 整数加法交换律: a + b == b + a
fn add_commutative(a: i32, b: i32) -> bool {
    a.wrapping_add(b) == b.wrapping_add(a)
}

/// 整数乘法分配律: a * (b + c) == a * b + a * c
fn mul_distributive(a: i32, b: i32, c: i32) -> bool {
    a.wrapping_mul(b.wrapping_add(c)) == a.wrapping_mul(b).wrapping_add(a.wrapping_mul(c))
}

/// 反转两次等于原序列
fn reverse_involution<T: Clone + PartialEq>(xs: &[T]) -> bool {
    let mut ys = xs.to_vec();
    ys.reverse();
    ys.reverse();
    ys == xs
}

// ============================================================
// 2. 自定义策略：生成有效数据
// ============================================================

/// 生成非空 ASCII 字符串
fn ascii_string_strategy() -> impl Strategy<Value = String> {
    "[a-zA-Z0-9_]{1,20}"
}

/// 生成有效邮箱地址（简化版）
fn email_strategy() -> impl Strategy<Value = String> {
    ("[a-z0-9]{3,10}", "[a-z]{3,8}", "[a-z]{2,4}")
        .prop_map(|(user, domain, tld)| format!("{}@{}.{}", user, domain, tld))
}

/// 生成有序向量（用于测试排序算法）
fn sorted_vec_strategy() -> impl Strategy<Value = Vec<i32>> {
    prop::collection::vec(any::<i32>(), 0..100).prop_map(|mut v| {
        v.sort();
        v
    })
}

// ============================================================
// 3. 被测代码：简易排序和解析
// ============================================================

fn bubble_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    for i in 0..n {
        for j in 0..n.saturating_sub(1).saturating_sub(i) {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
            }
        }
    }
}

fn parse_u32(s: &str) -> Option<u32> {
    s.parse().ok()
}

fn sanitize_username(input: &str) -> String {
    input
        .chars()
        .filter(|c| c.is_alphanumeric() || *c == '_')
        .take(20)
        .collect()
}

// ============================================================
// 4. 状态机测试：银行账户
// ============================================================

#[derive(Clone, Debug)]
struct BankAccount {
    balance: i64,
    transactions: Vec<String>,
}

impl BankAccount {
    fn new() -> Self {
        Self {
            balance: 0,
            transactions: Vec::new(),
        }
    }

    fn deposit(&mut self, amount: u64) {
        self.balance = self.balance.wrapping_add(amount as i64);
        self.transactions.push(format!("+{}", amount));
    }

    fn withdraw(&mut self, amount: u64) -> Result<(), &'static str> {
        if amount as i64 > self.balance {
            return Err("余额不足");
        }
        self.balance = self.balance.wrapping_sub(amount as i64);
        self.transactions.push(format!("-{}", amount));
        Ok(())
    }

    fn balance(&self) -> i64 {
        self.balance
    }
}

// ============================================================
// 5. proptest 测试定义
// ============================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// 测试加法交换律
    #[test]
    fn test_add_commutative(a in any::<i32>(), b in any::<i32>()) {
        prop_assert!(add_commutative(a, b));
    }

    /// 测试乘法分配律
    #[test]
    fn test_mul_distributive(a in any::<i32>(), b in any::<i32>(), c in any::<i32>()) {
        prop_assert!(mul_distributive(a, b, c));
    }

    /// 测试反转反转等于原序列
    #[test]
    fn test_reverse_involution(xs in prop::collection::vec(any::<i32>(), 0..50)) {
        prop_assert!(reverse_involution(&xs));
    }

    /// 测试冒泡排序结果有序
    #[test]
    fn test_bubble_sort_produces_sorted(
        mut xs in prop::collection::vec(any::<i32>(), 0..50)
    ) {
        bubble_sort(&mut xs);
        for i in 1..xs.len() {
            prop_assert!(xs[i - 1] <= xs[i]);
        }
    }

    /// 测试排序稳定性：结果长度不变
    #[test]
    fn test_sort_preserves_length(
        mut xs in prop::collection::vec(any::<i32>(), 0..50)
    ) {
        let original_len = xs.len();
        bubble_sort(&mut xs);
        prop_assert_eq!(xs.len(), original_len);
    }

    /// 测试解析与字符串化互为逆操作
    #[test]
    fn test_parse_u32_roundtrip(n in 0u32..=u32::MAX) {
        let s = n.to_string();
        prop_assert_eq!(parse_u32(&s), Some(n));
    }

    /// 测试用户名清理只保留合法字符
    #[test]
    fn test_sanitize_username_only_legal_chars(input in "[a-zA-Z0-9!@#$%^&*()]{0,30}") {
        let sanitized = sanitize_username(&input);
        prop_assert!(sanitized.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'));
        prop_assert!(sanitized.len() <= 20);
    }

    /// 测试自定义邮箱策略生成的邮箱包含 @
    #[test]
    fn test_email_contains_at(email in email_strategy()) {
        prop_assert!(email.contains('@'));
    }

    /// 测试有序向量策略确实有序
    #[test]
    fn test_sorted_vec_strategy(v in sorted_vec_strategy()) {
        for i in 1..v.len() {
            prop_assert!(v[i - 1] <= v[i]);
        }
    }
}

// ============================================================
// 6. 状态机 proptest
// ============================================================

#[derive(Clone, Debug)]
enum AccountAction {
    Deposit(u64),
    Withdraw(u64),
}

fn action_strategy() -> impl Strategy<Value = AccountAction> {
    prop_oneof![
        any::<u64>().prop_map(AccountAction::Deposit),
        any::<u64>().prop_map(AccountAction::Withdraw),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// 银行账户：存款后余额增加
    #[test]
    fn test_account_deposit_increases_balance(
        actions in prop::collection::vec(action_strategy(), 0..20)
    ) {
        let mut account = BankAccount::new();
        let mut expected_balance = 0i64;

        for action in actions {
            match action {
                AccountAction::Deposit(amount) => {
                    account.deposit(amount);
                    expected_balance = expected_balance.wrapping_add(amount as i64);
                }
                AccountAction::Withdraw(amount) => {
                    if amount as i64 <= expected_balance {
                        let result = account.withdraw(amount);
                        prop_assert!(result.is_ok());
                        expected_balance = expected_balance.wrapping_sub(amount as i64);
                    } else {
                        let result = account.withdraw(amount);
                        prop_assert!(result.is_err());
                    }
                }
            }
        }

        prop_assert_eq!(account.balance(), expected_balance);
    }
}

// ============================================================
// 7. 手动运行演示（非测试模式）
// ============================================================

fn demo_properties() {
    println!("=== 属性测试概念演示 ===\n");

    println!("1. 加法交换律: 3 + 5 == 5 + 3 => {}", add_commutative(3, 5));
    println!(
        "2. 乘法分配律: 2*(3+4) == 2*3+2*4 => {}",
        mul_distributive(2, 3, 4)
    );

    let xs = vec![1, 2, 3, 4, 5];
    println!(
        "3. 反转两次等于原序列: {:?} => {}",
        xs,
        reverse_involution(&xs)
    );

    let mut arr = vec![5, 2, 8, 1, 9];
    bubble_sort(&mut arr);
    println!("4. 冒泡排序: [5,2,8,1,9] -> {:?}", arr);

    println!(
        "5. 用户名清理: 'user@123!' -> '{}'",
        sanitize_username("user@123!")
    );

    println!(
        "\n✅ 概念演示完成。运行 `cargo test --example property_testing_demo -p c03_control_fn` \
         执行 proptest。"
    );
}

fn main() {
    demo_properties();
}
