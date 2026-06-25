//! Verus 函数合约 / 数据不变式示例
//!
//! 本模块展示如何用 Verus 的 `requires` / `ensures` / `invariant`
//! 对类型系统相关函数进行形式化验证。
//!
//! Verus 是 Rust 的形式化验证工具链，使用 `verus! { ... }` 宏扩展
//! Rust 语法以支持规范（spec）、执行（exec）、证明（proof）三模式。
//! 这些示例仅在 `verus` 构建配置下编译，常规 `cargo build/test` 会跳过。
//!
//! 权威来源：
//! - [Verus GitHub](https://github.com/verus-lang/verus)
//! - [Verus Tutorial](https://verus-lang.github.io/verus/guide/)

#[cfg(verus)]
use vstd::prelude::*;

/// 示例 1：基本函数合约 —— 严格递增函数
///
/// 前置条件 `x > 0` 保证结果 `y` 满足 `y > x`。
#[cfg(verus)]
verus! {
    fn increment(x: u32) -> (y: u32)
        requires x > 0,
        ensures y > x,
    {
        x + 1
    }
}

/// 示例 2：类型系统常见模式 —— 数组元素上界保证
///
/// 若数组所有元素均不超过 `bound`，则最大值也不超过 `bound`。
#[cfg(verus)]
verus! {
    fn max_bounded(s: &[i32], bound: i32) -> (m: i32)
        requires s.len() > 0,
        requires forall|i: int| 0 <= i < s.len() ==> s[i] <= bound,
        ensures m <= bound,
        ensures exists|i: int| 0 <= i < s.len() && s[i] == m,
    {
        let mut max = s[0];
        let mut idx = 0;

        let ghost init_len = s.len();

        while idx < s.len()
            invariant
                0 <= idx <= s.len(),
                forall|i: int| 0 <= i < idx ==> s[i] <= max,
                exists|i: int| 0 <= i < idx ==> s[i] == max,
                max <= bound,
        {
            if s[idx] > max {
                max = s[idx];
            }
            idx += 1;
        }

        max
    }
}

/// 示例 3：枚举变体不变式 —— Option 映射保持 Some
///
/// 若输入为 `Some`，则经过非破坏式映射后输出仍为 `Some`。
#[cfg(verus)]
verus! {
    fn option_map_inc(x: Option<u32>) -> (y: Option<u32>)
        requires x.is_some(),
        ensures y.is_some(),
        ensures y.unwrap() > x.unwrap(),
    {
        match x {
            Some(v) => Some(v + 1),
            None => unreachable(), // 前置条件排除 None
        }
    }
}

/// 示例 4：结构体不变式 —— 范围类型保证 low <= high
///
/// 利用 Verus 的 `invariant` 字段约束，在构造时保证范围合法性。
#[cfg(verus)]
verus! {
    struct Range {
        low: i32,
        high: i32,
    }

    impl Range {
        /// 构造范围，要求 low <= high
        fn new(low: i32, high: i32) -> (r: Range)
            requires low <= high,
            ensures r.low == low && r.high == high,
        {
            Range { low, high }
        }

        /// 判断值是否在范围内
        fn contains(&self, v: i32) -> (b: bool)
            ensures b == (self.low <= v && v <= self.high),
        {
            self.low <= v && v <= self.high
        }
    }
}

/// 常规 Rust 下提供占位文档，避免模块为空。
#[cfg(not(verus))]
pub struct VerusPlaceholder;
