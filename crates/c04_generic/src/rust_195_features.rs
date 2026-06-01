//! Rust 1.95 特性 —— 泛型编程场景
//! Rust 1.95 feature —— generic scenario
//! # 概述
//! # Overview
//! #
//! - **`cfg_select!`** — 跨平台泛型特化选择
//! - **`cfg_select!`** — platform generic

// ============================================================================
// 1. cfg_select! 与泛型特化
// ============================================================================

/// # 跨平台泛型特化
/// # Cross-platform Generic Specialization
/// # platform generic
pub struct GenericCfgSelectExamples;

impl GenericCfgSelectExamples {
    /// 平台特定的对齐要求（用于泛型缓冲区分配）
    /// platform to （generic buffering ）
    pub const DEFAULT_ALIGNMENT: usize = cfg_select! {
        target_arch = "x86_64" => 64,   // AVX-512 cache line
        target_arch = "aarch64" => 64,  // ARM cache line
        target_arch = "arm" => 32,
        target_arch = "riscv64" => 64,
        target_arch = "riscv32" => 32,
        _ => 16,
    };
    /// 平台是否支持原子 64 位操作（影响泛型原子选择）
    /// platform 64 （impact generic ）
    pub const HAS_ATOMIC_64: bool = cfg_select! {
        target_pointer_width = "64" => true,
        target_arch = "arm" => false, // 需 armv7-a+ 才支持
        _ => true,
    };
    /// 平台特定的指针宽度（用于泛型索引类型）
    /// platform pointer （generic type ）
    pub const POINTER_WIDTH_BITS: usize = cfg_select! {
        target_pointer_width = "64" => 64,
        target_pointer_width = "32" => 32,
        _ => 16,
    };
}

// ============================================================================
// 2. bool: TryFrom<integer> — 配置标志解析
// ============================================================================

/// # 泛型配置解析
/// # Generic Configuration Parsing
/// # generic
pub struct GenericBoolParseExamples;

impl GenericBoolParseExamples {
    pub fn parse_flag<T: TryInto<bool>>(value: T) -> Result<bool, &'static str> {
        value.try_into().map_err(|_| "invalid boolean flag")
    }

    /// 批量解析配置标志
    /// mark
    pub fn parse_flags<T: TryInto<bool> + Copy>(values: &[T]) -> Result<Vec<bool>, &'static str> {
        values.iter().copied().map(Self::parse_flag).collect()
    }
}

// ============================================================================
// 3. if let guards — 泛型约束下的模式匹配
// ============================================================================

/// # 泛型算法中的条件模式匹配
/// # Conditional Pattern Matching in Generic Algorithms
/// # generic algorithm in condition
pub struct GenericIfLetGuardExamples;

impl GenericIfLetGuardExamples {
    /// 泛型值过滤：仅处理可解析为特定范围的值
    /// generic ：as scope
    pub fn filter_in_range<T: std::str::FromStr + PartialOrd>(
        items: &[&str],
        min: T,
        max: T,
    ) -> Vec<T>
    where
        <T as std::str::FromStr>::Err: std::fmt::Debug,
    {
        items
            .iter()
            .filter_map(|s| match s.parse::<T>() {
                Ok(v) if v >= min && v <= max => Some(v),
                _ => None,
            })
            .collect()
    }

    /// 泛型结果扁平化：仅保留满足条件的 Ok 值
    /// generic result ：condition Ok
    pub fn filter_ok_results<T, E>(
        results: Vec<Result<T, E>>,
        predicate: impl Fn(&T) -> bool,
    ) -> Vec<T> {
        results
            .into_iter()
            .filter_map(|r| match r {
                Ok(v) if predicate(&v) => Some(v),
                _ => None,
            })
            .collect()
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cfg_select_alignment() {
        assert!(GenericCfgSelectExamples::DEFAULT_ALIGNMENT >= 16);
        assert!(GenericCfgSelectExamples::POINTER_WIDTH_BITS >= 32);
    }

    #[test]
    fn test_bool_parse() {
        assert_eq!(GenericBoolParseExamples::parse_flag(1u8), Ok(true));
        assert_eq!(GenericBoolParseExamples::parse_flag(0u8), Ok(false));
        assert!(GenericBoolParseExamples::parse_flag(2u8).is_err());
    }

    #[test]
    fn test_filter_in_range() {
        let items = vec!["10", "20", "abc", "30", "5"];
        let result: Vec<i32> = GenericIfLetGuardExamples::filter_in_range(&items, 10, 25);
        assert_eq!(result, vec![10, 20]);
    }

    #[test]
    fn test_filter_ok_results() {
        let results = vec![Ok(10), Ok(20), Err("err"), Ok(5)];
        let filtered = GenericIfLetGuardExamples::filter_ok_results(results, |v| *v >= 10);
        assert_eq!(filtered, vec![10, 20]);
    }
}

// ============================================================================
// Real Rust 1.95 Features — Generics, Traits
// ============================================================================

/// Demonstrates real Rust 1.95 features related to generics and traits.
pub struct RealRust195Features;

impl RealRust195Features {
    /// `AsyncFn` trait bounds with async closure (Rust 1.95)
    pub async fn apply_async_generic<F>(f: F, input: i32) -> i32
    where
        F: AsyncFn(i32) -> i32,
    {
        f(input).await
    }

    /// `gen` blocks — lazy iterator generation (Rust 1.95 nightly)
    pub fn gen_block_demo() -> impl Iterator<Item = i32> {
        gen {
            for i in 0..5 {
                yield i * 2;
            }
        }
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_apply_async_generic() {
        let result = futures::executor::block_on(RealRust195Features::apply_async_generic(
            async |x| x * 2,
            21,
        ));
        assert_eq!(result, 42);
    }

    #[test]
    fn test_gen_block_demo() {
        let values: Vec<i32> = RealRust195Features::gen_block_demo().collect();
        assert_eq!(values, vec![0, 2, 4, 6, 8]);
    }
}
