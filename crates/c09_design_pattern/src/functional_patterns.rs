//! # 函数式编程模式
//! # function pattern
//!
//! Rust 支持多种函数式编程模式，包括高阶函数、闭包组合、
//! Rust functional ，function 、combination 、
//! 迭代器适配器链、Monoid 概念等。
//! adapter 、Monoid concept etc. 。

/// 高阶函数模式
/// Higher-order Function Pattern
///
/// 接受函数作为参数或返回函数的函数。
/// function as parameter or function function 。
pub struct HigherOrderFunctions;

impl HigherOrderFunctions {
    /// map-reduce 模式
    /// map-reduce pattern
    pub fn map_reduce<T, R>(
        items: &[T],
        map: impl Fn(&T) -> R,
        reduce: impl Fn(R, R) -> R,
    ) -> Option<R>
    where
        R: Clone,
    {
        items.iter().map(map).reduce(reduce)
    }

    /// 函数组合: (f ∘ g)(x) = f(g(x))
    /// function combination : (f ∘ g)(x) = f(g(x))
    pub fn compose<A, B, C>(f: impl Fn(B) -> C, g: impl Fn(A) -> B) -> impl Fn(A) -> C {
        move |x| f(g(x))
    }

    /// 部分应用（currying 概念）
    /// part application （currying concept ）
    pub fn add_n(n: i32) -> impl Fn(i32) -> i32 {
        move |x| x + n
    }
}

/// 迭代器适配器链模式
///
/// 通过链式调用构建惰性计算管道。
pub struct IteratorPipeline;

impl IteratorPipeline {
    /// 数据处理管道示例
    pub fn process_numbers(numbers: &[i32]) -> Vec<i32> {
        numbers
            .iter()
            .filter(|&&n| n > 0)
            .map(|&n| n * 2)
            .filter(|&n| n % 3 == 0)
            .collect()
    }

    /// 分组聚合
    /// grouping aggregation
    pub fn group_by_parity(numbers: &[i32]) -> (Vec<i32>, Vec<i32>) {
        numbers.iter().copied().partition(|n| n % 2 == 0)
    }

    /// 滑动窗口分析
    /// analyze
    pub fn sliding_average(numbers: &[i32], window: usize) -> Vec<f64> {
        numbers
            .windows(window)
            .map(|w| w.iter().sum::<i32>() as f64 / w.len() as f64)
            .collect()
    }
}

/// Monoid 模式概念
/// Monoid concept
///
/// Monoid 是带有结合律二元运算和单位元的代数结构。
/// Rust 中通过 trait 表达。
/// Rust in trait express 。
pub trait Monoid {
    /// 单位元
    fn identity() -> Self;
    /// 结合律运算
    fn combine(self, other: Self) -> Self;
}

impl Monoid for i32 {
    fn identity() -> Self {
        0
    }
    fn combine(self, other: Self) -> Self {
        self + other
    }
}

impl Monoid for String {
    fn identity() -> Self {
        String::new()
    }
    fn combine(mut self, other: Self) -> Self {
        self.push_str(&other);
        self
    }
}

/// 使用 Monoid 进行泛化折叠
pub fn fold_monoid<T: Monoid>(items: impl Iterator<Item = T>) -> T {
    items.fold(T::identity(), |acc, item| acc.combine(item))
}

/// Option/Result 组合子模式
/// Option/Result combinator pattern
/// functional error handling core tip 。
pub struct Combinators;

impl Combinators {
    /// 链式 Option 处理
    /// Option processing
    pub fn chain_options(x: Option<i32>) -> Option<i32> {
        x.map(|n| n * 2).filter(|&n| n > 10).or(Some(0))
    }

    /// Result 转换与收集
    /// Result conversion and
    pub fn parse_numbers(strings: &[&str]) -> Result<Vec<i32>, String> {
        strings
            .iter()
            .map(|s| s.parse::<i32>().map_err(|e| e.to_string()))
            .collect()
    }

    /// 早期返回模式（使用 ? 运算符）
    pub fn validate_and_compute(a: Option<i32>, b: Option<i32>) -> Option<i32> {
        let x = a?;
        let y = b?;
        Some(x * y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map_reduce() {
        let numbers = vec![1, 2, 3, 4, 5];
        let sum = HigherOrderFunctions::map_reduce(&numbers, |&x| x, |a, b| a + b);
        assert_eq!(sum, Some(15));
    }

    #[test]
    fn test_compose() {
        let double = |x: i32| x * 2;
        let add_one = |x: i32| x + 1;
        let composed = HigherOrderFunctions::compose(double, add_one);
        assert_eq!(composed(3), 8); // (3 + 1) * 2 = 8
    }

    #[test]
    fn test_add_n() {
        let add_5 = HigherOrderFunctions::add_n(5);
        assert_eq!(add_5(10), 15);
    }

    #[test]
    fn test_process_numbers() {
        let nums = vec![-2, 3, 4, 5, 6, -1];
        let result = IteratorPipeline::process_numbers(&nums);
        assert_eq!(result, vec![6, 12]); // 3*2=6, 6*2=12 (都 > 0 且 % 3 == 0)
    }

    #[test]
    fn test_group_by_parity() {
        let nums = vec![1, 2, 3, 4, 5, 6];
        let (even, odd) = IteratorPipeline::group_by_parity(&nums);
        assert_eq!(even, vec![2, 4, 6]);
        assert_eq!(odd, vec![1, 3, 5]);
    }

    #[test]
    fn test_sliding_average() {
        let nums = vec![1, 2, 3, 4, 5];
        let avg = IteratorPipeline::sliding_average(&nums, 3);
        assert_eq!(avg, vec![2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_monoid_i32() {
        let numbers = vec![1, 2, 3, 4, 5];
        let sum = fold_monoid(numbers.into_iter());
        assert_eq!(sum, 15);
    }

    #[test]
    fn test_monoid_string() {
        let words = vec!["Hello".to_string(), " ".to_string(), "World".to_string()];
        let sentence = fold_monoid(words.into_iter());
        assert_eq!(sentence, "Hello World");
    }

    #[test]
    fn test_parse_numbers() {
        let strings = vec!["1", "2", "3"];
        assert_eq!(Combinators::parse_numbers(&strings), Ok(vec![1, 2, 3]));

        let bad = vec!["1", "not_a_number", "3"];
        assert!(Combinators::parse_numbers(&bad).is_err());
    }

    #[test]
    fn test_validate_and_compute() {
        assert_eq!(
            Combinators::validate_and_compute(Some(3), Some(4)),
            Some(12)
        );
        assert_eq!(Combinators::validate_and_compute(None, Some(4)), None);
    }
}
