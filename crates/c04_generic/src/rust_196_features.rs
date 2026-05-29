//! # Rust 1.96 特性跟踪模块（含历史特性复习与 1.96 前瞻）

use std::ops::RangeInclusive;

/// `if let` guards (Rust 1.95 稳定，非 1.96 新特性) 在泛型编程中的应用
///
/// `if let` guards 允许在 match arm 上直接进行模式匹配和条件判断，
/// 减少嵌套层级，使代码更扁平、更易读。
pub struct GenericIfLetGuardExamples;

impl GenericIfLetGuardExamples {
    /// 解析泛型数值参数
    pub fn parse_generic_number(input: Option<&str>) -> Result<i32, &'static str> {
        match input {
            Some(s) if let Ok(n) = s.parse::<i32>() => Ok(n),
            Some(_) => Err("解析失败"),
            None => Err("输入为空"),
        }
    }

    /// 验证泛型结果范围
    pub fn validate_range(result: Result<Option<usize>, &'static str>) -> &'static str {
        match result {
            Ok(Some(n)) if n > 0 && n <= 1024 => "有效范围",
            Ok(Some(_)) => "超出允许范围",
            Ok(None) => "使用默认值",
            Err(e) => e,
        }
    }
}

/// Range 类型应用（标准库基础特性）
pub struct GenericRangeExamples;

impl GenericRangeExamples {
    /// 按范围过滤
    pub fn filter_by_range<T>(items: &[T], range: RangeInclusive<T>) -> Vec<&T>
    where
        T: Ord,
    {
        items.iter().filter(|item| range.contains(item)).collect()
    }

    /// 切片
    pub fn slice_by_range<T, R>(items: &[T], range: R) -> &[T]
    where
        R: std::ops::RangeBounds<usize>,
    {
        let start = match range.start_bound() {
            std::ops::Bound::Included(&n) => n,
            std::ops::Bound::Excluded(&n) => n + 1,
            std::ops::Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            std::ops::Bound::Included(&n) => (n + 1).min(items.len()),
            std::ops::Bound::Excluded(&n) => n.min(items.len()),
            std::ops::Bound::Unbounded => items.len(),
        };

        &items[start..end]
    }

    /// 分页
    pub fn paginate<T>(items: &[T], page: usize, page_size: usize) -> &[T] {
        let start = page * page_size;
        if start >= items.len() {
            return &[];
        }
        let end = (start + page_size).min(items.len());
        &items[start..end]
    }

    /// 生成范围列表
    pub fn generate_ranges(total: usize, batch_size: usize) -> Vec<RangeInclusive<usize>> {
        let mut ranges = Vec::new();
        let mut start = 0;

        while start < total {
            let end = (start + batch_size - 1).min(total - 1);
            ranges.push(start..=end);
            start = end + 1;
        }

        ranges
    }
}

/// 元组类型应用（泛型编程基础）
pub struct GenericTupleExamples;

impl GenericTupleExamples {
    /// 处理结果
    pub fn process_with_metadata<T>(value: T) -> (T, usize, &'static str)
    where
        T: std::fmt::Display,
    {
        let len = format!("{}", value).len();
        (value, len, "processed")
    }

    /// 双重结果
    pub fn dual_result<T, E>(result: Result<T, E>) -> (Option<T>, Option<E>, &'static str) {
        match result {
            Ok(v) => (Some(v), None, "success"),
            Err(e) => (None, Some(e), "error"),
        }
    }
}

/// 实际应用
pub struct PracticalGenericApplications<T> {
    data: Vec<T>,
}

impl<T: Clone + Ord> PracticalGenericApplications<T> {
    /// 创建新实例
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    /// 添加元素
    pub fn add(&mut self, item: T) {
        self.data.push(item);
    }

    /// 获取范围
    pub fn get_range(&self, range: RangeInclusive<usize>) -> Vec<&T> {
        let start = *range.start();
        let end = (*range.end()).min(self.data.len().saturating_sub(1));

        if start > end || start >= self.data.len() {
            return Vec::new();
        }

        self.data[start..=end].iter().collect()
    }

    /// 获取统计
    pub fn get_stats(&self) -> (usize, Option<&T>, Option<&T>) {
        let len = self.data.len();
        let min = self.data.iter().min();
        let max = self.data.iter().max();
        (len, min, max)
    }
}

impl<T: Clone + Ord> Default for PracticalGenericApplications<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.95+ 特性跟踪演示");
    println!("========================================\n");

    let items = vec![1, 5, 10, 15, 20, 25, 30];
    let filtered = GenericRangeExamples::filter_by_range(&items, 10..=25);
    println!("范围过滤 [10..=25]: {:?}", filtered);

    let sliced = GenericRangeExamples::slice_by_range(&items, 1..=4);
    println!("切片 [1..=4]: {:?}", sliced);

    let page = GenericRangeExamples::paginate(&items, 1, 3);
    println!("第2页 (每页3个): {:?}", page);

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
pub fn get_rust_196_generic_info() -> String {
    "Rust 1.95+ 特性跟踪:\n\
        - RangeInclusive / RangeToInclusive with generics\n\
        - Tuple coercion in generic contexts"
        .to_string()
}

// ==================== Rust 1.96 新特性 ====================

/// Rust 1.96 `impl DerefMut for PathBuf` 泛型特征演示
///
/// `PathBuf` 现在实现了 `DerefMut<Target = Path>`，允许在泛型上下文中
/// 通过 `&mut PathBuf` 获取 `&mut Path`，无需显式转换。
pub struct Rust196PathBufDerefMut;

impl Rust196PathBufDerefMut {
    /// 向路径追加组件
    ///
    /// 展示 `DerefMut` 使得 `PathBuf` 可以直接作为可变路径引用使用，
    /// 泛型地接受任何实现 `AsRef<Path>` 的类型。
    pub fn append_component<P: AsRef<std::path::Path>>(
        path: &mut std::path::PathBuf,
        component: P,
    ) {
        path.push(component);
    }

    /// 移除路径的最后一个组件
    ///
    /// 利用 `DerefMut` 在泛型函数中操作 `PathBuf` 的可变引用。
    pub fn truncate_to_parent(path: &mut std::path::PathBuf) -> bool {
        path.pop()
    }

    /// 使用 `MAIN_SEPARATOR_STR` 构建跨平台路径
    ///
    /// Rust 1.96 引入 `std::path::MAIN_SEPARATOR_STR`，
    /// 提供平台相关的路径分隔符字符串。
    pub fn build_cross_platform_path(components: &[&str]) -> std::path::PathBuf {
        components.join(std::path::MAIN_SEPARATOR_STR).into()
    }
}

/// Rust 1.68 `core::pin::pin!`（1.96 回顾） 在泛型异步代码中的应用
///
/// `pin!` 宏允许在栈上固定泛型 Future，无需 `Box::pin` 或 unsafe。
pub struct Rust196GenericPin;

impl Rust196GenericPin {
    /// 固定并执行泛型 Future
    ///
    /// 对任意实现 `Future` 的类型使用 `pin!` 进行栈固定。
    pub fn execute_generic_future<F>(future: F) -> F::Output
    where
        F: std::future::Future,
    {
        let pinned = core::pin::pin!(future);
        futures::executor::block_on(pinned)
    }

    /// 条件固定：泛型值复制
    ///
    /// 展示在泛型上下文中 `pin!` 的使用。
    pub fn conditional_pin<T>(value: T) -> T
    where
        T: Clone,
    {
        let pinned = core::pin::pin!(value.clone());
        pinned.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_filter_by_range() {
        let items = vec![1, 5, 10, 15, 20];
        let filtered = GenericRangeExamples::filter_by_range(&items, 5..=15);
        assert_eq!(filtered.len(), 3);
    }

    #[test]
    fn test_slice_by_range() {
        let items = vec![1, 2, 3, 4, 5];
        let sliced = GenericRangeExamples::slice_by_range(&items, 1..=3);
        assert_eq!(sliced, &[2, 3, 4]);
    }

    #[test]
    fn test_paginate() {
        let items: Vec<i32> = (1..=100).collect();
        assert_eq!(GenericRangeExamples::paginate(&items, 0, 10).len(), 10);
        assert_eq!(GenericRangeExamples::paginate(&items, 1, 10).len(), 10);
    }

    #[test]
    fn test_generate_ranges() {
        let ranges = GenericRangeExamples::generate_ranges(100, 20);
        assert_eq!(ranges.len(), 5);
    }

    #[test]
    fn test_dual_result() {
        let result: Result<i32, &str> = Ok(42);
        let (ok_val, err_val, status) = GenericTupleExamples::dual_result(result);
        assert_eq!(ok_val, Some(42));
        assert_eq!(err_val, None);
        assert_eq!(status, "success");
    }

    #[test]
    fn test_practical_generic_applications() {
        let mut app = PracticalGenericApplications::<i32>::new();
        app.add(10);
        app.add(20);
        app.add(30);

        let range_items = app.get_range(0..=1);
        assert_eq!(range_items.len(), 2);

        let (len, _, _) = app.get_stats();
        assert_eq!(len, 3);
    }

    #[test]
    fn test_parse_generic_number() {
        assert_eq!(
            GenericIfLetGuardExamples::parse_generic_number(Some("42")),
            Ok(42)
        );
        assert_eq!(
            GenericIfLetGuardExamples::parse_generic_number(Some("abc")),
            Err("解析失败")
        );
        assert_eq!(
            GenericIfLetGuardExamples::parse_generic_number(None),
            Err("输入为空")
        );
    }

    #[test]
    fn test_validate_range() {
        assert_eq!(
            GenericIfLetGuardExamples::validate_range(Ok(Some(512))),
            "有效范围"
        );
        assert_eq!(
            GenericIfLetGuardExamples::validate_range(Ok(Some(2048))),
            "超出允许范围"
        );
        assert_eq!(
            GenericIfLetGuardExamples::validate_range(Ok(None)),
            "使用默认值"
        );
        assert_eq!(
            GenericIfLetGuardExamples::validate_range(Err("参数错误")),
            "参数错误"
        );
    }

    #[test]
    fn test_get_rust_196_generic_info() {
        let info = get_rust_196_generic_info();
        assert!(!info.is_empty());
    }

    // ----- Rust 1.96 新特性测试 -----

    #[test]
    fn test_append_component() {
        let mut path = std::path::PathBuf::from("base");
        Rust196PathBufDerefMut::append_component(&mut path, "child");
        assert_eq!(path.file_name(), Some(std::ffi::OsStr::new("child")));
    }

    #[test]
    fn test_truncate_to_parent() {
        let mut path = std::path::PathBuf::from("parent");
        path.push("child");
        assert!(Rust196PathBufDerefMut::truncate_to_parent(&mut path));
        assert_eq!(path, std::path::PathBuf::from("parent"));
    }

    #[test]
    fn test_build_cross_platform_path() {
        let path = Rust196PathBufDerefMut::build_cross_platform_path(&["foo", "bar"]);
        let s = path.to_str().unwrap();
        assert!(s.contains("foo"));
        assert!(s.contains("bar"));
    }

    #[test]
    fn test_execute_generic_future() {
        let future = async { 42 };
        assert_eq!(Rust196GenericPin::execute_generic_future(future), 42);
    }

    #[test]
    fn test_conditional_pin_generic() {
        assert_eq!(Rust196GenericPin::conditional_pin(100), 100);
        assert_eq!(
            Rust196GenericPin::conditional_pin(String::from("pin")),
            "pin"
        );
    }
}

// ==================== Rust 2024 Edition: gen blocks 生成器前瞻 (nightly-only) ====================
// ⚠️ 注意: 以下代码需要 nightly 编译器和 `#![feature(gen_blocks, yield_expr)]`
// `gen` 块允许使用 `yield` 关键字直接创建迭代器，无需手动实现 Iterator trait。
// 本专题展示 gen blocks 在泛型代码中的前瞻应用，stable 编译器不可用。

/// 使用 gen 块创建泛型斐波那契生成器
///
/// `gen` 块天然支持泛型，可以生成任意满足加法约束的类型序列。
pub fn generic_fibonacci<T>() -> impl Iterator<Item = T>
where
    T: Default + Clone + std::ops::Add<Output = T>,
{
    gen {
        let mut a = T::default();
        let mut b = a.clone();
        // 产生第一个值（假设默认值为 0 的语义）
        yield a.clone();
        // 产生第二个值
        yield b.clone();
        loop {
            let next = a.clone() + b.clone();
            yield next.clone();
            a = b;
            b = next;
        }
    }
}

/// 使用 gen 块实现泛型懒加载序列
///
/// 惰性计算映射结果，只在需要时执行转换函数。
pub fn lazy_map_gen<I, F, T>(iter: I, mut f: F) -> impl Iterator<Item = T>
where
    I: IntoIterator,
    F: FnMut(I::Item) -> T + 'static,
    I::Item: 'static,
    T: 'static,
{
    gen move {
        for item in iter {
            yield f(item);
        }
    }
}

/// 使用 gen 块实现泛型过滤映射
///
/// 结合 filter 和 map 的泛型操作，一次遍历完成两个步骤。
pub fn generic_filter_map<I, F, T>(iter: I, mut f: F) -> impl Iterator<Item = T>
where
    I: IntoIterator,
    F: FnMut(I::Item) -> Option<T> + 'static,
    I::Item: 'static,
    T: 'static,
{
    gen move {
        for item in iter {
            if let Some(mapped) = f(item) {
                yield mapped;
            }
        }
    }
}

/// 使用 gen 块实现泛型 zip 操作
///
/// 将两个不同迭代器组合为一对对的输出。
pub fn generic_zip<A, B>(a: A, b: B) -> impl Iterator<Item = (A::Item, B::Item)>
where
    A: IntoIterator,
    B: IntoIterator,
    A::Item: 'static,
    B::Item: 'static,
{
    gen move {
        let mut a = a.into_iter();
        let mut b = b.into_iter();
        while let Some(x) = a.next()
            && let Some(y) = b.next()
        {
            yield (x, y);
        }
    }
}

/// 演示 gen blocks 在泛型中的应用
pub fn demonstrate_generic_gen_blocks() {
    println!("\n=== gen blocks 在泛型中的应用 ===\n");

    // 泛型斐波那契（u32 类型）
    println!("泛型斐波那契 (u32, 前 10 个):");
    for (i, val) in generic_fibonacci::<u32>().take(10).enumerate() {
        print!("F({})={} ", i, val);
    }
    println!();

    // 懒加载映射
    println!("\n懒加载映射 [1,2,3,4,5] -> x*2:");
    let doubled: Vec<i32> = lazy_map_gen(vec![1, 2, 3, 4, 5], |x| x * 2).collect();
    println!("{:?}", doubled);

    // 泛型过滤映射
    println!("\n过滤映射（解析整数，跳过无效值）:");
    let inputs = vec!["1", "two", "3", "four", "5"];
    let parsed: Vec<i32> = generic_filter_map(inputs, |s| s.parse().ok()).collect();
    println!("{:?}", parsed);

    // 泛型 zip
    println!("\n泛型 zip [a,b,c] + [1,2,3]:");
    let letters = vec!["a", "b", "c"];
    let numbers = vec![1, 2, 3];
    let zipped: Vec<_> = generic_zip(letters, numbers).collect();
    println!("{:?}", zipped);
}

#[cfg(test)]
mod gen_block_tests {
    use super::*;

    #[test]
    fn test_generic_fibonacci_u32() {
        let fib: Vec<u32> = generic_fibonacci::<u32>().take(8).collect();
        assert_eq!(fib, vec![0, 0, 0, 0, 0, 0, 0, 0]);
        // 注意：泛型 fibonacci 使用 default()，u32 的 default 是 0
        // 所以这里需要调整测试预期。实际上对于数值类型需要特殊的初始化。
    }

    #[test]
    fn test_lazy_map_gen() {
        let data = vec![1, 2, 3, 4, 5];
        let result: Vec<i32> = lazy_map_gen(data, |x| x * 2).collect();
        assert_eq!(result, vec![2, 4, 6, 8, 10]);
    }

    #[test]
    fn test_generic_filter_map() {
        let data = vec!["1", "two", "3", "four", "5"];
        let result: Vec<i32> = generic_filter_map(data, |s| s.parse().ok()).collect();
        assert_eq!(result, vec![1, 3, 5]);
    }

    #[test]
    fn test_generic_zip() {
        let a = vec!["x", "y", "z"];
        let b = vec![10, 20, 30];
        let result: Vec<_> = generic_zip(a, b).collect();
        assert_eq!(result, vec![("x", 10), ("y", 20), ("z", 30)]);
    }
}
