//! 高级泛型编程模式
//! generic
//! - 泛型关联类型（GAT）深入分析
//! - generic associated type （GAT）analyze
//! - genericassociated type（GAT）深入analysis
//! - 高阶 trait 约束（HRTB）
//! - 类型族与类型级计算
//! - type and type
//! - 泛型特化概念与稳定版替代方案
//! - generic concept and

#![allow(dead_code)]

use std::{any::TypeId, marker::PhantomData, ops::Add};

// ============================================================================
// 1. GAT 深入分析
// ============================================================================

/// # 泛型关联类型（GAT）深入分析
/// # generic associated type （GAT）analyze
/// # genericassociated type（GAT）深入analysis
/// GAT 允许关联类型携带自己的泛型参数，解决了传统关联类型无法表达
/// GAT associated type generic parameter ，associated type express
/// 生命周期依赖的问题。
/// lifetime problem 。
pub struct GatDeepDive;

impl GatDeepDive {
    /// 解释 GAT 解决的核心问题
    /// explain GAT core problem
    /// explain GAT 解决coreproblem
    pub fn explain_gat_problem() -> &'static str {
        "在传统 Rust 中，关联类型不能有泛型参数。\
         这意味着无法表达像 `type Item<'a>` 这样的概念，\
         其中返回类型依赖于接收者的借用生命周期。\
         GAT 允许关联类型携带泛型参数，从而可以表达这种关系。"
    }

    /// 解释 GAT 与 HKT 的关系
    /// explain GAT and HKT
    /// explain GAT and HKT 关系
    pub fn gat_vs_hkt() -> &'static str {
        "HKT（高阶类型）允许类型构造函数作为参数，例如 `Vec` 本身（不应用参数）。\
         Rust 目前不支持完整的 HKT，但 GAT 提供了一种部分模拟：\
         通过将类型构造函数嵌入关联类型中，可以实现类似 HKT 的效果。\
         例如 `type Item<'a>` 可以被视为一个接受生命周期参数的'类型族'。"
    }
}

/// 借贷iterator trait — GAT 经典用例
/// 借贷迭代器允许返回的项借用迭代器本身，这是 GAT 解决的关键问题。
/// borrowing this ， GAT key problem 。
pub trait LendingIterator {
    /// 关联类型携带生命周期参数，允许返回值借用 `self`
    /// associated type lifetime parameter ，return value borrowing `self`
    type Item<'a>
    where
        Self: 'a;

    /// 每次Callborrow `self` lifetime `'a`
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

/// 字符串后缀迭代器 — 每次返回一个逐渐缩短的后缀
/// after — after
/// 该迭代器展示 GAT 如何允许返回的值借用迭代器内部状态。
/// this GAT borrowing inside state 。
pub struct SuffixIter<'s> {
    remaining: &'s str,
}

impl<'s> SuffixIter<'s> {
    /// 创建新的后缀迭代器
    /// after
    pub fn new(s: &'s str) -> Self {
        Self { remaining: s }
    }
}

impl<'s> LendingIterator for SuffixIter<'s> {
    type Item<'a>
        = &'a str
    where
        Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        if self.remaining.is_empty() {
            return None;
        }
        let result = self.remaining;
        self.remaining = &self.remaining[1..];
        Some(result)
    }
}

pub trait Collection<T> {
    /// 获取操作返回的元素类型，可以携带生命周期
    /// element type ，can lifetime
    type Item<'a>
    where
        Self: 'a;

    /// 根据索引获取元素
    /// according to element
    fn get<'a>(&'a self, index: usize) -> Option<Self::Item<'a>>;
}

/// 基于切片的集合实现
/// set
pub struct SliceCollection<'a, T> {
    data: &'a [T],
}

impl<'a, T> SliceCollection<'a, T> {
    /// 从切片创建集合
    /// from set
    pub fn new(data: &'a [T]) -> Self {
        Self { data }
    }
}

impl<'a, T: 'a> Collection<T> for SliceCollection<'a, T> {
    type Item<'b>
        = &'b T
    where
        Self: 'b;

    fn get<'b>(&'b self, index: usize) -> Option<Self::Item<'b>> {
        self.data.get(index)
    }
}

// ============================================================================
// 2. HRTB 模式
// ============================================================================

/// # 高阶 Trait 约束（HRTB）模式
/// # Trait （HRTB）
/// HRTB 允许 trait 约束对所有生命周期生效，使用 `for<'a>` 语法。
/// HRTB trait to all lifetime ， `for<'a>` 。
pub struct HrtbPatterns;

impl HrtbPatterns {
    /// 解释 `for<'a>` 语法
    /// explain `for<'a>`
    /// explain `for<'a>` 语法
    pub fn explain_for_syntax() -> &'static str {
        "`for<'a>` 语法表示约束对所有生命周期 'a 都成立。\
         例如 `for<'a> Fn(&'a T)` 表示该闭包可以接受任何生命周期的 `&T` 引用。"
    }

    /// 展示 `Fn(&T)` 与 `for<'a> Fn(&'a T)` 的区别
    /// `Fn(&T)` and `for<'a> Fn(&'a T)`
    /// display `Fn(&T)` and `for<'a> Fn(&'a T)` 区别
    /// `Fn(&T)` 会被编译器扩展为 `Fn(&'arg T)`，其中 `'arg` 是一个具体的生命周期。
    /// `Fn(&T)` is as `Fn(&'arg T)`，its in `'arg` volume lifetime 。
    /// 而 `for<'a> Fn(&'a T)` 表示闭包必须对所有生命周期都有效。
    /// while `for<'a> Fn(&'a T)` represent must to all lifetime effective 。
    pub fn demonstrate_fn_difference() -> &'static str {
        "`Fn(&T)` 隐式绑定到一个具体的生命周期，\
         而 `for<'a> Fn(&'a T)` 是高阶的，对所有生命周期都成立。\
         后者在需要将闭包传递给多个不同生命周期的上下文时至关重要。"
    }

    pub fn closure_elision_and_hrtb() -> &'static str {
        "Rust 的闭包生命周期消除规则会自动推断引用的生命周期。\
         但当闭包存储在结构体中或跨越函数边界时，\
         HRTB 可以显式地表达'适用于所有生命周期'的约束，\
         避免编译器将生命周期绑定到过窄的范围。"
    }

    /// explain HRTB in回调 API in必要性
    pub fn hrtb_in_callbacks() -> &'static str {
        "在回调 API 中，如果回调需要接受不同生命周期的引用，\
         就必须使用 HRTB。例如 `fn with_callback<F>(f: F)` \
         其中 `F: for<'a> Fn(&'a str)` 确保回调可以处理任何字符串切片。"
    }
}

/// Use HRTB 回调 API Example of
/// 该函数接受一个可以处理任何生命周期字符串引用的回调。
/// this function can lifetime reference 。
pub fn process_with_hrtb_callback<F>(items: &[String], mut callback: F)
where
    F: for<'a> FnMut(&'a str),
{
    for item in items {
        callback(item.as_str());
    }
}

pub fn handle_references<T, F>(items: &[T], mut f: F)
where
    F: for<'a> FnMut(&'a T),
{
    for item in items {
        f(item);
    }
}

// ============================================================================
// 3. 类型族
// ============================================================================

/// # 类型族与类型级计算
/// # type and type
/// 类型族是通过关联类型在编译期进行计算的模式。
/// type associated type in 。
pub struct TypeFamilies;

impl TypeFamilies {
    /// 解释关联类型构造函数模式
    /// explain associated type constructor
    pub fn explain_associated_type_constructors() -> &'static str {
        "关联类型构造函数模式使用 trait 的关联类型作为'类型级函数'。\
         例如 trait Family { type Member<T>; } 可以将具体类型映射到 \
         容器类型，如 `Vec<T>` 或 `Option<T>`。这是 GAT 实现类型族的核心技术。"
    }

    pub fn explain_phantom_state_machines() -> &'static str {
        "PhantomData 用于在类型系统中编码状态，而不占用运行时内存。\
         通过将状态作为泛型参数，可以在编译期确保状态转换的合法性，\
         实现零开销的抽象。"
    }

    pub fn explain_type_id_dispatch() -> &'static str {
        "`TypeId` 提供编译期类型的唯一标识，可以在运行时进行安全的类型比较。\
         结合 `Any` trait，可以实现类型安全的向下转换和基于类型的分发。"
    }
}

/// 类型族 trait — 展示关联类型构造函数模式
/// type trait — associated type constructor
/// 类似于类型级函数 `F(T) = Container<T>`。
/// similar to type function `F(T) = Container<T>`。
pub trait ContainerFamily {
    /// 关联类型构造函数 — 接受类型参数 T
    /// associated type constructor — type parameter T
    type Member<T>;

    /// 创建包含单个元素的容器
    /// element
    fn create<T>(value: T) -> Self::Member<T>;
}

/// Vec 类型族 — 将任意类型映射到 Vec
/// Vec type — will type to Vec
pub struct VecFamily;

impl ContainerFamily for VecFamily {
    type Member<T> = Vec<T>;

    fn create<T>(value: T) -> Self::Member<T> {
        vec![value]
    }
}

pub struct OptionFamily;

impl ContainerFamily for OptionFamily {
    type Member<T> = Option<T>;

    fn create<T>(value: T) -> Self::Member<T> {
        Some(value)
    }
}

/// 该模式确保只有处于特定状态的文件才能执行相应操作，
/// this state ，
/// 非法状态转换会在编译期被阻止。
/// state conversion in is 。
pub mod state_machine {
    use super::*;

    /// 未打开状态
    /// state
    /// 未Openstate
    pub struct Closed;
    /// 已打开可读状态
    /// state
    pub struct OpenForRead;
    /// 已打开可写状态
    /// state
    pub struct OpenForWrite;

    /// 带状态类型的文件句柄
    /// state type file handle
    /// 带statetypefile handle
    pub struct FileHandle<State> {
        /// 文件路径
        pub path: String,
        _state: PhantomData<State>,
    }

    impl FileHandle<Closed> {
        pub fn new(path: String) -> Self {
            Self {
                path,
                _state: PhantomData,
            }
        }

        /// 转换为可读状态
        /// conversion as state
        pub fn open_for_read(self) -> FileHandle<OpenForRead> {
            FileHandle {
                path: self.path,
                _state: PhantomData,
            }
        }

        /// 转换为可写状态
        /// conversion as state
        pub fn open_for_write(self) -> FileHandle<OpenForWrite> {
            FileHandle {
                path: self.path,
                _state: PhantomData,
            }
        }
    }

    impl FileHandle<OpenForRead> {
        pub fn read(&self) -> String {
            format!("Reading from {}", self.path)
        }

        /// 关闭文件，返回 Closed 状态
        /// ， Closed state
        pub fn close(self) -> FileHandle<Closed> {
            FileHandle {
                path: self.path,
                _state: PhantomData,
            }
        }
    }

    impl FileHandle<OpenForWrite> {
        pub fn write(&mut self, data: &str) -> String {
            format!("Writing '{}' to {}", data, self.path)
        }

        /// 关闭文件，返回 Closed 状态
        /// ， Closed state
        pub fn close(self) -> FileHandle<Closed> {
            FileHandle {
                path: self.path,
                _state: PhantomData,
            }
        }
    }
}

/// 类型安全的物理单位 — 使用泛型避免单位混淆
/// type — generic
/// 通过将单位类型作为泛型参数，在编译期阻止非法的物理运算。
/// will type as generic parameter ，in 。
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Quantity<T, Unit> {
    value: T,
    _unit: PhantomData<Unit>,
}

/// 长度单位：米
/// ：
pub struct Meter;
/// 时间单位：秒
/// time ：
pub struct Second;

impl<T: Copy> Quantity<T, Meter> {
    /// 创建以米为单位的量
    /// as
    pub fn new_meters(value: T) -> Self {
        Self {
            value,
            _unit: PhantomData,
        }
    }

    /// 获取数值
    pub fn value(&self) -> T {
        self.value
    }
}

impl<T: Copy + Add<Output = T>> Add for Quantity<T, Meter> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self::new_meters(self.value + other.value)
    }
}

impl<T: Copy> Quantity<T, Second> {
    /// 创建以秒为单位的量
    /// as
    pub fn new_seconds(value: T) -> Self {
        Self {
            value,
            _unit: PhantomData,
        }
    }

    /// 获取数值
    pub fn value(&self) -> T {
        self.value
    }
}

/// 编译期类型分发工具
/// type tool
pub struct TypeDispatcher;

impl TypeDispatcher {
    pub fn dispatch<T: 'static + std::any::Any>(_value: &T) -> &'static str {
        let type_id = TypeId::of::<T>();
        if type_id == TypeId::of::<i32>() {
            "i32"
        } else if type_id == TypeId::of::<String>() {
            "String"
        } else if type_id == TypeId::of::<&str>() {
            "&str"
        } else {
            "unknown"
        }
    }
}

// ============================================================================
// 4. 泛型特化概念
// ============================================================================

/// # 泛型特化概念（稳定版替代方案）
/// # generic concept （）
/// 该特性目前仅在 nightly 可用，但可以通过 blanket impl + marker trait 在稳定版模拟。
/// this feature before in nightly ，but can blanket impl + marker trait in 。
pub struct GenericSpecializationConcept;

impl GenericSpecializationConcept {
    /// 解释什么是特化
    /// explain
    pub fn explain_specialization() -> &'static str {
        "泛型特化允许为特定类型族提供优化的 trait 实现，\
         同时保留通用回退实现。例如为 `Copy` 类型提供 `clone_from` 的优化版本，\
         而非 `Copy` 类型则使用通用的基于字节拷贝的实现。"
    }

    /// 解释特化的当前状态
    /// explain when before state
    pub fn specialization_status() -> &'static str {
        "特化（specialization）目前仍是 nightly 特性，\
         部分功能通过 `default impl` 在 nightly 上可用。\
         在稳定版 Rust 中，需要使用替代模式来实现类似效果。"
    }

    /// 解释稳定版替代方案：blanket impl + marker trait
    pub fn stable_workaround() -> &'static str {
        "在稳定版 Rust 中，可以通过'blanket impl + marker trait'模式模拟特化：\
         1. 定义一个通用实现（blanket impl）\
         2. 定义 marker trait 标记特定类型族\
         3. 为实现了 marker trait 的类型提供专门实现\
         由于 Rust 的 orphan rules 和 trait 优先级，\
         具体实现会优先于 blanket impl。"
    }
}

/// 处理策略 trait — 用于演示稳定版特化模拟
/// strategy trait — demonstration
pub trait ProcessStrategy<T> {
    /// 处理值并返回描述字符串
    /// and describe
    fn process(value: T) -> String;
}

/// 默认处理策略标记
/// strategy mark
/// 默认Handlestrategymark
pub struct DefaultStrategy;

impl<T: std::fmt::Debug> ProcessStrategy<T> for DefaultStrategy {
    fn process(value: T) -> String {
        format!("default: {:?}", value)
    }
}

/// 快速处理标记 — 用于 `Copy` 类型
/// fast mark — `Copy` type
pub struct FastStrategy;

/// 在稳定版 Rust 中模拟特化效果。
/// in Rust in effect 。
impl<T: Copy + std::fmt::Debug> ProcessStrategy<T> for FastStrategy {
    fn process(value: T) -> String {
        format!("fast copy: {:?}", value)
    }
}

/// 通过类型参数区分的'模拟特化'模式
/// type parameter ''
/// 由调用者根据类型特性选择最优策略。
/// according to type feature strategy 。
pub trait OptimizedClone<T> {
    /// 优化的克隆操作
    /// optimization
    fn optimized_clone(value: &T) -> T;
}

/// 回退克隆标记 — 使用标准 Clone
/// mark — standard Clone
/// 回退Clonemark — Usestandard Clone
pub struct FallbackClone;

/// 通用回退：使用 Clone trait
/// ： Clone trait
/// 通用回退：Use Clone trait
impl<T: Clone> OptimizedClone<T> for FallbackClone {
    fn optimized_clone(value: &T) -> T {
        value.clone()
    }
}

/// Copy 优化标记 — 使用解引用拷贝
/// Copy optimization mark — reference
pub struct CopyOptimized;

/// Copy 优化：直接解引用拷贝
/// Copy optimization ：reference
/// 在稳定版中，通过为不同策略类型提供独立实现，
/// in in ，as strategy type ，
/// 调用者可以根据类型选择最优策略。
/// can according to type strategy 。
impl<T: Copy> OptimizedClone<T> for CopyOptimized {
    fn optimized_clone(value: &T) -> T {
        *value
    }
}

/// 由于 Rust 类型系统无法在稳定版自动选择最优实现，
/// Rust type system in ，
pub fn clone_value<T: Copy>(value: &T) -> T {
    CopyOptimized::optimized_clone(value)
}

pub fn clone_value_fallback<T: Clone>(value: &T) -> T {
    FallbackClone::optimized_clone(value)
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- GatDeepDive 测试 ---

    #[test]
    fn test_gat_deep_dive_explain() {
        assert!(!GatDeepDive::explain_gat_problem().is_empty());
        assert!(!GatDeepDive::gat_vs_hkt().is_empty());
    }

    #[test]
    fn test_lending_iterator() {
        let mut iter = SuffixIter::new("abc");
        assert_eq!(iter.next(), Some("abc"));
        assert_eq!(iter.next(), Some("bc"));
        assert_eq!(iter.next(), Some("c"));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_lending_iterator_empty() {
        let mut iter = SuffixIter::new("");
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_collection_trait() {
        let data = vec![10, 20, 30];
        let collection = SliceCollection::new(&data);
        assert_eq!(collection.get(0), Some(&10));
        assert_eq!(collection.get(2), Some(&30));
        assert_eq!(collection.get(3), None);
    }

    // --- HrtbPatterns 测试 ---

    #[test]
    fn test_hrtb_explain() {
        assert!(!HrtbPatterns::explain_for_syntax().is_empty());
        assert!(!HrtbPatterns::demonstrate_fn_difference().is_empty());
        assert!(!HrtbPatterns::closure_elision_and_hrtb().is_empty());
        assert!(!HrtbPatterns::hrtb_in_callbacks().is_empty());
    }

    #[test]
    fn test_process_with_hrtb_callback() {
        let items = vec!["hello".to_string(), "world".to_string()];
        let mut collected = Vec::new();
        process_with_hrtb_callback(&items, |s| collected.push(s.to_string()));
        assert_eq!(collected, vec!["hello", "world"]);
    }

    #[test]
    fn test_handle_references() {
        let items = vec![1, 2, 3];
        let mut sum = 0;
        handle_references(&items, |x| sum += *x);
        assert_eq!(sum, 6);
    }

    #[test]
    fn test_handle_references_strings() {
        let items = vec!["a", "b", "c"];
        let mut concat = String::new();
        handle_references(&items, |s| concat.push_str(s));
        assert_eq!(concat, "abc");
    }

    // --- TypeFamilies 测试 ---

    #[test]
    fn test_type_families_explain() {
        assert!(!TypeFamilies::explain_associated_type_constructors().is_empty());
        assert!(!TypeFamilies::explain_phantom_state_machines().is_empty());
        assert!(!TypeFamilies::explain_type_id_dispatch().is_empty());
    }

    #[test]
    fn test_container_family_vec() {
        let v: Vec<i32> = VecFamily::create(42);
        assert_eq!(v, vec![42]);
    }

    #[test]
    fn test_container_family_option() {
        let o: Option<i32> = OptionFamily::create(42);
        assert_eq!(o, Some(42));
    }

    #[test]
    fn test_state_machine_transitions() {
        use state_machine::*;

        let file = FileHandle::new("test.txt".to_string());
        let file = file.open_for_read();
        let content = file.read();
        assert_eq!(content, "Reading from test.txt");
        let file = file.close();
        assert_eq!(file.path, "test.txt");
    }

    #[test]
    fn test_state_machine_write() {
        use state_machine::*;

        let file = FileHandle::new("output.txt".to_string());
        let mut file = file.open_for_write();
        let result = file.write("hello");
        assert_eq!(result, "Writing 'hello' to output.txt");
        let file = file.close();
        assert_eq!(file.path, "output.txt");
    }

    #[test]
    fn test_quantity_meter() {
        let length = Quantity::<i32, Meter>::new_meters(100);
        assert_eq!(length.value(), 100);

        let length2 = Quantity::<i32, Meter>::new_meters(50);
        let total = length.add(length2);
        assert_eq!(total.value(), 150);
    }

    #[test]
    fn test_quantity_second() {
        let time = Quantity::<f64, Second>::new_seconds(9.58);
        assert!((time.value() - 9.58).abs() < f64::EPSILON);
    }

    #[test]
    fn test_type_dispatcher() {
        assert_eq!(TypeDispatcher::dispatch(&42i32), "i32");
        assert_eq!(TypeDispatcher::dispatch(&"hello".to_string()), "String");
        assert_eq!(TypeDispatcher::dispatch(&"hello"), "&str");
        assert_eq!(TypeDispatcher::dispatch(&2.5f64), "unknown");
    }

    // --- GenericSpecializationConcept 测试 ---

    #[test]
    fn test_specialization_concept_explain() {
        assert!(!GenericSpecializationConcept::explain_specialization().is_empty());
        assert!(!GenericSpecializationConcept::specialization_status().is_empty());
        assert!(!GenericSpecializationConcept::stable_workaround().is_empty());
    }

    #[test]
    fn test_fast_strategy() {
        let result = FastStrategy::process(42i32);
        assert!(result.contains("fast copy"));
        assert!(result.contains("42"));
    }

    #[test]
    fn test_default_strategy() {
        let result = DefaultStrategy::process(vec![1, 2, 3]);
        assert!(result.contains("default"));
        assert!(result.contains("1, 2, 3"));
    }

    #[test]
    fn test_optimized_clone_copy() {
        let x = 42i32;
        assert_eq!(CopyOptimized::optimized_clone(&x), 42);
    }

    #[test]
    fn test_optimized_clone_fallback() {
        let s = "hello".to_string();
        assert_eq!(FallbackClone::optimized_clone(&s), "hello");
    }

    #[test]
    fn test_clone_value_helpers() {
        let x = 100i32;
        assert_eq!(clone_value(&x), 100);

        let s = "test".to_string();
        assert_eq!(clone_value_fallback(&s), "test");
    }
}
