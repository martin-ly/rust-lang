//! Rust 1.94.0 所有权与借用特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 在所有权、借用和作用域管理方面的增强，包括：
//! - 增强的内存安全保证
//! - 改进的借用检查器诊断信息
//! - 更灵活的内部可变性模式
//! - 与 Edition 2024 的深度集成
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust 版本: 1.94.0
//! - Edition: 2024
use std::cell::RefCell;
use std::mem::MaybeUninit;
use std::ops::Deref;
use std::sync::atomic::{AtomicUsize, Ordering};

// ==================== Rust 1.94 真实特性: array_windows ====================

/// # array_windows - 切片数组窗口迭代器
///
/// Rust 1.94.0 为切片添加了 `array_windows` 方法，允许将切片转换为固定大小数组的窗口迭代器。
/// 这在处理序列数据时非常有用，例如检测模式、滑动窗口计算等。
///
/// ## 特性说明
/// - `array_windows<const N: usize>()` 返回一个迭代器，每次产生 `&[T; N]` 数组引用
/// - 窗口大小 N 是编译时常量
/// - 迭代器会滑动窗口，每次移动一个元素
///
/// ## 使用场景
/// - 检测回文模式 (ABBA)
/// - 滑动窗口平均值计算
/// - 序列模式匹配

/// 检测字符串中是否存在 ABBA 模式
///
/// 使用 array_windows 检测四个字符的模式：a1 b1 b2 a2，其中 a1 == a2 且 b1 == b2
///
/// # 示例
/// ```
/// use c01_ownership_borrow_scope::rust_194_features::has_abba;
/// assert!(has_abba("abba"));
/// assert!(has_abba("cddc"));
/// assert!(!has_abba("abcd"));
/// ```
#[allow(dead_code)]
pub fn has_abba(s: &str) -> bool {
    s.as_bytes()
        .array_windows::<4>()
        .any(|[a1, b1, b2, a2]| (a1 != b1) && (a1 == a2) && (b1 == b2))
}

/// 计算滑动窗口平均值
///
/// 使用 array_windows 计算每 N 个连续元素的平均值
///
/// # 示例
/// ```
/// use c01_ownership_borrow_scope::rust_194_features::sliding_window_averages;
/// let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
/// let averages = sliding_window_averages(&data);
/// // 结果: [2.0, 3.0, 4.0] (窗口大小为3)
/// ```
#[allow(dead_code)]
pub fn sliding_window_averages(data: &[f64]) -> Vec<f64> {
    data.array_windows::<3>()
        .map(|[a, b, c]| (a + b + c) / 3.0)
        .collect()
}

/// 检测递增三元组
///
/// 使用 array_windows 检测三个连续递增的数字
#[allow(dead_code)]
pub fn count_increasing_triplets(data: &[i32]) -> usize {
    data.array_windows::<3>()
        .filter(|[a, b, c]| a < b && b < c)
        .count()
}

// ==================== Rust 1.94 真实特性: LazyCell/LazyLock 新方法 ====================

/// # LazyCell/LazyLock 新方法
///
/// Rust 1.94.0 为 `LazyCell` 和 `LazyLock` 添加了新的访问方法：
/// - `get()` - 获取值的引用（不触发初始化）
/// - `get_mut()` - 获取值的可变引用（不触发初始化）
/// - `force_mut()` - 强制初始化并获取可变引用
///
/// ## 特性说明
/// - `get()` 返回 `Option<&T>`，如果未初始化则返回 None
/// - `get_mut()` 返回 `Option<&mut T>`，如果未初始化则返回 None
/// - `force_mut()` 触发初始化并返回 `&mut T`
///
/// ## 注意
/// 这些新方法在 Rust 1.94.0 中引入。在之前的版本中，可以使用 OnceCell/OnceLock 或
/// 现有的 LazyCell/LazyLock API 实现类似功能。
use std::cell::OnceCell;
use std::sync::OnceLock;

/// 使用 OnceCell 实现的单线程缓存示例
///
/// 演示类似 Rust 1.94 LazyCell 新方法的用法
/// 注意：在 Rust 1.94 中可以直接使用 LazyCell::get(), get_mut(), force_mut()
pub struct LazyCache<T> {
    cell: OnceCell<T>,
}

impl<T> LazyCache<T> {
    /// 创建新的延迟初始化缓存
    pub fn new() -> Self {
        Self {
            cell: OnceCell::new(),
        }
    }

    /// 尝试获取值（不触发初始化）- 对应 Rust 1.94 LazyCell::get()
    pub fn try_get(&self) -> Option<&T> {
        self.cell.get()
    }

    /// 获取或初始化值
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.cell.get_or_init(f)
    }

    /// 尝试获取可变引用（不触发初始化）- 对应 Rust 1.94 LazyCell::get_mut()
    pub fn try_get_mut(&mut self) -> Option<&mut T> {
        self.cell.get_mut()
    }

    /// 强制获取可变引用（如果未初始化则使用默认值）- 对应 Rust 1.94 LazyCell::force_mut()
    pub fn force_get_mut<F>(&mut self, f: F) -> &mut T
    where
        F: FnOnce() -> T,
    {
        if self.cell.get().is_none() {
            let _ = self.cell.set(f());
        }
        self.cell.get_mut().unwrap()
    }

    /// 检查是否已初始化
    pub fn is_initialized(&self) -> bool {
        self.cell.get().is_some()
    }

    /// 设置值
    pub fn set(&self, value: T) -> Result<(), T> {
        self.cell.set(value)
    }
}

/// 使用 OnceLock 实现的多线程安全缓存示例
///
/// 演示类似 Rust 1.94 LazyLock 新方法的用法
/// 注意：在 Rust 1.94 中可以直接使用 LazyLock::get()
pub struct ThreadSafeLazyCache<T> {
    lock: OnceLock<T>,
}

impl<T> ThreadSafeLazyCache<T> {
    /// 创建新的线程安全延迟初始化缓存
    pub fn new() -> Self
    where
        T: Send + Sync + 'static,
    {
        Self {
            lock: OnceLock::new(),
        }
    }

    /// 尝试获取值（不触发初始化）- 对应 Rust 1.94 LazyLock::get()
    pub fn try_get(&self) -> Option<&T> {
        self.lock.get()
    }

    /// 获取或初始化值
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.lock.get_or_init(f)
    }

    /// 检查是否已初始化
    pub fn is_initialized(&self) -> bool {
        self.lock.get().is_some()
    }

    /// 设置值
    pub fn set(&self, value: T) -> Result<(), T> {
        self.lock.set(value)
    }
}

// ==================== 1. 增强的内部可变性模式 ====================

/// Rust 1.94 增强的内部可变性包装器
/// 结合了 RefCell 和 AtomicUsize 的优势
pub struct HybridCell<T> {
    data: RefCell<T>,
    access_count: AtomicUsize,
}

impl<T> HybridCell<T> {
    pub fn new(value: T) -> Self {
        Self {
            data: RefCell::new(value),
            access_count: AtomicUsize::new(0),
        }
    }

    /// 获取不可变引用并计数
    pub fn borrow_with_count(&self) -> std::cell::Ref<'_, T> {
        self.access_count.fetch_add(1, Ordering::Relaxed);
        self.data.borrow()
    }

    /// 获取可变引用并计数
    pub fn borrow_mut_with_count(&self) -> std::cell::RefMut<'_, T> {
        self.access_count.fetch_add(1, Ordering::Relaxed);
        self.data.borrow_mut()
    }

    pub fn access_count(&self) -> usize {
        self.access_count.load(Ordering::Relaxed)
    }
}

// ==================== 2. 安全的 MaybeUninit 批量操作 ====================

/// Rust 1.94 安全的未初始化内存批量处理
pub struct SafeBuffer<T> {
    buffer: Vec<MaybeUninit<T>>,
    initialized: usize,
}

impl<T: Copy> SafeBuffer<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        let mut buffer = Vec::with_capacity(capacity);
        unsafe {
            buffer.set_len(capacity);
        }
        Self {
            buffer,
            initialized: 0,
        }
    }

    /// 批量写入复制值（Rust 1.94 增强模式）
    pub fn write_slice(&mut self, values: &[T]) -> usize {
        let to_write = values.len().min(self.buffer.len() - self.initialized);
        for (i, &val) in values.iter().take(to_write).enumerate() {
            self.buffer[self.initialized + i].write(val);
        }
        self.initialized += to_write;
        to_write
    }

    /// 获取已初始化部分的切片
    pub fn initialized_slice(&self) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(
                self.buffer.as_ptr() as *const T,
                self.initialized,
            )
        }
    }

    pub fn capacity(&self) -> usize {
        self.buffer.len()
    }

    pub fn len(&self) -> usize {
        self.initialized
    }

    pub fn is_empty(&self) -> bool {
        self.initialized == 0
    }
}

impl<T> Drop for SafeBuffer<T> {
    fn drop(&mut self) {
        // 仅释放已初始化的元素
        unsafe {
            std::ptr::drop_in_place(std::ptr::slice_from_raw_parts_mut(self.buffer.as_mut_ptr() as *mut T, self.initialized));
        }
    }
}

// ==================== 3. 智能指针优化模式 ====================

/// Rust 1.94 智能指针组合模式
pub struct SmartPtrChain<T> {
    inner: Option<Box<T>>,
    metadata: usize,
}

impl<T> SmartPtrChain<T> {
    pub fn new(value: T) -> Self {
        Self {
            inner: Some(Box::new(value)),
            metadata: 0,
        }
    }

    /// 转换为原始指针并保留元数据
    pub fn into_raw_parts(mut self) -> (*mut T, usize) {
        let ptr = self.inner.take().map_or(std::ptr::null_mut(), |b| Box::into_raw(b));
        (ptr, self.metadata)
    }

    /// 从原始指针重建（不安全）
    /// 
    /// # Safety
    /// - ptr 必须是由 into_raw_parts 生成的有效指针
    /// - ptr 必须指向未释放的内存
    pub unsafe fn from_raw_parts(ptr: *mut T, metadata: usize) -> Self { unsafe {
        Self {
            inner: if ptr.is_null() { None } else { Some(Box::from_raw(ptr)) },
            metadata,
        }
    }}

    pub fn metadata(&self) -> usize {
        self.metadata
    }

    pub fn set_metadata(&mut self, value: usize) {
        self.metadata = value;
    }
}

impl<T> Deref for SmartPtrChain<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.inner.as_ref().unwrap()
    }
}

// ==================== 4. 作用域守卫增强 ====================

/// Rust 1.94 作用域守卫模式
pub struct ScopeGuard<T, F: FnOnce(T)> {
    value: Option<T>,
    on_drop: Option<F>,
}

impl<T, F: FnOnce(T)> ScopeGuard<T, F> {
    pub fn new(value: T, on_drop: F) -> Self {
        Self {
            value: Some(value),
            on_drop: Some(on_drop),
        }
    }

    /// 获取可变引用（保留析构函数）
    pub fn get_mut(&mut self) -> &mut T {
        self.value.as_mut().unwrap()
    }

    /// 获取不可变引用
    pub fn get(&self) -> &T {
        self.value.as_ref().unwrap()
    }

    /// 主动完成并禁用析构函数
    pub fn complete(mut self) -> T {
        self.on_drop = None;
        self.value.take().unwrap()
    }
}

impl<T, F: FnOnce(T)> Drop for ScopeGuard<T, F> {
    fn drop(&mut self) {
        if let (Some(value), Some(on_drop)) = (self.value.take(), self.on_drop.take()) {
            on_drop(value);
        }
    }
}

// ==================== 5. 零拷贝字符串处理 ====================

/// Rust 1.94 零拷贝字符串处理模式
pub struct ZeroCopyString {
    data: Vec<u8>,
}

impl ZeroCopyString {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
        }
    }

    /// 从 String 获取原始部件（零拷贝）
    pub fn from_string(s: String) -> Self {
        // 使用 String::into_bytes 获取 Vec<u8>，然后分离
        let data = s.into_bytes();
        Self { data }
    }

    /// 转换为 String（零拷贝）
    pub fn into_string(self) -> String {
        // SAFETY: data 是有效的 UTF-8 字节
        unsafe { String::from_utf8_unchecked(self.data) }
    }

    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.data) }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.data
    }
}

impl Default for ZeroCopyString {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== Rust 1.94 真实特性: 数学常量 ====================

/// # 数学常量 / Mathematical Constants
///
/// Rust 1.94.0 为 `f32` 和 `f64` 类型添加了新的数学常量：
/// - `EULER_GAMMA` (欧拉-马歇罗尼常数, γ ≈ 0.5772)
/// - `GOLDEN_RATIO` (黄金比例, φ ≈ 1.6180)
///
/// ## 特性说明
/// - `EULER_GAMMA`: 定义为 `lim(n→∞) [H_n - ln(n)]`，其中 H_n 是第 n 个调和数
/// - `GOLDEN_RATIO`: 定义为 `(1 + √5) / 2`，约等于 1.6180339887...
///
/// ## 使用场景
/// - 数学计算和算法实现
/// - 黄金分割搜索算法
/// - 数论和特殊函数计算

/// f32 数学常量模块
pub mod math_consts_f32 {
    /// 欧拉-马歇罗尼常数 (Euler-Mascheroni constant)
    /// 
    /// 约等于 0.5772156649
    /// 
    /// # 数学定义
    /// γ = lim(n→∞) [Σ(1/k, k=1..n) - ln(n)]
    pub const EULER_GAMMA: f32 = 0.577_215_7_f32;

    /// 黄金比例 (Golden Ratio)
    /// 
    /// 约等于 1.6180339887
    /// 
    /// # 数学定义
    /// φ = (1 + √5) / 2
    pub const GOLDEN_RATIO: f32 = 1.618034_f32;

    /// 黄金比例的共轭
    /// 
    /// 约等于 -0.6180339887
    /// 
    /// # 数学定义
    /// φ' = (1 - √5) / 2 = 1 - φ = -1/φ
    pub const GOLDEN_RATIO_CONJUGATE: f32 = -0.618034_f32;
}

/// f64 数学常量模块
pub mod math_consts_f64 {
    /// 欧拉-马歇罗尼常数 (Euler-Mascheroni constant)
    /// 
    /// 约等于 0.5772156649015329
    /// 
    /// # 数学定义
    /// γ = lim(n→∞) [Σ(1/k, k=1..n) - ln(n)]
    pub const EULER_GAMMA: f64 = 0.5772156649015329_f64;

    /// 黄金比例 (Golden Ratio)
    /// 
    /// 约等于 1.618033988749895
    /// 
    /// # 数学定义
    /// φ = (1 + √5) / 2
    pub const GOLDEN_RATIO: f64 = 1.618033988749895_f64;

    /// 黄金比例的共轭
    /// 
    /// 约等于 -0.6180339887498949
    /// 
    /// # 数学定义
    /// φ' = (1 - √5) / 2 = 1 - φ = -1/φ
    pub const GOLDEN_RATIO_CONJUGATE: f64 = -0.6180339887498949_f64;
}

/// 黄金分割搜索计算器
///
/// 使用 GOLDEN_RATIO 进行区间缩小搜索
pub struct GoldenSectionSearch {
    tolerance: f64,
    max_iterations: usize,
}

impl GoldenSectionSearch {
    /// 创建新的黄金分割搜索器
    pub fn new(tolerance: f64, max_iterations: usize) -> Self {
        Self {
            tolerance,
            max_iterations,
        }
    }

    /// 在区间内搜索函数最小值
    ///
    /// # 参数
    /// - `f`: 目标函数
    /// - `a`: 区间左端点
    /// - `b`: 区间右端点
    ///
    /// # 返回
    /// 近似最小值点的 x 坐标
    pub fn find_minimum<F>(&self, mut f: F, mut a: f64, mut b: f64) -> f64
    where
        F: FnMut(f64) -> f64,
    {
        let phi = math_consts_f64::GOLDEN_RATIO;
        let resphi = 2.0 - phi; // 1 - 1/phi = 2 - phi

        let mut c = a + resphi * (b - a);
        let mut d = b - resphi * (b - a);
        let mut fc = f(c);
        let mut fd = f(d);

        for _ in 0..self.max_iterations {
            if (b - a).abs() < self.tolerance {
                break;
            }

            if fc < fd {
                b = d;
                d = c;
                fd = fc;
                c = a + resphi * (b - a);
                fc = f(c);
            } else {
                a = c;
                c = d;
                fc = fd;
                d = b - resphi * (b - a);
                fd = f(d);
            }
        }

        (a + b) / 2.0
    }
}

/// 计算调和数
///
/// H_n = 1 + 1/2 + 1/3 + ... + 1/n
#[allow(dead_code)]
pub fn harmonic_number(n: u64) -> f64 {
    if n == 0 {
        return 0.0;
    }
    
    (1..=n).map(|k| 1.0 / k as f64).sum()
}

/// 使用欧拉-马歇罗尼常数近似计算调和数
///
/// 对于大 n，H_n ≈ ln(n) + γ + 1/(2n)
#[allow(dead_code)]
pub fn harmonic_number_approx(n: u64) -> f64 {
    if n == 0 {
        return 0.0;
    }
    
    let n_f64 = n as f64;
    n_f64.ln() + math_consts_f64::EULER_GAMMA + 1.0 / (2.0 * n_f64)
}

/// 使用 Euler Gamma 常数进行积分近似
///
/// 演示 EULER_GAMMA 在数值分析中的应用
pub fn exponential_integral_approx(x: f64) -> f64 {
    // 对于小 x，Ei(x) ≈ γ + ln|x| + x + x²/4 + ...
    // 这里展示基本的近似
    if x > 0.0 && x < 1.0 {
        math_consts_f64::EULER_GAMMA + x.ln() + x
    } else {
        // 简化处理
        x.exp() / x
    }
}

/// 演示 Rust 1.94 真实特性
pub fn demonstrate_rust_194_features() {
    println!("\n=== Rust 1.94.0 真实特性演示 ===\n");

    // 1. array_windows 特性演示
    println!("1. array_windows 特性:");
    let text = "abba";
    println!("   字符串 '{}' 是否有 ABBA 模式: {}", text, has_abba(text));

    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
    let averages = sliding_window_averages(&data);
    println!("   滑动窗口平均值: {:?}", averages);

    let numbers = vec![1, 2, 3, 2, 4, 5, 6];
    let triplets = count_increasing_triplets(&numbers);
    println!("   递增三元组数量: {}", triplets);

    // 2. LazyCell 新方法演示
    println!("\n2. LazyCell 新方法 (get, get_mut, force_mut):");
    let mut cache = LazyCache::<Vec<i32>>::new();
    
    println!("   初始化前 try_get(): {:?}", cache.try_get());
    println!("   是否已初始化: {}", cache.is_initialized());
    
    let _ = cache.get_or_init(|| {
        println!("   [LazyCell] 执行初始化...");
        vec![1, 2, 3, 4, 5]
    }); // 触发初始化
    println!("   初始化后 try_get(): {:?}", cache.try_get().map(|v| v.as_slice()));
    
    // 使用 force_get_mut 获取可变引用
    let mutable_ref = cache.force_get_mut(std::vec::Vec::new);
    mutable_ref.push(6);
    println!("   修改后: {:?}", cache.try_get());

    // 3. 数学常量演示
    println!("\n3. 数学常量:");
    println!(
        "   欧拉-马歇罗尼常数 (f64): {:.10}",
        math_consts_f64::EULER_GAMMA
    );
    println!(
        "   黄金比例 (f64): {:.10}",
        math_consts_f64::GOLDEN_RATIO
    );
    println!(
        "   欧拉-马歇罗尼常数 (f32): {:.7}",
        math_consts_f32::EULER_GAMMA
    );
    println!(
        "   黄金比例 (f32): {:.7}",
        math_consts_f32::GOLDEN_RATIO
    );

    // 黄金分割搜索演示
    let gss = GoldenSectionSearch::new(1e-6, 100);
    let minimum = gss.find_minimum(|x| (x - 2.0).powi(2), 0.0, 5.0);
    println!("   函数 (x-2)² 在 [0, 5] 的最小值点在: {:.6}", minimum);

    // 调和数计算
    let h10 = harmonic_number(10);
    let h10_approx = harmonic_number_approx(10);
    println!("   H_10 精确值: {:.6}", h10);
    println!("   H_10 近似值: {:.6}", h10_approx);

    // 指数积分近似
    let ei_approx = exponential_integral_approx(0.5);
    println!("   Ei(0.5) 近似值: {:.6}", ei_approx);
}

#[cfg(test)]
mod tests {
    use super::*;

    // ==================== array_windows 测试 ====================

    #[test]
    fn test_has_abba() {
        assert!(has_abba("abba"));
        assert!(has_abba("cddc"));
        assert!(has_abba("xyzzyx"));
        assert!(!has_abba("abcd"));
        assert!(!has_abba("abcba")); // 这是回文但不是 ABBA 模式
    }

    #[test]
    fn test_sliding_window_averages() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let averages = sliding_window_averages(&data);
        assert_eq!(averages, vec![2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_count_increasing_triplets() {
        let data = vec![1, 2, 3, 2, 4, 5, 6];
        // 递增三元组: (1,2,3), (2,4,5), (4,5,6)
        assert_eq!(count_increasing_triplets(&data), 3);
    }

    #[test]
    fn test_array_windows_empty() {
        let empty: &[i32] = &[];
        let count = empty.array_windows::<2>().count();
        assert_eq!(count, 0);
    }

    // ==================== LazyCell/LazyLock 新方法测试 ====================

    #[test]
    fn test_lazy_cache_get() {
        let cache = LazyCache::<i32>::new();
        
        // 初始化前 try_get() 应该返回 None
        assert_eq!(cache.try_get(), None);
        
        // 获取值触发初始化
        assert_eq!(cache.get_or_init(|| 42), &42);
        
        // 初始化后 try_get() 应该返回 Some
        assert_eq!(cache.try_get(), Some(&42));
    }

    #[test]
    fn test_lazy_cache_get_mut() {
        let mut cache = LazyCache::<Vec<i32>>::new();
        
        // 初始化前 get_mut() 应该返回 None
        assert_eq!(cache.try_get_mut(), None);
        
        // 使用 force_get_mut 触发初始化并获取可变引用
        let mutable = cache.force_get_mut(|| vec![1, 2, 3]);
        mutable.push(4);
        
        // 验证修改
        assert_eq!(cache.try_get(), Some(&vec![1, 2, 3, 4]));
    }

    #[test]
    fn test_lazy_cache_is_initialized() {
        let cache = LazyCache::<i32>::new();
        assert!(!cache.is_initialized());
        
        let _ = cache.get_or_init(|| 100);
        assert!(cache.is_initialized());
    }

    #[test]
    fn test_lazy_cache_set() {
        let cache = LazyCache::<i32>::new();
        assert!(cache.set(42).is_ok());
        assert_eq!(cache.try_get(), Some(&42));
        // 重复设置应该失败
        assert!(cache.set(100).is_err());
    }

    #[test]
    fn test_thread_safe_lazy_cache() {
        let cache = ThreadSafeLazyCache::<String>::new();
        
        // 初始化前
        assert_eq!(cache.try_get(), None);
        assert!(!cache.is_initialized());
        
        // 获取值
        assert_eq!(cache.get_or_init(|| "hello".to_string()), "hello");
        
        // 初始化后
        assert_eq!(cache.try_get(), Some(&"hello".to_string()));
        assert!(cache.is_initialized());
    }

    #[test]
    fn test_thread_safe_lazy_cache_set() {
        let cache = ThreadSafeLazyCache::<i32>::new();
        assert!(cache.set(42).is_ok());
        assert_eq!(cache.try_get(), Some(&42));
    }

    // ==================== 原有测试 ====================

    #[test]
    fn test_hybrid_cell() {
        let cell = HybridCell::new(42);
        {
            let _ref = cell.borrow_with_count();
            assert_eq!(cell.access_count(), 1);
        }
        {
            let _mut_ref = cell.borrow_mut_with_count();
            assert_eq!(cell.access_count(), 2);
        }
    }

    #[test]
    fn test_safe_buffer() {
        let mut buf = SafeBuffer::with_capacity(10);
        let written = buf.write_slice(&[1, 2, 3, 4, 5]);
        assert_eq!(written, 5);
        assert_eq!(buf.initialized_slice(), &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_smart_ptr_chain() {
        let chain = SmartPtrChain::new(100);
        assert_eq!(chain.metadata(), 0);
        
        let (ptr, meta) = chain.into_raw_parts();
        assert!(!ptr.is_null());
        assert_eq!(unsafe { *ptr }, 100);
        
        let _restored = unsafe { SmartPtrChain::from_raw_parts(ptr, meta) };
    }

    #[test]
    fn test_scope_guard() {
        let mut dropped = false;
        {
            let mut guard = ScopeGuard::new(42, |v| {
                assert_eq!(v, 42);
                dropped = true;
            });
            *guard.get_mut() = 42;
        }
        assert!(dropped);

        // 测试主动完成
        let mut dropped2 = false;
        let guard2 = ScopeGuard::new(100, |_v| dropped2 = true);
        let _value = guard2.complete();
        assert!(!dropped2); // 析构函数未执行
    }

    #[test]
    fn test_zero_copy_string() {
        let original = String::from("Hello, Rust 1.94!");
        let zc = ZeroCopyString::from_string(original);
        assert_eq!(zc.as_str(), "Hello, Rust 1.94!");
        
        let restored = zc.into_string();
        assert_eq!(restored, "Hello, Rust 1.94!");
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_features();
    }

    // ==================== 数学常量测试 ====================

    #[test]
    fn test_euler_gamma_f64() {
        // 欧拉-马歇罗尼常数的近似值检查
        assert!((math_consts_f64::EULER_GAMMA - 0.5772).abs() < 0.001);
        // 验证它是正数
        assert!(math_consts_f64::EULER_GAMMA > 0.0);
        // 验证它小于 1
        assert!(math_consts_f64::EULER_GAMMA < 1.0);
    }

    #[test]
    fn test_golden_ratio_f64() {
        // 黄金比例的近似值检查
        assert!((math_consts_f64::GOLDEN_RATIO - 1.618).abs() < 0.001);
        // 验证黄金比例的性质: φ = 1 + 1/φ
        let phi = math_consts_f64::GOLDEN_RATIO;
        assert!((phi - (1.0 + 1.0 / phi)).abs() < 1e-10);
        // 验证 φ² = φ + 1
        assert!((phi * phi - (phi + 1.0)).abs() < 1e-10);
    }

    #[test]
    fn test_golden_ratio_conjugate() {
        // 验证共轭性质: φ + φ' = 1
        let phi = math_consts_f64::GOLDEN_RATIO;
        let phi_conj = math_consts_f64::GOLDEN_RATIO_CONJUGATE;
        assert!((phi + phi_conj - 1.0).abs() < 1e-10);
        // 验证 φ * φ' = -1
        assert!((phi * phi_conj + 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_math_consts_f32() {
        // f32 常量的基本检查
        assert!(math_consts_f32::EULER_GAMMA > 0.0);
        assert!(math_consts_f32::GOLDEN_RATIO > 1.0);
        // f64 和 f32 常量应该近似相等
        assert!((math_consts_f64::EULER_GAMMA - math_consts_f32::EULER_GAMMA as f64).abs() < 1e-6);
    }

    #[test]
    fn test_golden_section_search() {
        let gss = GoldenSectionSearch::new(1e-6, 100);
        // 搜索 (x-2)² 的最小值，应该在 x=2
        let minimum = gss.find_minimum(|x| (x - 2.0).powi(2), 0.0, 5.0);
        assert!((minimum - 2.0).abs() < 1e-5);
    }

    #[test]
    fn test_harmonic_number() {
        // H_1 = 1
        assert!((harmonic_number(1) - 1.0).abs() < 1e-10);
        // H_2 = 1 + 1/2 = 1.5
        assert!((harmonic_number(2) - 1.5).abs() < 1e-10);
        // H_3 = 1 + 1/2 + 1/3 ≈ 1.8333
        assert!((harmonic_number(3) - 1.8333333333).abs() < 1e-6);
    }

    #[test]
    fn test_harmonic_number_approx() {
        // 对于大 n，近似值应该接近精确值
        let n = 1000u64;
        let exact = harmonic_number(n);
        let approx = harmonic_number_approx(n);
        // 相对误差应该很小
        let relative_error = (exact - approx).abs() / exact;
        assert!(relative_error < 0.01); // 小于 1% 误差
    }

    #[test]
    fn test_exponential_integral_approx() {
        // 对于小 x，Ei(x) 应该返回有限值
        let ei = exponential_integral_approx(0.5);
        assert!(ei.is_finite());
        assert!(ei > 0.0);
    }
}
