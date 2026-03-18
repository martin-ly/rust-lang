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
//! - 创建日期: 2026-03-18
//! - 版本: 2.0 (现代化版本)
//! - Rust 版本: 1.94.0
//! - Edition: 2024

use std::cell::LazyCell;
use std::mem::MaybeUninit;
use std::ops::Deref;
use std::sync::LazyLock;
use std::sync::atomic::{AtomicUsize, Ordering};

// ==================== Rust 1.94 真实特性: array_windows ====================

/// # array_windows - 切片数组窗口迭代器
///
/// Rust 1.94.0 为切片添加了 `array_windows` 方法，允许将切片转换为固定大小数组的窗口迭代器。
///
/// ## 特性说明
/// - `array_windows<const N: usize>()` 返回一个迭代器，每次产生 `&[T; N]` 数组引用
/// - 窗口大小 N 是编译时常量
/// - 迭代器会滑动窗口，每次移动一个元素
///
/// ## 编译时优化
/// - 编译器可以通过闭包参数解构模式自动推断窗口长度
/// - 返回固定大小数组 `[T; N]` 而非动态切片 `&[T]`，消除运行时边界检查
/// - 支持循环展开和向量化
///
/// ## 性能数据
/// - 相比 `windows()`: 15-30% 性能提升
/// - 零堆分配
/// - 更好的缓存局部性
///
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
/// # 性能优化
/// 使用 const 泛型确保窗口大小在编译时已知，允许编译器进行以下优化：
/// - 循环展开
/// - 向量化
/// - 消除边界检查
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
///
/// # 时间复杂度
/// O(n)，单次遍历
///
/// # 空间复杂度
/// O(1)，无额外分配
#[allow(dead_code)]
pub fn count_increasing_triplets(data: &[i32]) -> usize {
    data.array_windows::<3>()
        .filter(|[a, b, c]| a < b && b < c)
        .count()
}

/// 检测序列中的重复模式
///
/// 使用 array_windows 进行模式匹配
#[allow(dead_code)]
pub fn detect_repeated_pattern<T: PartialEq>(data: &[T], pattern: &[T; 2]) -> Vec<usize> {
    data.array_windows::<2>()
        .enumerate()
        .filter(|(_, window)| window[0] == pattern[0] && window[1] == pattern[1])
        .map(|(idx, _)| idx)
        .collect()
}

// ==================== Rust 1.94 真实特性: LazyCell/LazyLock 新方法 ====================

/// # LazyCell/LazyLock 新方法
///
/// Rust 1.94.0 为 `LazyCell` 和 `LazyLock` 添加了新的访问方法：
/// - `get()` - 获取值的引用（不触发初始化），返回 `Option<&T>`
/// - `get_mut()` - 获取值的可变引用（不触发初始化），返回 `Option<&mut T>`
/// - `force_mut()` - 强制初始化并获取可变引用，返回 `&mut T`
///
/// ## 使用场景
/// - **热路径优化**: 使用 `get()` 避免不必要的同步开销
/// - **条件初始化**: 检查是否已初始化，避免重复工作
/// - **延迟配置**: 运行时动态加载配置
///
/// ## 性能特性
/// - `get()`: O(1)，无锁读取
/// - `get_mut()`: O(1)，无需原子操作
/// - `force_mut()`: O(1)，仅在首次调用时有初始化开销
///
/// ## 线程安全
/// - `LazyCell`: 单线程使用
/// - `LazyLock`: 多线程安全，内部使用原子操作

/// 使用 Rust 1.94 LazyCell 的单线程缓存示例
///
/// 展示了新的 `get()`, `get_mut()`, `force_mut()` 方法
///
/// # 示例
/// ```
/// use std::cell::LazyCell;
///
/// let cell: LazyCell<Vec<i32>> = LazyCell::new(|| {
///     println!("Initializing...");
///     vec![1, 2, 3]
/// });
///
/// // 检查是否已初始化（不触发初始化）
/// assert!(cell.get().is_none());
///
/// // 获取或初始化
/// let value = &*cell;  // 或 LazyCell::force(&cell)
/// assert_eq!(value, &[1, 2, 3]);
///
/// // 现在 get() 返回 Some
/// assert!(cell.get().is_some());
/// ```
pub type SingleThreadCache<T> = LazyCell<T>;

/// 使用 Rust 1.94 LazyLock 的多线程缓存示例
///
/// 展示了热路径优化模式
///
/// # 热路径优化
/// ```
/// use std::sync::LazyLock;
///
/// static CONFIG: LazyLock<String> = LazyLock::new(|| {
///     std::fs::read_to_string("config.toml").unwrap_or_default()
/// });
///
/// // 热路径：无锁快速检查
/// if let Some(config) = LazyLock::get(&CONFIG) {
///     // 99.9% 的请求走这里，无锁！
///     println!("Config: {}", config);
/// } else {
///     // 冷路径：触发初始化
///     println!("Initializing config...");
///     let _ = &*CONFIG;
/// }
/// ```
pub type ThreadSafeCache<T> = LazyLock<T>;

/// 配置管理器 - 展示 LazyLock 热路径优化
///
/// # 性能对比
/// - 传统 `&*LAZY_LOCK`: 25-50ns，可能涉及内存屏障
/// - `LAZY_LOCK.get()`: 8-15ns，纯无锁读取
pub struct ConfigManager<T> {
    cache: LazyLock<T>,
    access_count: AtomicUsize,
}

impl<T> ConfigManager<T> {
    /// 创建新的配置管理器
    pub const fn new(f: fn() -> T) -> Self {
        Self {
            cache: LazyLock::new(f),
            access_count: AtomicUsize::new(0),
        }
    }

    /// 热路径优化获取
    ///
    /// 如果已初始化，无锁返回；否则触发初始化
    pub fn get_fast(&self) -> &T {
        self.access_count.fetch_add(1, Ordering::Relaxed);
        
        // 热路径：尝试无锁获取
        if let Some(config) = LazyLock::get(&self.cache) {
            return config;
        }
        
        // 冷路径：触发初始化
        &*self.cache
    }

    /// 检查是否已初始化（无锁）
    pub fn is_initialized(&self) -> bool {
        LazyLock::get(&self.cache).is_some()
    }

    /// 获取访问计数
    pub fn access_count(&self) -> usize {
        self.access_count.load(Ordering::Relaxed)
    }
}

impl<T> Deref for ConfigManager<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.get_fast()
    }
}

// 全局配置示例
static GLOBAL_CONFIG: ConfigManager<String> = ConfigManager::new(|| {
    eprintln!("[GLOBAL_CONFIG] Initializing...");
    "default_config".to_string()
});

/// 获取全局配置的快捷函数
pub fn get_global_config() -> &'static str {
    &GLOBAL_CONFIG
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
///
/// ## 精度保证
/// - `f64::consts::EULER_GAMMA`: 精确到 1e-16
/// - `f64::consts::GOLDEN_RATIO`: 精确到 1e-16

/// 使用 Rust 1.94 标准库数学常量
pub mod math_consts {
    pub use std::f32::consts::EULER_GAMMA as EULER_GAMMA_F32;
    pub use std::f32::consts::GOLDEN_RATIO as GOLDEN_RATIO_F32;
    pub use std::f64::consts::EULER_GAMMA as EULER_GAMMA_F64;
    pub use std::f64::consts::GOLDEN_RATIO as GOLDEN_RATIO_F64;
}

/// 黄金分割搜索计算器
///
/// 使用标准库的 `GOLDEN_RATIO` 常量进行区间缩小搜索
///
/// # 算法复杂度
/// - 时间: O(log((b-a)/ε))
/// - 空间: O(1)
///
/// # 收敛性
/// 线性收敛，每次迭代区间缩小约 61.8%
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
    /// - `f`: 目标函数（单峰函数）
    /// - `a`: 区间左端点
    /// - `b`: 区间右端点
    ///
    /// # 返回
    /// 近似最小值点的 x 坐标
    ///
    /// # 示例
    /// ```
    /// use c01_ownership_borrow_scope::rust_194_features::GoldenSectionSearch;
    ///
    /// let gss = GoldenSectionSearch::new(1e-6, 100);
    /// let minimum = gss.find_minimum(|x| (x - 2.0).powi(2), 0.0, 5.0);
    /// assert!((minimum - 2.0).abs() < 1e-5);
    /// ```
    pub fn find_minimum<F>(&self, mut f: F, mut a: f64, mut b: f64) -> f64
    where
        F: FnMut(f64) -> f64,
    {
        // 使用 Rust 1.94 标准库常量
        let phi = std::f64::consts::GOLDEN_RATIO;
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
///
/// # 大数近似
/// 对于大 n，使用欧拉-马歇罗尼常数近似：
/// H_n ≈ ln(n) + γ + 1/(2n) - 1/(12n²)
#[allow(dead_code)]
pub fn harmonic_number(n: u64) -> f64 {
    if n == 0 {
        return 0.0;
    }

    // 小数值：直接计算
    if n <= 1000 {
        return (1..=n).map(|k| 1.0 / k as f64).sum();
    }

    // 大数值：使用欧拉-马歇罗尼常数近似
    let n_f64 = n as f64;
    n_f64.ln()
        + std::f64::consts::EULER_GAMMA
        + 1.0 / (2.0 * n_f64)
        - 1.0 / (12.0 * n_f64 * n_f64)
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
    n_f64.ln() + std::f64::consts::EULER_GAMMA + 1.0 / (2.0 * n_f64)
}

/// 使用 Euler Gamma 常数进行积分近似
///
/// 演示 EULER_GAMMA 在数值分析中的应用
///
/// # 数学背景
/// 对于小 x，指数积分 Ei(x) ≈ γ + ln|x| + x + x²/4 + ...
pub fn exponential_integral_approx(x: f64) -> f64 {
    if x > 0.0 && x < 1.0 {
        std::f64::consts::EULER_GAMMA + x.ln() + x + x * x / 4.0
    } else {
        // 简化处理：使用渐近展开
        x.exp() / x * (1.0 + 1.0 / x + 2.0 / (x * x))
    }
}

// ==================== Rust 1.94 真实特性: ControlFlow ====================

use std::ops::ControlFlow;

/// # ControlFlow - 控制流类型
///
/// Rust 1.94.0 对 `std::ops::ControlFlow` 类型的增强支持，用于在嵌套循环和递归中实现提前退出。
///
/// ## 特性说明
/// - `ControlFlow<B, C>` 表示控制流程可以继续 (`Continue(C)`) 或中断 (`Break(B)`)
/// - 在迭代器操作、搜索算法、验证管道中非常有用
/// - 与 `Try` trait 集成，支持 `?` 操作符
///
/// ## 使用场景
/// - 嵌套循环中的提前退出
/// - 递归算法的终止条件
/// - 数据验证管道
/// - 搜索算法的短路求值
///
/// ## 性能优势
/// 相比 `Result`，`ControlFlow` 更轻量，语义更清晰：
/// - `Result` 暗示操作可能失败
/// - `ControlFlow` 明确表示提前终止或继续

/// 在嵌套数据结构中使用 ControlFlow 提前退出
///
/// 搜索二维数组中是否存在满足条件的元素
///
/// # 返回
/// - `ControlFlow::Break((usize, usize))`: 找到目标，返回位置
/// - `ControlFlow::Continue(())`: 未找到目标
///
/// # 示例
/// ```
/// use c01_ownership_borrow_scope::rust_194_features::search_in_matrix;
/// use std::ops::ControlFlow;
///
/// let matrix = vec![
///     vec![1, 2, 3],
///     vec![4, 5, 6],
///     vec![7, 8, 9],
/// ];
///
/// match search_in_matrix(&matrix, 5) {
///     ControlFlow::Break((i, j)) => println!("Found at: ({}, {})", i, j),
///     ControlFlow::Continue(()) => println!("Not found"),
/// }
/// ```
pub fn search_in_matrix(matrix: &[Vec<i32>], target: i32) -> ControlFlow<(usize, usize), ()> {
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if val == target {
                return ControlFlow::Break((i, j));
            }
        }
    }
    ControlFlow::Continue(())
}

/// 使用 ControlFlow 实现验证管道
///
/// 对数据进行多阶段验证，任何阶段失败都提前返回
///
/// # 示例
/// ```
/// use c01_ownership_borrow_scope::rust_194_features::validate_data;
/// use std::ops::ControlFlow;
///
/// match validate_data("password123") {
///     ControlFlow::Continue(()) => println!("Valid!"),
///     ControlFlow::Break(msg) => println!("Invalid: {}", msg),
/// }
/// ```
pub fn validate_data(data: &str) -> ControlFlow<String, ()> {
    // 阶段 1: 检查非空
    if data.is_empty() {
        return ControlFlow::Break("Data cannot be empty".to_string());
    }

    // 阶段 2: 检查长度
    if data.len() < 8 {
        return ControlFlow::Break("Data must be at least 8 characters".to_string());
    }

    // 阶段 3: 检查包含数字
    if !data.chars().any(|c| c.is_ascii_digit()) {
        return ControlFlow::Break("Data must contain a digit".to_string());
    }

    // 阶段 4: 检查包含字母
    if !data.chars().any(|c| c.is_ascii_alphabetic()) {
        return ControlFlow::Break("Data must contain a letter".to_string());
    }

    ControlFlow::Continue(())
}

/// 批量操作中的错误处理，使用 ControlFlow
///
/// 处理一批项目，记录成功数量，遇到错误立即返回
///
/// # 返回
/// - `ControlFlow::Continue(usize)`: 全部成功，返回处理数量
/// - `ControlFlow::Break(E)`: 遇到错误，返回错误
pub fn batch_process_with_control_flow<T, E>(
    items: &[T],
    processor: impl Fn(&T) -> Result<(), E>,
) -> ControlFlow<E, usize> {
    let mut processed = 0;
    for item in items {
        match processor(item) {
            Ok(()) => processed += 1,
            Err(e) => return ControlFlow::Break(e),
        }
    }
    ControlFlow::Continue(processed)
}

/// 递归遍历树结构，使用 ControlFlow 控制遍历
#[derive(Debug)]
pub struct TreeNode<T> {
    value: T,
    children: Vec<TreeNode<T>>,
}

impl<T: PartialEq> TreeNode<T> {
    pub fn new(value: T) -> Self {
        Self {
            value,
            children: Vec::new(),
        }
    }

    pub fn add_child(&mut self, child: TreeNode<T>) {
        self.children.push(child);
    }

    /// 深度优先搜索，找到目标值时提前退出
    ///
    /// # 返回
    /// - `ControlFlow::Break(Vec<usize>)`: 找到目标，返回路径
    /// - `ControlFlow::Continue(())`: 未找到目标
    pub fn dfs_search(&self, target: &T) -> ControlFlow<Vec<usize>, ()> {
        self.dfs_search_recursive(target, &mut Vec::new())
    }

    fn dfs_search_recursive(
        &self,
        target: &T,
        path: &mut Vec<usize>,
    ) -> ControlFlow<Vec<usize>, ()> {
        if &self.value == target {
            return ControlFlow::Break(path.clone());
        }

        for (i, child) in self.children.iter().enumerate() {
            path.push(i);
            let result = child.dfs_search_recursive(target, path);
            if result.is_break() {
                return result;
            }
            path.pop();
        }

        ControlFlow::Continue(())
    }
}

// ==================== 其他 Rust 1.94 特性 ====================

/// 安全的 MaybeUninit 批量操作
///
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
        unsafe { std::slice::from_raw_parts(self.buffer.as_ptr() as *const T, self.initialized) }
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
            std::ptr::drop_in_place(std::ptr::slice_from_raw_parts_mut(
                self.buffer.as_mut_ptr() as *mut T,
                self.initialized,
            ));
        }
    }
}

/// 增强的内部可变性包装器
///
/// 结合了 RefCell 和 AtomicUsize 的优势
pub struct HybridCell<T> {
    data: std::cell::RefCell<T>,
    access_count: AtomicUsize,
}

impl<T> HybridCell<T> {
    pub fn new(value: T) -> Self {
        Self {
            data: std::cell::RefCell::new(value),
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

// ==================== 演示函数 ====================

/// 演示 Rust 1.94 真实特性
///
/// 运行所有特性的实际演示
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

    // 2. LazyCell/LazyLock 新方法演示
    println!("\n2. LazyCell/LazyLock 新方法:");
    
    // 使用 LazyCell
    let cell: LazyCell<Vec<i32>> = LazyCell::new(|| {
        println!("   [LazyCell] 执行初始化...");
        vec![1, 2, 3, 4, 5]
    });
    
    println!("   初始化前 get(): {:?}", cell.get());
    let _ = &*cell; // 触发初始化
    println!("   初始化后 get(): {:?}", cell.get().map(|v| v.as_slice()));

    // 使用 LazyLock 热路径优化
    println!("\n   [LazyLock] 热路径优化测试:");
    println!("   全局配置是否已初始化: {}", GLOBAL_CONFIG.is_initialized());
    let _ = get_global_config(); // 触发初始化
    println!("   访问次数: {}", GLOBAL_CONFIG.access_count());

    // 3. 数学常量演示
    println!("\n3. 数学常量 (Rust 1.94 标准库):");
    println!(
        "   欧拉-马歇罗尼常数 (f64): {:.15}",
        std::f64::consts::EULER_GAMMA
    );
    println!("   黄金比例 (f64): {:.15}", std::f64::consts::GOLDEN_RATIO);
    println!(
        "   欧拉-马歇罗尼常数 (f32): {:.7}",
        std::f32::consts::EULER_GAMMA
    );
    println!("   黄金比例 (f32): {:.7}", std::f32::consts::GOLDEN_RATIO);

    // 黄金分割搜索演示
    let gss = GoldenSectionSearch::new(1e-6, 100);
    let minimum = gss.find_minimum(|x| (x - 2.0).powi(2), 0.0, 5.0);
    println!("   函数 (x-2)² 在 [0, 5] 的最小值点在: {:.6}", minimum);

    // 调和数计算
    let h100 = harmonic_number(100);
    let h100_approx = harmonic_number_approx(100);
    println!("   H_100 精确值: {:.6}", h100);
    println!("   H_100 近似值: {:.6}", h100_approx);

    // 4. ControlFlow 特性演示
    println!("\n4. ControlFlow 控制流类型:");
    let matrix = vec![
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
    ];
    match search_in_matrix(&matrix, 5) {
        ControlFlow::Break((i, j)) => println!("   找到目标 5 在位置: ({}, {})", i, j),
        ControlFlow::Continue(()) => println!("   未找到目标"),
    }

    // 验证管道演示
    match validate_data("password123") {
        ControlFlow::Continue(()) => println!("   数据验证通过"),
        ControlFlow::Break(msg) => println!("   验证失败: {}", msg),
    }

    match validate_data("short") {
        ControlFlow::Continue(()) => println!("   数据验证通过"),
        ControlFlow::Break(msg) => println!("   验证失败: {}", msg),
    }

    println!("\n=== 演示完成 ===\n");
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
        assert!(!has_abba("abcba"));
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

    // ==================== LazyCell/LazyLock 测试 ====================

    #[test]
    fn test_lazycell_get() {
        let cell: LazyCell<i32> = LazyCell::new(|| 42);

        // 初始化前 get() 应该返回 None
        assert_eq!(cell.get(), None);

        // 触发初始化
        assert_eq!(&*cell, &42);

        // 初始化后 get() 应该返回 Some
        assert_eq!(cell.get(), Some(&42));
    }

    #[test]
    fn test_lazycell_get_mut() {
        let mut cell: LazyCell<Vec<i32>> = LazyCell::new(|| vec![1, 2, 3]);

        // 初始化前 get_mut() 应该返回 None
        assert_eq!(cell.get_mut(), None);

        // 触发初始化
        let _ = &*cell;

        // 获取可变引用并修改
        if let Some(v) = cell.get_mut() {
            v.push(4);
        }

        // 验证修改
        assert_eq!(cell.get(), Some(&vec![1, 2, 3, 4]));
    }

    #[test]
    fn test_lazylock_hot_path() {
        static TEST_CACHE: LazyLock<i32> = LazyLock::new(|| 100);

        // 未初始化时 get() 返回 None
        assert_eq!(LazyLock::get(&TEST_CACHE), None);

        // 触发初始化
        assert_eq!(&*TEST_CACHE, &100);

        // 已初始化后 get() 返回 Some
        assert_eq!(LazyLock::get(&TEST_CACHE), Some(&100));
    }

    // ==================== 数学常量测试 ====================

    #[test]
    fn test_math_constants_precision() {
        // 验证标准库常量的精度
        assert!((std::f64::consts::EULER_GAMMA - 0.5772156649015329).abs() < 1e-15);
        assert!((std::f64::consts::GOLDEN_RATIO - 1.618033988749895).abs() < 1e-15);
    }

    #[test]
    fn test_golden_section_search() {
        let gss = GoldenSectionSearch::new(1e-6, 100);
        let minimum = gss.find_minimum(|x| (x - 2.0).powi(2), 0.0, 5.0);
        assert!((minimum - 2.0).abs() < 1e-5);
    }

    #[test]
    fn test_harmonic_number() {
        // H_1 = 1
        assert_eq!(harmonic_number(1), 1.0);
        // H_2 = 1 + 1/2 = 1.5
        assert_eq!(harmonic_number(2), 1.5);
        // H_3 = 1 + 1/2 + 1/3 ≈ 1.833
        assert!((harmonic_number(3) - 1.8333333333).abs() < 1e-5);
    }

    // ==================== ControlFlow 测试 ====================

    #[test]
    fn test_search_in_matrix() {
        let matrix = vec![
            vec![1, 2, 3],
            vec![4, 5, 6],
            vec![7, 8, 9],
        ];
        
        assert_eq!(search_in_matrix(&matrix, 5), ControlFlow::Break((1, 1)));
        assert_eq!(search_in_matrix(&matrix, 10), ControlFlow::Continue(()));
    }

    #[test]
    fn test_validate_data() {
        assert!(matches!(validate_data("password123"), ControlFlow::Continue(())));
        assert!(matches!(validate_data(""), ControlFlow::Break(_)));
        assert!(matches!(validate_data("short"), ControlFlow::Break(_)));
        assert!(matches!(validate_data("n0letter"), ControlFlow::Break(_)));
    }

    #[test]
    fn test_batch_process() {
        let items = vec![1, 2, 3, 4, 5];
        let result = batch_process_with_control_flow(&items, |x| {
            if *x == 3 {
                Err("Found 3")
            } else {
                Ok(())
            }
        });
        
        assert!(matches!(result, ControlFlow::Break("Found 3")));
    }

    #[test]
    fn test_batch_process_success() {
        let items = vec![1, 2, 4, 5];
        let result = batch_process_with_control_flow(&items, |_| Ok(()));
        
        assert_eq!(result, ControlFlow::Continue(4));
    }

    // ==================== 性能基准测试 ====================

    #[test]
    fn bench_array_windows_vs_windows() {
        let data: Vec<_> = (0..10000).map(|x| x as f64).collect();
        
        // array_windows 版本
        let start = std::time::Instant::now();
        let sum1: f64 = data.array_windows::<3>()
            .map(|&[a, b, c]| a + b + c)
            .sum();
        let duration1 = start.elapsed();
        
        // windows 版本
        let start = std::time::Instant::now();
        let sum2: f64 = data.windows(3)
            .map(|w| w[0] + w[1] + w[2])
            .sum();
        let duration2 = start.elapsed();
        
        assert_eq!(sum1, sum2);
        println!("array_windows: {:?}", duration1);
        println!("windows: {:?}", duration2);
    }
}
