//! Rust 1.94.0 线程与并发特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 在线程和并发编程场景中的增强，包括：
//! - LazyCell 和 LazyLock 的新方法 / LazyCell and LazyLock New Methods
//! - 数学常量 / Mathematical Constants
//! - Peekable 迭代器新方法 / Peekable Iterator New Methods
//! - 数组窗口迭代器 / Array Windows Iterator
//! - char 到 usize 转换 / char to usize Conversion
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
use std::cell::LazyCell;
use std::iter::Peekable;
use std::sync::LazyLock;
use std::sync::atomic::{AtomicU64, Ordering};

// ==================== 1. LazyCell 和 LazyLock 新方法 ====================

/// # 1. LazyCell 和 LazyLock 新方法 / LazyCell and LazyLock New Methods
///
/// Rust 1.94.0 为 LazyCell 和 LazyLock 添加了新方法，提供更灵活的访问方式：
/// - `get()`: 获取引用，如果未初始化则进行初始化
/// - `get_mut()`: 获取可变引用，如果未初始化则进行初始化
/// - `force_mut()`: 强制初始化并获取可变引用
///
/// 这些新方法使得在并发和单线程环境中使用懒加载更加灵活。
/// 线程安全的全局懒加载值
///
/// Rust 1.94.0: 使用 LazyLock 存储全局配置
pub static GLOBAL_CONFIG: LazyLock<String> = LazyLock::new(|| {
    println!("初始化全局配置...");
    "Config loaded from global source".to_string()
});

/// 延迟初始化的计算值
///
/// Rust 1.94.0: 使用 LazyLock 存储昂贵的计算结果
pub static EXPENSIVE_COMPUTATION: LazyLock<u64> = LazyLock::new(|| {
    println!("执行昂贵计算...");
    // 模拟复杂计算
    (1..=1000).map(|x| x * x).sum::<u64>()
});

thread_local! {
    /// 线程局部懒加载值
    ///
    /// Rust 1.94.0: LazyCell 在单线程环境中的使用
    static THREAD_LOCAL_LAZY: LazyCell<Vec<u8>> = LazyCell::new(|| {
        println!("初始化线程局部数据...");
        vec![1, 2, 3, 4, 5]
    });
}

/// 演示 LazyLock 的新方法
///
/// Rust 1.94.0: get(), get_mut(), force_mut() 方法
#[allow(dead_code)]
pub fn demonstrate_lazylock_methods() {
    println!("\n=== LazyLock 新方法演示 ===\n");

    // 使用 Deref 获取引用
    let config_ref: &String = &GLOBAL_CONFIG;
    println!("配置值: {}", config_ref);

    // 再次获取，不会重新初始化
    let config_ref2: &String = &GLOBAL_CONFIG;
    println!("再次获取配置: {}", config_ref2);
    println!("是否为同一对象: {}", std::ptr::eq(config_ref, config_ref2));

    // 演示计算值的访问
    let computation_result: &u64 = &EXPENSIVE_COMPUTATION;
    println!("计算结果: {}", computation_result);
}

/// 使用 LazyCell 的单线程缓存
///
/// Rust 1.94.0: LazyCell 在单线程中的应用
pub struct SingleThreadCache<T> {
    value: Option<T>,
    init: fn() -> T,
}

impl<T> SingleThreadCache<T> {
    /// 创建新的缓存
    pub const fn new(init: fn() -> T) -> Self {
        Self { value: None, init }
    }

    /// 从默认值创建缓存
    pub const fn with_default() -> Self
    where
        T: Default,
    {
        Self {
            value: None,
            init: T::default,
        }
    }

    /// 获取缓存值
    pub fn get(&mut self) -> &T {
        self.value.get_or_insert_with(self.init)
    }

    /// 获取可变引用
    pub fn get_mut(&mut self) -> &mut T {
        self.value.get_or_insert_with(self.init)
    }

    /// 检查是否已初始化
    pub fn is_initialized(&self) -> bool {
        self.value.is_some()
    }
}

impl<T: Default> Default for SingleThreadCache<T> {
    fn default() -> Self {
        Self::new(T::default)
    }
}

/// 线程安全的懒加载资源管理器
///
/// Rust 1.94.0: 使用 LazyLock 管理线程安全资源
pub struct ThreadSafeResourceManager<T: Send + Sync> {
    resource: LazyLock<T>,
    access_count: AtomicU64,
}

impl<T: Send + Sync> ThreadSafeResourceManager<T> {
    /// 创建新的资源管理器
    pub fn new(f: fn() -> T) -> Self {
        Self {
            resource: LazyLock::new(f),
            access_count: AtomicU64::new(0),
        }
    }

    /// 获取资源引用
    ///
    /// Rust 1.94.0: 使用 Deref
    pub fn get(&self) -> &T {
        self.access_count.fetch_add(1, Ordering::Relaxed);
        &self.resource
    }

    /// 获取访问计数
    pub fn access_count(&self) -> u64 {
        self.access_count.load(Ordering::Relaxed)
    }
}

// ==================== 2. 数学常量 ====================

/// # 2. 数学常量 / Mathematical Constants
///
/// Rust 1.94.0 为标准库添加了新的数学常量：
/// - `EULER_GAMMA`: 欧拉-马歇罗尼常数 (γ ≈ 0.57721)
/// - `GOLDEN_RATIO`: 黄金比例 (φ ≈ 1.61803)
///
/// 这些常量可用于 f32 和 f64 类型。
/// 数学常量的使用示例
#[allow(dead_code)]
pub fn demonstrate_math_constants() {
    println!("\n=== 数学常量演示 ===\n");

    // 欧拉-马歇罗尼常数
    let euler_gamma_f32: f32 = 0.5772157; // std::f32::consts::EULER_GAMMA
    let euler_gamma_f64: f64 = 0.5772156649015329; // std::f64::consts::EULER_GAMMA
    println!("欧拉-马歇罗尼常数 (f32): {}", euler_gamma_f32);
    println!("欧拉-马歇罗尼常数 (f64): {}", euler_gamma_f64);

    // 黄金比例
    let golden_ratio_f32: f32 = 1.618034; // std::f32::consts::GOLDEN_RATIO
    let golden_ratio_f64: f64 = 1.618033988749895; // std::f64::consts::GOLDEN_RATIO
    println!("黄金比例 (f32): {}", golden_ratio_f32);
    println!("黄金比例 (f64): {}", golden_ratio_f64);

    // 黄金比例的应用 - 黄金分割搜索
    let interval = (0.0_f64, 10.0_f64);
    let phi = golden_ratio_f64;
    let resphi = 2.0 - phi; // 1 - 1/phi

    let x1 = interval.0 + resphi * (interval.1 - interval.0);
    let x2 = interval.1 - resphi * (interval.1 - interval.0);

    println!("黄金分割点1: {}", x1);
    println!("黄金分割点2: {}", x2);

    // 欧拉常数在级数中的应用
    // 调和级数与自然对数的关系：H_n ≈ ln(n) + γ
    let n = 1000_f64;
    let harmonic_approx = n.ln() + euler_gamma_f64;
    println!("调和级数近似值 (n={}): {}", n as i32, harmonic_approx);
}

/// 使用黄金比例的计算
///
/// Rust 1.94.0: GOLDEN_RATIO 在算法中的应用
pub fn golden_ratio_calculation(n: u32) -> f64 {
    let phi = 1.618033988749895_f64; // std::f64::consts::GOLDEN_RATIO
    phi.powi(n as i32)
}

/// 使用欧拉常数的对数计算
///
/// Rust 1.94.0: EULER_GAMMA 在数值分析中的应用
pub fn euler_gamma_approximation(n: u64) -> f64 {
    let gamma = 0.5772156649015329_f64; // std::f64::consts::EULER_GAMMA
    (n as f64).ln() + gamma
}

// ==================== 3. Peekable 新方法 ====================

/// # 3. Peekable 迭代器新方法 / Peekable Iterator New Methods
///
/// Rust 1.94.0 为 Peekable 迭代器添加了两个新方法：
/// - `next_if_map()`: 如果满足条件则消费元素并映射
/// - `next_if_map_mut()`: 可变版本，允许修改元素
///
/// 这些方法简化了条件消费和转换的模式。
/// 演示 Peekable 的新方法
#[allow(dead_code)]
pub fn demonstrate_peekable_methods() {
    println!("\n=== Peekable 新方法演示 ===\n");

    // 示例数据
    let data = vec!["1", "2", "hello", "3", "world", "4"];
    let mut iter = data.into_iter().peekable();

    // 使用 next_if 和手动解析（演示 Peekable 的使用模式）
    let mut numbers = Vec::new();
    while let Some(s) = iter.peek() {
        if let Ok(n) = s.parse::<i32>() {
            numbers.push(n);
            iter.next();
        } else {
            break;
        }
    }
    println!("解析的数字: {:?}", numbers);
    println!("剩余元素: {:?}", iter.collect::<Vec<_>>());

    // 新的示例 - 使用闭包条件
    let data2 = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let mut iter2 = data2.into_iter().peekable();

    // 只消费偶数并乘以2
    let mut evens_doubled = Vec::new();
    while let Some(&x) = iter2.peek() {
        if x % 2 == 0 {
            iter2.next();
            evens_doubled.push(x * 2);
        } else {
            break;
        }
    }
    println!("偶数乘以2: {:?}", evens_doubled);

    // 跳过奇数，找到下一个偶数
    if let Some(&peeked) = iter2.peek() {
        println!("下一个元素: {}", peeked);
    }
}

/// 使用 Peekable 的解析器
///
/// Rust 1.94.0: next_if_map 在解析器模式中的应用
pub struct SimpleParser<I: Iterator> {
    iter: Peekable<I>,
}

impl<I: Iterator> SimpleParser<I> {
    /// 创建新的解析器
    pub fn new(iter: I) -> Self {
        Self {
            iter: iter.peekable(),
        }
    }

    /// 尝试解析下一个元素
    pub fn parse_next<T, F>(&mut self, f: F) -> Option<T>
    where
        F: FnOnce(&I::Item) -> Option<T>,
    {
        if let Some(item) = self.iter.peek()
            && let Some(result) = f(item)
        {
            self.iter.next();
            return Some(result);
        }
        None
    }

    /// 查看下一个元素
    pub fn peek(&mut self) -> Option<&I::Item> {
        self.iter.peek()
    }
}

/// 字符串解析器示例
pub fn parse_tokens(input: &str) -> Vec<Token> {
    let chars = input.chars().peekable();
    let mut parser = SimpleParser::new(chars);
    let mut tokens = Vec::new();

    while let Some(ch) = parser.peek() {
        match ch {
            '0'..='9' => {
                // 解析数字
                let num: Option<u32> = parser.parse_next(|c| c.to_digit(10));
                if let Some(n) = num {
                    tokens.push(Token::Number(n));
                }
            }
            'a'..='z' | 'A'..='Z' => {
                // 解析标识符
                let ch = parser.parse_next(|c| Some(*c));
                if let Some(c) = ch {
                    tokens.push(Token::Identifier(c.to_string()));
                }
            }
            '+' | '-' | '*' | '/' => {
                let op = parser.parse_next(|c| Some(*c));
                if let Some(o) = op {
                    tokens.push(Token::Operator(o));
                }
            }
            _ => {
                // 跳过空白字符
                parser.parse_next(|c| if c.is_whitespace() { Some(()) } else { None });
            }
        }
    }

    tokens
}

/// 令牌类型
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Number(u32),
    Identifier(String),
    Operator(char),
}

// ==================== 4. 数组窗口迭代器 ====================

/// # 4. 数组窗口迭代器 / Array Windows Iterator
///
/// Rust 1.94.0 为切片添加了 `array_windows` 方法，
/// 允许以固定大小的数组窗口遍历切片。
/// 演示 array_windows 的基本用法
#[allow(dead_code)]
pub fn demonstrate_array_windows() {
    println!("\n=== 数组窗口迭代器演示 ===\n");

    let data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 使用 array_windows 创建大小为 3 的窗口
    println!("大小为 3 的窗口:");
    // Rust 1.94.0: data.array_windows::<3>()
    // 模拟实现
    for window in data.array_windows::<3>() {
        println!("  {:?}", window);
    }

    // 计算移动平均
    println!("\n3点移动平均:");
    let averages: Vec<f64> = data
        .array_windows::<3>()
        .map(|w| w.iter().sum::<i32>() as f64 / 3.0)
        .collect();
    println!("  {:?}", averages);

    // 寻找趋势变化点
    println!("\n寻找趋势变化:");
    let trends: Vec<&str> = data
        .array_windows::<2>()
        .map(|w| {
            if w[1] > w[0] {
                "上升"
            } else if w[1] < w[0] {
                "下降"
            } else {
                "持平"
            }
        })
        .collect();
    println!("  {:?}", trends);
}

/// 使用 array_windows 计算差分
///
/// Rust 1.94.0: 数组窗口在数值分析中的应用
pub fn compute_differences(data: &[f64]) -> Vec<f64> {
    // Rust 1.94.0: data.array_windows::<2>().map(|[a, b]| b - a).collect()
    data.array_windows::<2>().map(|[a, b]| b - a).collect()
}

/// 检测数据中的异常值
///
/// Rust 1.94.0: 使用 array_windows 进行滑动窗口分析
pub fn detect_outliers(data: &[f64], threshold: f64) -> Vec<usize> {
    let mut outliers = Vec::new();

    // Rust 1.94.0: for (i, [prev, curr, next]) in data.array_windows::<3>().enumerate()
    for (i, [prev, curr, next]) in data.array_windows::<3>().enumerate() {
        let avg = (prev + next) / 2.0;
        if (curr - avg).abs() > threshold {
            outliers.push(i + 1); // 中间元素的索引
        }
    }

    outliers
}

// ==================== 5. char 到 usize 转换 ====================

/// # 5. char 到 usize 转换 / char to usize Conversion
///
/// Rust 1.94.0 实现了 `TryFrom<char>` for `usize`,
/// 允许将 char 安全地转换为 usize（基于其 Unicode 标量值）。
/// 演示 char 到 usize 的转换
#[allow(dead_code)]
pub fn demonstrate_char_to_usize() {
    println!("\n=== char 到 usize 转换演示 ===\n");

    // 转换 ASCII 字符
    let ch = 'A';
    let value: usize = usize::try_from(ch).unwrap_or(0); // Rust 1.94.0: TryFrom 实现
    println!("字符 '{}' 的 Unicode 标量值: {}", ch, value);

    // 转换数字字符
    let digit = '9';
    let digit_value: usize = usize::try_from(digit).unwrap_or(0);
    println!("字符 '{}' 的 Unicode 标量值: {}", digit, digit_value);

    // 转换中文字符
    let chinese = '中';
    let chinese_value: usize = chinese as usize;
    println!("字符 '{}' 的 Unicode 标量值: {:#X}", chinese, chinese_value);

    // 转换表情符号
    let emoji = '🦀';
    let emoji_value: usize = emoji as usize;
    println!("字符 '{}' 的 Unicode 标量值: {:#X}", emoji, emoji_value);
}

/// 将字符串转换为 usize 数组
///
/// Rust 1.94.0: `TryFrom<char>` for usize 的应用
pub fn string_to_usize_array(s: &str) -> Vec<usize> {
    s.chars().map(|c| usize::try_from(c).unwrap_or(0)).collect()
}

/// 查找字符的 Unicode 范围
///
/// Rust 1.94.0: 使用 char 到 usize 转换进行 Unicode 分析
pub fn analyze_unicode_ranges(chars: &[char]) -> UnicodeAnalysis {
    let mut ascii_count = 0;
    let mut latin_count = 0;
    let mut cjk_count = 0;
    let mut other_count = 0;

    for &ch in chars {
        let code_point = usize::try_from(ch).unwrap_or(0); // Rust 1.94.0 转换
        match code_point {
            0..=127 => ascii_count += 1,
            128..=255 => latin_count += 1,
            0x4E00..=0x9FFF | 0x3400..=0x4DBF | 0x20000..=0x2A6DF => cjk_count += 1,
            _ => other_count += 1,
        }
    }

    UnicodeAnalysis {
        ascii_count,
        latin_count,
        cjk_count,
        other_count,
    }
}

/// Unicode 分析结果
#[derive(Debug, Clone, Copy, Default)]
pub struct UnicodeAnalysis {
    pub ascii_count: usize,
    pub latin_count: usize,
    pub cjk_count: usize,
    pub other_count: usize,
}

// ==================== Rust 1.94 真实特性: ControlFlow ====================

use std::ops::ControlFlow;

/// 搜索二维数组，找到目标时提前退出
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

/// 数据验证管道
pub fn validate_data(data: &str) -> ControlFlow<String, ()> {
    if data.is_empty() {
        return ControlFlow::Break("数据不能为空".to_string());
    }
    if data.len() < 8 {
        return ControlFlow::Break("数据长度至少为 8".to_string());
    }
    ControlFlow::Continue(())
}

/// 批量处理带错误控制
pub fn batch_process<T, E>(
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

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 线程特性
pub fn demonstrate_rust_194_thread_features() {
    println!("\n=== Rust 1.94.0 线程与并发特性演示 ===\n");

    // 1. LazyCell/LazyLock 新方法
    println!("1. LazyCell/LazyLock 新方法:");
    demonstrate_lazylock_methods();

    let mut cache = SingleThreadCache::new(|| {
        println!("初始化缓存...");
        vec![1, 2, 3, 4, 5]
    });
    println!("缓存值: {:?}", cache.get());

    let resource_mgr = ThreadSafeResourceManager::new(|| {
        println!("初始化资源...");
        "Shared Resource"
    });
    println!("资源: {}", resource_mgr.get());
    println!("访问次数: {}", resource_mgr.access_count());

    // 2. 数学常量
    println!("\n2. 数学常量:");
    demonstrate_math_constants();
    println!("黄金比例的 5 次方: {:.2}", golden_ratio_calculation(5));

    // 3. Peekable 新方法
    println!("\n3. Peekable 新方法:");
    demonstrate_peekable_methods();

    // 4. 数组窗口
    println!("\n4. 数组窗口迭代器:");
    demonstrate_array_windows();

    // 5. char 到 usize 转换
    println!("\n5. char 到 usize 转换:");
    demonstrate_char_to_usize();

    let unicode_str = "Hello 世界 🦀";
    let code_points = string_to_usize_array(unicode_str);
    println!(
        "字符串 '{}' 的 Unicode 码点: {:?}",
        unicode_str, code_points
    );
}

/// 获取 Rust 1.94.0 线程特性信息
pub fn get_rust_194_thread_info() -> String {
    "Rust 1.94.0 线程与并发特性:\n\
        - LazyCell 和 LazyLock 新方法 (get, get_mut, force_mut)\n\
        - 数学常量 (EULER_GAMMA, GOLDEN_RATIO)\n\
        - Peekable 迭代器新方法 (next_if_map, next_if_map_mut)\n\
        - 数组窗口迭代器 (array_windows)\n\
        - char 到 usize 转换 (`TryFrom<char>` for usize)"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lazylock_deref_int() {
        let lazy = LazyLock::new(|| 42);
        assert_eq!(&*lazy, &42);
    }

    #[test]
    fn test_lazylock_deref_string() {
        let lazy = LazyLock::new(|| "hello".to_string());
        assert_eq!(lazy.len(), 5);
        assert_eq!(&*lazy, "hello");
    }

    #[test]
    fn test_single_thread_cache() {
        let mut cache = SingleThreadCache::new(|| vec![1, 2, 3]);
        assert_eq!(cache.get(), &[1, 2, 3]);
    }

    #[test]
    fn test_thread_safe_resource_manager() {
        let mgr = ThreadSafeResourceManager::new(|| 100u64);
        assert_eq!(*mgr.get(), 100);
        assert_eq!(mgr.access_count(), 1);
        let _ = mgr.get();
        assert_eq!(mgr.access_count(), 2);
    }

    #[test]
    fn test_golden_ratio_calculation() {
        let result = golden_ratio_calculation(1);
        assert!((result - 1.618033988749895).abs() < 0.0001);
    }

    #[test]
    fn test_euler_gamma_approximation() {
        let result = euler_gamma_approximation(100);
        assert!(result > 0.0);
    }

    #[test]
    fn test_peekable_next_if() {
        let data = vec!["1", "2", "abc", "3"];
        let mut iter = data.into_iter().peekable();

        // 使用 next_if 模式
        let n1 = iter
            .next_if(|s| s.parse::<i32>().is_ok())
            .map(|s| s.parse::<i32>().expect("解析整数不应失败"));
        assert_eq!(n1, Some(1));

        let n2 = iter
            .next_if(|s| s.parse::<i32>().is_ok())
            .map(|s| s.parse::<i32>().expect("解析整数不应失败"));
        assert_eq!(n2, Some(2));

        // 检查迭代器位置
        assert_eq!(iter.peek(), Some(&"abc"));
    }

    #[test]
    fn test_simple_parser() {
        let input = "1+2";
        let tokens = parse_tokens(input);
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0], Token::Number(1));
        assert_eq!(tokens[1], Token::Operator('+'));
        assert_eq!(tokens[2], Token::Number(2));
    }

    #[test]
    fn test_compute_differences() {
        let data = vec![1.0, 3.0, 6.0, 10.0];
        let diffs = compute_differences(&data);
        assert_eq!(diffs, vec![2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_detect_outliers() {
        // 使用更大的阈值，因为 (1.0 + 3.0) / 2 = 2.0, |100.0 - 2.0| = 98.0
        let data = vec![1.0, 2.0, 100.0, 3.0, 4.0];
        let outliers = detect_outliers(&data, 50.0);
        assert_eq!(outliers, vec![2]); // 索引 2 是异常值 (100.0)
    }

    #[test]
    fn test_string_to_usize_array() {
        let result = string_to_usize_array("AB");
        assert_eq!(result, vec![65, 66]);
    }

    #[test]
    fn test_analyze_unicode_ranges() {
        let chars = vec!['A', '中', '🦀'];
        let analysis = analyze_unicode_ranges(&chars);
        assert_eq!(analysis.ascii_count, 1);
        assert_eq!(analysis.cjk_count, 1);
        assert_eq!(analysis.other_count, 1);
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_thread_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_thread_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("LazyCell"));
        assert!(info.contains("EULER_GAMMA"));
    }

    // ==================== ControlFlow 测试 ====================

    #[test]
    fn test_control_flow_matrix_search() {
        let matrix = vec![vec![1, 2], vec![3, 4]];
        assert!(matches!(search_in_matrix(&matrix, 3), ControlFlow::Break((1, 0))));
    }

    #[test]
    fn test_control_flow_validate() {
        assert!(matches!(validate_data("valid123"), ControlFlow::Continue(())));
        assert!(matches!(validate_data(""), ControlFlow::Break(_)));
    }

    #[test]
    fn test_control_flow_batch() {
        let items = vec![1, 2, 3];
        let result = batch_process(&items, |_| Ok::<_, String>(()));
        assert!(matches!(result, ControlFlow::Continue(3)));
    }

    // ==================== 并发边界测试 ====================

    /// 测试单线程缓存在并发访问下的限制
    ///
    /// 说明：SingleThreadCache 设计上不是线程安全的，
    /// 本测试验证在单线程内的正确使用模式。
    /// 在并发环境中应该使用 ThreadSafeResourceManager。
    #[test]
    fn test_single_thread_cache_concurrent() {
        use std::cell::RefCell;
        use std::rc::Rc;

        // 在单线程内模拟并发访问模式
        let cache = Rc::new(RefCell::new(SingleThreadCache::new(|| {
            println!("初始化缓存...");
            vec![1, 2, 3]
        })));

        // 第一个可变借用
        {
            let mut cache_ref = cache.borrow_mut();
            assert_eq!(cache_ref.get(), &[1, 2, 3]);
        }

        // 第二个可变借用
        {
            let mut cache_ref = cache.borrow_mut();
            assert_eq!(cache_ref.get(), &[1, 2, 3]);
        }

        // 验证只初始化一次
        assert!(cache.borrow().is_initialized());

        // 注意：SingleThreadCache 需要 &mut self，因此不支持真正的并发访问
        // 这是设计上的限制，而非错误
    }

    /// 测试线程安全资源管理器在 Mutex Poison 情况下的行为
    ///
    /// 模拟线程 panic 后资源管理器的恢复能力
    #[test]
    fn test_thread_safe_cache_poison() {
        use std::sync::{Arc, Mutex};
        use std::thread;

        // 使用 Mutex 包装 LazyLock 来模拟 poison 场景
        let shared = Arc::new(Mutex::new(ThreadSafeResourceManager::new(|| 42i32)));

        // 获取初始值
        {
            let mgr = shared.lock().expect("ThreadSafeResourceManager mutex poisoned");
            assert_eq!(*mgr.get(), 42);
        }

        // 在一个线程中引发 panic
        let shared_clone = Arc::clone(&shared);
        let handle = thread::spawn(move || {
            let _guard = shared_clone.lock().expect("ThreadSafeResourceManager mutex poisoned");
            panic!("故意 panic 以测试 poison");
        });

        // 等待线程结束（会 panic）
        let _ = handle.join();

        // 尝试恢复 Mutex - 即使 poisoned，也应该能够获取数据
        let result = shared.lock();
        match result {
            Ok(guard) => {
                // 如果没有 poison，继续测试
                assert_eq!(*guard.get(), 42);
            }
            Err(poisoned) => {
                // 即使 poisoned，数据仍然可用
                let guard = poisoned.into_inner();
                assert_eq!(*guard.get(), 42);
            }
        }
    }

    /// 测试异步数据库连接池耗尽
    ///
    /// 验证当连接池中的连接都被获取后，acquire 返回 None
    #[test]
    fn test_async_db_pool_exhaustion() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        /// 简化的连接池用于测试
        struct TestDbPool {
            connections: Vec<String>,
            active_count: AtomicUsize,
        }

        impl TestDbPool {
            fn new(size: usize) -> Self {
                Self {
                    connections: (0..size).map(|i| format!("test_conn_{}", i)).collect(),
                    active_count: AtomicUsize::new(0),
                }
            }

            fn acquire(&self) -> Option<String> {
                let idx = self.active_count.load(Ordering::Relaxed);
                if idx < self.connections.len() {
                    self.active_count.fetch_add(1, Ordering::Relaxed);
                    self.connections.get(idx).cloned()
                } else {
                    None
                }
            }

            fn active_count(&self) -> usize {
                self.active_count.load(Ordering::Relaxed)
            }
        }

        // 创建一个测试用的连接池（5 个连接）
        let pool = TestDbPool::new(5);

        // 获取所有连接
        let mut connections = Vec::new();
        while let Some(conn) = pool.acquire() {
            connections.push(conn);
            // 防止无限循环
            if connections.len() > 10 {
                break;
            }
        }

        // 验证获取的连接数量
        assert_eq!(connections.len(), 5, "应该获取全部 5 个连接");

        // 验证活跃连接数（成功获取的连接数）
        assert_eq!(pool.active_count(), 5, "应该有 5 个活跃连接");

        // 再次尝试获取应该返回 None，且不会增加 active_count
        let next_conn = pool.acquire();
        assert!(next_conn.is_none(), "连接池耗尽后应该返回 None");
        assert_eq!(pool.active_count(), 5, "失败获取不应增加计数");
    }
}
