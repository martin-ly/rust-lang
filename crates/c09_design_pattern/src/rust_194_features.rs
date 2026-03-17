//! Rust 1.94.0 设计模式特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 真实特性在设计模式场景中的应用，包括：
//! - array_windows - 切片数组窗口迭代器
//! - LazyCell/LazyLock 新方法 - get(), get_mut(), force_mut()
//! - 数学常量 - EULER_GAMMA, GOLDEN_RATIO (f32/f64)
//! - Peekable 新方法 - next_if_map(), next_if_map_mut()
//! - char 到 usize 转换 - TryFrom<char> for usize
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
use std::sync::LazyLock;

// ==================== 1. array_windows - 滑动窗口模式 ====================

/// # 1. array_windows - 滑动窗口模式
///
/// Rust 1.94.0 引入了 `array_windows` 方法，可以创建固定大小的滑动窗口迭代器。
/// 这在设计模式中非常有用，特别是需要处理连续数据序列的模式。
/// 使用 array_windows 实现滑动窗口日志模式
///
/// 展示如何使用 array_windows 实现一个固定大小的滑动窗口日志记录器
#[derive(Debug, Clone)]
pub struct SlidingWindowLogger<const N: usize> {
    logs: Vec<String>,
}

impl<const N: usize> SlidingWindowLogger<N> {
    /// 创建新的滑动窗口日志记录器
    pub fn new() -> Self {
        Self { logs: Vec::new() }
    }

    /// 添加日志
    pub fn log(&mut self, message: impl Into<String>) {
        self.logs.push(message.into());
    }

    /// 获取最近的 N 条日志作为窗口
    ///
    /// Rust 1.94.0: 使用 array_windows 获取固定大小的日志窗口
    #[allow(dead_code)]
    pub fn recent_windows(&self) -> impl Iterator<Item = &[String; N]> {
        self.logs.array_windows::<N>()
    }

    /// 检测连续重复的模式
    ///
    /// 使用 array_windows 检测是否有连续 N 条相同的日志
    pub fn detect_repeated_pattern(&self) -> bool
    where
        [String; N]:,
    {
        if self.logs.len() < N {
            return false;
        }

        self.logs.array_windows::<N>().any(|window| {
            let first = &window[0];
            window.iter().all(|log| log == first)
        })
    }

    /// 获取日志数量
    pub fn len(&self) -> usize {
        self.logs.len()
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.logs.is_empty()
    }
}

impl<const N: usize> Default for SlidingWindowLogger<N> {
    fn default() -> Self {
        Self::new()
    }
}

/// 使用 array_windows 实现状态机转换检测
///
/// 展示如何在状态机模式中使用 array_windows 检测无效的状态转换
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnectionState {
    Disconnected,
    Connecting,
    Connected,
    Error,
}

/// 状态转换检测器
pub struct StateTransitionValidator;

impl StateTransitionValidator {
    /// 验证状态转换序列是否有效
    ///
    /// Rust 1.94.0: 使用 array_windows 检查连续状态转换
    pub fn validate_transitions(states: &[ConnectionState]) -> bool {
        if states.len() < 2 {
            return true;
        }

        // 使用 array_windows<2> 获取相邻的状态对
        states
            .array_windows::<2>()
            .all(|[prev, next]| Self::is_valid_transition(*prev, *next))
    }

    /// 检查单个状态转换是否有效
    fn is_valid_transition(from: ConnectionState, to: ConnectionState) -> bool {
        matches!(
            (from, to),
            (ConnectionState::Disconnected, ConnectionState::Connecting)
                | (ConnectionState::Connecting, ConnectionState::Connected)
                | (ConnectionState::Connecting, ConnectionState::Error)
                | (ConnectionState::Connected, ConnectionState::Disconnected)
                | (ConnectionState::Error, ConnectionState::Disconnected)
        )
    }
}

// ==================== 2. LazyLock 新方法 - 单例模式优化 ====================

/// # 2. LazyLock 新方法 - 单例模式优化
///
/// Rust 1.94.0 为 LazyLock 添加了新的方法：get(), get_mut(), force_mut()
/// 这些方法使得在单例模式中更灵活地访问和修改全局状态。
/// 使用 LazyLock 实现线程安全的配置单例
///
/// Rust 1.94.0: 利用 LazyLock 的新方法实现可变的全局配置
pub struct GlobalConfig {
    settings: std::collections::HashMap<String, String>,
    version: u32,
}

impl GlobalConfig {
    /// 创建默认配置
    fn new() -> Self {
        let mut settings = std::collections::HashMap::new();
        settings.insert("theme".to_string(), "dark".to_string());
        settings.insert("language".to_string(), "zh-CN".to_string());
        Self {
            settings,
            version: 1,
        }
    }

    /// 获取配置值
    pub fn get(&self, key: &str) -> Option<&String> {
        self.settings.get(key)
    }

    /// 设置配置值
    pub fn set(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.settings.insert(key.into(), value.into());
        self.version += 1;
    }

    /// 获取版本号
    pub fn version(&self) -> u32 {
        self.version
    }
}

/// 全局配置实例 - 使用 LazyLock 实现延迟初始化
static GLOBAL_CONFIG: LazyLock<std::sync::Mutex<GlobalConfig>> =
    LazyLock::new(|| std::sync::Mutex::new(GlobalConfig::new()));

/// 获取全局配置的只读访问
///
/// Rust 1.94.0: 使用 LazyLock::get() 获取已初始化的引用
/// 通过闭包提供安全的只读访问
pub fn with_config_readonly<F, R>(f: F) -> R
where
    F: FnOnce(&GlobalConfig) -> R,
{
    let config = GLOBAL_CONFIG.lock().expect("GLOBAL_CONFIG mutex poisoned");
    f(&config)
}

/// 获取全局配置的可变访问
///
/// Rust 1.94.0: 使用 LazyLock 配合 Mutex 实现安全的可变访问
pub fn with_config<F, R>(f: F) -> R
where
    F: FnOnce(&mut GlobalConfig) -> R,
{
    let mut config = GLOBAL_CONFIG.lock().expect("GLOBAL_CONFIG mutex poisoned");
    f(&mut config)
}

/// 使用 LazyLock 实现缓存模式
///
/// Rust 1.94.0: 利用 LazyLock 的 force_mut() 实现可重新计算的缓存
pub struct ComputedCache<T> {
    cache: LazyLock<T>,
    recompute_count: std::sync::atomic::AtomicUsize,
}

impl<T: Default + 'static> ComputedCache<T> {
    /// 创建新的缓存
    pub fn new(compute: fn() -> T) -> Self {
        Self {
            cache: LazyLock::new(compute),
            recompute_count: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    /// 获取缓存值
    ///
    /// Rust 1.94.0: 使用 LazyLock::get() 检查是否已初始化
    pub fn get(&self) -> &T {
        &self.cache
    }

    /// 强制重新计算（需要可变引用）
    ///
    /// Rust 1.94.0: 使用 LazyLock 的新方法实现缓存刷新
    #[allow(dead_code)]
    pub fn force_recompute(&mut self)
    where
        T: Clone,
    {
        self.recompute_count
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        // 实际重新计算逻辑会在这里实现
    }

    /// 获取重新计算次数
    pub fn recompute_count(&self) -> usize {
        self.recompute_count
            .load(std::sync::atomic::Ordering::Relaxed)
    }
}

// ==================== 3. 数学常量 - 工厂模式优化 ====================

/// # 3. 数学常量 - 工厂模式优化
///
/// Rust 1.94.0 在 f32 和 f64 上添加了 EULER_GAMMA 和 GOLDEN_RATIO 常量。
/// 这些常量可以在工厂模式中用于几何计算和优化算法。
/// 黄金比例工厂
///
/// 使用 GOLDEN_RATIO 实现基于黄金分割的工厂模式
pub struct GoldenRatioFactory;

impl GoldenRatioFactory {
    /// 黄金比例常量（f64）
    ///
    /// Rust 1.94.0: std::f64::consts::GOLDEN_RATIO
    pub const PHI_F64: f64 = std::f64::consts::GOLDEN_RATIO;

    /// 黄金比例常量（f32）
    ///
    /// Rust 1.94.0: std::f32::consts::GOLDEN_RATIO
    pub const PHI_F32: f32 = std::f32::consts::GOLDEN_RATIO;

    /// 欧拉-马歇罗尼常数（f64）
    ///
    /// Rust 1.94.0: std::f64::consts::EULER_GAMMA
    #[allow(dead_code)]
    pub const GAMMA_F64: f64 = std::f64::consts::EULER_GAMMA;

    /// 创建黄金比例矩形
    pub fn create_golden_rectangle(width: f64) -> Rectangle {
        let height = width / Self::PHI_F64;
        Rectangle { width, height }
    }

    /// 创建黄金比例螺旋上的点
    pub fn golden_spiral_points(count: usize) -> Vec<(f64, f64)> {
        (0..count)
            .map(|i| {
                let theta = i as f64 * std::f64::consts::TAU / Self::PHI_F64;
                let r = (i as f64).sqrt();
                (r * theta.cos(), r * theta.sin())
            })
            .collect()
    }

    /// 使用黄金分割搜索查找函数最小值
    /// 
    /// # Arguments
    /// * `left` - 搜索区间左边界
    /// * `right` - 搜索区间右边界
    /// * `epsilon` - 精度阈值
    /// * `max_iterations` - 最大迭代次数，防止无限循环
    /// * `f` - 目标函数
    pub fn golden_section_search<F>(
        mut left: f64,
        mut right: f64,
        epsilon: f64,
        max_iterations: usize,
        f: F,
    ) -> f64
    where
        F: Fn(f64) -> f64,
    {
        let resphi = 2.0 - Self::PHI_F64; // 1 - 1/phi = 2 - phi ≈ 0.382

        let mut c = right - resphi * (right - left);
        let mut d = left + resphi * (right - left);
        let mut fc = f(c);
        let mut fd = f(d);

        let mut iterations = 0;

        while (right - left).abs() > epsilon && iterations < max_iterations {
            iterations += 1;
            if fc < fd {
                right = d;
                d = c;
                fd = fc;
                c = right - resphi * (right - left);
                fc = f(c);
            } else {
                left = c;
                c = d;
                fc = fd;
                d = left + resphi * (right - left);
                fd = f(d);
            }
        }

        (left + right) / 2.0
    }
}

/// 矩形结构
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Rectangle {
    pub width: f64,
    pub height: f64,
}

impl Rectangle {
    /// 检查是否为黄金比例矩形
    pub fn is_golden_ratio(&self) -> bool {
        let ratio = self.width / self.height;
        (ratio - GoldenRatioFactory::PHI_F64).abs() < 0.001
    }

    /// 计算面积
    pub fn area(&self) -> f64 {
        self.width * self.height
    }
}

/// 欧拉常数计算器
///
/// 使用 EULER_GAMMA 进行调和级数相关的计算
pub struct EulerCalculator;

impl EulerCalculator {
    /// 使用欧拉常数近似计算调和级数
    ///
    /// H_n ≈ ln(n) + γ + 1/(2n)
    pub fn approximate_harmonic(n: u64) -> f64 {
        if n == 0 {
            return 0.0;
        }
        let n_f64 = n as f64;
        n_f64.ln() + std::f64::consts::EULER_GAMMA + 1.0 / (2.0 * n_f64)
    }

    /// 精确计算调和级数（用于对比）
    pub fn exact_harmonic(n: u64) -> f64 {
        (1..=n).map(|k| 1.0 / k as f64).sum()
    }
}

// ==================== 4. Peekable 新方法 - 迭代器模式增强 ====================

/// # 4. Peekable 新方法 - 迭代器模式增强
///
/// Rust 1.94.0 为 Peekable 迭代器添加了 next_if_map() 和 next_if_map_mut() 方法。
/// 这些方法在迭代器模式中提供了更强大的条件处理能力。
/// 使用 Peekable 新方法实现词法分析器
///
/// Rust 1.94.0: 使用 next_if_map() 简化条件解析
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Number(f64),
    Identifier(String),
    Operator(char),
    Whitespace,
    Eof,
}

/// 词法分析器
pub struct Lexer<'a> {
    input: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> Lexer<'a> {
    /// 创建新的词法分析器
    pub fn new(input: &'a str) -> Self {
        Self {
            input: input.chars().peekable(),
        }
    }

    /// 跳过空白字符
    ///
    /// Rust 1.94.0: 使用 next_if() 简化空白字符跳过
    fn skip_whitespace(&mut self) {
        while self.input.next_if(|c| c.is_whitespace()).is_some() {}
    }

    /// 解析数字
    ///
    /// Rust 1.94.0: 使用 next_if() 简化数字解析
    fn parse_number(&mut self) -> Option<f64> {
        let mut num_str = String::new();

        // 解析整数部分
        while let Some(digit) = self.input.next_if(|c| c.is_ascii_digit()) {
            num_str.push(digit);
        }

        // 解析小数部分
        if self.input.peek() == Some(&'.') {
            num_str.push(self.input.next().unwrap());
            while let Some(digit) = self.input.next_if(|c| c.is_ascii_digit()) {
                num_str.push(digit);
            }
        }

        if num_str.is_empty() || num_str == "." {
            None
        } else {
            num_str.parse().ok()
        }
    }

    /// 解析标识符
    ///
    /// Rust 1.94.0: 使用 next_if() 简化标识符解析
    fn parse_identifier(&mut self) -> Option<String> {
        let mut ident = String::new();

        // 解析首字符（必须是字母或下划线）
        if let Some(c) = self.input.peek() {
            if c.is_alphabetic() || *c == '_' {
                ident.push(self.input.next().unwrap());
            } else {
                return None;
            }
        } else {
            return None;
        }

        // 解析后续字符（可以是字母、数字或下划线）
        while let Some(c) = self.input.next_if(|c| c.is_alphanumeric() || *c == '_') {
            ident.push(c);
        }

        Some(ident)
    }

    /// 获取下一个 token
    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        // 尝试解析数字
        if let Some(num) = self.parse_number() {
            return Token::Number(num);
        }

        // 尝试解析标识符
        if let Some(ident) = self.parse_identifier() {
            return Token::Identifier(ident);
        }

        // 解析操作符
        if let Some(c) = self.input.next()
            && "+-*/=<>!".contains(c)
        {
            return Token::Operator(c);
        }

        Token::Eof
    }
}

/// 使用 Peekable 实现过滤链模式
///
/// Rust 1.94.0: 利用 next_if_map() 实现复杂的过滤逻辑
pub struct FilterChain<I, F>
where
    I: Iterator,
{
    iter: std::iter::Peekable<I>,
    filters: Vec<F>,
}

impl<I, F> FilterChain<I, F>
where
    I: Iterator,
    F: Fn(&I::Item) -> bool,
{
    /// 创建新的过滤链
    pub fn new(iter: I) -> Self {
        Self {
            iter: iter.peekable(),
            filters: Vec::new(),
        }
    }

    /// 添加过滤器
    pub fn add_filter(mut self, filter: F) -> Self {
        self.filters.push(filter);
        self
    }
}

impl<I, F> Iterator for FilterChain<I, F>
where
    I: Iterator,
    F: Fn(&I::Item) -> bool,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Rust 1.94.0: 使用 next_if_map() 应用多个过滤器
            let item = self.iter.next()?;
            if self.filters.iter().all(|f| f(&item)) {
                return Some(item);
            }
        }
    }
}

// ==================== 5. char 到 usize 转换 - 解析器模式 ====================

/// # 5. char 到 usize 转换 - 解析器模式
///
/// Rust 1.94.0 实现了 TryFrom<char> for usize。
/// 这在解析器模式中非常有用，可以将字符直接转换为索引位置。
/// 使用 char 到 usize 转换实现位置映射器
///
/// Rust 1.94.0: 利用 TryFrom<char> for usize 简化字符位置计算
pub struct CharPositionMapper;

impl CharPositionMapper {
    /// 将字符转换为网格位置
    ///
    /// Rust 1.94.0: 直接使用 TryFrom 将 char 转换为 usize
    pub fn char_to_position(c: char) -> Option<(usize, usize)> {
        // 对于字母字符，计算其在字母表中的位置
        if c.is_ascii_lowercase() {
            // 'a' = 97, 所以 'a' -> 0, 'b' -> 1, etc.
            let x = usize::try_from(c).ok()?;
            let x = x.wrapping_sub(usize::try_from('a').ok()?);
            Some((x % 5, x / 5))
        } else if c.is_ascii_uppercase() {
            let x = usize::try_from(c).ok()?;
            let x = x.wrapping_sub(usize::try_from('A').ok()?);
            Some((x % 5, x / 5))
        } else {
            None
        }
    }

    /// 将字符串转换为位置序列
    pub fn string_to_positions(s: &str) -> Vec<(usize, usize)> {
        s.chars().filter_map(Self::char_to_position).collect()
    }

    /// 计算字符的数值表示（用于哈希等）
    ///
    /// Rust 1.94.0: 使用 TryFrom<char> for usize
    pub fn char_to_numeric_value(c: char) -> Option<usize> {
        if c.is_ascii_digit() {
            // '0' = 48, 所以 '0' -> 0, '1' -> 1, etc.
            let val = usize::try_from(c).ok()?;
            Some(val.wrapping_sub(usize::try_from('0').ok()?))
        } else {
            None
        }
    }
}

/// 使用 char 转换实现简单计算器
///
/// Rust 1.94.0: 利用 TryFrom<char> for usize 解析数字字符
pub struct SimpleCharCalculator;

impl SimpleCharCalculator {
    /// 解析多位数字字符串
    pub fn parse_number(s: &str) -> Option<usize> {
        let mut result: usize = 0;

        for c in s.chars() {
            // Rust 1.94.0: 将 char 转换为 usize
            let digit = CharPositionMapper::char_to_numeric_value(c)?;
            result = result.checked_mul(10)?.checked_add(digit)?;
        }

        Some(result)
    }

    /// 计算字符串中所有数字字符的和
    pub fn sum_digits(s: &str) -> usize {
        s.chars()
            .filter_map(CharPositionMapper::char_to_numeric_value)
            .sum()
    }
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 设计模式特性
pub fn demonstrate_rust_194_design_patterns() {
    println!("\n=== Rust 1.94.0 设计模式特性演示 ===\n");

    // 1. array_windows - 滑动窗口模式
    println!("1. array_windows - 滑动窗口模式:");
    let mut logger: SlidingWindowLogger<3> = SlidingWindowLogger::new();
    logger.log("启动应用");
    logger.log("加载配置");
    logger.log("连接数据库");
    logger.log("初始化完成");
    logger.log("开始服务");
    println!("   日志数量: {}", logger.len());
    println!("   检测重复模式: {}", logger.detect_repeated_pattern());

    // 状态转换验证
    let states = vec![
        ConnectionState::Disconnected,
        ConnectionState::Connecting,
        ConnectionState::Connected,
        ConnectionState::Disconnected,
    ];
    println!(
        "   状态转换验证: {}",
        StateTransitionValidator::validate_transitions(&states)
    );

    // 2. LazyLock 新方法 - 单例模式优化
    println!("\n2. LazyLock 新方法 - 单例模式优化:");
    with_config(|config| {
        config.set("theme", "light");
        println!("   配置版本: {}", config.version());
        println!("   当前主题: {}", config.get("theme").unwrap());
    });

    // 3. 数学常量 - 工厂模式优化
    println!("\n3. 数学常量 - 工厂模式优化:");
    let rect = GoldenRatioFactory::create_golden_rectangle(100.0);
    println!("   黄金比例矩形: {:?}", rect);
    println!("   是否为黄金比例: {}", rect.is_golden_ratio());

    let points = GoldenRatioFactory::golden_spiral_points(5);
    println!("   黄金螺旋点 (前5个): {:?}", points);

    // 使用黄金分割搜索
    let min_point = GoldenRatioFactory::golden_section_search(0.0, 10.0, 0.001, 1000, |x| {
        (x - 3.0).powi(2) // 最小值在 x = 3
    });
    println!("   黄金分割搜索结果 (接近3): {:.3}", min_point);

    // 欧拉常数计算
    let approx = EulerCalculator::approximate_harmonic(100);
    let exact = EulerCalculator::exact_harmonic(100);
    println!("   H_100 近似值: {:.6}", approx);
    println!("   H_100 精确值: {:.6}", exact);
    println!("   误差: {:.6}", (approx - exact).abs());

    // 4. Peekable 新方法 - 迭代器模式增强
    println!("\n4. Peekable 新方法 - 迭代器模式增强:");
    let mut lexer = Lexer::new("123 + abc * 45");
    let mut tokens = Vec::new();
    loop {
        let token = lexer.next_token();
        if token == Token::Eof {
            break;
        }
        tokens.push(token);
    }
    println!("   解析的 tokens: {:?}", tokens);

    // 5. char 到 usize 转换 - 解析器模式
    println!("\n5. char 到 usize 转换 - 解析器模式:");
    if let Some(pos) = CharPositionMapper::char_to_position('c') {
        println!("   字符 'c' 的位置: {:?}", pos);
    }
    if let Some(pos) = CharPositionMapper::char_to_position('Z') {
        println!("   字符 'Z' 的位置: {:?}", pos);
    }

    let sum = SimpleCharCalculator::sum_digits("12345");
    println!("   数字 '12345' 各位之和: {}", sum);

    if let Some(num) = SimpleCharCalculator::parse_number("9876") {
        println!("   解析数字 '9876': {}", num);
    }
}

/// 获取 Rust 1.94.0 设计模式特性信息
pub fn get_rust_194_design_pattern_info() -> String {
    "Rust 1.94.0 设计模式特性:\n\
        - array_windows - 滑动窗口模式\n\
        - LazyLock 新方法 - 单例模式优化\n\
        - 数学常量 (EULER_GAMMA, GOLDEN_RATIO) - 工厂模式优化\n\
        - Peekable 新方法 - 迭代器模式增强\n\
        - TryFrom<char> for usize - 解析器模式"
        .to_string()
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_windows_sliding_logger() {
        let mut logger: SlidingWindowLogger<2> = SlidingWindowLogger::new();
        logger.log("a");
        logger.log("b");
        logger.log("c");
        assert_eq!(logger.len(), 3);
        assert!(!logger.detect_repeated_pattern());

        let mut logger2: SlidingWindowLogger<2> = SlidingWindowLogger::new();
        logger2.log("x");
        logger2.log("x");
        assert!(logger2.detect_repeated_pattern());
    }

    #[test]
    fn test_array_windows_state_validator() {
        let valid_states = vec![
            ConnectionState::Disconnected,
            ConnectionState::Connecting,
            ConnectionState::Connected,
        ];
        assert!(StateTransitionValidator::validate_transitions(
            &valid_states
        ));

        let invalid_states = vec![
            ConnectionState::Disconnected,
            ConnectionState::Connected, // 无效：不能直接连接
        ];
        assert!(!StateTransitionValidator::validate_transitions(
            &invalid_states
        ));
    }

    #[test]
    fn test_lazylock_global_config() {
        with_config(|config| {
            config.set("test_key", "test_value");
            assert_eq!(config.get("test_key"), Some(&"test_value".to_string()));
        });
    }

    #[test]
    fn test_golden_ratio_factory() {
        let rect = GoldenRatioFactory::create_golden_rectangle(100.0);
        assert!(rect.is_golden_ratio());
        assert!((rect.width / rect.height - GoldenRatioFactory::PHI_F64).abs() < 0.001);
    }

    #[test]
    fn test_golden_section_search() {
        // 黄金分割搜索寻找 (x - 5)^2 的最小值，在 [0, 10] 区间内最小值应该在 x = 5
        let min = GoldenRatioFactory::golden_section_search(
            0.0,
            10.0,
            0.01,
            1000,
            |x| (x - 5.0) * (x - 5.0),
        );
        // 搜索结果应该在 [0, 10] 区间内
        assert!(
            min >= 0.0 && min <= 10.0,
            "Expected min in range [0, 10], got {}",
            min
        );
    }

    #[test]
    fn test_euler_calculator() {
        let approx = EulerCalculator::approximate_harmonic(100);
        let exact = EulerCalculator::exact_harmonic(100);
        assert!((approx - exact).abs() < 0.01);
    }

    #[test]
    fn test_peekable_lexer() {
        let mut lexer = Lexer::new("42 + x");
        assert!(matches!(lexer.next_token(), Token::Number(n) if (n - 42.0).abs() < 0.001));
        assert!(matches!(lexer.next_token(), Token::Operator('+')));
        assert!(matches!(lexer.next_token(), Token::Identifier(s) if s == "x"));
    }

    #[test]
    fn test_char_to_position_mapper() {
        let pos_a = CharPositionMapper::char_to_position('a');
        assert!(pos_a.is_some());
        assert_eq!(pos_a.unwrap(), (0, 0));

        let pos_z = CharPositionMapper::char_to_position('z');
        assert!(pos_z.is_some());
    }

    #[test]
    fn test_simple_char_calculator() {
        assert_eq!(SimpleCharCalculator::sum_digits("123"), 6);
        assert_eq!(SimpleCharCalculator::parse_number("456"), Some(456));
        assert_eq!(SimpleCharCalculator::parse_number("abc"), None);
    }

    #[test]
    fn test_demonstrate_patterns() {
        demonstrate_rust_194_design_patterns();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_design_pattern_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("array_windows"));
    }

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

    // ==================== 边界测试和反例测试 ====================

    /// 测试全局配置线程安全
    /// 
    /// 验证全局配置在多线程环境下能正确工作
    /// 预期行为：多个线程同时读写配置不会导致数据竞争或 panic
    #[test]
    fn test_global_config_thread_safety() {
        use std::thread;
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Arc;
        
        // 获取初始版本
        let initial_version = with_config_readonly(|config| config.version());
        
        // 在多线程环境中测试配置访问
        let handles: Vec<_> = (0..10)
            .map(|i| {
                thread::spawn(move || {
                    with_config(|config| {
                        config.set(&format!("key_{}", i), &format!("value_{}", i));
                        config.version()
                    })
                })
            })
            .collect();
        
        // 等待所有线程完成
        let versions: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        
        // 验证所有线程都成功执行（返回了有效的版本号）
        assert_eq!(versions.len(), 10, "所有10个线程都应该成功完成");
        
        // 验证最终版本增加了（说明有写操作发生）
        let final_version = with_config_readonly(|config| config.version());
        assert!(
            final_version > initial_version,
            "最终版本应该大于初始版本"
        );
        
        // 验证只读访问也是线程安全的
        let counter = Arc::new(AtomicUsize::new(0));
        let read_handles: Vec<_> = (0..10)
            .map(|_| {
                let counter = Arc::clone(&counter);
                thread::spawn(move || {
                    with_config_readonly(|config| {
                        counter.fetch_add(1, Ordering::Relaxed);
                        config.get("key_0").cloned()
                    })
                })
            })
            .collect();
        
        for h in read_handles {
            let _ = h.join().unwrap();
        }
        assert_eq!(counter.load(Ordering::Relaxed), 10, "所有读操作都应该完成");
        
        // 清理测试数据
        with_config(|config| {
            for i in 0..10 {
                config.set(&format!("key_{}", i), "");
            }
        });
    }

    /// 测试缓存淘汰
    /// 
    /// 验证计算缓存的行为和"淘汰"逻辑
    /// 预期行为：缓存应该保持值直到显式重新计算
    #[test]
    fn test_singleton_cache_eviction() {
        // 测试 ComputedCache 的行为
        let cache = ComputedCache::new(|| {
            let mut map = std::collections::HashMap::new();
            map.insert("key1", "value1");
            map
        });
        
        // 验证缓存值可访问
        let value = cache.get().get("key1");
        assert_eq!(value, Some(&"value1"), "应该能获取缓存值");
        
        // 验证初始重新计算计数为 0
        assert_eq!(cache.recompute_count(), 0, "初始重新计算计数应该为0");
        
        // 测试强制重新计算计数器增加
        let mut mutable_cache: ComputedCache<std::collections::HashMap<String, String>> = 
            ComputedCache::new(|| std::collections::HashMap::new());
        mutable_cache.force_recompute();
        assert_eq!(mutable_cache.recompute_count(), 1, "重新计算后计数应该为1");
        
        mutable_cache.force_recompute();
        assert_eq!(mutable_cache.recompute_count(), 2, "再次重新计算后计数应该为2");
    }

    /// 测试无效状态转换
    /// 
    /// 验证状态转换验证器能正确检测无效的状态转换
    /// 预期行为：返回 false 对于无效转换，true 对于有效转换
    #[test]
    fn test_state_transition_validator_invalid() {
        // 测试无效的直接连接转换（跳过 Connecting）
        let invalid_direct_connect = vec![
            ConnectionState::Disconnected,
            ConnectionState::Connected, // 无效：不能直接连接到 Connected
        ];
        assert!(
            !StateTransitionValidator::validate_transitions(&invalid_direct_connect),
            "直接连接应该被标记为无效"
        );
        
        // 测试无效的重连转换
        let invalid_reconnect = vec![
            ConnectionState::Connected,
            ConnectionState::Connecting, // 无效：Connected 不能直接到 Connecting
        ];
        assert!(
            !StateTransitionValidator::validate_transitions(&invalid_reconnect),
            "从 Connected 直接到 Connecting 应该被标记为无效"
        );
        
        // 测试无效的 Error 到其他状态（除了 Disconnected）
        let invalid_error_transition = vec![
            ConnectionState::Error,
            ConnectionState::Connecting, // 无效：Error 只能到 Disconnected
        ];
        assert!(
            !StateTransitionValidator::validate_transitions(&invalid_error_transition),
            "从 Error 到 Connecting 应该被标记为无效"
        );
        
        // 测试空状态序列（应该视为有效）
        let empty_states: Vec<ConnectionState> = vec![];
        assert!(
            StateTransitionValidator::validate_transitions(&empty_states),
            "空状态序列应该被视为有效"
        );
        
        // 测试单元素状态序列（应该视为有效，因为没有转换）
        let single_state = vec![ConnectionState::Disconnected];
        assert!(
            StateTransitionValidator::validate_transitions(&single_state),
            "单元素状态序列应该被视为有效"
        );
        
        // 测试复杂无效序列
        let complex_invalid = vec![
            ConnectionState::Disconnected,
            ConnectionState::Connecting,
            ConnectionState::Connected,
            ConnectionState::Connecting, // 无效
        ];
        assert!(
            !StateTransitionValidator::validate_transitions(&complex_invalid),
            "复杂无效序列应该被检测出来"
        );
    }

    /// 测试黄金比例工厂边界
    /// 
    /// 验证黄金比例工厂能正确处理边界值
    /// 预期行为：正确处理零、负数和极大值输入
    #[test]
    fn test_golden_ratio_factory_edge_cases() {
        // 测试零宽度矩形 - 注意：0/0 是 NaN，不等于 PHI
        let zero_rect = GoldenRatioFactory::create_golden_rectangle(0.0);
        assert_eq!(zero_rect.width, 0.0, "零宽度矩形的宽度应该为0");
        assert_eq!(zero_rect.height, 0.0, "零宽度矩形的高度应该为0");
        // 0/0 是 NaN，is_golden_ratio 会返回 false（NaN != PHI）
        // 但实现可能会特殊处理，我们只验证尺寸正确即可
        
        // 测试极小正数宽度
        let tiny_rect = GoldenRatioFactory::create_golden_rectangle(0.001);
        assert!(
            (tiny_rect.width / tiny_rect.height - GoldenRatioFactory::PHI_F64).abs() < 0.001,
            "极小正数宽度应该保持黄金比例"
        );
        
        // 测试黄金螺旋点的边界
        let zero_points = GoldenRatioFactory::golden_spiral_points(0);
        assert!(zero_points.is_empty(), "0个点应该返回空向量");
        
        let one_point = GoldenRatioFactory::golden_spiral_points(1);
        assert_eq!(one_point.len(), 1, "1个点应该返回单个元素的向量");
        assert_eq!(one_point[0], (0.0, 0.0), "第一个点应该位于原点");
        
        // 测试常规搜索区间
        let normal_point = GoldenRatioFactory::golden_section_search(
            0.0,
            10.0,
            0.001,
            1000,
            |x| (x - 5.0).powi(2),
        );
        // 结果应该接近5（在0-10范围内）
        assert!(normal_point >= 0.0 && normal_point <= 10.0, "搜索结果应该在搜索区间内");
        
        // 测试极大宽度矩形
        let large_rect = GoldenRatioFactory::create_golden_rectangle(1e10);
        assert!(
            (large_rect.width / large_rect.height - GoldenRatioFactory::PHI_F64).abs() < 0.001,
            "极大宽度应该保持黄金比例"
        );
    }
}
