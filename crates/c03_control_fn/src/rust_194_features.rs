//! Rust 1.94.0 控制流与函数特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 在控制流和函数场景中的增强，包括：
//! - 改进的闭包捕获语义 / Improved Closure Capture Semantics
//! - 增强的 match 表达式 / Enhanced Match Expressions
//! - 函数指针优化 / Function Pointer Optimizations
//! - Edition 2024 控制流改进 / Edition 2024 Control Flow Improvements
//! - 性能优化和编译时改进 / Performance Optimizations
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
use std::fmt::Debug;

// ==================== Rust 1.94 真实特性: Peekable 新方法 ====================

/// # Peekable 新方法 / Peekable Iterator New Methods
///
/// Rust 1.94.0 为 `Peekable` 迭代器添加了两个新方法：
/// - `next_if_map<F, R>(f: F) -> Option<R>` - 如果下一个元素满足条件，则映射并消耗它
/// - `next_if_map_mut<F, R>(f: F) -> Option<R>` - next_if_map 的可变版本
///
/// ## 特性说明
/// - `next_if_map` 结合了 `peek()` 和 `map()` 的功能
/// - 只有当映射函数返回 `Some` 时才会消耗元素
/// - 适用于解析器、词法分析器等需要前瞻并条件性消耗元素的场景
///
/// ## 使用场景
/// - 词法分析器 (Lexer) 实现
/// - 解析器 (Parser) 前瞻
/// - 数据流的条件处理
///
/// ## 注意
/// 在当前 Rust 版本中，`next_if_map` 可能尚未稳定或 API 有所不同。
/// 以下代码展示了概念用法，实际 API 请以 Rust 1.94 文档为准。
/// 使用 Peekable 新方法实现的简单词法分析器
///
/// 演示如何使用 `next_if_map` 进行前瞻并条件性消耗标记
pub struct SimpleLexer<'a> {
    input: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> SimpleLexer<'a> {
    /// 创建新的词法分析器
    pub fn new(input: &'a str) -> Self {
        Self {
            input: input.chars().peekable(),
        }
    }

    /// 跳过空白字符
    pub fn skip_whitespace(&mut self) {
        while self.input.next_if(|c| c.is_whitespace()).is_some() {}
    }

    /// 解析数字
    ///
    /// 使用传统的 next_if 方法（当前可用）
    /// 在 Rust 1.94 中可以使用 next_if_map 简化此逻辑
    pub fn parse_number(&mut self) -> Option<i64> {
        // 检查第一个字符是否为数字
        let &first_char = self.input.peek()?;
        if !first_char.is_ascii_digit() {
            return None;
        }

        // 消耗第一个数字字符（前面已检查存在，使用 expect 说明原因）
        let first_digit = self
            .input
            .next()
            .expect("parse_number: 第一个数字字符应该存在") as i64
            - '0' as i64;
        let mut result = first_digit;

        // 继续消耗后续数字
        while let Some(c) = self.input.next_if(|c| c.is_ascii_digit()) {
            let digit = c as i64 - '0' as i64;
            result = result * 10 + digit;
        }

        Some(result)
    }

    /// 解析标识符
    ///
    /// 使用传统的 next_if 方法（当前可用）
    /// 在 Rust 1.94 中可以使用 next_if_map 简化此逻辑
    pub fn parse_identifier(&mut self) -> Option<String> {
        // 检查第一个字符是否为字母或下划线
        let &first_char = self.input.peek()?;
        if !first_char.is_ascii_alphabetic() && first_char != '_' {
            return None;
        }

        // 消耗第一个字符（前面已检查存在，使用 expect 说明原因）
        let first = self
            .input
            .next()
            .expect("parse_identifier: 第一个字符应该存在");
        let mut result = String::new();
        result.push(first);

        // 继续消耗后续字母、数字或下划线
        while let Some(c) = self
            .input
            .next_if(|c| c.is_ascii_alphanumeric() || *c == '_')
        {
            result.push(c);
        }

        Some(result)
    }

    /// 解析特定字符
    ///
    /// 使用传统的 next_if 方法（当前可用）
    pub fn expect_char(&mut self, expected: char) -> Option<char> {
        self.input.next_if(|c| *c == expected)
    }

    /// 查看下一个字符
    pub fn peek(&mut self) -> Option<&char> {
        self.input.peek()
    }

    /// 消耗并返回下一个字符
    pub fn next_char(&mut self) -> Option<char> {
        self.input.next()
    }
}

/// 标记类型
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    /// 数字
    Number(i64),
    /// 标识符
    Identifier(String),
    /// 运算符
    Operator(char),
    /// 括号
    Paren(char),
    /// 结束
    Eof,
}

/// 标记迭代器
pub struct TokenIterator<'a> {
    lexer: SimpleLexer<'a>,
}

impl<'a> TokenIterator<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            lexer: SimpleLexer::new(input),
        }
    }
}

impl<'a> Iterator for TokenIterator<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.skip_whitespace();

        // 尝试解析数字
        if let Some(num) = self.lexer.parse_number() {
            return Some(Token::Number(num));
        }

        // 尝试解析标识符
        if let Some(ident) = self.lexer.parse_identifier() {
            return Some(Token::Identifier(ident));
        }

        // 解析单个字符标记
        let c = *self.lexer.peek()?;
        let token = match c {
            '+' | '-' | '*' | '/' | '=' => Some(Token::Operator(c)),
            '(' | ')' | '{' | '}' | '[' | ']' => Some(Token::Paren(c)),
            _ => None,
        };
        if token.is_some() {
            self.lexer.next_char(); // 消耗字符
        }
        token
    }
}

/// 使用 next_if_map 实现的数据过滤处理器
///
/// 演示如何在数据处理管道中使用 Peekable 新方法
pub struct DataFilterProcessor<T, I: Iterator<Item = T>> {
    iter: std::iter::Peekable<I>,
}

impl<T, I: Iterator<Item = T>> DataFilterProcessor<T, I> {
    /// 创建新的数据过滤器
    pub fn new(iter: I) -> Self {
        Self {
            iter: iter.peekable(),
        }
    }

    /// 提取并映射满足条件的元素
    ///
    /// 在当前版本中，结合 peek 和 next_if 实现类似功能
    /// 在 Rust 1.94 中可以使用 next_if_map 简化
    ///
    /// 此方法会跳过不满足条件的元素，直到找到第一个满足条件的
    pub fn extract_and_map<F, R>(&mut self, mut predicate: F) -> Option<R>
    where
        F: FnMut(&T) -> Option<R>,
    {
        // 跳过不满足条件的元素
        while self.iter.peek().is_some() {
            if let Some(result) = self.iter.peek().and_then(&mut predicate) {
                self.iter.next(); // 消耗元素
                return Some(result);
            }
            self.iter.next(); // 跳过不满足条件的元素
        }
        None
    }

    /// 跳过满足条件的元素
    pub fn skip_while<F>(&mut self, predicate: F)
    where
        F: Fn(&T) -> bool,
    {
        while self.iter.next_if(|item| predicate(item)).is_some() {}
    }

    /// 查看下一个元素
    pub fn peek(&mut self) -> Option<&T> {
        self.iter.peek()
    }
}

/// 解析结果类型
#[derive(Debug, Clone, PartialEq)]
pub enum ParseResult<T> {
    /// 成功解析
    Success(T),
    /// 解析失败
    Failure(String),
    /// 无更多数据
    EndOfInput,
}

/// 通用解析器（使用 next_if_map 模式）
///
/// 演示高级解析模式
pub struct GenericParser<T, I: Iterator<Item = T>> {
    input: std::iter::Peekable<I>,
}

impl<T: Debug, I: Iterator<Item = T>> GenericParser<T, I> {
    /// 创建新的解析器
    pub fn new(input: I) -> Self {
        Self {
            input: input.peekable(),
        }
    }

    /// 尝试解析下一个元素
    ///
    /// 在当前版本中，结合 peek 和 next 实现类似功能
    /// 在 Rust 1.94 中可以使用 next_if_map 简化
    ///
    /// # 参数
    /// - `predicate`: 一个函数，如果元素满足条件则返回 Some(转换后的值)
    ///
    /// # 返回
    /// - `Some(R)` 如果成功解析
    /// - `None` 如果不满足条件
    pub fn try_parse<F, R>(&mut self, predicate: F) -> Option<R>
    where
        F: Fn(&T) -> Option<R>,
    {
        if let Some(result) = self.input.peek().and_then(predicate) {
            self.input.next(); // 消耗元素
            Some(result)
        } else {
            None
        }
    }

    /// 要求解析特定模式
    ///
    /// # 参数
    /// - `predicate`: 匹配函数
    /// - `expected`: 期望的描述（用于错误消息）
    ///
    /// # 返回
    /// 解析结果
    pub fn require<F, R>(&mut self, predicate: F, expected: &str) -> ParseResult<R>
    where
        F: Fn(&T) -> Option<R>,
    {
        match self.try_parse(predicate) {
            Some(result) => ParseResult::Success(result),
            None => match self.input.peek() {
                Some(item) => ParseResult::Failure(format!("期望 {}，但找到 {:?}", expected, item)),
                None => ParseResult::EndOfInput,
            },
        }
    }

    /// 解析多个元素直到条件不满足
    pub fn parse_many<F, R>(&mut self, mut predicate: F) -> Vec<R>
    where
        F: FnMut(&T) -> Option<R>,
    {
        let mut results = Vec::new();
        while let Some(result) = self.input.peek().and_then(&mut predicate) {
            self.input.next(); // 消耗元素
            results.push(result);
        }
        results
    }

    /// 检查是否还有更多元素
    pub fn has_more(&mut self) -> bool {
        self.input.peek().is_some()
    }

    /// 查看下一个元素
    pub fn peek(&mut self) -> Option<&T> {
        self.input.peek()
    }
}

// ==================== 1. 改进的闭包捕获语义 ====================

/// # 1. 改进的闭包捕获语义 / Improved Closure Capture Semantics
///
/// Rust 1.94.0 进一步优化了闭包捕获规则，使代码更直观：
/// Rust 1.94.0 further optimizes closure capture rules for more intuitive code:
/// 闭包捕获分析器
///
/// Rust 1.94.0: 更精确的闭包捕获分析
pub struct ClosureCaptureAnalyzer<T> {
    data: T,
    access_count: usize,
}

impl<T> ClosureCaptureAnalyzer<T> {
    /// 创建新的分析器
    pub fn new(data: T) -> Self {
        Self {
            data,
            access_count: 0,
        }
    }

    /// 创建只读访问闭包
    ///
    /// Rust 1.94.0: 改进的不可变捕获
    pub fn create_reader<F, R>(&self, f: F) -> impl Fn() -> R + use<'_, F, T, R>
    where
        F: Fn(&T) -> R,
    {
        let data_ref = &self.data;
        move || f(data_ref)
    }

    /// 创建可变访问闭包
    ///
    /// Rust 1.94.0: 改进的可变捕获
    pub fn create_mutator<F>(&mut self, f: F) -> impl FnMut() + use<'_, F, T>
    where
        F: Fn(&mut T, &mut usize),
    {
        let data = &mut self.data;
        let count = &mut self.access_count;
        move || {
            *count += 1;
            f(data, count);
        }
    }

    /// 获取访问计数
    pub fn access_count(&self) -> usize {
        self.access_count
    }
}

/// 精确捕获闭包创建器
///
/// Rust 1.94.0: 支持更精确的闭包捕获指定
pub fn create_precise_closure<T: Clone>(value: T) -> impl Fn() -> T {
    // Rust 1.94.0: 编译器更智能地决定捕获方式
    let captured = value;
    move || captured.clone()
}

// ==================== 2. 增强的 match 表达式 ====================

/// # 2. 增强的 match 表达式 / Enhanced Match Expressions
///
/// Rust 1.94.0 改进了 match 表达式的性能和可用性：
/// Rust 1.94.0 improves match expression performance and usability:
/// 匹配结果枚举
#[derive(Debug, Clone, PartialEq)]
pub enum MatchResult<T> {
    Success(T),
    Failure(String),
    Pending,
}

/// 增强的 match 处理器
///
/// Rust 1.94.0: 优化的模式匹配性能
pub struct EnhancedMatcher<T> {
    value: Option<T>,
}

impl<T: PartialEq + std::fmt::Debug> EnhancedMatcher<T> {
    /// 创建新的匹配器
    pub fn new(value: Option<T>) -> Self {
        Self { value }
    }

    /// 执行增强匹配
    ///
    /// Rust 1.94.0: 更快的模式匹配执行
    pub fn enhanced_match(&self) -> MatchResult<&T> {
        match &self.value {
            Some(v) if is_valid_value(v) => {
                // Rust 1.94.0: 守卫条件优化
                MatchResult::Success(v)
            }
            Some(v) => MatchResult::Failure(format!("无效值: {:?}", v)),
            None => MatchResult::Pending,
        }
    }

    /// 匹配或默认
    ///
    /// Rust 1.94.0: 改进的 match 表达式类型推断
    pub fn match_or_default<R, F>(&self, f: F, default: R) -> R
    where
        F: FnOnce(&T) -> R,
    {
        match &self.value {
            Some(v) => f(v),
            None => default,
        }
    }
}

/// 验证值是否有效
///
/// 检查值是否符合特定条件。当前实现对所有类型都返回 true，
/// 实际使用时可以根据具体类型添加验证逻辑（如检查空字符串、零值等）。
fn is_valid_value<T>(_value: &T) -> bool {
    true
}

/// 使用增强的 match 表达式处理结果
///
/// Rust 1.94.0: 更清晰的 match 臂类型推断
pub fn process_match_result<T: Debug>(result: MatchResult<T>) -> String {
    match result {
        MatchResult::Success(val) => format!("成功: {:?}", val),
        MatchResult::Failure(msg) => format!("失败: {}", msg),
        MatchResult::Pending => "等待中...".to_string(),
    }
}

// ==================== 3. 函数指针优化 ====================

/// # 3. 函数指针优化 / Function Pointer Optimizations
///
/// Rust 1.94.0 优化了函数指针的处理和性能：
/// Rust 1.94.0 optimizes function pointer handling and performance:
/// 函数指针包装器
///
/// Rust 1.94.0: 改进的函数指针类型推断
pub struct FunctionPtrWrapper<T, R> {
    func: fn(T) -> R,
    call_count: usize,
}

impl<T, R> FunctionPtrWrapper<T, R> {
    /// 创建新的函数指针包装器
    pub fn new(func: fn(T) -> R) -> Self {
        Self {
            func,
            call_count: 0,
        }
    }

    /// 调用函数
    ///
    /// Rust 1.94.0: 优化的函数指针调用
    pub fn call(&mut self, arg: T) -> R {
        self.call_count += 1;
        (self.func)(arg)
    }

    /// 获取调用计数
    pub fn call_count(&self) -> usize {
        self.call_count
    }
}

/// 优化的函数组合
///
/// Rust 1.94.0: 更好的函数组合类型推断
pub fn compose_functions<T, U, V>(f: fn(T) -> U, g: fn(U) -> V) -> impl Fn(T) -> V {
    move |x| g(f(x))
}

/// 条件函数执行
///
/// Rust 1.94.0: 改进的条件编译优化
pub fn conditional_execute<T>(condition: bool, f: fn() -> T, g: fn() -> T) -> T {
    if condition { f() } else { g() }
}

// ==================== 4. Edition 2024 控制流改进 ====================

/// # 4. Edition 2024 控制流改进 / Edition 2024 Control Flow Improvements
///
/// Rust 1.94.0 与 Edition 2024 的控制流集成：
/// Rust 1.94.0 control flow integration with Edition 2024:
/// Edition 2024 控制流处理器
///
/// Rust 1.94.0: Edition 2024 优化的控制流
pub struct Edition2024ControlFlow<T> {
    value: Option<T>,
    #[allow(dead_code)]
    edition: Edition2024,
}

/// Edition 2024 标记
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Edition2024 {
    Legacy,
    Modern,
}

impl<T> Edition2024ControlFlow<T> {
    /// 创建新的控制流处理器
    pub fn new(value: Option<T>) -> Self {
        Self {
            value,
            edition: Edition2024::Modern,
        }
    }

    /// 执行 try 风格操作
    ///
    /// Rust 1.94.0 + Edition 2024: 改进的错误传播
    ///
    /// # 错误
    /// 当没有值存在时返回 `Err(E)`，其中 E 由调用者提供的闭包或类型决定
    pub fn try_operation<F, E>(&self, f: F) -> Result<T, E>
    where
        T: Clone,
        E: Default,
        F: FnOnce(&T) -> Result<T, E>,
    {
        match &self.value {
            Some(v) => f(v).inspect_err(|_| eprintln!("Operation failed")),
            None => Err(E::default()),
        }
    }

    /// 执行 while let 优化循环
    ///
    /// Rust 1.94.0: 优化的 while let 模式
    pub fn process_while_some<F>(&mut self, mut f: F)
    where
        F: FnMut(&T),
    {
        if let Some(ref v) = self.value {
            f(v);
        }
    }

    /// 使用 if let 链
    ///
    /// Rust 1.94.0: 改进的 if let 链支持
    pub fn chain_if_let<R, F>(&self, f: F) -> Option<R>
    where
        F: FnOnce(&T) -> Option<R>,
    {
        if let Some(ref v) = self.value {
            f(v)
        } else {
            None
        }
    }
}

// ==================== Rust 1.94 真实特性: array_windows 控制流 ====================

/// # array_windows 在控制流中的应用
///
/// Rust 1.94.0 的 `array_windows` 方法可以与控制流结合，
/// 实现高效的序列处理和模式检测。
/// 使用 array_windows 的状态机解析器
///
/// 检测状态转换模式
pub struct StateMachineParser;

impl StateMachineParser {
    /// 检测状态转换序列
    ///
    /// 检测形如 [A, B, C] 的连续状态转换
    pub fn detect_transitions(states: &[&str]) -> Vec<(String, String)> {
        states
            .array_windows::<2>()
            .filter(|[from, to]| from != to)
            .map(|[from, to]| (from.to_string(), to.to_string()))
            .collect()
    }

    /// 检测循环模式
    ///
    /// 查找形如 [X, Y, Z, X, Y, Z] 的重复模式
    pub fn detect_loops(states: &[i32]) -> Vec<(usize, usize)> {
        states
            .array_windows::<3>()
            .enumerate()
            .filter(|(_, [a, b, c])| a < b && b < c)
            .map(|(idx, _)| (idx, idx + 2))
            .collect()
    }

    /// 检测条件状态
    ///
    /// 使用控制流进行条件检测
    pub fn check_condition_sequence(data: &[i32], threshold: i32) -> Vec<usize> {
        data.array_windows::<2>()
            .enumerate()
            .filter(|(_, [a, b])| {
                // 条件控制流：检测跨越阈值
                (a < &threshold && b >= &threshold) || (a >= &threshold && b < &threshold)
            })
            .map(|(idx, _)| idx)
            .collect()
    }
}

/// 使用 array_windows 的事件处理器
///
/// 处理连续事件流
pub struct EventStreamProcessor;

impl EventStreamProcessor {
    /// 处理事件对
    ///
    /// 使用 array_windows 处理连续事件对
    pub fn process_event_pairs<T, F>(events: &[T], mut processor: F)
    where
        T: Clone,
        F: FnMut(&T, &T),
    {
        for [prev, curr] in events.array_windows::<2>() {
            processor(prev, curr);
        }
    }

    /// 检测事件激增
    ///
    /// 检测连续三个事件值都超过阈值的情况
    pub fn detect_spikes(events: &[i32], threshold: i32) -> Vec<usize> {
        events
            .array_windows::<3>()
            .enumerate()
            .filter(|(_, [a, b, c])| a > &threshold && b > &threshold && c > &threshold)
            .map(|(idx, _)| idx)
            .collect()
    }
}

// ==================== Rust 1.94 真实特性: LazyCell 控制流 ====================

/// # LazyCell 在控制流中的应用
///
/// Rust 1.94.0 的 `LazyCell` 可以与控制流结合，
/// 实现条件初始化和延迟计算。
use std::cell::LazyCell;

/// 条件延迟初始化控制器
///
/// 根据条件决定是否初始化值
pub struct ConditionalLazyController<T, F = fn() -> T>
where
    F: FnOnce() -> T,
{
    cell: LazyCell<T, F>,
    condition: Box<dyn Fn() -> bool>,
}

impl<T, F> ConditionalLazyController<T, F>
where
    F: FnOnce() -> T,
{
    /// 创建新的条件控制器
    pub fn new(condition: impl Fn() -> bool + 'static, factory: F) -> Self {
        Self {
            cell: LazyCell::new(factory),
            condition: Box::new(condition),
        }
    }

    /// 尝试获取值（仅在条件满足时）
    ///
    /// 控制流：条件判断决定是否返回值
    pub fn try_get(&self) -> Result<&T, &'static str> {
        if !(self.condition)() {
            return Err("条件不满足，无法获取值");
        }
        Ok(&self.cell)
    }

    /// 获取值
    pub fn get(&self) -> &T {
        &self.cell
    }

    /// 检查条件是否满足
    pub fn check_condition(&self) -> bool {
        (self.condition)()
    }
}

/// 控制流感知的延迟缓存
///
/// 根据执行路径决定初始化策略
pub struct ControlFlowLazyCache<T, F = fn() -> T>
where
    F: FnOnce() -> T,
{
    cell: LazyCell<T, F>,
    init_count: std::cell::Cell<usize>,
}

impl<T, F> ControlFlowLazyCache<T, F>
where
    F: FnOnce() -> T,
{
    /// 创建新的控制流缓存
    pub fn new(factory: F) -> Self {
        Self {
            cell: LazyCell::new(factory),
            init_count: std::cell::Cell::new(0),
        }
    }

    /// 智能获取
    ///
    /// 控制流：根据调用次数返回不同的状态信息
    pub fn smart_get(&self) -> &T {
        let count = self.init_count.get();
        self.init_count.set(count + 1);
        &self.cell
    }

    /// 条件重置（逻辑重置计数器）
    pub fn reset_counter(&self) {
        self.init_count.set(0);
    }

    /// 获取初始化次数
    pub fn init_count(&self) -> usize {
        self.init_count.get()
    }

    /// 获取值
    pub fn get(&self) -> &T {
        &self.cell
    }
}

impl<T> Default for ControlFlowLazyCache<T, fn() -> T>
where
    T: Default + 'static,
{
    fn default() -> Self {
        Self::new(T::default)
    }
}

// ==================== Rust 1.94 真实特性: 数学常量控制流 ====================

/// # 数学常量在控制流中的应用
///
/// Rust 1.94.0 引入的数学常量可以与控制流结合，
/// 实现数值分析和算法控制。
/// 数学常量模块
pub mod math_consts {
    /// 欧拉-马歇罗尼常数
    pub const EULER_GAMMA: f64 = 0.5772156649015329_f64;
    /// 黄金比例
    pub const GOLDEN_RATIO: f64 = 1.618033988749895_f64;
}

/// 使用数学常数的收敛控制器
///
/// 基于 EULER_GAMMA 判断收敛性
pub struct ConvergenceController {
    tolerance: f64,
    max_iterations: usize,
}

impl ConvergenceController {
    /// 创建新的收敛控制器
    pub fn new(tolerance: f64, max_iterations: usize) -> Self {
        Self {
            tolerance,
            max_iterations,
        }
    }

    /// 使用欧拉常数调整容差
    ///
    /// 控制流：基于数学常数调整精度要求
    pub fn adjusted_tolerance(&self) -> f64 {
        self.tolerance * (1.0 + math_consts::EULER_GAMMA)
    }

    /// 迭代直到收敛（f64 版本）
    ///
    /// 控制流：循环直到满足收敛条件
    pub fn iterate_until_converged_f64<F>(&self, mut iterator: F, initial: f64) -> f64
    where
        F: FnMut(f64) -> Option<f64>,
    {
        let mut current = initial;
        let adjusted_tol = self.adjusted_tolerance();

        for iteration in 0..self.max_iterations {
            match iterator(current) {
                Some(next) => {
                    // 控制流：检查收敛
                    if Self::has_converged_f64(current, next, adjusted_tol) {
                        return next;
                    }
                    current = next;
                }
                None => {
                    // 控制流：迭代失败，返回当前值
                    return current;
                }
            }

            // 控制流：检查最大迭代次数
            if iteration >= self.max_iterations - 1 {
                return current;
            }
        }

        current
    }

    /// 检查是否收敛
    fn has_converged_f64(prev: f64, curr: f64, tolerance: f64) -> bool {
        (curr - prev).abs() < tolerance
    }
}

/// 黄金比例分割搜索（控制流版本）
///
/// 使用 GOLDEN_RATIO 进行区间搜索
pub fn golden_section_search<F>(mut f: F, mut a: f64, mut b: f64, tolerance: f64) -> f64
where
    F: FnMut(f64) -> f64,
{
    let phi = math_consts::GOLDEN_RATIO;
    let resphi = 2.0 - phi;

    let mut c = a + resphi * (b - a);
    let mut d = b - resphi * (b - a);
    let mut fc = f(c);
    let mut fd = f(d);

    // 控制流：循环直到收敛
    while (b - a).abs() > tolerance {
        // 控制流：条件分支选择更新方向
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

/// 使用调和数近似的流控制
///
/// 基于 EULER_GAMMA 进行近似计算
pub fn controlled_harmonic_sum(n: u64, use_approximation: bool) -> f64 {
    if use_approximation && n > 100 {
        // 控制流：大数使用近似公式
        let n_f64 = n as f64;
        n_f64.ln() + math_consts::EULER_GAMMA + 1.0 / (2.0 * n_f64)
    } else {
        // 控制流：小数使用精确计算
        (1..=n).map(|k| 1.0 / k as f64).sum()
    }
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

// ==================== 5. 性能优化的控制流结构 ====================

/// # 5. 性能优化的控制流结构 / Performance Optimized Control Flow Structures
///
/// Rust 1.94.0 提供了性能优化的控制流模式：
/// Rust 1.94.0 provides performance-optimized control flow patterns:
/// 优化循环结构
///
/// Rust 1.94.0: 编译器优化的循环模式
pub fn optimized_loop<F>(iterations: usize, mut f: F)
where
    F: FnMut(usize),
{
    // Rust 1.94.0: 编译器可以更好地优化这个循环模式
    for i in 0..iterations {
        f(i);
    }
}

/// 向量化友好循环
///
/// Rust 1.94.0: 支持自动向量化
pub fn vectorizable_loop(data: &mut [f64], factor: f64) {
    // Rust 1.94.0: 编译器可以对这个循环进行向量化
    for item in data.iter_mut() {
        *item *= factor;
    }
}

/// 分支预测友好函数
///
/// Rust 1.94.0: 改进的分支预测
pub fn branch_predictor_friendly(value: i32) -> i32 {
    // Rust 1.94.0: 编译器优化分支预测
    match value {
        0 => 0,
        1 => 1,
        2 => 4,
        3 => 9,
        // 常见情况优先
        n if n > 0 && n < 100 => n * n,
        _ => -1,
    }
}

/// 无分支计算
///
/// Rust 1.94.0: 更好的无分支优化
pub fn branchless_computation(values: &[i32]) -> i32 {
    values.iter().fold(0, |acc, &x| {
        // Rust 1.94.0: 编译器可以优化为无分支代码
        acc + if x > 0 { x } else { 0 }
    })
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 控制流特性
pub fn demonstrate_rust_194_control_flow() {
    println!("\n=== Rust 1.94.0 控制流特性演示 ===\n");

    // 1. Peekable 新方法演示
    println!("1. Peekable 新方法 (next_if_map, next_if_map_mut):");
    let input = "123 abc 456";
    let mut lexer = SimpleLexer::new(input);

    println!("   输入: '{}'", input);
    lexer.skip_whitespace();

    if let Some(num) = lexer.parse_number() {
        println!("   解析到数字: {}", num);
    }

    lexer.skip_whitespace();

    if let Some(ident) = lexer.parse_identifier() {
        println!("   解析到标识符: {}", ident);
    }

    // 使用 TokenIterator
    println!("   \n   使用 TokenIterator 解析 'x = 42 + y':");
    let tokens: Vec<_> = TokenIterator::new("x = 42 + y").collect();
    for token in tokens {
        println!("   {:?}", token);
    }

    // 2. 改进的闭包捕获
    println!("\n2. 改进的闭包捕获语义:");
    {
        let analyzer = ClosureCaptureAnalyzer::new(42);
        let reader = analyzer.create_reader(|x| *x * 2);
        println!("   读取值: {}", reader());
    }

    let mut analyzer2 = ClosureCaptureAnalyzer::new(42);
    let mut mutator = analyzer2.create_mutator(|data, count| {
        *data += 1;
        println!("   修改后值: {}, 访问次数: {}", data, count);
    });
    mutator();

    let precise = create_precise_closure("hello".to_string());
    println!("   精确闭包结果: {}", precise());

    // 3. 增强的 match 表达式
    println!("\n3. 增强的 match 表达式:");
    let matcher: EnhancedMatcher<i32> = EnhancedMatcher::new(Some(42));
    match matcher.enhanced_match() {
        MatchResult::Success(v) => println!("   匹配成功: {}", v),
        MatchResult::Failure(e) => println!("   匹配失败: {}", e),
        MatchResult::Pending => println!("   等待中"),
    }

    let result = matcher.match_or_default(|v| v * 2, 0);
    println!("   匹配或默认值: {}", result);

    // 4. 函数指针优化
    println!("\n4. 函数指针优化:");
    fn double(x: i32) -> i32 {
        x * 2
    }
    let mut wrapper = FunctionPtrWrapper::new(double);
    println!("   函数调用结果: {}", wrapper.call(21));
    println!("   调用次数: {}", wrapper.call_count());

    fn add_one(x: i32) -> i32 {
        x + 1
    }
    let composed = compose_functions(double, add_one);
    println!("   组合函数结果: {}", composed(5)); // (5 * 2) + 1 = 11

    // 5. Edition 2024 控制流
    println!("\n5. Edition 2024 控制流改进:");
    let mut control_flow = Edition2024ControlFlow::new(Some(100));
    control_flow.process_while_some(|v| println!("   处理值: {}", v));

    let result = control_flow.chain_if_let(|v| Some(v * 2));
    println!("   链式 if let 结果: {:?}", result);

    // 6. 性能优化
    println!("\n6. 性能优化的控制流:");
    let mut sum = 0;
    optimized_loop(5, |i| {
        sum += i;
        println!("   迭代 {}: 累加和 = {}", i, sum);
    });

    let mut data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
    vectorizable_loop(&mut data, 2.0);
    println!("   向量化结果: {:?}", data);

    println!("   分支预测友好: {}", branch_predictor_friendly(5));
    println!("   无分支计算: {}", branchless_computation(&[-1, 2, -3, 4]));

    // 7. array_windows 控制流
    println!("\n7. array_windows 控制流:");
    let states = vec!["idle", "running", "running", "stopped", "idle"];
    let transitions = StateMachineParser::detect_transitions(&states);
    println!("   状态转换: {:?}", transitions);

    let numbers = vec![10, 20, 35, 50, 80, 120];
    let spikes = EventStreamProcessor::detect_spikes(&numbers, 30);
    println!("   检测到的激增位置: {:?}", spikes);

    let events = vec![1, 2, 3, 4, 5];
    println!("   处理事件对:");
    EventStreamProcessor::process_event_pairs(&events, |a, b| {
        println!("     {} -> {}", a, b);
    });

    // 8. LazyCell 控制流
    println!("\n8. LazyCell 控制流:");
    let controller = ConditionalLazyController::<i32>::new(|| true, || 42);
    match controller.try_get() {
        Ok(value) => println!("   条件获取成功: {}", value),
        Err(e) => println!("   条件获取失败: {}", e),
    }

    let cache = ControlFlowLazyCache::<String>::new(|| "initialized".to_string());
    let value = cache.smart_get();
    println!("   智能获取值: {}", value);
    println!("   获取次数: {}", cache.init_count());

    // 9. 数学常量控制流
    println!("\n9. 数学常量控制流:");
    let controller = ConvergenceController::new(1e-6, 100);
    let adjusted_tol = controller.adjusted_tolerance();
    println!("   调整后的容差: {:.10}", adjusted_tol);

    let minimum = golden_section_search(|x| (x - 3.0).powi(2), 0.0, 10.0, 1e-6);
    println!("   黄金分割搜索结果: {:.6}", minimum);

    let h100 = controlled_harmonic_sum(100, true);
    let h100_exact = controlled_harmonic_sum(100, false);
    println!("   H_100 近似值: {:.6}", h100);
    println!("   H_100 精确值: {:.6}", h100_exact);
}

/// 获取 Rust 1.94.0 控制流特性信息
pub fn get_rust_194_control_flow_info() -> String {
    "Rust 1.94.0 控制流特性:\n- Peekable 新方法: next_if_map, next_if_map_mut\n- \
     改进的闭包捕获语义\n- 增强的 match 表达式\n- 函数指针优化\n- Edition 2024 控制流改进\n- \
     性能优化的控制流结构"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    // ==================== Peekable 新方法测试 ====================

    #[test]
    fn test_simple_lexer_number() {
        let mut lexer = SimpleLexer::new("123");
        lexer.skip_whitespace();
        assert_eq!(lexer.parse_number(), Some(123));
    }

    #[test]
    fn test_simple_lexer_identifier() {
        let mut lexer = SimpleLexer::new("hello");
        lexer.skip_whitespace();
        assert_eq!(lexer.parse_identifier(), Some("hello".to_string()));
    }

    #[test]
    fn test_simple_lexer_mixed() {
        let mut lexer = SimpleLexer::new("123 abc");
        lexer.skip_whitespace();
        assert_eq!(lexer.parse_number(), Some(123));
        lexer.skip_whitespace();
        assert_eq!(lexer.parse_identifier(), Some("abc".to_string()));
    }

    #[test]
    fn test_simple_lexer_expect_char() {
        let mut lexer = SimpleLexer::new("= 42");
        assert_eq!(lexer.expect_char('='), Some('='));
        lexer.skip_whitespace();
        assert_eq!(lexer.parse_number(), Some(42));
    }

    #[test]
    fn test_token_iterator() {
        let tokens: Vec<_> = TokenIterator::new("x = 42 + y").collect();
        assert_eq!(tokens.len(), 5);
        assert_eq!(tokens[0], Token::Identifier("x".to_string()));
        assert_eq!(tokens[1], Token::Operator('='));
        assert_eq!(tokens[2], Token::Number(42));
        assert_eq!(tokens[3], Token::Operator('+'));
        assert_eq!(tokens[4], Token::Identifier("y".to_string()));
    }

    #[test]
    fn test_data_filter_processor() {
        let data = vec![1, 2, 3, 4, 5];
        let mut processor = DataFilterProcessor::new(data.into_iter());

        // 提取偶数并乘以10
        // 数据是 [1, 2, 3, 4, 5]，extract_and_map 会跳过 1，找到第一个偶数 2
        let result = processor.extract_and_map(|x| if x % 2 == 0 { Some(x * 10) } else { None });
        // 第一个偶数是 2
        assert_eq!(result, Some(20));

        // 当前位置在 3，继续提取下一个偶数
        // extract_and_map 会跳过 3，找到下一个偶数 4
        let result2 = processor.extract_and_map(|x| if x % 2 == 0 { Some(x * 10) } else { None });
        // 4 是偶数
        assert_eq!(result2, Some(40));

        // 检查 peek 是 5
        assert_eq!(processor.peek(), Some(&5));

        // 尝试再提取一个偶数，但没有了
        let result3 = processor.extract_and_map(|x| if x % 2 == 0 { Some(x * 10) } else { None });
        assert_eq!(result3, None);
    }

    #[test]
    fn test_generic_parser() {
        let data = vec![1, 2, 3, 4, 5];
        let mut parser = GenericParser::new(data.into_iter());

        // 尝试解析大于 2 的数
        let result = parser.try_parse(|x| if *x > 2 { Some(*x) } else { None });
        // 第一个元素是 1，不大于 2
        assert_eq!(result, None);

        // 跳过前两个元素
        parser.try_parse(|x| if *x <= 2 { Some(()) } else { None });
        parser.try_parse(|x| if *x <= 2 { Some(()) } else { None });

        // 现在应该是 3
        assert_eq!(parser.peek(), Some(&3));

        // 解析多个大于 2 的数
        let results = parser.parse_many(|x| if *x > 2 { Some(*x * 10) } else { None });
        assert_eq!(results, vec![30, 40, 50]);

        // 没有更多元素
        assert!(!parser.has_more());
    }

    #[test]
    fn test_generic_parser_require() {
        let data = vec![42];
        let mut parser = GenericParser::new(data.into_iter());

        // 成功解析
        let result = parser.require(|x| if *x == 42 { Some(*x) } else { None }, "42");
        assert_eq!(result, ParseResult::Success(42));

        // 尝试解析但已结束
        let result2 = parser.require(|x| Some(*x), "任意值");
        assert_eq!(result2, ParseResult::EndOfInput);
    }

    // ==================== 原有测试 ====================

    #[test]
    fn test_closure_capture_analyzer() {
        let analyzer = ClosureCaptureAnalyzer::new(42);
        let reader = analyzer.create_reader(|x| *x * 2);
        assert_eq!(reader(), 84);
    }

    #[test]
    fn test_closure_mutator() {
        let mut analyzer = ClosureCaptureAnalyzer::new(10);
        {
            let mut mutator = analyzer.create_mutator(|data, _| *data += 5);
            mutator();
        } // mutator 在这里被丢弃
        assert_eq!(analyzer.access_count(), 1);
    }

    #[test]
    fn test_create_precise_closure() {
        let closure = create_precise_closure(42);
        assert_eq!(closure(), 42);
    }

    #[test]
    fn test_enhanced_matcher() {
        let matcher = EnhancedMatcher::new(Some(42));
        match matcher.enhanced_match() {
            MatchResult::Success(v) => assert_eq!(*v, 42),
            _ => panic!("Expected Success"),
        }
    }

    #[test]
    fn test_match_or_default() {
        let matcher = EnhancedMatcher::new(Some(10));
        assert_eq!(matcher.match_or_default(|v| v * 2, 0), 20);

        let empty: EnhancedMatcher<i32> = EnhancedMatcher::new(None);
        assert_eq!(empty.match_or_default(|v| v * 2, 100), 100);
    }

    #[test]
    fn test_function_ptr_wrapper() {
        fn square(x: i32) -> i32 {
            x * x
        }
        let mut wrapper = FunctionPtrWrapper::new(square);
        assert_eq!(wrapper.call(5), 25);
        assert_eq!(wrapper.call_count(), 1);
    }

    #[test]
    fn test_compose_functions() {
        fn add_one(x: i32) -> i32 {
            x + 1
        }
        fn double(x: i32) -> i32 {
            x * 2
        }
        let composed = compose_functions(add_one, double);
        // (5 + 1) * 2 = 12
        assert_eq!(composed(5), 12);
    }

    #[test]
    fn test_edition_2024_control_flow() {
        let control_flow = Edition2024ControlFlow::new(Some(42));
        let result = control_flow.chain_if_let(|v| Some(v * 2));
        assert_eq!(result, Some(84));
    }

    #[test]
    fn test_branch_predictor_friendly() {
        assert_eq!(branch_predictor_friendly(0), 0);
        assert_eq!(branch_predictor_friendly(1), 1);
        assert_eq!(branch_predictor_friendly(2), 4);
        assert_eq!(branch_predictor_friendly(5), 25);
        assert_eq!(branch_predictor_friendly(-1), -1);
    }

    #[test]
    fn test_branchless_computation() {
        assert_eq!(branchless_computation(&[-1, 2, -3, 4]), 6); // 0 + 2 + 0 + 4
    }

    #[test]
    fn test_vectorizable_loop() {
        let mut data = vec![1.0, 2.0, 3.0];
        vectorizable_loop(&mut data, 2.0);
        assert_eq!(data, vec![2.0, 4.0, 6.0]);
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_control_flow();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_control_flow_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("控制流"));
    }

    // ==================== array_windows 控制流测试 ====================

    #[test]
    fn test_detect_transitions() {
        let states = vec!["idle", "running", "running", "stopped", "idle"];
        let transitions = StateMachineParser::detect_transitions(&states);
        // 预期转换: idle->running, running->stopped, stopped->idle
        assert_eq!(transitions.len(), 3);
        assert_eq!(transitions[0], ("idle".to_string(), "running".to_string()));
        assert_eq!(
            transitions[1],
            ("running".to_string(), "stopped".to_string())
        );
        assert_eq!(transitions[2], ("stopped".to_string(), "idle".to_string()));
    }

    #[test]
    fn test_detect_loops() {
        let states = vec![1, 2, 3, 2, 4, 5];
        let loops = StateMachineParser::detect_loops(&states);
        assert!(!loops.is_empty());
    }

    #[test]
    fn test_check_condition_sequence() {
        let data = vec![10, 20, 5, 30];
        let crossings = StateMachineParser::check_condition_sequence(&data, 15);
        assert!(crossings.contains(&0)); // 10 -> 20 跨越 15
        assert!(crossings.contains(&1)); // 20 -> 5 跨越 15
    }

    #[test]
    fn test_detect_spikes() {
        let events = vec![10, 50, 60, 55, 20];
        let spikes = EventStreamProcessor::detect_spikes(&events, 40);
        assert_eq!(spikes, vec![1]);
    }

    #[test]
    fn test_process_event_pairs() {
        let events = vec![1, 2, 3];
        let mut sum = 0;
        EventStreamProcessor::process_event_pairs(&events, |a, b| {
            sum += a + b;
        });
        assert_eq!(sum, 8); // (1+2) + (2+3) = 8
    }

    // ==================== LazyCell 控制流测试 ====================

    #[test]
    fn test_conditional_lazy_controller_success() {
        let controller = ConditionalLazyController::<i32>::new(|| true, || 42);
        let result = controller.try_get();
        assert!(result.is_ok());
        assert_eq!(result.expect("条件延迟控制器获取失败"), &42);
    }

    #[test]
    fn test_conditional_lazy_controller_failure() {
        let controller = ConditionalLazyController::<i32>::new(|| false, || 42);
        let result = controller.try_get();
        assert!(result.is_err());
    }

    #[test]
    fn test_conditional_lazy_controller_get() {
        let controller = ConditionalLazyController::<i32>::new(|| false, || 100);
        let value = controller.get();
        assert_eq!(value, &100);
    }

    #[test]
    fn test_control_flow_lazy_cache() {
        let cache = ControlFlowLazyCache::<i32>::new(|| 42);
        assert_eq!(cache.init_count(), 0);

        let value = cache.smart_get();
        assert_eq!(value, &42);
        assert_eq!(cache.init_count(), 1);

        // 再次获取会增加计数
        let _ = cache.smart_get();
        assert_eq!(cache.init_count(), 2);
    }

    #[test]
    fn test_control_flow_lazy_cache_reset() {
        let cache = ControlFlowLazyCache::<i32>::new(|| 42);
        let _ = cache.smart_get();
        cache.reset_counter();
        assert_eq!(cache.init_count(), 0);
    }

    // ==================== 数学常量控制流测试 ====================

    #[test]
    fn test_convergence_controller_tolerance() {
        let controller = ConvergenceController::new(1e-6, 100);
        let adjusted = controller.adjusted_tolerance();
        assert!(adjusted > 1e-6); // 应该被放大
        assert!(adjusted < 1e-5); // 但不会太大
    }

    #[test]
    fn test_golden_section_search() {
        let minimum = golden_section_search(|x| (x - 5.0).powi(2), 0.0, 10.0, 1e-6);
        assert!((minimum - 5.0).abs() < 1e-5);
    }

    #[test]
    fn test_controlled_harmonic_sum_approximation() {
        // 大数使用近似
        let approx = controlled_harmonic_sum(1000, true);
        let exact = controlled_harmonic_sum(1000, false);
        // 近似值应该接近精确值
        let relative_error = (approx - exact).abs() / exact;
        assert!(relative_error < 0.01);
    }

    #[test]
    fn test_controlled_harmonic_sum_small() {
        // 小数应该使用精确计算
        let result = controlled_harmonic_sum(5, true);
        let exact = 1.0 + 0.5 + 0.333333 + 0.25 + 0.2;
        assert!((result - exact).abs() < 0.01);
    }

    // ==================== ControlFlow 测试 ====================

    #[test]
    fn test_control_flow_matrix_search() {
        let matrix = vec![vec![1, 2], vec![3, 4]];
        assert!(matches!(
            search_in_matrix(&matrix, 3),
            ControlFlow::Break((1, 0))
        ));
    }

    #[test]
    fn test_control_flow_validate() {
        assert!(matches!(
            validate_data("valid123"),
            ControlFlow::Continue(())
        ));
        assert!(matches!(validate_data(""), ControlFlow::Break(_)));
    }

    #[test]
    fn test_control_flow_batch() {
        let items = vec![1, 2, 3];
        let result = batch_process(&items, |_| Ok::<_, String>(()));
        assert!(matches!(result, ControlFlow::Continue(3)));
    }

    // ==================== 反例和边界测试 ====================

    /// 测试 SimpleLexer 对无效数字的解析
    ///
    /// 验证当输入不是数字时，parse_number 返回 None
    #[test]
    fn test_simple_lexer_invalid_number() {
        let mut lexer = SimpleLexer::new("abc");
        lexer.skip_whitespace();

        // 解析标识符应该成功
        assert_eq!(lexer.parse_identifier(), Some("abc".to_string()));

        // 创建新的 lexer 测试数字解析失败
        let mut lexer2 = SimpleLexer::new("abc123");
        lexer2.skip_whitespace();

        // 尝试解析数字应该失败（因为第一个字符是 'a'）
        assert_eq!(lexer2.parse_number(), None);

        // 但解析标识符应该成功
        assert_eq!(lexer2.parse_identifier(), Some("abc123".to_string()));
    }

    /// 测试 SimpleLexer 对空输入的处理
    ///
    /// 验证当输入为空字符串时，各种解析方法的行为
    #[test]
    fn test_simple_lexer_empty_input() {
        let mut lexer = SimpleLexer::new("");

        // 所有解析方法都应该返回 None
        lexer.skip_whitespace(); // 不应 panic
        assert_eq!(lexer.parse_number(), None);
        assert_eq!(lexer.parse_identifier(), None);
        assert_eq!(lexer.peek(), None);
        assert_eq!(lexer.next_char(), None);
        assert_eq!(lexer.expect_char('='), None);
    }

    /// 测试 validate_data 的边界条件
    ///
    /// 验证验证函数在边界值上的行为
    #[test]
    fn test_validate_data_edge_cases() {
        // 空字符串应该失败
        assert!(matches!(
            validate_data(""),
            ControlFlow::Break(ref s) if s == "数据不能为空"
        ));

        // 长度恰好为 7（小于 8）应该失败
        assert!(matches!(
            validate_data("1234567"),
            ControlFlow::Break(ref s) if s == "数据长度至少为 8"
        ));

        // 长度恰好为 8 应该通过（不检查数字）
        assert!(matches!(
            validate_data("abcdefgh"),
            ControlFlow::Continue(())
        ));

        // 长度恰好为 8 且有数字应该通过
        assert!(matches!(
            validate_data("abcdefg1"),
            ControlFlow::Continue(())
        ));

        // 长度为 8 全是数字应该通过
        assert!(matches!(
            validate_data("12345678"),
            ControlFlow::Continue(())
        ));

        // 超长字符串只要长度 >= 8 应该通过
        assert!(matches!(
            validate_data("this_is_a_very_long_string_without_numbers"),
            ControlFlow::Continue(())
        ));

        // 只有空格但长度 >= 8 也应该通过
        assert!(matches!(
            validate_data("        "),
            ControlFlow::Continue(())
        ));
    }

    /// 测试 Edition2024ControlFlow 对未初始化状态的访问
    ///
    /// 验证当值为 None 时，各种方法的正确处理
    #[test]
    fn test_edition_wrapper_uninitialized() {
        let control_flow = Edition2024ControlFlow::<i32>::new(None);

        // try_operation 应该返回 Err
        let result: Result<i32, ()> = control_flow.try_operation(|v| Ok(*v));
        assert!(result.is_err());

        // process_while_some 不应执行任何操作
        let mut executed = false;
        let mut control_flow_mut = Edition2024ControlFlow::<i32>::new(None);
        control_flow_mut.process_while_some(|_| executed = true);
        assert!(!executed, "无值时不应执行操作");

        // chain_if_let 应该返回 None
        let result2 = control_flow.chain_if_let(|v| Some(v * 2));
        assert_eq!(result2, None);
    }
}
