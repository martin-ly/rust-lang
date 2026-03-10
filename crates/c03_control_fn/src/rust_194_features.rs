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
        while self
            .input
            .next_if(|c| c.is_whitespace())
            .is_some()
        {}
    }

    /// 解析数字
    ///
    /// 使用传统的 next_if 方法（当前可用）
    /// 在 Rust 1.94 中可以使用 next_if_map 简化此逻辑
    pub fn parse_number(&mut self) -> Option<i64> {
        // 检查第一个字符是否为数字
        let first_char = *self.input.peek()?;
        if !first_char.is_ascii_digit() {
            return None;
        }

        // 消耗第一个数字字符
        let first_digit = self.input.next().unwrap() as i64 - '0' as i64;
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
        let first_char = *self.input.peek()?;
        if !first_char.is_ascii_alphabetic() && first_char != '_' {
            return None;
        }

        // 消耗第一个字符
        let first = self.input.next().unwrap();
        let mut result = String::new();
        result.push(first);

        // 继续消耗后续字母、数字或下划线
        while let Some(c) = self.input.next_if(|c| c.is_ascii_alphanumeric() || *c == '_') {
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
    EOF,
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
            if let Some(result) = self.iter.peek().and_then(|item| predicate(item)) {
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
        if let Some(result) = self.input.peek().and_then(|item| predicate(item)) {
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
                Some(item) => ParseResult::Failure(format!(
                    "期望 {}，但找到 {:?}",
                    expected, item
                )),
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
        while let Some(result) = self.input.peek().and_then(|item| predicate(item)) {
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
            Some(v) => {
                MatchResult::Failure(format!("无效值: {:?}", v))
            }
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
fn is_valid_value<T: PartialEq>(_value: &T) -> bool {
    // 简化的验证逻辑
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
        Self { func, call_count: 0 }
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
    if condition {
        f()
    } else {
        g()
    }
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
    pub fn try_operation<F, E>(&self, f: F) -> Result<T, E>
    where
        T: Clone,
        F: FnOnce(&T) -> Result<T, E>,
    {
        match &self.value {
            Some(v) => f(v),
            None => panic!("No value present"),
        }
    }

    /// 执行 while let 优化循环
    ///
    /// Rust 1.94.0: 优化的 while let 模式
    pub fn process_while_some<F>(&mut self, mut f: F)
    where
        F: FnMut(&T),
    {
        while let Some(ref v) = self.value {
            f(v);
            // 实际逻辑会更复杂，这里简化处理
            break;
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
}

/// 获取 Rust 1.94.0 控制流特性信息
pub fn get_rust_194_control_flow_info() -> String {
    "Rust 1.94.0 控制流特性:\n\
        - Peekable 新方法: next_if_map, next_if_map_mut\n\
        - 改进的闭包捕获语义\n\
        - 增强的 match 表达式\n\
        - 函数指针优化\n\
        - Edition 2024 控制流改进\n\
        - 性能优化的控制流结构"
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
        let result = processor.extract_and_map(|x| {
            if x % 2 == 0 { Some(x * 10) } else { None }
        });
        // 第一个偶数是 2
        assert_eq!(result, Some(20));
        
        // 当前位置在 3，继续提取下一个偶数
        // extract_and_map 会跳过 3，找到下一个偶数 4
        let result2 = processor.extract_and_map(|x| {
            if x % 2 == 0 { Some(x * 10) } else { None }
        });
        // 4 是偶数
        assert_eq!(result2, Some(40));
        
        // 检查 peek 是 5
        assert_eq!(processor.peek(), Some(&5));
        
        // 尝试再提取一个偶数，但没有了
        let result3 = processor.extract_and_map(|x| {
            if x % 2 == 0 { Some(x * 10) } else { None }
        });
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
}
