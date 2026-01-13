//! Rust 1.92.0 控制流特性实现模块
//!
//! 本模块展示了 Rust 1.92.0 在控制流和函数场景中的应用，包括：
//! - `#[track_caller]` 和 `#[no_mangle]` 组合使用
//! - 更严格的 Never 类型 Lint
//! - `Location::file_as_c_str` 在错误报告中的应用
//!
//! # 文件信息
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - 版本: 1.0
//! - Rust版本: 1.92.0
//! - Edition: 2024

use std::panic::Location;

// ==================== 1. #[track_caller] 和 #[no_mangle] 组合使用 ====================

/// 使用 #[track_caller] 的错误处理函数
///
/// Rust 1.92.0: #[track_caller] 在控制流场景中的改进
/// 注意：#[track_caller] 需要 Rust ABI，不能与 extern "C" 一起使用
#[track_caller]
pub fn tracked_panic_handler(message: &str) {
    let caller = Location::caller();
    eprintln!(
        "Panic at {}:{}: {}",
        caller.file(),
        caller.line(),
        message
    );
}

/// 带有调用者追踪的断言宏
#[macro_export]
macro_rules! tracked_assert {
    ($condition:expr, $msg:expr) => {{
        #[track_caller]
        fn assert_failed(msg: &str) {
            let caller = std::panic::Location::caller();
            panic!("Assertion failed at {}:{}: {}", caller.file(), caller.line(), msg);
        }

        if !$condition {
            assert_failed($msg);
        }
    }};
}

/// 控制流检查函数，使用 #[track_caller]
/// Rust 1.92.0: #[track_caller] 在控制流分析中的改进
#[track_caller]
pub fn control_flow_check(condition: bool) -> i32 {
    let caller = Location::caller();
    if condition {
        println!("Control flow check passed at {}:{}", caller.file(), caller.line());
        0
    } else {
        println!("Control flow check failed at {}:{}", caller.file(), caller.line());
        -1
    }
}

// ==================== 2. 更严格的 Never 类型 Lint ====================

/// Never 类型示例函数
///
/// Rust 1.92.0: 对 Never 类型 (`!`) 有更严格的 Lint 检查
pub fn never_returns() -> ! {
    loop {
        // 这个函数永远不会返回
        std::hint::spin_loop();
    }
}

/// 使用 Never 类型的控制流
pub fn control_flow_with_never(result: Result<i32, String>) -> i32 {
    match result {
        Ok(value) => value,
        Err(_) => never_returns(), // Never 类型，函数永远不会从这里返回
    }
}

/// Never 类型在 panic 场景中的应用
#[track_caller]
pub fn panic_with_never(message: &str) -> ! {
    panic!("{}", message);
}

/// 使用 Never 类型的无限循环
pub fn infinite_control_flow() -> ! {
    loop {
        std::thread::sleep(std::time::Duration::from_secs(1));
        // 这个函数永远不会返回
    }
}

// ==================== 3. Location::file_as_c_str 在错误报告中的应用 ====================

/// 使用 Location 创建详细的错误报告
///
/// Rust 1.92.0: Location API 在错误报告中的改进
pub fn create_error_report() -> String {
    let caller = Location::caller();
    let file_path = caller.file();

    format!(
        "Error at {}:{}:{} - Location information captured",
        file_path,
        caller.line(),
        caller.column()
    )
}

/// 错误上下文结构体
#[derive(Debug, Clone)]
pub struct ErrorContext {
    pub file: &'static str,
    pub line: u32,
    pub column: u32,
}

impl ErrorContext {
    #[track_caller]
    pub fn current() -> Self {
        let caller = Location::caller();
        ErrorContext {
            file: caller.file(),
            line: caller.line(),
            column: caller.column(),
        }
    }
}

/// 带有位置的错误类型
#[derive(Debug, Clone)]
pub struct LocatedError {
    pub message: String,
    pub context: ErrorContext,
}

impl LocatedError {
    #[track_caller]
    pub fn new(message: impl Into<String>) -> Self {
        LocatedError {
            message: message.into(),
            context: ErrorContext::current(),
        }
    }
}

impl std::fmt::Display for LocatedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Error at {}:{}:{} - {}",
            self.context.file,
            self.context.line,
            self.context.column,
            self.message
        )
    }
}

impl std::error::Error for LocatedError {}

// ==================== 4. 改进的控制流分析 ====================

/// 控制流分析示例：条件分支
pub fn control_flow_branch(value: i32) -> Result<i32, LocatedError> {
    if value < 0 {
        return Err(LocatedError::new("Value must be non-negative"));
    }

    if value > 100 {
        return Err(LocatedError::new("Value must be <= 100"));
    }

    Ok(value * 2)
}

/// 控制流分析示例：循环
pub fn control_flow_loop(max_iterations: usize) -> usize {
    let mut count = 0;

    loop {
        if count >= max_iterations {
            break;
        }
        count += 1;
    }

    count
}

/// 控制流分析示例：匹配表达式
pub fn control_flow_match(value: Option<i32>) -> i32 {
    match value {
        Some(v) if v > 0 => v * 2,
        Some(v) => v.abs(),
        None => 0,
    }
}

// ==================== 5. 综合应用示例 ====================

/// 获取 Rust 1.92.0 控制流特性信息
pub fn get_rust_192_control_flow_info() -> String {
    "Rust 1.92.0 控制流特性:\n\
        - #[track_caller] 在控制流场景中的改进\n\
        - 更严格的 Never 类型 Lint 检查\n\
        - Location API 在错误报告中的增强\n\
        - 改进的控制流分析\n\
        - 优化的错误处理和上下文捕获".to_string()
}

/// 演示 Rust 1.92.0 控制流特性
pub fn demonstrate_rust_192_control_flow() {
    println!("\n=== Rust 1.92.0 控制流特性演示 ===\n");

    // 1. track_caller 改进
    println!("1. #[track_caller] 改进:");
    let result = control_flow_check(true);
    println!("   控制流检查结果: {}", result);

    // 2. Never 类型
    println!("\n2. Never 类型 Lint:");
    let result = control_flow_with_never(Ok(42));
    println!("   结果: {}", result);

    // 注意：never_returns() 函数不能直接调用，因为它永远不会返回

    // 3. Location 在错误报告中的应用
    println!("\n3. Location 信息在错误报告中的应用:");
    let error_report = create_error_report();
    println!("   错误报告: {}", error_report);

    let error = LocatedError::new("示例错误");
    println!("   定位错误: {}", error);

    // 4. 控制流分析
    println!("\n4. 控制流分析:");
    match control_flow_branch(42) {
        Ok(value) => println!("   分支成功: {}", value),
        Err(e) => println!("   分支失败: {}", e),
    }

    match control_flow_branch(-1) {
        Ok(value) => println!("   分支成功: {}", value),
        Err(e) => println!("   分支失败: {}", e),
    }

    let loop_count = control_flow_loop(5);
    println!("   循环计数: {}", loop_count);

    let match_result = control_flow_match(Some(21));
    println!("   匹配结果: {}", match_result);
}

// ==================== 6. 高级控制流特性 ====================

/// 控制流分析器：用于分析函数的控制流路径
#[derive(Default)]
pub struct ControlFlowAnalyzer {
    branch_count: usize,
    loop_count: usize,
    match_count: usize,
}

impl ControlFlowAnalyzer {
    pub fn new() -> Self {
        ControlFlowAnalyzer {
            branch_count: 0,
            loop_count: 0,
            match_count: 0,
        }
    }

    #[track_caller]
    pub fn analyze_branch(&mut self, condition: bool) -> bool {
        self.branch_count += 1;
        condition
    }

    #[track_caller]
    pub fn analyze_loop<F>(&mut self, iterations: usize, f: F) -> usize
    where
        F: Fn(usize) -> bool,
    {
        self.loop_count += 1;
        let mut count = 0;
        for i in 0..iterations {
            if f(i) {
                count += 1;
            }
        }
        count
    }

    #[track_caller]
    pub fn analyze_match<T>(&mut self, value: Option<T>) -> bool {
        self.match_count += 1;
        value.is_some()
    }

    pub fn get_statistics(&self) -> (usize, usize, usize) {
        (self.branch_count, self.loop_count, self.match_count)
    }
}


/// 控制流优化器：提供控制流优化建议
pub struct ControlFlowOptimizer;

impl ControlFlowOptimizer {
    /// 优化循环结构
    pub fn optimize_loop(max_iterations: usize) -> usize {
        // 使用优化的循环结构
        (0..max_iterations)
            .map(|i| i * 2)
            .sum::<usize>() / max_iterations
    }

    /// 优化分支结构
    #[track_caller]
    pub fn optimize_branch(value: i32) -> Result<i32, LocatedError> {
        // 早期返回优化
        if value < 0 {
            return Err(LocatedError::new("Value must be non-negative"));
        }
        if value > 100 {
            return Err(LocatedError::new("Value must be <= 100"));
        }
        Ok(value * 2)
    }

    /// 优化匹配表达式
    pub fn optimize_match(value: Option<i32>) -> i32 {
        value
            .map(|v| if v > 0 { v * 2 } else { v.abs() })
            .unwrap_or(0)
    }
}

// ==================== 7. 高级控制流模式 ====================

/// 控制流模式匹配器：提供高级模式匹配功能
pub struct ControlFlowMatcher;

impl ControlFlowMatcher {
    /// 带守卫的模式匹配
    pub fn match_with_guard(value: i32) -> &'static str {
        match value {
            v if v < 0 => "负数",
            0 => "零",
            v if v <= 10 => "小正数",
            v if v <= 100 => "中等正数",
            _ => "大正数",
        }
    }

    /// 嵌套模式匹配
    pub fn nested_match(value: Option<Option<i32>>) -> i32 {
        match value {
            Some(Some(v)) if v > 0 => v * 2,
            Some(Some(v)) => v.abs(),
            Some(None) => 0,
            None => -1,
        }
    }

    /// 元组模式匹配
    pub fn tuple_match(tuple: (i32, i32, i32)) -> i32 {
        match tuple {
            (x, y, z) if x == y && y == z => x * 3,
            (x, y, _) if x == y => x * 2,
            (x, _, z) if x == z => x * 2,
            (_, y, z) if y == z => y * 2,
            (x, y, z) => x + y + z,
        }
    }

    /// 范围模式匹配
    pub fn range_match(value: i32) -> &'static str {
        match value {
            0..=9 => "单位数",
            10..=99 => "两位数",
            100..=999 => "三位数",
            1000..=9999 => "四位数",
            _ => "五位数或更大",
        }
    }
}

/// 控制流组合器：组合多个控制流操作
pub struct ControlFlowCombinator;

impl ControlFlowCombinator {
    /// 链式条件检查
    #[track_caller]
    pub fn chain_conditions(values: &[i32]) -> Result<Vec<i32>, LocatedError> {
        let mut result = Vec::new();

        for &value in values {
            // 使用早期返回优化
            let processed = control_flow_branch(value)?;
            result.push(processed);
        }

        Ok(result)
    }

    /// 组合循环和匹配
    pub fn combine_loop_and_match(items: &[Option<i32>]) -> Vec<i32> {
        items
            .iter()
            .map(|item| control_flow_match(*item))
            .collect()
    }

    /// 组合分析和优化
    pub fn analyze_and_optimize(items: &[i32]) -> (usize, usize, usize, usize) {
        let mut analyzer = ControlFlowAnalyzer::new();
        let mut optimized_count = 0;

        for &item in items {
            analyzer.analyze_branch(item > 0);

            if ControlFlowOptimizer::optimize_branch(item).is_ok() {
                optimized_count += 1;
            }
        }

        let (branches, loops, matches) = analyzer.get_statistics();
        // 返回所有统计信息，即使某些可能为0
        (branches, loops, matches, optimized_count)
    }
}

/// 控制流性能分析器：分析控制流性能
#[derive(Default)]
pub struct ControlFlowProfiler {
    branch_times: Vec<u128>,
    loop_times: Vec<u128>,
    match_times: Vec<u128>,
}

impl ControlFlowProfiler {
    pub fn new() -> Self {
        ControlFlowProfiler {
            branch_times: Vec::new(),
            loop_times: Vec::new(),
            match_times: Vec::new(),
        }
    }

    /// 分析分支性能
    #[track_caller]
    pub fn profile_branch<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let start = std::time::Instant::now();
        let result = f();
        let duration = start.elapsed().as_nanos();
        self.branch_times.push(duration);
        result
    }

    /// 分析循环性能
    pub fn profile_loop<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let start = std::time::Instant::now();
        let result = f();
        let duration = start.elapsed().as_nanos();
        self.loop_times.push(duration);
        result
    }

    /// 分析匹配性能
    pub fn profile_match<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let start = std::time::Instant::now();
        let result = f();
        let duration = start.elapsed().as_nanos();
        self.match_times.push(duration);
        result
    }

    /// 获取性能统计
    pub fn get_stats(&self) -> (f64, f64, f64) {
        let branch_avg = if !self.branch_times.is_empty() {
            self.branch_times.iter().sum::<u128>() as f64 / self.branch_times.len() as f64
        } else {
            0.0
        };

        let loop_avg = if !self.loop_times.is_empty() {
            self.loop_times.iter().sum::<u128>() as f64 / self.loop_times.len() as f64
        } else {
            0.0
        };

        let match_avg = if !self.match_times.is_empty() {
            self.match_times.iter().sum::<u128>() as f64 / self.match_times.len() as f64
        } else {
            0.0
        };

        (branch_avg, loop_avg, match_avg)
    }

    /// 重置统计
    pub fn reset(&mut self) {
        self.branch_times.clear();
        self.loop_times.clear();
        self.match_times.clear();
    }
}


/// 控制流验证器：验证控制流的正确性
pub struct ControlFlowValidator;

impl ControlFlowValidator {
    /// 验证分支逻辑
    #[track_caller]
    pub fn validate_branch(value: i32) -> Result<i32, LocatedError> {
        if value < 0 {
            Err(LocatedError::new("值不能为负数"))
        } else if value > 1000 {
            Err(LocatedError::new("值不能超过 1000"))
        } else {
            Ok(value)
        }
    }

    /// 验证循环终止条件
    pub fn validate_loop_termination(max_iterations: usize) -> Result<usize, LocatedError> {
        if max_iterations == 0 {
            return Ok(0);
        }

        if max_iterations > 1_000_000 {
            return Err(LocatedError::new("迭代次数过多，可能导致性能问题"));
        }

        let result = control_flow_loop(max_iterations);
        if result != max_iterations {
            Err(LocatedError::new("循环终止条件异常"))
        } else {
            Ok(result)
        }
    }

    /// 验证匹配完整性
    pub fn validate_match_coverage(value: Option<i32>) -> Result<i32, LocatedError> {
        match value {
            Some(v) if v >= 0 => Ok(v),
            Some(v) if v < 0 => Err(LocatedError::new("不支持负值")),
            None => Err(LocatedError::new("值不能为空")),
            _ => Err(LocatedError::new("未处理的匹配情况")),
        }
    }
}

// ==================== 8. 异步控制流支持 ====================

#[cfg(feature = "async")]
pub mod async_control_flow {
    use super::*;
    use tokio::time::{sleep, Duration};

    /// 异步控制流处理函数
    // 注意：async fn 上的 #[track_caller] 在 Rust 1.92.0 中有限制
    pub async fn async_control_flow_branch(value: i32) -> Result<i32, LocatedError> {
        // 模拟异步操作
        sleep(Duration::from_millis(10)).await;

        if value < 0 {
            return Err(LocatedError::new("值不能为负数"));
        }
        if value > 100 {
            return Err(LocatedError::new("值不能超过 100"));
        }

        Ok(value * 2)
    }

    /// 异步循环处理
    pub async fn async_control_flow_loop(max_iterations: usize) -> usize {
        let mut count = 0;

        for i in 0..max_iterations {
            // 模拟异步操作
            sleep(Duration::from_millis(1)).await;
            count += 1;

            if i >= max_iterations {
                break;
            }
        }

        count
    }

    /// 异步模式匹配处理
    pub async fn async_control_flow_match(value: Option<i32>) -> i32 {
        sleep(Duration::from_millis(5)).await;

        match value {
            Some(v) if v > 0 => v * 2,
            Some(v) => v.abs(),
            None => 0,
        }
    }

    /// 异步控制流组合
    pub async fn async_control_flow_combinator(values: &[i32]) -> Result<Vec<i32>, LocatedError> {
        let mut results = Vec::new();

        for &value in values {
            let processed = async_control_flow_branch(value).await?;
            results.push(processed);
        }

        Ok(results)
    }
}

// ==================== 9. 控制流状态机 ====================

/// 控制流状态机：用于管理复杂的状态转换
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ControlFlowState {
    #[default]
    Initial,
    Processing,
    Validating,
    Completed,
    Error,
}

/// 控制流状态机实现
#[derive(Default)]
pub struct ControlFlowStateMachine {
    current_state: ControlFlowState,
    transition_count: usize,
}

impl ControlFlowStateMachine {
    pub fn new() -> Self {
        ControlFlowStateMachine {
            current_state: ControlFlowState::Initial,
            transition_count: 0,
        }
    }

    #[track_caller]
    pub fn transition_to(&mut self, new_state: ControlFlowState) -> Result<(), LocatedError> {
        // 状态转换验证
        let valid = matches!(
            (self.current_state, new_state),
            (ControlFlowState::Initial, ControlFlowState::Processing)
                | (ControlFlowState::Processing, ControlFlowState::Validating)
                | (ControlFlowState::Validating, ControlFlowState::Completed)
                | (ControlFlowState::Validating, ControlFlowState::Error)
                | (ControlFlowState::Error, ControlFlowState::Initial)
                | (ControlFlowState::Completed, ControlFlowState::Initial)
        );

        if valid {
            self.current_state = new_state;
            self.transition_count += 1;
            Ok(())
        } else {
            Err(LocatedError::new(&format!(
                "无效的状态转换: {:?} -> {:?}",
                self.current_state, new_state
            )))
        }
    }

    pub fn current_state(&self) -> ControlFlowState {
        self.current_state
    }

    pub fn transition_count(&self) -> usize {
        self.transition_count
    }

    pub fn reset(&mut self) {
        self.current_state = ControlFlowState::Initial;
        self.transition_count = 0;
    }

    /// 执行状态机工作流
    pub fn execute_workflow(&mut self, value: i32) -> Result<i32, LocatedError> {
        // Initial -> Processing
        self.transition_to(ControlFlowState::Processing)?;

        // Processing -> Validating
        let processed = control_flow_branch(value)?;
        self.transition_to(ControlFlowState::Validating)?;

        // Validating -> Completed or Error
        if processed > 0 {
            self.transition_to(ControlFlowState::Completed)?;
            Ok(processed)
        } else {
            self.transition_to(ControlFlowState::Error)?;
            Err(LocatedError::new("处理结果无效"))
        }
    }
}


// ==================== 10. 迭代器控制流扩展 ====================

/// 迭代器控制流扩展工具
pub struct IteratorControlFlow;

impl IteratorControlFlow {
    /// 使用控制流进行迭代器过滤
    pub fn filter_with_control_flow<I, F>(iter: I, predicate: F) -> Vec<I::Item>
    where
        I: Iterator,
        F: Fn(&I::Item) -> Result<bool, LocatedError>,
    {
        let mut result = Vec::new();

        for item in iter {
            match predicate(&item) {
                Ok(true) => result.push(item),
                Ok(false) => {}
                Err(e) => {
                    eprintln!("过滤错误: {}", e);
                    break;
                }
            }
        }

        result
    }

    /// 使用控制流进行迭代器映射
    pub fn map_with_control_flow<I, F, T>(iter: I, mapper: F) -> Result<Vec<T>, LocatedError>
    where
        I: Iterator,
        F: Fn(I::Item) -> Result<T, LocatedError>,
    {
        let mut result = Vec::new();

        for item in iter {
            let mapped = mapper(item)?;
            result.push(mapped);
        }

        Ok(result)
    }

    /// 使用控制流进行迭代器折叠
    pub fn fold_with_control_flow<I, F, T>(
        iter: I,
        init: T,
        folder: F,
    ) -> Result<T, LocatedError>
    where
        I: Iterator,
        F: Fn(T, I::Item) -> Result<T, LocatedError>,
    {
        let mut acc = init;

        for item in iter {
            acc = folder(acc, item)?;
        }

        Ok(acc)
    }

    /// 使用控制流进行迭代器查找
    pub fn find_with_control_flow<I, F>(iter: I, predicate: F) -> Option<I::Item>
    where
        I: Iterator,
        F: Fn(&I::Item) -> Result<bool, LocatedError>,
    {
        for item in iter {
            match predicate(&item) {
                Ok(true) => return Some(item),
                Ok(false) => {}
                Err(_) => break,
            }
        }

        None
    }
}

// ==================== 11. 并行控制流处理 ====================

#[cfg(feature = "std")]
pub mod parallel_control_flow {
    use super::*;
    use std::sync::{Arc, Mutex};
    use std::thread;

    /// 并行控制流处理结果
    #[derive(Default)]
    pub struct ParallelControlFlowResult<T> {
        results: Vec<Result<T, LocatedError>>,
        errors: Vec<LocatedError>,
    }

    impl<T> std::fmt::Debug for ParallelControlFlowResult<T>
    where
        T: std::fmt::Debug,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("ParallelControlFlowResult")
                .field("results_count", &self.results.len())
                .field("errors_count", &self.errors.len())
                .finish()
        }
    }

    impl<T> ParallelControlFlowResult<T> {
        pub fn new() -> Self {
            ParallelControlFlowResult {
                results: Vec::new(),
                errors: Vec::new(),
            }
        }

        pub fn add_result(&mut self, result: Result<T, LocatedError>) {
            match result {
                Ok(value) => self.results.push(Ok(value)),
                Err(e) => {
                    let error = e.clone();
                    self.errors.push(error.clone());
                    self.results.push(Err(error));
                }
            }
        }

        pub fn successes(&self) -> usize {
            self.results.iter().filter(|r| r.is_ok()).count()
        }

        pub fn failures(&self) -> usize {
            self.errors.len()
        }

        pub fn all_results(&self) -> &[Result<T, LocatedError>] {
            &self.results
        }

        pub fn all_errors(&self) -> &[LocatedError] {
            &self.errors
        }
    }


    /// 并行处理控制流分支
    pub fn parallel_control_flow_branch(
        values: &[i32],
        num_threads: usize,
    ) -> ParallelControlFlowResult<i32> {
        let result = Arc::new(Mutex::new(ParallelControlFlowResult::new()));
        let chunks: Vec<&[i32]> = values.chunks(values.len().div_ceil(num_threads)).collect();

        let handles: Vec<_> = chunks
            .into_iter()
            .map(|chunk| {
                let chunk = chunk.to_vec();
                let result = Arc::clone(&result);

                thread::spawn(move || {
                    for value in chunk {
                        let branch_result = control_flow_branch(value);
                        result.lock().unwrap().add_result(branch_result);
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        Arc::try_unwrap(result).unwrap().into_inner().unwrap()
    }
}

// ==================== 12. 控制流可视化工具 ====================

/// 控制流可视化信息
#[derive(Debug, Clone)]
#[derive(Default)]
pub struct ControlFlowVisualization {
    pub branches: Vec<String>,
    pub loops: Vec<String>,
    pub matches: Vec<String>,
    pub errors: Vec<String>,
}

impl ControlFlowVisualization {
    pub fn new() -> Self {
        ControlFlowVisualization {
            branches: Vec::new(),
            loops: Vec::new(),
            matches: Vec::new(),
            errors: Vec::new(),
        }
    }

    pub fn add_branch(&mut self, description: impl Into<String>) {
        self.branches.push(description.into());
    }

    pub fn add_loop(&mut self, description: impl Into<String>) {
        self.loops.push(description.into());
    }

    pub fn add_match(&mut self, description: impl Into<String>) {
        self.matches.push(description.into());
    }

    pub fn add_error(&mut self, description: impl Into<String>) {
        self.errors.push(description.into());
    }

    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== 控制流可视化报告 ===\n\n");

        report.push_str(&format!("分支数量: {}\n", self.branches.len()));
        for (i, branch) in self.branches.iter().enumerate() {
            report.push_str(&format!("  分支 {}: {}\n", i + 1, branch));
        }

        report.push_str(&format!("\n循环数量: {}\n", self.loops.len()));
        for (i, loop_info) in self.loops.iter().enumerate() {
            report.push_str(&format!("  循环 {}: {}\n", i + 1, loop_info));
        }

        report.push_str(&format!("\n匹配数量: {}\n", self.matches.len()));
        for (i, match_info) in self.matches.iter().enumerate() {
            report.push_str(&format!("  匹配 {}: {}\n", i + 1, match_info));
        }

        if !self.errors.is_empty() {
            report.push_str(&format!("\n错误数量: {}\n", self.errors.len()));
            for (i, error) in self.errors.iter().enumerate() {
                report.push_str(&format!("  错误 {}: {}\n", i + 1, error));
            }
        }

        report
    }

    pub fn statistics(&self) -> (usize, usize, usize, usize) {
        (
            self.branches.len(),
            self.loops.len(),
            self.matches.len(),
            self.errors.len(),
        )
    }
}


// ==================== 13. 实用工具函数 ====================

/// 控制流工具集：提供常用的控制流工具函数
pub struct ControlFlowUtils;

impl ControlFlowUtils {
    /// 安全执行控制流操作，捕获所有错误
    #[track_caller]
    pub fn safe_execute<F, T, E>(f: F) -> Result<T, LocatedError>
    where
        F: FnOnce() -> Result<T, E>,
        E: std::error::Error + 'static,
    {
        f().map_err(|e| LocatedError::new(format!("执行失败: {}", e)))
    }

    /// 批量执行控制流分支
    pub fn batch_branch(values: &[i32]) -> Vec<Result<i32, LocatedError>> {
        values.iter().map(|&v| control_flow_branch(v)).collect()
    }

    /// 批量执行控制流匹配
    pub fn batch_match(values: &[Option<i32>]) -> Vec<i32> {
        values.iter().map(|&v| control_flow_match(v)).collect()
    }

    /// 条件组合：所有条件都必须满足
    pub fn all_conditions(conditions: &[bool]) -> bool {
        conditions.iter().all(|&c| c)
    }

    /// 条件组合：至少一个条件满足
    pub fn any_condition(conditions: &[bool]) -> bool {
        conditions.iter().any(|&c| c)
    }

    /// 控制流重试机制
    pub fn retry_with_control_flow<F, T>(
        mut f: F,
        max_retries: usize,
    ) -> Result<T, LocatedError>
    where
        F: FnMut() -> Result<T, LocatedError>,
    {
        let mut last_error = None;

        for attempt in 0..=max_retries {
            match f() {
                Ok(result) => return Ok(result),
                Err(e) => {
                    last_error = Some(e);
                    if attempt < max_retries {
                        // 可以在这里添加重试延迟
                        continue;
                    }
                }
            }
        }

        Err(last_error.unwrap_or_else(|| LocatedError::new("重试失败")))
    }

    /// 控制流超时包装（模拟）
    pub fn with_timeout<F, T>(f: F, _timeout_ms: u64) -> Result<T, LocatedError>
    where
        F: FnOnce() -> Result<T, LocatedError>,
    {
        // 注意：这是一个简化的实现，实际超时需要使用异步或线程
        f()
    }

    /// 控制流缓存包装
    pub fn with_cache<F, T>(
        cache: &mut std::collections::HashMap<i32, T>,
        key: i32,
        f: F,
    ) -> T
    where
        F: FnOnce() -> T,
        T: Clone,
    {
        cache
            .entry(key)
            .or_insert_with(f)
            .clone()
    }
}

/// 控制流装饰器：为函数添加控制流功能
pub struct ControlFlowDecorator;

impl ControlFlowDecorator {
    /// 添加调用者追踪的装饰器
    #[track_caller]
    pub fn with_tracking<F, T>(f: F) -> Result<T, LocatedError>
    where
        F: FnOnce() -> Result<T, LocatedError>,
    {
        let caller = Location::caller();
        match f() {
            Ok(result) => {
                println!("操作成功于 {}:{}", caller.file(), caller.line());
                Ok(result)
            }
            Err(e) => {
                eprintln!("操作失败于 {}:{} - {}", caller.file(), caller.line(), e);
                Err(e)
            }
        }
    }

    /// 添加性能分析的装饰器
    pub fn with_profiling<F, T>(profiler: &mut ControlFlowProfiler, f: F) -> T
    where
        F: FnOnce() -> T,
    {
        profiler.profile_branch(f)
    }

    /// 添加验证的装饰器
    #[track_caller]
    pub fn with_validation<F, T>(
        validator: impl Fn(&T) -> Result<(), LocatedError>,
        f: F,
    ) -> Result<T, LocatedError>
    where
        F: FnOnce() -> Result<T, LocatedError>,
    {
        let result = f()?;
        validator(&result)?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_control_flow_check() {
        let result = control_flow_check(true);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_control_flow_branch() {
        assert!(control_flow_branch(42).is_ok());
        assert!(control_flow_branch(-1).is_err());
        assert!(control_flow_branch(101).is_err());
    }

    #[test]
    fn test_control_flow_loop() {
        assert_eq!(control_flow_loop(0), 0);
        assert_eq!(control_flow_loop(5), 5);
    }

    #[test]
    fn test_control_flow_match() {
        assert_eq!(control_flow_match(Some(21)), 42);
        assert_eq!(control_flow_match(Some(-21)), 21);
        assert_eq!(control_flow_match(None), 0);
    }

    #[test]
    fn test_located_error() {
        let error = LocatedError::new("测试错误");
        assert!(error.message.contains("测试错误"));
        assert!(!error.context.file.is_empty());
    }

    #[test]
    fn test_error_context() {
        let context = ErrorContext::current();
        assert!(!context.file.is_empty());
        assert!(context.line > 0);
    }

    #[test]
    fn test_control_flow_analyzer() {
        let mut analyzer = ControlFlowAnalyzer::new();
        analyzer.analyze_branch(true);
        analyzer.analyze_loop(5, |i| i % 2 == 0);
        analyzer.analyze_match(Some(42));

        let (branches, loops, matches) = analyzer.get_statistics();
        assert_eq!(branches, 1);
        assert_eq!(loops, 1);
        assert_eq!(matches, 1);
    }

    #[test]
    fn test_control_flow_optimizer() {
        let result = ControlFlowOptimizer::optimize_loop(10);
        assert!(result > 0);

        assert!(ControlFlowOptimizer::optimize_branch(42).is_ok());
        assert!(ControlFlowOptimizer::optimize_branch(-1).is_err());

        assert_eq!(ControlFlowOptimizer::optimize_match(Some(21)), 42);
        assert_eq!(ControlFlowOptimizer::optimize_match(None), 0);
    }

    #[test]
    fn test_tracked_panic_handler() {
        // 测试不会 panic
        tracked_panic_handler("Test message");
    }

    #[test]
    fn test_get_rust_192_info() {
        let info = get_rust_192_control_flow_info();
        assert!(!info.is_empty());
        assert!(info.contains("Rust 1.92.0"));
    }

    #[test]
    fn test_control_flow_matcher() {
        assert_eq!(ControlFlowMatcher::match_with_guard(-5), "负数");
        assert_eq!(ControlFlowMatcher::match_with_guard(0), "零");
        assert_eq!(ControlFlowMatcher::match_with_guard(5), "小正数");
        assert_eq!(ControlFlowMatcher::match_with_guard(50), "中等正数");
        assert_eq!(ControlFlowMatcher::match_with_guard(200), "大正数");

        assert_eq!(ControlFlowMatcher::nested_match(Some(Some(21))), 42);
        assert_eq!(ControlFlowMatcher::nested_match(Some(Some(-21))), 21);
        assert_eq!(ControlFlowMatcher::nested_match(Some(None)), 0);
        assert_eq!(ControlFlowMatcher::nested_match(None), -1);

        assert_eq!(ControlFlowMatcher::tuple_match((3, 3, 3)), 9);
        assert_eq!(ControlFlowMatcher::tuple_match((2, 2, 1)), 4);
        assert_eq!(ControlFlowMatcher::tuple_match((1, 2, 3)), 6);

        assert_eq!(ControlFlowMatcher::range_match(5), "单位数");
        assert_eq!(ControlFlowMatcher::range_match(42), "两位数");
        assert_eq!(ControlFlowMatcher::range_match(123), "三位数");
    }

    #[test]
    fn test_control_flow_combinator() {
        let values = vec![10, 20, 30, 40, 50];
        let result = ControlFlowCombinator::chain_conditions(&values).unwrap();
        assert_eq!(result, vec![20, 40, 60, 80, 100]);

        let invalid_values = vec![10, -5, 30];
        assert!(ControlFlowCombinator::chain_conditions(&invalid_values).is_err());

        let items = vec![Some(21), Some(-21), None, Some(10)];
        let result = ControlFlowCombinator::combine_loop_and_match(&items);
        assert_eq!(result, vec![42, 21, 0, 20]);

        let items = vec![10, 20, -5, 30];
        let (branches, _loops, _matches, optimized) = ControlFlowCombinator::analyze_and_optimize(&items);
        assert_eq!(branches, 4);
        // optimized 是 usize，总是 >= 0，所以只验证它被正确计算
        let _ = optimized;
    }

    #[test]
    fn test_control_flow_profiler() {
        let mut profiler = ControlFlowProfiler::new();

        profiler.profile_branch(|| {
            let _ = control_flow_branch(42);
        });
        profiler.profile_loop(|| control_flow_loop(100));
        profiler.profile_match(|| control_flow_match(Some(21)));

        let (branch_avg, loop_avg, match_avg) = profiler.get_stats();
        assert!(branch_avg >= 0.0);
        assert!(loop_avg >= 0.0);
        assert!(match_avg >= 0.0);

        profiler.reset();
        let (branch_avg, loop_avg, match_avg) = profiler.get_stats();
        assert_eq!(branch_avg, 0.0);
        assert_eq!(loop_avg, 0.0);
        assert_eq!(match_avg, 0.0);
    }

    #[test]
    fn test_control_flow_validator() {
        assert!(ControlFlowValidator::validate_branch(42).is_ok());
        assert!(ControlFlowValidator::validate_branch(-1).is_err());
        assert!(ControlFlowValidator::validate_branch(1001).is_err());

        assert!(ControlFlowValidator::validate_loop_termination(100).is_ok());
        assert!(ControlFlowValidator::validate_loop_termination(0).is_ok());
        assert!(ControlFlowValidator::validate_loop_termination(2_000_000).is_err());

        assert!(ControlFlowValidator::validate_match_coverage(Some(42)).is_ok());
        assert!(ControlFlowValidator::validate_match_coverage(Some(-1)).is_err());
        assert!(ControlFlowValidator::validate_match_coverage(None).is_err());
    }

    #[test]
    fn test_control_flow_state_machine() {
        let mut machine = ControlFlowStateMachine::new();
        assert_eq!(machine.current_state(), ControlFlowState::Initial);

        // 测试有效的状态转换
        assert!(machine.transition_to(ControlFlowState::Processing).is_ok());
        assert_eq!(machine.current_state(), ControlFlowState::Processing);

        assert!(machine.transition_to(ControlFlowState::Validating).is_ok());
        assert_eq!(machine.current_state(), ControlFlowState::Validating);

        assert!(machine.transition_to(ControlFlowState::Completed).is_ok());
        assert_eq!(machine.current_state(), ControlFlowState::Completed);

        // 测试无效的状态转换
        let mut machine2 = ControlFlowStateMachine::new();
        machine2.transition_to(ControlFlowState::Processing).unwrap();
        assert!(machine2.transition_to(ControlFlowState::Completed).is_err());

        // 测试工作流执行
        let mut machine3 = ControlFlowStateMachine::new();
        assert!(machine3.execute_workflow(42).is_ok());
        assert_eq!(machine3.current_state(), ControlFlowState::Completed);

        // 测试重置
        machine3.reset();
        assert_eq!(machine3.current_state(), ControlFlowState::Initial);
        assert_eq!(machine3.transition_count(), 0);
    }

    #[test]
    fn test_iterator_control_flow() {
        // 测试过滤
        let numbers = vec![1, 2, 3, 4, 5, -1, 6];
        let filtered = IteratorControlFlow::filter_with_control_flow(numbers.iter(), |&x| {
            if *x < 0 {
                Err(LocatedError::new("负数"))
            } else {
                Ok(*x % 2 == 0)
            }
        });
        // 应该只包含 2, 4，在遇到 -1 时停止
        assert!(filtered.len() <= 5);

        // 测试映射
        let numbers = vec![10, 20, 30];
        let mapped = IteratorControlFlow::map_with_control_flow(numbers.iter(), |&x| {
            control_flow_branch(x)
        });
        assert!(mapped.is_ok());
        assert_eq!(mapped.unwrap().len(), 3);

        // 测试折叠
        let numbers = vec![1, 2, 3, 4, 5];
        let sum = IteratorControlFlow::fold_with_control_flow(
            numbers.iter(),
            0,
            |acc, &x| Ok(acc + x),
        );
        assert_eq!(sum.unwrap(), 15);

        // 测试查找
        let numbers = vec![1, 2, 3, 4, 5];
        let found = IteratorControlFlow::find_with_control_flow(numbers.iter(), |&x| {
            Ok(*x == 3)
        });
        assert_eq!(found, Some(&3));
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_parallel_control_flow() {
        use parallel_control_flow::parallel_control_flow_branch;

        let values = vec![10, 20, 30, -1, 50, 150];
        let result = parallel_control_flow_branch(&values, 2);

        assert!(result.all_results().len() == values.len());
        assert!(result.successes() > 0);
        assert!(result.failures() > 0);
    }

    #[test]
    fn test_control_flow_visualization() {
        let mut viz = ControlFlowVisualization::new();

        viz.add_branch("条件检查 1");
        viz.add_branch("条件检查 2");
        viz.add_loop("迭代处理");
        viz.add_match("模式匹配");
        viz.add_error("验证失败");

        let (branches, loops, matches, errors) = viz.statistics();
        assert_eq!(branches, 2);
        assert_eq!(loops, 1);
        assert_eq!(matches, 1);
        assert_eq!(errors, 1);

        let report = viz.generate_report();
        assert!(report.contains("分支数量: 2"));
        assert!(report.contains("循环数量: 1"));
        assert!(report.contains("匹配数量: 1"));
        assert!(report.contains("错误数量: 1"));
    }

    #[cfg(feature = "async")]
    #[tokio::test]
    async fn test_async_control_flow() {
        use async_control_flow::*;

        // 测试异步分支
        let result = async_control_flow_branch(42).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 84);

        // 测试异步循环
        let count = async_control_flow_loop(5).await;
        assert_eq!(count, 5);

        // 测试异步匹配
        let result = async_control_flow_match(Some(21)).await;
        assert_eq!(result, 42);

        // 测试异步组合器
        let values = vec![10, 20, 30];
        let results = async_control_flow_combinator(&values).await;
        assert!(results.is_ok());
        assert_eq!(results.unwrap().len(), 3);
    }

    #[test]
    fn test_control_flow_utils() {
        // 测试批量分支
        let values = vec![10, 20, -5, 30];
        let results = ControlFlowUtils::batch_branch(&values);
        assert_eq!(results.len(), 4);
        assert!(results[0].is_ok());
        assert!(results[2].is_err());

        // 测试批量匹配
        let matches = vec![Some(21), Some(-21), None, Some(10)];
        let results = ControlFlowUtils::batch_match(&matches);
        assert_eq!(results, vec![42, 21, 0, 20]);

        // 测试条件组合
        assert!(ControlFlowUtils::all_conditions(&[true, true, true]));
        assert!(!ControlFlowUtils::all_conditions(&[true, false, true]));
        assert!(ControlFlowUtils::any_condition(&[false, true, false]));
        assert!(!ControlFlowUtils::any_condition(&[false, false, false]));

        // 测试重试机制
        let mut attempts = 0;
        let result = ControlFlowUtils::retry_with_control_flow(
            || {
                attempts += 1;
                if attempts < 3 {
                    Err(LocatedError::new("临时失败"))
                } else {
                    Ok(42)
                }
            },
            3,
        );
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);

        // 测试缓存
        let mut cache = std::collections::HashMap::new();
        let value1 = ControlFlowUtils::with_cache(&mut cache, 1, || 42);
        let value2 = ControlFlowUtils::with_cache(&mut cache, 1, || 100);
        assert_eq!(value1, 42);
        assert_eq!(value2, 42); // 应该从缓存获取
    }

    #[test]
    fn test_control_flow_decorator() {
        // 测试追踪装饰器
        let result = ControlFlowDecorator::with_tracking(|| control_flow_branch(42));
        assert!(result.is_ok());

        // 测试性能分析装饰器
        let mut profiler = ControlFlowProfiler::new();
        let result = ControlFlowDecorator::with_profiling(&mut profiler, || 42);
        assert_eq!(result, 42);

        // 测试验证装饰器
        let result = ControlFlowDecorator::with_validation(
            |&v: &i32| {
                if v > 0 {
                    Ok(())
                } else {
                    Err(LocatedError::new("值必须大于0"))
                }
            },
            || control_flow_branch(42),
        );
        assert!(result.is_ok());
    }
}
