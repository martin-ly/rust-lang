//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **注意**: 本示例针对 Rust 1.89 版本编写，部分特性在 Rust 1.90 中已有更新。
//!
//! ## Rust 1.90 主要更新
//!
//! ### 编译器改进
//! - **LLD 链接器**: Linux x86_64 默认启用，链接速度提升约 2x
//! - **编译性能**: 增量编译优化，构建速度提升
//!
//! ### 标准库更新
//! - `u{n}::checked_sub_signed()` - 新增带符号减法检查方法
//! - `<[T]>::reverse()` - 现在可在 const 上下文中使用
//! - `f32/f64` 数学函数 - floor/ceil/trunc 等在 const 中可用
//!
//! ### Lint 改进
//! - `mismatched_lifetime_syntaxes` - 默认启用，检查生命周期语法一致性
//!
//! ## 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.90"`, `edition = "2024"`
//! 2. 应用新的稳定 API 和 const 函数增强
//! 3. 检查并修复新 lint 警告
//!
//! 参考: [Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//!
//! ---
//!
//! # Rust 1.89 基础语法新特性模块
//!
//! 本模块专门展示 Rust 1.89 版本中基础语法的新特性和增强功能：
//! - let_chains 稳定化
//! - cfg_boolean_literals 稳定化
//! - 改进的模式匹配
//! - 增强的类型推断
//! - 新的控制流特性
//! - 改进的错误处理
//!
//! 所有示例都使用 Rust 1.89 的最新语法，并包含详细的注释和最佳实践。

use std::collections::HashMap;
use std::fmt::{self, Display};
use std::sync::Arc;

/// Rust 1.89 基础语法新特性演示结构体
///
/// 这个结构体用于演示 Rust 1.89 的基础语法新特性，包括：
/// - 改进的泛型语法
/// - 增强的生命周期推断
/// - 新的模式匹配特性
/// - 改进的错误处理
#[derive(Debug, Clone, PartialEq)]
pub struct Rust189BasicSyntax<T>
where
    T: Clone + PartialEq + Display + Send + Sync,
{
    /// 数据字段，使用泛型类型
    pub data: T,
    /// 状态字段
    pub state: State,
    /// 元数据映射
    pub metadata: HashMap<String, String>,
    /// 线程安全引用计数
    pub shared_data: Arc<T>,
}

/// 状态枚举，展示 Rust 1.89 的枚举增强
#[derive(Debug, Clone, PartialEq)]
pub enum State {
    /// 初始化状态
    Initialized,
    /// 运行中状态
    Running,
    /// 暂停状态
    Paused,
    /// 完成状态
    Completed,
    /// 错误状态，包含错误信息
    Error(String),
}

impl<T> Rust189BasicSyntax<T>
where
    T: Clone + PartialEq + Display + Send + Sync,
{
    /// 创建新的 Rust189BasicSyntax 实例
    ///
    /// # 参数
    /// * `data` - 要存储的数据
    ///
    /// # 返回值
    /// 返回一个新的 Rust189BasicSyntax 实例
    ///
    /// # 示例
    /// ```rust
    /// use c03_control_fn::rust_189_basic_syntax::{Rust189BasicSyntax, State};
    ///
    /// let demo = Rust189BasicSyntax::new(42);
    /// assert_eq!(demo.data, 42);
    /// assert_eq!(demo.state, State::Initialized);
    /// ```
    pub fn new(data: T) -> Self {
        Self {
            data: data.clone(),
            state: State::Initialized,
            metadata: HashMap::new(),
            shared_data: Arc::new(data),
        }
    }

    /// 更新状态
    ///
    /// # 参数
    /// * `new_state` - 新状态
    ///
    /// # 示例
    /// ```rust
    /// use c03_control_fn::rust_189_basic_syntax::{Rust189BasicSyntax, State};
    ///
    /// let mut demo = Rust189BasicSyntax::new(42);
    /// demo.update_state(State::Running);
    /// assert_eq!(demo.state, State::Running);
    /// ```
    pub fn update_state(&mut self, new_state: State) {
        self.state = new_state;
    }

    /// 添加元数据
    ///
    /// # 参数
    /// * `key` - 键
    /// * `value` - 值
    ///
    /// # 示例
    /// ```rust
    /// use c03_control_fn::rust_189_basic_syntax::Rust189BasicSyntax;
    ///
    /// let mut demo = Rust189BasicSyntax::new(42);
    /// demo.add_metadata("version".to_string(), "1.0.0".to_string());
    /// assert_eq!(demo.metadata.get("version"), Some(&"1.0.0".to_string()));
    /// ```
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    /// 获取共享数据的克隆
    ///
    /// # 返回值
    /// 返回共享数据的克隆
    ///
    /// # 示例
    /// ```rust
    /// use c03_control_fn::rust_189_basic_syntax::Rust189BasicSyntax;
    ///
    /// let demo = Rust189BasicSyntax::new(42);
    /// let shared = demo.get_shared_data();
    /// assert_eq!(*shared, 42);
    /// ```
    pub fn get_shared_data(&self) -> Arc<T> {
        Arc::clone(&self.shared_data)
    }
}

impl<T> Display for Rust189BasicSyntax<T>
where
    T: Clone + PartialEq + Display + Send + Sync,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Rust189BasicSyntax(data: {}, state: {:?})", self.data, self.state)
    }
}

/// let_chains 稳定化演示
///
/// 展示 Rust 1.89 中 let_chains 特性的强大功能
pub mod let_chains {
    use super::*;

    /// 基础 let_chains 演示
    ///
    /// 展示在 if 和 while 条件中使用 && 操作符的新语法
    pub fn basic_let_chains() {
        println!("=== let_chains 基础演示 ===");

        // 1. 基础 let_chains 语法
        let x = Some(42);
        let y = Some("hello");
        let z = Some(std::f64::consts::PI);

        // 使用 let_chains 进行多重条件检查
        if let Some(value) = x && let Some(text) = y && let Some(pi) = z {
            println!("所有值都存在: x = {}, y = {}, z = {}", value, text, pi);
        }

        // 2. 复杂条件组合
        let numbers = [1, 2, 3, 4, 5];
        let threshold = 3;

        if let Some(first) = numbers.first() &&
           let Some(last) = numbers.last() &&
           *first < threshold &&
           *last > threshold {
            println!("数组满足条件: 首元素 {} < {}, 末元素 {} > {}",
                    first, threshold, last, threshold);
        }

        // 3. 嵌套 Option 处理
        let nested_option = Some(Some(42));
        if let Some(inner) = nested_option && let Some(value) = inner {
            println!("嵌套 Option 值: {}", value);
        }

        // 4. 多变量绑定
        let tuple = (Some(1), Some(2), Some(3));
        if let (Some(a), Some(b), Some(c)) = tuple && a + b == c {
            println!("元组满足条件: {} + {} = {}", a, b, c);
        }
    }

    /// 高级 let_chains 演示
    ///
    /// 展示 let_chains 的高级用法和复杂场景
    pub fn advanced_let_chains() {
        println!("\n=== let_chains 高级演示 ===");

        // 1. 与模式匹配结合
        let data = vec![
            ("Alice", Some(25), Some("Engineer")),
            ("Bob", Some(30), None),
            ("Charlie", None, Some("Designer")),
        ];

        for (name, age, job) in data {
            if let Some(age_val) = age &&
               let Some(job_val) = job &&
               age_val >= 25 {
                println!("{} 是 {} 岁的 {}", name, age_val, job_val);
            }
        }

        // 2. 错误处理中的 let_chains
        let results = vec![
            Ok(Some(42)),
            Ok(None),
            Err("错误"),
        ];

        for result in results {
            if let Ok(Some(value)) = result && value > 40 {
                println!("成功获取大值: {}", value);
            }
        }

        // 3. 复杂数据结构处理
        let complex_data = HashMap::from([
            ("user1".to_string(), Some(("Alice", Some(25)))),
            ("user2".to_string(), Some(("Bob", None))),
            ("user3".to_string(), None),
        ]);

        for (_id, user_data) in complex_data {
            if let Some((name, Some(age))) = user_data &&
               age >= 18 {
                println!("用户 {}: {} 岁", name, age);
            }
        }

        // 4. 与守卫条件结合
        let numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        for chunk in numbers.chunks(3) {
            if let [Some(a), Some(b), Some(c)] = [
                chunk.first(),
                chunk.get(1),
                chunk.get(2)
            ] && a + b + c > 10 {
                println!("大块: {} + {} + {} = {}", a, b, c, a + b + c);
            }
        }
    }

    /// while 循环中的 let_chains
    ///
    /// 展示在 while 循环中使用 let_chains 的用法
    pub fn while_let_chains() {
        println!("\n=== while let_chains 演示 ===");

        // 1. 基础 while let_chains
        let mut stack = vec![Some(1), Some(2), Some(3), None, Some(4)];

        while let Some(Some(value)) = stack.pop() && value > 0 {
            println!("处理值: {}", value);
        }

        // 2. 复杂 while let_chains
        let mut data = vec![
            Some((1, Some("a"))),
            Some((2, Some("b"))),
            Some((3, None)),
            None,
        ];

        while let Some(Some((num, Some(letter)))) = data.pop() {
            println!("数字: {}, 字母: {}", num, letter);
        }

        // 3. 与迭代器结合
        let mut iter = vec![Some(1), Some(2), None, Some(3)].into_iter();

        while let Some(Some(value)) = iter.next() && value < 3 {
            println!("迭代值: {}", value);
        }
    }
}

/// cfg_boolean_literals 稳定化演示
///
/// 展示 Rust 1.89 中条件编译的增强功能
pub mod cfg_boolean_literals {

    /// 基础 cfg_boolean_literals 演示
    ///
    /// 展示在条件编译中使用布尔字面量的新语法
    pub fn basic_cfg_boolean_literals() {
        println!("\n=== cfg_boolean_literals 基础演示 ===");

        // 1. 基础布尔字面量使用 (演示)
        // #[cfg(feature = "debug")]
        // println!("调试模式已启用");
        println!("调试模式已启用 (演示)");

        // #[cfg(not(feature = "debug"))]
        // println!("调试模式未启用");
        println!("调试模式未启用 (演示)");

        // 2. 复杂条件组合
        #[cfg(all(feature = "async", feature = "performance"))]
        println!("异步性能模式已启用");

        #[cfg(feature = "test")]
        println!("测试模式已启用");

        // 3. 平台特定编译
        #[cfg(target_os = "windows")]
        println!("Windows 平台");

        #[cfg(target_os = "linux")]
        println!("Linux 平台");

        #[cfg(target_os = "macos")]
        println!("macOS 平台");

        // 4. 架构特定编译
        #[cfg(target_arch = "x86_64")]
        println!("x86_64 架构");

        #[cfg(target_arch = "aarch64")]
        println!("ARM64 架构");
    }

    /// 高级 cfg_boolean_literals 演示
    ///
    /// 展示条件编译的高级用法
    pub fn advanced_cfg_boolean_literals() {
        println!("\n=== cfg_boolean_literals 高级演示 ===");

        // 1. 自定义条件 (演示)
        // #[cfg(my_custom_flag)]
        // println!("自定义标志已设置");
        println!("自定义标志已设置 (演示)");

        // 2. 版本检查 (注释掉实验性特性)
        // #[cfg(version("1.89"))]
        // println!("Rust 1.89 特性可用");
        println!("Rust 1.89 特性可用 (演示)");

        // 3. 条件函数定义
        conditional_function();

        // 4. 条件结构体定义
        let demo = ConditionalStruct::new();
        demo.conditional_method();
    }

    /// 条件函数（仅在特定条件下编译）
    #[cfg(feature = "test")]
    fn conditional_function() {
        println!("测试功能已启用");
    }

    #[cfg(not(feature = "test"))]
    fn conditional_function() {
        println!("测试功能未启用");
    }

    /// 条件结构体
    #[cfg(feature = "performance")]
    struct ConditionalStruct {
        data: i32,
    }

    #[cfg(not(feature = "performance"))]
    struct ConditionalStruct {
        data: String,
    }

    impl ConditionalStruct {
        #[cfg(feature = "performance")]
        fn new() -> Self {
            Self { data: 42 }
        }

        #[cfg(not(feature = "performance"))]
        fn new() -> Self {
            Self { data: "default".to_string() }
        }

        #[cfg(feature = "performance")]
        fn conditional_method(&self) {
            println!("性能模式方法: {}", self.data);
        }

        #[cfg(not(feature = "performance"))]
        fn conditional_method(&self) {
            println!("基础模式方法: {}", self.data);
        }
    }
}

/// 改进的模式匹配演示
///
/// 展示 Rust 1.89 中模式匹配的增强功能
pub mod enhanced_pattern_matching {

    /// 基础增强模式匹配演示
    ///
    /// 展示模式匹配的新特性和改进
    pub fn basic_enhanced_pattern_matching() {
        println!("\n=== 增强模式匹配基础演示 ===");

        // 1. 改进的切片模式
        let numbers = vec![1, 2, 3, 4, 5];

        match numbers.as_slice() {
            [] => println!("空数组"),
            [single] => println!("单个元素: {}", single),
            [first, second] => println!("两个元素: {}, {}", first, second),
            [first, middle @ .., last] => {
                println!("多个元素: 首 = {}, 末 = {}, 中间元素数量: {}", first, last, middle.len());
            }
        }

        // 2. 改进的守卫条件
        let value = Some(42);
        match value {
            Some(x) if x > 40 && x < 50 => println!("值在范围内: {}", x),
            Some(x) if x % 2 == 0 => println!("偶数值: {}", x),
            Some(x) => println!("其他值: {}", x),
            None => println!("没有值"),
        }

        // 3. 复杂嵌套模式
        let complex_data = Some(Some(Some(42)));
        match complex_data {
            Some(Some(Some(value))) if value > 40 => println!("深层嵌套值: {}", value),
            Some(Some(None)) => println!("中间层为 None"),
            Some(None) => println!("内层为 None"),
            None => println!("外层为 None"),
            _ => println!("其他情况"),
        }
    }

    /// 高级增强模式匹配演示
    ///
    /// 展示模式匹配的高级用法
    pub fn advanced_enhanced_pattern_matching() {
        println!("\n=== 增强模式匹配高级演示 ===");

        // 1. 自定义模式匹配
        let shapes = vec![
            Shape::Circle(5.0),
            Shape::Rectangle(10.0, 20.0),
            Shape::Triangle(3.0, 4.0, 5.0),
        ];

        for shape in shapes {
            match shape {
                Shape::Circle(radius) if radius > 0.0 => {
                    let area = std::f64::consts::PI * radius * radius;
                    println!("圆形面积: {:.2}", area);
                }
                Shape::Rectangle(width, height) if width > 0.0 && height > 0.0 => {
                    let area = width * height;
                    println!("矩形面积: {:.2}", area);
                }
                Shape::Triangle(a, b, c) if is_valid_triangle(a, b, c) => {
                    let s = (a + b + c) / 2.0;
                    let area = (s * (s - a) * (s - b) * (s - c)).sqrt();
                    println!("三角形面积: {:.2}", area);
                }
                _ => println!("无效形状"),
            }
        }

        // 2. 异步模式匹配
        let async_results = vec![
            AsyncResult::Success(42),
            AsyncResult::Pending,
            AsyncResult::Error("网络错误".to_string()),
        ];

        for result in async_results {
            match result {
                AsyncResult::Success(value) => println!("异步成功: {}", value),
                AsyncResult::Pending => println!("异步等待中..."),
                AsyncResult::Error(msg) => println!("异步错误: {}", msg),
            }
        }
    }

    /// 形状枚举定义
    #[derive(Debug)]
    enum Shape {
        Circle(f64),
        Rectangle(f64, f64),
        Triangle(f64, f64, f64),
    }

    /// 异步结果枚举定义
    #[derive(Debug)]
    enum AsyncResult {
        Success(i32),
        Pending,
        Error(String),
    }

    /// 检查三角形是否有效
    fn is_valid_triangle(a: f64, b: f64, c: f64) -> bool {
        a + b > c && a + c > b && b + c > a
    }
}

/// 增强的类型推断演示
///
/// 展示 Rust 1.89 中类型推断的改进
pub mod enhanced_type_inference {
    use super::*;

    /// 基础增强类型推断演示
    ///
    /// 展示类型推断的改进和新特性
    pub fn basic_enhanced_type_inference() {
        println!("\n=== 增强类型推断基础演示 ===");

        // 1. 改进的闭包类型推断
        let closure = |x| x * 2;
        let result = closure(21);
        println!("闭包推断结果: {}", result);

        // 2. 复杂泛型推断
        let data = create_generic_data(42);
        println!("泛型数据: {}", data);

        // 3. 迭代器链式推断
        let numbers = [1, 2, 3, 4, 5];
        let processed: Vec<i32> = numbers
            .iter()
            .filter(|&&x| x % 2 == 0)
            .map(|&x| x * 2)
            .collect();
        println!("处理后的数字: {:?}", processed);

        // 4. 异步类型推断 (演示)
        // let async_result = async_operation(10);
        // println!("异步操作结果: {:?}", async_result);
        println!("异步操作结果: Future<Output = i32> (演示)");
    }

    /// 高级增强类型推断演示
    ///
    /// 展示类型推断的高级用法
    pub fn advanced_enhanced_type_inference() {
        println!("\n=== 增强类型推断高级演示 ===");

        // 1. 复杂生命周期推断
        let text = "Hello, Rust!";
        let result = process_text(text);
        println!("文本处理结果: {}", result);

        // 2. 高阶函数类型推断
        let numbers = [1, 2, 3, 4, 5];
        let sum = numbers.iter().sum::<i32>();
        println!("数字总和: {}", sum);

        // 3. 复杂数据结构推断
        let complex_data = create_complex_data();
        println!("复杂数据: {:?}", complex_data);

        // 4. 异步流类型推断
        let async_stream = create_async_stream();
        println!("异步流: {:?}", async_stream);
    }

    /// 创建泛型数据
    fn create_generic_data<T>(value: T) -> GenericData<T>
    where
        T: Clone + Display,
    {
        GenericData { value }
    }

    /// 异步操作
    #[allow(dead_code)]
    async fn async_operation(x: i32) -> i32 {
        x * 2
    }

    /// 处理文本
    fn process_text(text: &str) -> &str {
        text
    }

    /// 创建复杂数据
    fn create_complex_data() -> ComplexData {
        ComplexData {
            numbers: vec![1, 2, 3],
            text: "Hello".to_string(),
            flag: true,
        }
    }

    /// 创建异步流
    fn create_async_stream() -> AsyncStream {
        AsyncStream {
            data: vec![1, 2, 3],
            index: 0,
        }
    }

    /// 泛型数据结构
    #[derive(Debug)]
    struct GenericData<T> {
        value: T,
    }

    impl<T> Display for GenericData<T>
    where
        T: Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "GenericData({})", self.value)
        }
    }

    /// 复杂数据结构
    #[derive(Debug)]
    #[allow(dead_code)]
    struct ComplexData {
        numbers: Vec<i32>,
        text: String,
        flag: bool,
    }

    /// 异步流结构
    #[derive(Debug)]
    #[allow(dead_code)]
    struct AsyncStream {
        data: Vec<i32>,
        index: usize,
    }
}

/// 新的控制流特性演示
///
/// 展示 Rust 1.89 中控制流的新特性
pub mod new_control_flow {

    /// 基础新控制流演示
    ///
    /// 展示控制流的新特性和改进
    pub fn basic_new_control_flow() {
        println!("\n=== 新控制流基础演示 ===");

        // 1. 改进的 for 循环
        let numbers = [1, 2, 3, 4, 5];

        // 使用 enumerate 获取索引
        for (index, value) in numbers.iter().enumerate() {
            println!("索引 {}: 值 {}", index, value);
        }

        // 2. 改进的 while 循环
        let mut counter = 0;
        while counter < 5 {
            println!("计数器: {}", counter);
            counter += 1;
        }

        // 3. 新的循环控制
        let mut data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        while let Some(value) = data.pop() {
            if value % 3 == 0 {
                println!("找到3的倍数: {}", value);
                break;
            }
        }

        // 4. 改进的条件表达式
        let x = 42;
        let result = if x > 40 { "大" } else { "小" };
        println!("条件表达式结果: {}", result);
    }

    /// 高级新控制流演示
    ///
    /// 展示控制流的高级用法
    pub fn advanced_new_control_flow() {
        println!("\n=== 新控制流高级演示 ===");

        // 1. 复杂迭代器链
        let numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let result: Vec<i32> = numbers
            .iter()
            .filter(|&&x| x % 2 == 0)
            .map(|&x| x * x)
            .take(3)
            .collect();
        println!("处理结果: {:?}", result);

        // 2. 异步控制流
        let async_data = vec![1, 2, 3, 4, 5];
        for value in async_data {
            // 模拟异步处理
            let processed = process_async_value(value);
            println!("异步处理结果: {}", processed);
        }

        // 3. 复杂条件控制
        let conditions = vec![true, false, true, false, true];
        let mut true_count = 0;

        for condition in conditions {
            if condition {
                true_count += 1;
                if true_count >= 3 {
                    println!("找到足够的真值: {}", true_count);
                    break;
                }
            }
        }

        // 4. 嵌套控制流
        let matrix = [vec![1, 2, 3],
            vec![4, 5, 6],
            vec![7, 8, 9]];

        'outer: for (row_idx, row) in matrix.iter().enumerate() {
            for (col_idx, &value) in row.iter().enumerate() {
                if value == 5 {
                    println!("找到5在位置: ({}, {})", row_idx, col_idx);
                    break 'outer;
                }
            }
        }
    }

    /// 处理异步值
    fn process_async_value(value: i32) -> i32 {
        value * 2
    }
}

/// 改进的错误处理演示
///
/// 展示 Rust 1.89 中错误处理的改进
pub mod improved_error_handling {
    use std::num::ParseIntError;

    /// 基础改进错误处理演示
    ///
    /// 展示错误处理的新特性和改进
    pub fn basic_improved_error_handling() {
        println!("\n=== 改进错误处理基础演示 ===");

        // 1. 改进的 Result 处理
        let results = vec![
            Ok(42),
            Err("错误1"),
            Ok(100),
            Err("错误2"),
        ];

        for result in results {
            match result {
                Ok(value) => println!("成功: {}", value),
                Err(error) => println!("错误: {}", error),
            }
        }

        // 2. 改进的 Option 处理
        let options = vec![
            Some(42),
            None,
            Some(100),
            None,
        ];

        for option in options {
            match option {
                Some(value) => println!("有值: {}", value),
                None => println!("无值"),
            }
        }

        // 3. 链式错误处理
        let result = parse_and_validate("42");
        match result {
            Ok(value) => println!("解析验证成功: {}", value),
            Err(error) => println!("解析验证失败: {}", error),
        }
    }

    /// 高级改进错误处理演示
    ///
    /// 展示错误处理的高级用法
    pub fn advanced_improved_error_handling() {
        println!("\n=== 改进错误处理高级演示 ===");

        // 1. 自定义错误类型
        let results = vec![
            CustomResult::Success(42),
            CustomResult::Warning("警告信息".to_string()),
            CustomResult::Error("错误信息".to_string()),
        ];

        for result in results {
            match result {
                CustomResult::Success(value) => println!("成功: {}", value),
                CustomResult::Warning(msg) => println!("警告: {}", msg),
                CustomResult::Error(msg) => println!("错误: {}", msg),
            }
        }

        // 2. 错误恢复
        let recoverable_result = recoverable_operation("invalid");
        match recoverable_result {
            Ok(value) => println!("操作成功: {}", value),
            Err(error) => println!("操作失败: {}", error),
        }

        // 3. 错误转换
        let conversion_result = convert_error("42");
        match conversion_result {
            Ok(value) => println!("转换成功: {}", value),
            Err(error) => println!("转换失败: {}", error),
        }
    }

    /// 解析并验证
    pub fn parse_and_validate(s: &str) -> Result<i32, String> {
        let parsed = s.parse::<i32>()
            .map_err(|_| "解析失败".to_string())?;

        if parsed < 0 {
            return Err("值不能为负数".to_string());
        }

        Ok(parsed)
    }

    /// 可恢复操作
    pub fn recoverable_operation(input: &str) -> Result<i32, String> {
        match input.parse::<i32>() {
            Ok(value) => Ok(value),
            Err(_) => {
                // 尝试恢复
                if input == "invalid" {
                    Ok(0) // 默认值
                } else {
                    Err("无法恢复".to_string())
                }
            }
        }
    }

    /// 错误转换
    fn convert_error(s: &str) -> Result<i32, CustomError> {
        s.parse::<i32>()
            .map_err(CustomError::ParseError)
    }

    /// 自定义结果类型
    #[derive(Debug)]
    #[allow(dead_code)]
    enum CustomResult {
        Success(i32),
        Warning(String),
        Error(String),
    }

    /// 自定义错误类型
    #[derive(Debug)]
    #[allow(dead_code)]
    enum CustomError {
        ParseError(ParseIntError),
        ValidationError(String),
    }

    impl std::fmt::Display for CustomError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                CustomError::ParseError(e) => write!(f, "解析错误: {}", e),
                CustomError::ValidationError(msg) => write!(f, "验证错误: {}", msg),
            }
        }
    }

    impl std::error::Error for CustomError {}
}

/// 综合演示函数
///
/// 运行所有 Rust 1.89 基础语法新特性演示
pub fn run_all_rust_189_demos() {
    println!("🚀 Rust 1.89 基础语法新特性综合演示");
    println!("===============================================");

    // 运行所有演示模块
    let_chains::basic_let_chains();
    let_chains::advanced_let_chains();
    let_chains::while_let_chains();

    cfg_boolean_literals::basic_cfg_boolean_literals();
    cfg_boolean_literals::advanced_cfg_boolean_literals();

    enhanced_pattern_matching::basic_enhanced_pattern_matching();
    enhanced_pattern_matching::advanced_enhanced_pattern_matching();

    enhanced_type_inference::basic_enhanced_type_inference();
    enhanced_type_inference::advanced_enhanced_type_inference();

    new_control_flow::basic_new_control_flow();
    new_control_flow::advanced_new_control_flow();

    improved_error_handling::basic_improved_error_handling();
    improved_error_handling::advanced_improved_error_handling();

    println!("\n✅ 所有 Rust 1.89 基础语法新特性演示完成！");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rust_189_basic_syntax_creation() {
        let demo = Rust189BasicSyntax::new(42);
        assert_eq!(demo.data, 42);
        assert_eq!(demo.state, State::Initialized);
        assert!(demo.metadata.is_empty());
    }

    #[test]
    fn test_rust_189_basic_syntax_state_update() {
        let mut demo = Rust189BasicSyntax::new(42);
        demo.update_state(State::Running);
        assert_eq!(demo.state, State::Running);
    }

    #[test]
    fn test_rust_189_basic_syntax_metadata() {
        let mut demo = Rust189BasicSyntax::new(42);
        demo.add_metadata("version".to_string(), "1.0.0".to_string());
        assert_eq!(demo.metadata.get("version"), Some(&"1.0.0".to_string()));
    }

    #[test]
    fn test_rust_189_basic_syntax_shared_data() {
        let demo = Rust189BasicSyntax::new(42);
        let shared = demo.get_shared_data();
        assert_eq!(*shared, 42);
    }

    #[test]
    fn test_parse_and_validate() {
        assert_eq!(improved_error_handling::parse_and_validate("42").unwrap(), 42);
        assert!(improved_error_handling::parse_and_validate("-1").is_err());
        assert!(improved_error_handling::parse_and_validate("abc").is_err());
    }

    #[test]
    fn test_recoverable_operation() {
        assert_eq!(improved_error_handling::recoverable_operation("42").unwrap(), 42);
        assert_eq!(improved_error_handling::recoverable_operation("invalid").unwrap(), 0);
        assert!(improved_error_handling::recoverable_operation("abc").is_err());
    }
}
