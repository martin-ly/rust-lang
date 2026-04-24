//! # Rust 2024 Edition `let chains` 深度专题
//!
//! `let chains` 是 Rust 2024 Edition 中稳定化的重要特性，
//! 允许在 `if` 和 `while` 条件中将 `let` 绑定与普通布尔表达式链式组合，
//! 大幅简化嵌套的 `if let` 代码。
//!
//! ## 语法
//! ```rust,ignore
//! if let Some(x) = opt && x > 0 && let Ok(y) = parse(x) {
//!     // 所有条件同时满足时执行
//! }
//! ```
//!
//! ## 优势
//! - 减少嵌套层级，代码更扁平
//! - 避免右漂移（rightward drift）
//! - 条件逻辑一目了然
//! - 在 `while` 循环中同样适用

// ==================== 示例 1: 基础 let chains ====================

/// 基础 let chains 示例：解析并验证数值
///
/// 传统写法需要三层嵌套，let chains 将其扁平化为单个条件表达式。
pub fn parse_and_validate(input: Option<&str>) -> Result<i32, &'static str> {
    // let chains 写法：依次检查 Option、数值范围、额外条件
    if let Some(s) = input
        && let Ok(n) = s.parse::<i32>()
        && n > 0
        && n <= 1000
    {
        Ok(n)
    } else {
        Err("输入必须是 1 到 1000 之间的正整数")
    }
}

/// while let chains：从迭代器中累加正数，遇到非正数或无效数据时停止
///
/// while let chains 的重要语义：如果链中任一条件不满足，循环终止（而非跳过）。
/// 因此它适合"当所有条件持续满足时进行处理"的场景。
pub fn sum_positive_entries<'a>(iter: &mut impl Iterator<Item = Option<&'a str>>) -> i32 {
    let mut total = 0;
    while let Some(Some(s)) = iter.next()
        && let Ok(n) = s.parse::<i32>()
        && n > 0
    {
        total += n;
    }
    total
}

// ==================== 示例 2: 多模式 let chains ====================

/// 多模式匹配与条件组合
///
/// 同时解构多个 Option/Result 值，并在同一条件链中检查。
pub fn combine_options(a: Option<i32>, b: Option<i32>, c: Result<i32, &str>) -> Option<i32> {
    if let Some(x) = a
        && let Some(y) = b
        && x < y
        && let Ok(z) = c
        && z > x + y
    {
        Some(x + y + z)
    } else {
        None
    }
}

/// 嵌套数据结构的条件访问
///
/// 安全地遍历嵌套的 Option 和 Result 类型。
pub fn extract_deep_value(data: Option<Result<Option<Vec<i32>>, &str>>) -> Option<i32> {
    if let Ok(inner) = data?
        && let Some(vec) = inner
        && let Some(first) = vec.first()
        && *first > 0
    {
        Some(*first)
    } else {
        None
    }
}

// ==================== 示例 3: let chains 在错误处理中的应用 ====================

/// 命令行参数解析器
///
/// 模拟解析命令行参数，验证端口、主机和超时配置。
#[derive(Debug, PartialEq, Clone)]
pub struct ServerConfig {
    /// 服务器主机地址
    pub host: String,
    /// 服务器端口
    pub port: u16,
    /// 连接超时（毫秒）
    pub timeout_ms: u64,
}

impl ServerConfig {
    /// 从字符串切片构建配置
    ///
    /// let chains 将多个解析和验证步骤合并为单一条件。
    pub fn from_args(
        host_arg: Option<&str>,
        port_arg: Option<&str>,
        timeout_arg: Option<&str>,
    ) -> Result<Self, &'static str> {
        if let Some(host) = host_arg
            && !host.is_empty()
            && let Some(port_str) = port_arg
            && let Ok(port) = port_str.parse::<u16>()
            && port > 1024
            && let Some(timeout_str) = timeout_arg
            && let Ok(timeout_ms) = timeout_str.parse::<u64>()
            && (100..=60000).contains(&timeout_ms)
        {
            Ok(ServerConfig {
                host: host.to_string(),
                port,
                timeout_ms,
            })
        } else {
            Err("参数无效：host 不能为空，port 必须是 1025-65535，timeout 必须是 100-60000ms")
        }
    }
}

/// 批量验证数据记录
///
/// 使用 let chains 过滤有效记录并计算统计信息。
pub fn filter_valid_records(records: &[Option<&str>]) -> (usize, i32, f64) {
    let mut count = 0usize;
    let mut sum = 0i32;

    for record in records {
        if let Some(s) = record
            && let Ok(n) = s.parse::<i32>()
            && (-100..=100).contains(&n)
        {
            count += 1;
            sum += n;
        }
    }

    let avg = if count > 0 {
        sum as f64 / count as f64
    } else {
        0.0
    };

    (count, sum, avg)
}

// ==================== 示例 4: let chains 与模式守卫 ====================

/// 使用 let chains 简化 match 守卫
///
/// 在 match 表达式中结合 let chains 进行复杂条件判断。
pub fn classify_value(value: Result<Option<&str>, &str>) -> &'static str {
    match value {
        Ok(Some(s)) if let Ok(n) = s.parse::<i32>() && n > 0 && n % 2 == 0 => "正偶数",
        Ok(Some(s)) if let Ok(n) = s.parse::<i32>() && n > 0 => "正奇数",
        Ok(Some(s)) if let Ok(n) = s.parse::<i32>() && n < 0 => "负数",
        Ok(Some(_)) => "非数字字符串",
        Ok(None) => "空值",
        Err(_) => "错误结果",
    }
}

// ==================== 演示函数 ====================

/// 演示 let chains 特性
pub fn demonstrate_let_chains() {
    println!("\n========================================");
    println!("   Rust 2024 Edition let chains 演示");
    println!("========================================\n");

    // 示例 1: 解析并验证
    println!("--- 示例 1: 解析并验证 ---");
    println!("parse_and_validate(Some(\"42\")) => {:?}", parse_and_validate(Some("42")));
    println!("parse_and_validate(Some(\"-5\")) => {:?}", parse_and_validate(Some("-5")));
    println!("parse_and_validate(Some(\"abc\")) => {:?}", parse_and_validate(Some("abc")));
    println!("parse_and_validate(None) => {:?}", parse_and_validate(None));

    // 示例 2: 多模式组合
    println!("\n--- 示例 2: 多模式组合 ---");
    println!("combine_options(Some(1), Some(5), Ok(10)) => {:?}", combine_options(Some(1), Some(5), Ok(10)));
    println!("combine_options(Some(5), Some(1), Ok(10)) => {:?}", combine_options(Some(5), Some(1), Ok(10)));

    // 示例 3: 配置解析
    println!("\n--- 示例 3: 配置解析 ---");
    let config = ServerConfig::from_args(Some("localhost"), Some("8080"), Some("5000"));
    println!("有效配置 => {:?}", config);
    let bad_config = ServerConfig::from_args(Some(""), Some("80"), Some("50"));
    println!("无效配置 => {:?}", bad_config);

    // 示例 4: 数据分类
    println!("\n--- 示例 4: 数据分类 ---");
    println!("classify_value(Ok(Some(\"24\"))) => {}", classify_value(Ok(Some("24"))));
    println!("classify_value(Ok(Some(\"25\"))) => {}", classify_value(Ok(Some("25"))));
    println!("classify_value(Ok(Some(\"-3\"))) => {}", classify_value(Ok(Some("-3"))));

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 let chains 特性信息
pub fn get_let_chains_info() -> String {
    "Rust 2024 Edition let chains 特性:\n\
        - 在 if/while 条件中链式组合 let 绑定与布尔表达式\n\
        - 语法: if let Some(x) = opt && x > 0 && let Ok(y) = parse(x)\n\
        - 消除嵌套 if let，代码更扁平\n\
        - 支持 match arm guards"
        .to_string()
}

// ==================== 测试 ====================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_and_validate() {
        assert_eq!(parse_and_validate(Some("42")), Ok(42));
        assert_eq!(parse_and_validate(Some("1000")), Ok(1000));
        assert_eq!(parse_and_validate(Some("0")), Err("输入必须是 1 到 1000 之间的正整数"));
        assert_eq!(parse_and_validate(Some("-5")), Err("输入必须是 1 到 1000 之间的正整数"));
        assert_eq!(parse_and_validate(Some("1001")), Err("输入必须是 1 到 1000 之间的正整数"));
        assert_eq!(parse_and_validate(Some("abc")), Err("输入必须是 1 到 1000 之间的正整数"));
        assert_eq!(parse_and_validate(None), Err("输入必须是 1 到 1000 之间的正整数"));
    }

    #[test]
    fn test_sum_positive_entries() {
        // 全是正数，累加所有
        let mut iter1 = vec![Some("10"), Some("20"), Some("30")].into_iter();
        assert_eq!(sum_positive_entries(&mut iter1), 60);

        // 遇到负数停止，不会跳过继续（这是 while let chains 的语义）
        let mut iter2 = vec![Some("10"), Some("-5"), Some("20")].into_iter();
        assert_eq!(sum_positive_entries(&mut iter2), 10);

        // 遇到解析失败停止
        let mut iter3 = vec![Some("10"), Some("abc"), Some("20")].into_iter();
        assert_eq!(sum_positive_entries(&mut iter3), 10);

        // 遇到 None 停止
        let mut iter4 = vec![Some("10"), None, Some("20")].into_iter();
        assert_eq!(sum_positive_entries(&mut iter4), 10);
    }

    #[test]
    fn test_combine_options() {
        assert_eq!(combine_options(Some(1), Some(5), Ok(10)), Some(16));
        assert_eq!(combine_options(Some(5), Some(1), Ok(10)), None); // x < y 不满足
        assert_eq!(combine_options(Some(1), Some(5), Ok(5)), None); // z > x + y 不满足
        assert_eq!(combine_options(None, Some(5), Ok(10)), None);
    }

    #[test]
    fn test_extract_deep_value() {
        let data: Option<Result<Option<Vec<i32>>, &str>> = Some(Ok(Some(vec![5, 10, 15])));
        assert_eq!(extract_deep_value(data), Some(5));

        let data2: Option<Result<Option<Vec<i32>>, &str>> = Some(Ok(Some(vec![-5, 10])));
        assert_eq!(extract_deep_value(data2), None); // first <= 0

        let data3: Option<Result<Option<Vec<i32>>, &str>> = None;
        assert_eq!(extract_deep_value(data3), None);
    }

    #[test]
    fn test_server_config_from_args() {
        let config = ServerConfig::from_args(Some("localhost"), Some("8080"), Some("5000"));
        assert_eq!(
            config,
            Ok(ServerConfig {
                host: "localhost".to_string(),
                port: 8080,
                timeout_ms: 5000,
            })
        );

        // 空主机名
        assert!(ServerConfig::from_args(Some(""), Some("8080"), Some("5000")).is_err());
        // 特权端口
        assert!(ServerConfig::from_args(Some("host"), Some("80"), Some("5000")).is_err());
        // 超时太短
        assert!(ServerConfig::from_args(Some("host"), Some("8080"), Some("50")).is_err());
    }

    #[test]
    fn test_filter_valid_records() {
        let records = vec![
            Some("10"),
            Some("-50"),
            Some("20"),
            Some("200"),
            Some("abc"),
            None,
            Some("-10"),
        ];
        let (count, sum, avg) = filter_valid_records(&records);
        // 有效记录：10, -50, 20, -10（都在 [-100, 100] 内且能解析）
        assert_eq!(count, 4);
        assert_eq!(sum, -30);
        assert!((avg - (-7.5)).abs() < 0.001);
    }

    #[test]
    fn test_classify_value() {
        assert_eq!(classify_value(Ok(Some("24"))), "正偶数");
        assert_eq!(classify_value(Ok(Some("25"))), "正奇数");
        assert_eq!(classify_value(Ok(Some("-3"))), "负数");
        assert_eq!(classify_value(Ok(Some("xyz"))), "非数字字符串");
        assert_eq!(classify_value(Ok(None)), "空值");
        assert_eq!(classify_value(Err("fail")), "错误结果");
    }

    #[test]
    fn test_get_let_chains_info() {
        let info = get_let_chains_info();
        assert!(info.contains("let chains"));
        assert!(info.contains("2024"));
    }
}
