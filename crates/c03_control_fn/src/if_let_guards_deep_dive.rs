//! `if let` Guards 深度解析 (Rust 1.95.0)
//! `if let` Guards 深度Parse (Rust 1.95.0)
//! 涵盖语法细节、实战模式、迁移指南和性能考量。
//! 、、and performance 。
//! # 版本信息
//! # this
//! - Rust 版本: 1.95.0
//! - Rust this : 1.95.0
//! - Rust 版this: 1.95.0
//! - 稳定日期: 2026-04-16
//! - date : 2026-04-16
//! - 稳定date: 2026-04-16
//! - date: 2026-04-16
//! # 参考
//! # reference
//! - [RFC 3637: Guard Patterns](https://rust-lang.github.io/rfcs/3637-guard-patterns.html)

// ============================================================================
// 1. IfLetGuardsSyntax — 语法与核心概念
// ============================================================================

/// # `if let` Guards 语法深度解析
/// # `if let` Guards
/// # `if let` Guards 语法深度Parse
/// ## 语法形式
/// ##
///     pattern if let P = expr2 && condition => { ... }
///     //     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ if let guard
/// }
/// ```
///
/// ## 核心规则
/// ## core rule
/// 1. `if let` guard 只能出现在 `match` arm 上，不能用于 `if let` 表达式本身
/// 1. `if let` guard present `match` arm on ，cannot `if let` express this
/// 2. guard in绑定in arm 右侧**不可见**
/// 2. guard inin arm ****
/// 3. 可以与常规布尔条件通过 `&&` 组合
/// 3. can and condition `&&` combination
/// | 维度 | `if let` guards | `let` chains |
/// | 位置 | match arm level | expression level |
/// | 语法上下文 | `match` | `if` / `while` |
/// | 绑定可见性 | guard 内，arm body 外 | then 块内 |
/// | | guard inside ，arm body outside | then inside |
/// | 绑定可见性 | guard inside，arm body outside | then 块inside |
/// | 组合能力 | `&&` 连接布尔条件 | 任意 `&&` 链 |
/// | combination | `&&` condition | `&&` |
pub struct IfLetGuardsSyntax;

impl IfLetGuardsSyntax {
    /// Return `if let` guard 语法explain
    pub fn explain_syntax() -> &'static str {
        "`if let` guard 语法: `pattern if let P = expr && condition => body`\n- 只能用于 match \
         arm\n- guard 中的绑定在 body 中不可见\n- 可与布尔条件通过 && 组合"
    }

    /// 展示同一场景下两种写法的对比，突出可读性差异。
    /// scenario under to ，。
    pub fn compare_nested_match_vs_guard(input: Option<&str>) -> Result<u32, &'static str> {
        // 传统写法：嵌套 match（箭头型缩进）
        let _traditional = match input {
            Some(s) => match s.parse::<u32>() {
                Ok(n) if n > 0 && n <= 100 => Ok(n),
                Ok(_) => Err("数值超出范围"),
                Err(_) => Err("解析失败"),
            },
            None => Err("输入为空"),
        };

        // 现代写法：if let guard（单层 match）
        match input {
            Some(s)
                if let Ok(n) = s.parse::<u32>()
                    && n > 0
                    && n <= 100 =>
            {
                Ok(n)
            }
            Some(s) if let Ok(_) = s.parse::<u32>() => Err("数值超出范围"),
            Some(_) => Err("解析失败"),
            None => Err("输入为空"),
        }
    }

    pub fn demonstrate_binding_scope_limitation(opt: Option<String>) -> String {
        match opt {
            // ❌ 错误理解：以为 `s` 可以在 guard 和 body 之间共享
            // 实际上 `if let Some(inner) = ...` 中的 `inner` 只在 guard 内部可见
            Some(ref s)
                if let Some(first) = s.chars().next()
                    && first.is_ascii() =>
            {
                // 注意：这里不能直接使用 `first`，因为它来自 guard
                // 但可以使用 `s`，因为 `s` 来自 pattern 匹配
                format!("ASCII string starting with {}", s.as_str())
            }
            Some(s) => format!("非 ASCII 开头或空字符串: {}", s),
            None => "None".to_string(),
        }
    }

    /// to比 `if let` guard（arm-level）and `let` chains（expression-level）
    /// 两者看起来相似，但语法位置和语义截然不同。
    /// ，but position and 。
    pub fn contrast_with_let_chains(input: Option<&str>) -> (String, String) {
        // if let guard: 在 match arm 上
        let guard_result = match input {
            Some(s)
                if let Ok(n) = s.parse::<i32>()
                    && n > 0 =>
            {
                format!("guard: positive {}", n)
            }
            Some(_) => "guard: not a positive number".to_string(),
            None => "guard: none".to_string(),
        };

        // let chains: 在 if 表达式条件中
        let chain_result = if let Some(s) = input
            && let Ok(n) = s.parse::<i32>()
            && n > 0
        {
            // `n` 在这里可见！
            format!("chain: positive {}", n)
        } else {
            "chain: not a positive number".to_string()
        };

        (guard_result, chain_result)
    }
}

// ============================================================================
// 2. IfLetGuardsPatterns — 实战模式
// ============================================================================

/// # `if let` Guards 实战模式
pub struct IfLetGuardsPatterns;

/// 词法分析器 Token 类型
/// analyze Token type
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Identifier(String),
    Number(i64),
    StringLiteral(String),
    Keyword(&'static str),
    Symbol(char),
    Eof,
}

/// 词法分析器状态
/// analyze state
#[derive(Debug, Clone, PartialEq)]
pub enum LexerState {
    Start,
    InIdentifier,
    InNumber { acc: i64 },
    InString { buf: String },
    Error { msg: String },
}

impl IfLetGuardsPatterns {
    /// 模式 1: 解析器/词法分析器状态机
    /// 1: /analyze state machine
    /// 从当前状态和输入事件推导出下一状态，guard 负责验证转换条件。
    /// from when before state and under state ，guard conversion condition 。
    pub fn lexer_state_machine(state: LexerState, ch: Option<char>) -> LexerState {
        match (state, ch) {
            // 从 Start 状态，遇到数字字符，转入 InNumber
            (LexerState::Start, Some(c)) if let Some(digit) = c.to_digit(10) => {
                LexerState::InNumber {
                    acc: i64::from(digit),
                }
            }

            // 从 InNumber 状态，继续遇到数字，累加
            (LexerState::InNumber { acc }, Some(c))
                if let Some(digit) = c.to_digit(10)
                    && let new_acc = acc * 10 + i64::from(digit)
                    && new_acc <= i64::MAX / 10 =>
            {
                LexerState::InNumber { acc: new_acc }
            }

            // 从 Start 状态，遇到字母，开始标识符
            (LexerState::Start, Some(c)) if c.is_alphabetic() => LexerState::InIdentifier,

            // 从 InIdentifier 状态，继续字母或数字
            (LexerState::InIdentifier, Some(c)) if c.is_alphanumeric() || c == '_' => {
                LexerState::InIdentifier
            }

            // 从 Start 状态，遇到引号，进入字符串
            (LexerState::Start, Some('"')) => LexerState::InString { buf: String::new() },

            // 其他情况：回到 Start（简化版词法分析器）
            (state, _) => state,
        }
    }

    /// 模式 2: 错误处理 —— 嵌套 Result/Option 解包
    /// 2: error handling —— Result/Option
    /// 模式 2: error handling —— 嵌套 Result/Option 解包
    pub fn handle_nested_result_option<T>(result: Result<Option<T>, &'static str>) -> &'static str
    where
        T: std::fmt::Display,
    {
        match result {
            Ok(Some(value)) if value.to_string() == "0" => "成功: 值为零",
            Ok(Some(value))
                if let Ok(n) = value.to_string().parse::<i64>()
                    && n > 0
                    && n % 2 == 0 =>
            {
                "成功: 值为正偶数"
            }
            Ok(Some(_)) => "成功: 值存在但不匹配特殊条件",
            Ok(None) => "成功: 但值为空",
            Err(e) if e.contains("timeout") => "失败: 超时",
            Err(e) if e.contains("io") => "失败: IO 错误",
            Err(_) => "失败: 未知错误",
        }
    }

    /// 模式 3: 过滤集合 —— 复杂条件筛选
    /// 3: set —— complex condition
    pub fn filter_valid_entries(entries: &[Option<&str>]) -> Vec<u32> {
        entries
            .iter()
            .filter_map(|entry| match entry {
                Some(s)
                    if let Ok(n) = s.parse::<u32>()
                        && (10..=100).contains(&n)
                        && n % 2 == 0 =>
                {
                    Some(n)
                }
                _ => None,
            })
            .collect()
    }

    /// 模式 4: 枚举变体匹配 + 额外条件
    /// 4: enum volume + outside condition
    /// 在匹配枚举变体时，通过 `if let` guard 进一步解构和验证内部数据。
    /// in enum volume ， `if let` guard and inside 。
    pub fn classify_event(event: &NetworkEvent) -> &'static str {
        match event {
            NetworkEvent::ConnectSuccess { session_id }
                if session_id.len() >= 16 && session_id.chars().all(|c| c.is_ascii_hexdigit()) =>
            {
                "连接成功: 有效 session ID"
            }
            NetworkEvent::ConnectSuccess { .. } => "连接成功: 无效 session ID 格式",
            NetworkEvent::ConnectFailed { retry_count }
                if let Some(count) = retry_count
                    && *count < 3 =>
            {
                "连接失败: 可重试"
            }
            NetworkEvent::ConnectFailed { .. } => "连接失败: 已达最大重试次数",
            NetworkEvent::DataReceived(payload)
                if let Ok(text) = std::str::from_utf8(payload)
                    && text.starts_with("PING") =>
            {
                "收到数据: PING 心跳"
            }
            NetworkEvent::DataReceived(payload) if payload.is_empty() => "收到数据: 空包",
            NetworkEvent::DataReceived(_) => "收到数据: 其他",
            NetworkEvent::Disconnected => "连接断开",
        }
    }
}

/// 网络事件枚举（用于模式匹配示例）
/// network enum （example ）
#[derive(Debug, Clone, PartialEq)]
pub enum NetworkEvent {
    ConnectSuccess { session_id: String },
    ConnectFailed { retry_count: Option<u32> },
    DataReceived(Vec<u8>),
    Disconnected,
}

// ============================================================================
// 3. IfLetGuardsMigrationGuide — 迁移指南
// ============================================================================

/// # `if let` Guards 迁移指南
/// 包括适用场景、禁忌场景和性能考量。
/// scenario 、scenario and performance 。
pub struct IfLetGuardsMigrationGuide;

impl IfLetGuardsMigrationGuide {
    /// 步骤 1: 识别候选代码 —— 寻找嵌套 match 或 if-let-inside-match
    /// step 1: —— match or if-let-inside-match
    /// step 1: 识别候选代码 —— 寻找嵌套 match or if-let-inside-match
    /// 返回迁移检查清单。
    /// 。
    pub fn migration_steps() -> [&'static str; 4] {
        [
            "1. 识别 match 内部嵌套的 if let 或次级 match",
            "2. 确认内层模式匹配的绑定不需要在 arm body 中使用",
            "3. 将内层模式提取为 guard: `if let P = expr`",
            "4. 验证穷尽性检查：确保所有分支仍被覆盖",
        ]
    }

    /// 示例：逐步迁移演示
    /// example ：demonstration
    /// Example of：逐步迁移Demonstration of
    pub fn step_by_step_migration(input: Option<&str>) -> Result<i32, &'static str> {
        // 原始代码（嵌套 match）
        let _before = match input {
            Some(s) => match s.parse::<i32>() {
                Ok(n) => match n.cmp(&0) {
                    std::cmp::Ordering::Greater => Ok(n),
                    _ => Err("非正数"),
                },
                Err(_) => Err("解析失败"),
            },
            None => Err("无输入"),
        };

        // 迁移后（if let guard）
        match input {
            Some(s)
                if let Ok(n) = s.parse::<i32>()
                    && n > 0 =>
            {
                Ok(n)
            }
            Some(_) => Err("解析失败或非正数"),
            None => Err("无输入"),
        }
    }

    /// 何时**不应**使用 `if let` guard
    /// **** `if let` guard
    /// 何时**不应**Use `if let` guard
    /// 可读性始终是首要考虑因素。
    /// factor 。
    pub fn when_not_to_use() -> [&'static str; 4] {
        [
            "guard 超过 2-3 个条件时，考虑拆分为独立函数",
            "需要 guard 中的绑定在 arm body 中使用时，不能用 guard",
            "简单的 match 不需要强行使用 guard（过度设计）",
            "团队对 guard 语法不熟悉时，优先保证代码可维护性",
        ]
    }

    /// 虽然可以编译，但可读性极差，应避免。
    /// can ，but ，。
    pub fn readability_antipattern(data: Option<&str>) -> &'static str {
        // ❌ 反模式：guard 过长，逻辑难以理解
        let _bad = match data {
            Some(s)
                if let Ok(n) = s.parse::<i64>()
                    && n > 0
                    && n % 2 == 0
                    && let Ok(m) = s.parse::<f64>()
                    && m.fract() == 0.0 =>
            {
                "complex"
            }
            _ => "other",
        };

        // ✅ 推荐：提取为辅助函数
        match data {
            Some(s) if Self::is_valid_positive_even_whole(s) => "complex",
            _ => "other",
        }
    }

    fn is_valid_positive_even_whole(s: &str) -> bool {
        let Ok(n) = s.parse::<i64>() else {
            return false;
        };
        if n <= 0 || n % 2 != 0 {
            return false;
        }
        let Ok(m) = s.parse::<f64>() else {
            return false;
        };
        m.fract() == 0.0
    }

    /// `if let` guard 本身不受 `cfg` 影响，但可以在不同平台使用不同验证逻辑。
    /// `if let` guard this `cfg` impact ，but can in platform 。
    pub fn interaction_with_cfg(input: Option<&str>) -> &'static str {
        // 平台特定的验证函数
        fn platform_validator(s: &str) -> Option<i32> {
            std::cfg_select! {
                windows => s.parse::<i32>().ok().filter(|&n| n >= 0),
                unix => s.parse::<i32>().ok().filter(|&n| n > 0),
                _ => s.parse::<i32>().ok(),
            }
        }

        match input {
            Some(s)
                if let Some(n) = platform_validator(s)
                    && n < 100 =>
            {
                "有效平台值"
            }
            Some(_) => "无效平台值",
            None => "无输入",
        }
    }

    /// 编译器in编译期will guard desugar asetc.效控制stream，
    pub fn performance_notes() -> &'static str {
        "`if let` guard 是零成本抽象:\n- 编译期 desugaring 为嵌套条件分支\n- \
         不引入额外运行时开销\n- 不生成临时堆分配\n- 优化器可将 guard 内联到单一决策树"
    }
}

// ============================================================================
// 4. 辅助演示函数
// ============================================================================

/// 演示 `if let` guards 核心特性
/// demonstration `if let` guards core feature
pub fn demonstrate_if_let_guards() {
    println!("\n========================================");
    println!("   if let Guards 深度解析演示");
    println!("========================================\n");

    // 语法对比
    println!("--- 语法对比: 嵌套 match vs if let guard ---");
    println!(
        "嵌套 match (Some(\"42\")): {:?}",
        IfLetGuardsSyntax::compare_nested_match_vs_guard(Some("42"))
    );
    println!(
        "嵌套 match (Some(\"abc\")): {:?}",
        IfLetGuardsSyntax::compare_nested_match_vs_guard(Some("abc"))
    );
    println!(
        "嵌套 match (None): {:?}",
        IfLetGuardsSyntax::compare_nested_match_vs_guard(None)
    );

    // 作用域限制
    println!("\n--- 绑定作用域限制 ---");
    println!(
        "ASCII 检查 (Some(\"hello\")): {}",
        IfLetGuardsSyntax::demonstrate_binding_scope_limitation(Some("hello".to_string()))
    );
    println!(
        "ASCII 检查 (Some(\"世界\")): {}",
        IfLetGuardsSyntax::demonstrate_binding_scope_limitation(Some("世界".to_string()))
    );

    // let chains 对比
    println!("\n--- if let guard vs let chains ---");
    let (guard, chain) = IfLetGuardsSyntax::contrast_with_let_chains(Some("42"));
    println!("guard 结果: {}", guard);
    println!("chain 结果: {}", chain);

    // 状态机
    println!("\n--- 词法分析器状态机 ---");
    let s1 = IfLetGuardsPatterns::lexer_state_machine(LexerState::Start, Some('5'));
    println!("Start + '5' => {:?}", s1);
    let s2 = IfLetGuardsPatterns::lexer_state_machine(s1, Some('3'));
    println!("InNumber + '3' => {:?}", s2);

    // 嵌套 Result/Option
    println!("\n--- 嵌套 Result/Option ---");
    let r1: Result<Option<i32>, &str> = Ok(Some(24));
    println!(
        "Ok(Some(24)): {}",
        IfLetGuardsPatterns::handle_nested_result_option(r1)
    );
    let r2: Result<Option<i32>, &str> = Err("io error");
    println!(
        "Err(\"io error\"): {}",
        IfLetGuardsPatterns::handle_nested_result_option(r2)
    );

    // 集合过滤
    println!("\n--- 集合过滤 ---");
    let entries = vec![Some("12"), Some("8"), Some("50"), None, Some("101")];
    println!(
        "有效条目: {:?}",
        IfLetGuardsPatterns::filter_valid_entries(&entries)
    );

    // 事件分类
    println!("\n--- 事件分类 ---");
    let evt = NetworkEvent::DataReceived(b"PING hello".to_vec());
    println!(
        "DataReceived(PING): {}",
        IfLetGuardsPatterns::classify_event(&evt)
    );

    // 迁移指南
    println!("\n--- 迁移指南 ---");
    for step in IfLetGuardsMigrationGuide::migration_steps() {
        println!("  {}", step);
    }

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 `if let` guards 特性信息
/// `if let` guards feature
pub fn get_if_let_guards_info() -> String {
    "Rust 1.95.0 if let guards 深度解析:\n- 语法: match arm 上直接使用 if let P = expr\n- \
     绑定作用域: guard 内可见，arm body 不可见\n- 与 let chains 区别: guard = arm-level, chains = \
     expression-level\n- 性能: 零成本抽象，编译期 desugaring"
        .to_string()
}

// ============================================================================
// 5. 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ----- IfLetGuardsSyntax 测试 -----

    #[test]
    fn test_explain_syntax() {
        let info = IfLetGuardsSyntax::explain_syntax();
        assert!(info.contains("if let"));
        assert!(info.contains("match arm"));
        assert!(info.contains("绑定"));
    }

    #[test]
    fn test_compare_nested_match_vs_guard() {
        assert_eq!(
            IfLetGuardsSyntax::compare_nested_match_vs_guard(Some("42")),
            Ok(42)
        );
        assert_eq!(
            IfLetGuardsSyntax::compare_nested_match_vs_guard(Some("0")),
            Err("数值超出范围")
        );
        assert_eq!(
            IfLetGuardsSyntax::compare_nested_match_vs_guard(Some("200")),
            Err("数值超出范围")
        );
        assert_eq!(
            IfLetGuardsSyntax::compare_nested_match_vs_guard(Some("abc")),
            Err("解析失败")
        );
        assert_eq!(
            IfLetGuardsSyntax::compare_nested_match_vs_guard(None),
            Err("输入为空")
        );
    }

    #[test]
    fn test_demonstrate_binding_scope_limitation() {
        assert_eq!(
            IfLetGuardsSyntax::demonstrate_binding_scope_limitation(Some("hello".to_string())),
            "ASCII string starting with hello"
        );
        assert_eq!(
            IfLetGuardsSyntax::demonstrate_binding_scope_limitation(Some("世界".to_string())),
            "非 ASCII 开头或空字符串: 世界"
        );
        assert_eq!(
            IfLetGuardsSyntax::demonstrate_binding_scope_limitation(None),
            "None"
        );
    }

    #[test]
    fn test_contrast_with_let_chains() {
        let (guard, chain) = IfLetGuardsSyntax::contrast_with_let_chains(Some("42"));
        assert_eq!(guard, "guard: positive 42");
        assert_eq!(chain, "chain: positive 42");

        let (guard2, chain2) = IfLetGuardsSyntax::contrast_with_let_chains(Some("-5"));
        assert_eq!(guard2, "guard: not a positive number");
        assert_eq!(chain2, "chain: not a positive number");

        let (guard3, chain3) = IfLetGuardsSyntax::contrast_with_let_chains(None);
        assert_eq!(guard3, "guard: none");
        assert_eq!(chain3, "chain: not a positive number");
    }

    // ----- IfLetGuardsPatterns 测试 -----

    #[test]
    fn test_lexer_state_machine() {
        let s1 = IfLetGuardsPatterns::lexer_state_machine(LexerState::Start, Some('7'));
        assert_eq!(s1, LexerState::InNumber { acc: 7 });

        let s2 = IfLetGuardsPatterns::lexer_state_machine(s1, Some('3'));
        assert_eq!(s2, LexerState::InNumber { acc: 73 });

        let s3 = IfLetGuardsPatterns::lexer_state_machine(LexerState::Start, Some('a'));
        assert_eq!(s3, LexerState::InIdentifier);

        let s4 = IfLetGuardsPatterns::lexer_state_machine(LexerState::InIdentifier, Some('1'));
        assert_eq!(s4, LexerState::InIdentifier);
    }

    #[test]
    fn test_handle_nested_result_option() {
        let r1: Result<Option<i32>, &str> = Ok(Some(0));
        assert_eq!(
            IfLetGuardsPatterns::handle_nested_result_option(r1),
            "成功: 值为零"
        );

        let r2: Result<Option<i32>, &str> = Ok(Some(24));
        assert_eq!(
            IfLetGuardsPatterns::handle_nested_result_option(r2),
            "成功: 值为正偶数"
        );

        let r3: Result<Option<i32>, &str> = Ok(Some(25));
        assert_eq!(
            IfLetGuardsPatterns::handle_nested_result_option(r3),
            "成功: 值存在但不匹配特殊条件"
        );

        let r4: Result<Option<i32>, &str> = Ok(None);
        assert_eq!(
            IfLetGuardsPatterns::handle_nested_result_option(r4),
            "成功: 但值为空"
        );

        let r5: Result<Option<i32>, &str> = Err("timeout error");
        assert_eq!(
            IfLetGuardsPatterns::handle_nested_result_option(r5),
            "失败: 超时"
        );

        let r6: Result<Option<i32>, &str> = Err("io failure");
        assert_eq!(
            IfLetGuardsPatterns::handle_nested_result_option(r6),
            "失败: IO 错误"
        );
    }

    #[test]
    fn test_filter_valid_entries() {
        let entries = vec![
            Some("12"),
            Some("8"),
            Some("50"),
            None,
            Some("101"),
            Some("abc"),
        ];
        assert_eq!(
            IfLetGuardsPatterns::filter_valid_entries(&entries),
            vec![12, 50]
        );

        let empty: Vec<Option<&str>> = vec![];
        assert!(IfLetGuardsPatterns::filter_valid_entries(&empty).is_empty());
    }

    #[test]
    fn test_classify_event() {
        let evt1 = NetworkEvent::ConnectSuccess {
            session_id: "0123456789abcdef0123456789abcdef".to_string(),
        };
        // session_id 全是 hex 且长度 >= 16，走第一个分支
        assert_eq!(
            IfLetGuardsPatterns::classify_event(&evt1),
            "连接成功: 有效 session ID"
        );

        let evt1b = NetworkEvent::ConnectSuccess {
            session_id: "short-id".to_string(),
        };
        // session_id 长度不足 16，走第二个分支
        assert_eq!(
            IfLetGuardsPatterns::classify_event(&evt1b),
            "连接成功: 无效 session ID 格式"
        );

        let evt2 = NetworkEvent::ConnectFailed {
            retry_count: Some(1),
        };
        assert_eq!(
            IfLetGuardsPatterns::classify_event(&evt2),
            "连接失败: 可重试"
        );

        let evt3 = NetworkEvent::ConnectFailed {
            retry_count: Some(5),
        };
        assert_eq!(
            IfLetGuardsPatterns::classify_event(&evt3),
            "连接失败: 已达最大重试次数"
        );

        let evt4 = NetworkEvent::DataReceived(b"PING hello".to_vec());
        assert_eq!(
            IfLetGuardsPatterns::classify_event(&evt4),
            "收到数据: PING 心跳"
        );

        let evt5 = NetworkEvent::DataReceived(vec![]);
        assert_eq!(IfLetGuardsPatterns::classify_event(&evt5), "收到数据: 空包");

        let evt6 = NetworkEvent::Disconnected;
        assert_eq!(IfLetGuardsPatterns::classify_event(&evt6), "连接断开");
    }

    // ----- IfLetGuardsMigrationGuide 测试 -----

    #[test]
    fn test_migration_steps() {
        let steps = IfLetGuardsMigrationGuide::migration_steps();
        assert_eq!(steps.len(), 4);
        assert!(steps[0].contains("嵌套"));
        assert!(steps[1].contains("绑定"));
        assert!(steps[2].contains("guard"));
        assert!(steps[3].contains("穷尽"));
    }

    #[test]
    fn test_step_by_step_migration() {
        assert_eq!(
            IfLetGuardsMigrationGuide::step_by_step_migration(Some("42")),
            Ok(42)
        );
        assert_eq!(
            IfLetGuardsMigrationGuide::step_by_step_migration(Some("-5")),
            Err("解析失败或非正数")
        );
        assert_eq!(
            IfLetGuardsMigrationGuide::step_by_step_migration(Some("abc")),
            Err("解析失败或非正数")
        );
        assert_eq!(
            IfLetGuardsMigrationGuide::step_by_step_migration(None),
            Err("无输入")
        );
    }

    #[test]
    fn test_when_not_to_use() {
        let reasons = IfLetGuardsMigrationGuide::when_not_to_use();
        assert_eq!(reasons.len(), 4);
        assert!(reasons.iter().all(|r| !r.is_empty()));
    }

    #[test]
    fn test_readability_antipattern() {
        assert_eq!(
            IfLetGuardsMigrationGuide::readability_antipattern(Some("24")),
            "complex"
        );
        assert_eq!(
            IfLetGuardsMigrationGuide::readability_antipattern(Some("25")),
            "other"
        );
        assert_eq!(
            IfLetGuardsMigrationGuide::readability_antipattern(None),
            "other"
        );
    }

    #[test]
    fn test_interaction_with_cfg() {
        // 不同平台行为可能不同，但基本路径应始终工作
        let result = IfLetGuardsMigrationGuide::interaction_with_cfg(Some("50"));
        assert!(["有效平台值", "无效平台值"].contains(&result));

        let result2 = IfLetGuardsMigrationGuide::interaction_with_cfg(None);
        assert_eq!(result2, "无输入");
    }

    #[test]
    fn test_performance_notes() {
        let notes = IfLetGuardsMigrationGuide::performance_notes();
        assert!(notes.contains("零成本"));
        assert!(notes.contains("desugaring"));
    }

    // ----- 演示函数测试 -----

    #[test]
    fn test_get_if_let_guards_info() {
        let info = get_if_let_guards_info();
        assert!(info.contains("if let guards"));
        assert!(info.contains("1.95.0"));
        assert!(info.contains("零成本"));
    }
}
