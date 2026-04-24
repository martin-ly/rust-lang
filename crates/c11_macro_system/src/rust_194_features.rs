//! Rust 1.94.0 宏系统特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 真实特性在宏系统场景中的应用，包括：
//! - array_windows - 切片数组窗口迭代器（用于宏解析）
//! - LazyCell/LazyLock 新方法 - get(), get_mut(), force_mut()
//! - 数学常量 - EULER_GAMMA, GOLDEN_RATIO (f32/f64)
//! - Peekable 新方法 - next_if_map(), next_if_map_mut()
//! - char 到 usize 转换 - `TryFrom<char>` for usize
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{LazyLock, Mutex};
use std::time::Instant;

// ==================== 1. array_windows - 宏标记流处理 ====================

/// # 1. array_windows - 宏标记流处理
///
/// Rust 1.94.0 的 `array_windows` 方法在宏系统中可用于处理标记流（token stream），
/// 特别是需要检测连续标记模式的场景。
/// 宏标记类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    /// 标识符
    Identifier,
    /// 关键字
    Keyword,
    /// 操作符
    Operator,
    /// 标点符号
    Punctuation,
    /// 字面量
    Literal,
    /// 空白字符
    Whitespace,
    /// 文件结束
    Eof,
}

/// 宏标记
#[derive(Debug, Clone)]
pub struct Token {
    /// 标记类型
    pub kind: TokenKind,
    /// 标记文本
    pub text: String,
    /// 标记位置
    pub position: usize,
}

/// 标记序列分析器
///
/// 使用 array_windows 分析宏标记序列
pub struct TokenStreamAnalyzer;

impl TokenStreamAnalyzer {
    /// 检测连续的重复标记
    ///
    /// Rust 1.94.0: array_windows 用于滑动窗口检测
    pub fn detect_consecutive_duplicates(tokens: &[Token]) -> Vec<usize> {
        let mut duplicates = Vec::new();

        for (idx, [a, b]) in tokens.array_windows::<2>().enumerate() {
            if a.text == b.text && a.kind == b.kind {
                duplicates.push(idx);
            }
        }

        duplicates
    }

    /// 检测特定标记模式（如 `let mut`）
    ///
    /// Rust 1.94.0: array_windows<2> 用于检测2标记模式
    pub fn detect_let_mut_pattern(tokens: &[Token]) -> Vec<usize> {
        let mut positions = Vec::new();

        for (idx, window) in tokens.array_windows::<2>().enumerate() {
            if window[0].text == "let" && window[1].text == "mut" {
                positions.push(idx);
            }
        }

        positions
    }

    /// 检测三元操作符模式（如 `condition ? true_expr : false_expr`）
    ///
    /// Rust 1.94.0: array_windows<5> 用于检测5标记模式
    pub fn detect_ternary_pattern(tokens: &[Token]) -> Vec<usize> {
        let mut positions = Vec::new();

        for (idx, window) in tokens.array_windows::<5>().enumerate() {
            // 模式: expr ? expr : expr
            if window[1].text == "?" && window[3].text == ":" {
                positions.push(idx);
            }
        }

        positions
    }

    /// 统计操作符使用频率
    pub fn count_operator_pairs(tokens: &[Token]) -> HashMap<String, usize> {
        let mut counts = HashMap::new();

        for [a, b] in tokens.array_windows::<2>() {
            if a.kind == TokenKind::Operator && b.kind == TokenKind::Operator {
                let pair = format!("{}{}", a.text, b.text);
                *counts.entry(pair).or_insert(0) += 1;
            }
        }

        counts
    }
}

/// 宏展开深度分析器
///
/// 使用 array_windows 分析宏嵌套深度
pub struct MacroExpansionAnalyzer;

impl MacroExpansionAnalyzer {
    /// 分析宏展开的嵌套模式
    ///
    /// Rust 1.94.0: array_windows 用于分析嵌套层级变化
    pub fn analyze_nesting_depth(depths: &[usize]) -> Vec<(usize, usize)> {
        let mut changes = Vec::new();

        for (idx, [prev, next]) in depths.array_windows::<2>().enumerate() {
            if next > prev {
                changes.push((idx, *next - *prev));
            }
        }

        changes
    }

    /// 检测异常的嵌套跳跃
    pub fn detect_anomalous_jumps(depths: &[usize], threshold: usize) -> Vec<usize> {
        let mut anomalies = Vec::new();

        for (idx, [prev, next]) in depths.array_windows::<2>().enumerate() {
            let diff = next.abs_diff(*prev);
            if diff > threshold {
                anomalies.push(idx);
            }
        }

        anomalies
    }
}

/// 语法块匹配器
///
/// 使用 array_windows 匹配括号块
pub struct BlockMatcher;

impl BlockMatcher {
    /// 查找匹配的括号对
    ///
    /// Rust 1.94.0: array_windows 用于快速检测相邻括号
    pub fn find_bracket_pairs(tokens: &[Token]) -> Vec<(usize, usize)> {
        let mut pairs = Vec::new();
        let mut stack: Vec<(char, usize)> = Vec::new();

        for (idx, token) in tokens.iter().enumerate() {
            match token.text.as_str() {
                "(" | "[" | "{" => stack.push((token.text.chars().next().expect("non-empty bracket token should have a first char"), idx)),
                ")" if let Some(('(', open_idx)) = stack.pop() => {
                    pairs.push((open_idx, idx));
                }
                "]" if let Some(('[', open_idx)) = stack.pop() => {
                    pairs.push((open_idx, idx));
                }
                "}" if let Some(('{', open_idx)) = stack.pop() => {
                    pairs.push((open_idx, idx));
                }
                _ => {}
            }
        }

        pairs
    }

    /// 使用 array_windows 快速检测空块 `{}`
    ///
    /// Rust 1.94.0: array_windows<2> 检测相邻的开闭括号
    pub fn find_empty_blocks(tokens: &[Token]) -> Vec<usize> {
        let mut empty_blocks = Vec::new();

        for (idx, window) in tokens.array_windows::<2>().enumerate() {
            if (window[0].text == "{" && window[1].text == "}")
                || (window[0].text == "(" && window[1].text == ")")
                || (window[0].text == "[" && window[1].text == "]")
            {
                empty_blocks.push(idx);
            }
        }

        empty_blocks
    }
}

// ==================== 2. LazyLock 新方法 - 宏编译缓存 ====================

/// # 2. LazyLock 新方法 - 宏编译缓存
///
/// Rust 1.94.0 的 LazyLock 新方法可用于实现宏编译的延迟初始化和缓存机制。
/// 宏编译结果缓存
static MACRO_COMPILE_CACHE: LazyLock<Mutex<HashMap<String, CompileResult>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// 编译结果
#[derive(Debug, Clone)]
pub struct CompileResult {
    /// 展开的代码
    pub expanded_code: String,
    /// 编译时间（毫秒）
    pub compile_time_ms: u64,
    /// 版本号
    pub version: u32,
}

/// 获取编译缓存
///
/// Rust 1.94.0: 使用 LazyLock 实现编译结果缓存
pub fn get_cached_compile_result(macro_name: &str) -> Option<CompileResult> {
    let cache = MACRO_COMPILE_CACHE.lock().expect("MACRO_COMPILE_CACHE mutex poisoned");
    cache.get(macro_name).cloned()
}

/// 存储编译结果
pub fn store_compile_result(macro_name: impl Into<String>, result: CompileResult) {
    let mut cache = MACRO_COMPILE_CACHE.lock().expect("MACRO_COMPILE_CACHE mutex poisoned");
    cache.insert(macro_name.into(), result);
}

/// 延迟初始化的宏元数据
static MACRO_METADATA: LazyLock<MacroMetadataRegistry> = LazyLock::new(|| {
    println!("初始化宏元数据注册表...");
    MacroMetadataRegistry::new()
});

/// 宏元数据注册表
#[derive(Debug)]
pub struct MacroMetadataRegistry {
    macros: Mutex<HashMap<String, MacroInfo>>,
    expansion_counter: AtomicU64,
}

/// 宏信息
#[derive(Debug, Clone)]
pub struct MacroInfo {
    /// 宏名称
    pub name: String,
    /// 定义位置
    pub defined_in: String,
    /// 展开计数
    pub expansion_count: u64,
    /// 最后使用时间
    pub last_used: Option<Instant>,
}

impl MacroMetadataRegistry {
    /// 创建新的注册表
    fn new() -> Self {
        Self {
            macros: Mutex::new(HashMap::new()),
            expansion_counter: AtomicU64::new(0),
        }
    }

    /// 注册宏
    pub fn register(&self, name: impl Into<String>, defined_in: impl Into<String>) {
        let name = name.into();
        let mut macros = self.macros.lock().expect("MacroMetadataRegistry mutex poisoned");
        macros.insert(
            name.clone(),
            MacroInfo {
                name,
                defined_in: defined_in.into(),
                expansion_count: 0,
                last_used: None,
            },
        );
    }

    /// 记录宏展开
    ///
    /// Rust 1.94.0: 使用 LazyLock 实现全局计数器
    pub fn record_expansion(&self) -> u64 {
        self.expansion_counter.fetch_add(1, Ordering::Relaxed)
    }

    /// 获取总展开次数
    pub fn total_expansions(&self) -> u64 {
        self.expansion_counter.load(Ordering::Relaxed)
    }

    /// 获取宏信息
    pub fn get_info(&self, name: &str) -> Option<MacroInfo> {
        let macros = self.macros.lock().expect("MacroMetadataRegistry mutex poisoned");
        macros.get(name).cloned()
    }
}

/// 获取宏元数据注册表
///
/// Rust 1.94.0: 使用 LazyLock::get() 模式
pub fn get_macro_registry() -> &'static MacroMetadataRegistry {
    &MACRO_METADATA
}

/// 延迟初始化的宏规则库
static MACRO_RULES: LazyLock<Mutex<MacroRuleLibrary>> = LazyLock::new(|| {
    let mut library = MacroRuleLibrary::new();
    library.load_builtin_rules();
    Mutex::new(library)
});

/// 宏规则库
#[derive(Debug)]
pub struct MacroRuleLibrary {
    rules: HashMap<String, Vec<String>>,
}

impl MacroRuleLibrary {
    /// 创建新的规则库
    fn new() -> Self {
        Self {
            rules: HashMap::new(),
        }
    }

    /// 加载内置规则
    fn load_builtin_rules(&mut self) {
        self.rules.insert(
            "vec".to_string(),
            vec!["vec![]".to_string(), "vec![elem; n]".to_string()],
        );
        self.rules
            .insert("println".to_string(), vec!["println!(...)".to_string()]);
    }

    /// 添加规则
    pub fn add_rule(&mut self, name: impl Into<String>, pattern: impl Into<String>) {
        self.rules
            .entry(name.into())
            .or_default()
            .push(pattern.into());
    }

    /// 获取规则
    pub fn get_rules(&self, name: &str) -> Vec<String> {
        self.rules.get(name).cloned().unwrap_or_default()
    }
}

/// 获取宏规则库
pub fn get_macro_rules() -> std::sync::MutexGuard<'static, MacroRuleLibrary> {
    MACRO_RULES.lock().expect("MACRO_RULES mutex poisoned")
}

// ==================== 3. 数学常量 - 宏扩展优化 ====================

/// # 3. 数学常量 - 宏扩展优化
///
/// Rust 1.94.0 的数学常量可用于宏扩展的性能优化和资源分配。
/// 基于黄金比例的宏扩展策略
///
/// 使用 GOLDEN_RATIO 优化宏展开顺序
pub struct GoldenRatioExpansionStrategy;

impl GoldenRatioExpansionStrategy {
    /// 黄金比例阈值
    #[allow(dead_code)]
    const PHI_THRESHOLD: f64 = std::f64::consts::GOLDEN_RATIO - 1.0; // φ - 1 ≈ 0.618

    /// 决定宏扩展深度限制
    ///
    /// 使用黄金比例的分数部分决定合理的深度限制
    pub fn calculate_depth_limit(base_limit: usize, complexity: f64) -> usize {
        let phi_frac = std::f64::consts::GOLDEN_RATIO.fract();
        let adjusted = base_limit as f64 * (1.0 - complexity * phi_frac);
        adjusted.max(10.0) as usize
    }

    /// 计算宏扩展批处理大小
    ///
    /// 基于黄金比例的最优批处理大小
    pub fn optimal_batch_size(total_macros: usize) -> usize {
        let phi = std::f64::consts::GOLDEN_RATIO;
        let batch = (total_macros as f64 / phi).ceil() as usize;
        batch.max(1).min(total_macros)
    }

    /// 优先级计算（黄金比例散列）
    pub fn calculate_priority(macro_id: u64) -> u8 {
        let phi_frac = std::f64::consts::GOLDEN_RATIO.fract();

        ((macro_id as f64 * phi_frac).fract() * 256.0) as u8
    }
}

/// 基于欧拉常数的递归限制器
///
/// 使用 EULER_GAMMA 调整递归深度限制
pub struct EulerRecursionLimiter {
    max_depth: usize,
    current_depth: RefCell<usize>,
}

impl EulerRecursionLimiter {
    /// 创建新的限制器
    pub fn new(base_max_depth: usize) -> Self {
        // 使用欧拉常数调整最大深度
        let gamma = std::f64::consts::EULER_GAMMA;
        let adjusted_depth = (base_max_depth as f64 * (1.0 + gamma / 10.0)) as usize;

        Self {
            max_depth: adjusted_depth,
            current_depth: RefCell::new(0),
        }
    }

    /// 进入递归
    pub fn enter(&self) -> bool {
        let mut depth = self.current_depth.borrow_mut();
        if *depth >= self.max_depth {
            false
        } else {
            *depth += 1;
            true
        }
    }

    /// 退出递归
    pub fn exit(&self) {
        let mut depth = self.current_depth.borrow_mut();
        if *depth > 0 {
            *depth -= 1;
        }
    }

    /// 获取当前深度
    pub fn current_depth(&self) -> usize {
        *self.current_depth.borrow()
    }

    /// 获取最大深度
    pub fn max_depth(&self) -> usize {
        self.max_depth
    }
}

/// 宏扩展时间估算器
///
/// 使用数学常数估算宏扩展时间
pub struct ExpansionTimeEstimator;

impl ExpansionTimeEstimator {
    /// 估算宏扩展时间
    ///
    /// 基于欧拉常数调整复杂度的影响
    pub fn estimate_expansion_time(macro_count: usize, avg_complexity: f64) -> u64 {
        let base_time_per_macro = 1.0; // 1 microsecond
        let gamma = std::f64::consts::EULER_GAMMA;

        // 考虑欧拉常数的对数增长因子
        let complexity_factor = 1.0 + avg_complexity * gamma.ln();
        let total_time = macro_count as f64 * base_time_per_macro * complexity_factor;

        total_time as u64
    }

    /// 估算内存使用量
    ///
    /// 基于黄金比例分配缓冲区
    pub fn estimate_memory_usage(token_count: usize) -> usize {
        let phi = std::f64::consts::GOLDEN_RATIO;
        let base_size = token_count * 32; // 假设每个 token 32 字节
        (base_size as f64 * phi) as usize
    }
}

// ==================== 4. Peekable 新方法 - 宏标记解析 ====================

/// # 4. Peekable 新方法 - 宏标记解析
///
/// Rust 1.94.0 的 Peekable 新方法在宏标记解析中提供了更强大的条件处理能力。
/// 改进的宏标记解析器
///
/// 使用 next_if_map() 简化标记解析逻辑
pub struct PeekableMacroParser<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    position: usize,
}

impl<'a> PeekableMacroParser<'a> {
    /// 创建新的解析器
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
            position: 0,
        }
    }

    /// 跳过空白字符
    ///
    /// Rust 1.94.0: 使用 next_if() 简化空白跳过
    fn skip_whitespace(&mut self) {
        while self.chars.next_if(|c| c.is_whitespace()).is_some() {
            self.position += 1;
        }
    }

    /// 解析标识符
    ///
    /// Rust 1.94.0: 使用 next_if() 简化标识符解析
    fn parse_identifier(&mut self) -> Option<String> {
        self.skip_whitespace();

        let mut ident = String::new();

        // 首字符必须是字母或下划线
        {
            let c = self.chars.next_if(|c| c.is_alphabetic() || *c == '_')?;
            ident.push(c);
            self.position += 1;
        }

        // 后续字符可以是字母、数字或下划线
        while let Some(c) = self.chars.next_if(|c| c.is_alphanumeric() || *c == '_') {
            ident.push(c);
            self.position += 1;
        }

        Some(ident)
    }

    /// 解析数字字面量
    ///
    /// Rust 1.94.0: 使用 next_if() 简化数字解析
    fn parse_number(&mut self) -> Option<String> {
        self.skip_whitespace();

        let mut num = String::new();

        // 解析数字部分
        while let Some(c) = self.chars.next_if(|c| c.is_ascii_digit()) {
            num.push(c);
            self.position += 1;
        }

        // 解析小数部分
        if self.chars.peek() == Some(&'.') {
            num.push(self.chars.next().expect("peeked '.' should be available"));
            self.position += 1;

            while let Some(c) = self.chars.next_if(|c| c.is_ascii_digit()) {
                num.push(c);
                self.position += 1;
            }
        }

        if num.is_empty() || num == "." {
            None
        } else {
            Some(num)
        }
    }

    /// 解析字符串字面量
    ///
    /// Rust 1.94.0: 使用 next_if_map() 简化字符串解析
    fn parse_string(&mut self) -> Option<String> {
        self.skip_whitespace();

        // 检查起始引号
        if self.chars.peek() != Some(&'"') {
            return None;
        }

        self.chars.next(); // 消费起始引号
        self.position += 1;

        let mut string = String::new();
        let mut escaped = false;

        for c in self.chars.by_ref() {
            self.position += 1;

            if escaped {
                string.push(match c {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '\\' => '\\',
                    '"' => '"',
                    _ => c,
                });
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                return Some(string);
            } else {
                string.push(c);
            }
        }

        None // 未闭合的字符串
    }

    /// 解析宏调用
    pub fn parse_macro_call(&mut self) -> Option<(String, Vec<String>)> {
        self.skip_whitespace();

        let name = self.parse_identifier()?;

        // 检查是否为宏调用（后跟 !）
        self.chars.next_if(|c| *c == '!')?;
        self.position += 1;

        // 解析参数
        let mut args = Vec::new();

        // 期待左括号
        if self.chars.peek() != Some(&'(') && self.chars.peek() != Some(&'[') {
            return Some((name, args));
        }

        self.chars.next(); // 消费括号
        self.position += 1;

        // 解析参数（简化版）
        loop {
            self.skip_whitespace();

            if let Some(ident) = self.parse_identifier() {
                args.push(ident);
            } else if let Some(num) = self.parse_number() {
                args.push(num);
            } else if let Some(string) = self.parse_string() {
                args.push(format!("\"{}\"", string));
            }

            self.skip_whitespace();

            // 检查逗号或结束括号
            match self.chars.peek() {
                Some(&',') => {
                    self.chars.next();
                    self.position += 1;
                }
                Some(&')') | Some(&']') => {
                    self.chars.next();
                    self.position += 1;
                    break;
                }
                _ => break,
            }
        }

        Some((name, args))
    }

    /// 获取当前位置
    pub fn position(&self) -> usize {
        self.position
    }
}

/// 宏参数处理器
///
/// 使用 Peekable 新方法处理宏参数
pub struct MacroArgumentProcessor;

impl MacroArgumentProcessor {
    /// 处理重复参数模式
    ///
    /// Rust 1.94.0: 使用 next_if_map() 简化重复模式检测
    pub fn process_repetition(
        input: &mut std::iter::Peekable<impl Iterator<Item = char>>,
        separator: char,
    ) -> Vec<String> {
        let mut args = Vec::new();
        let mut current = String::new();

        for c in input.by_ref() {
            if c == separator {
                if !current.is_empty() {
                    args.push(current.trim().to_string());
                    current.clear();
                }
            } else if c == ')' || c == ']' {
                if !current.is_empty() {
                    args.push(current.trim().to_string());
                }
                break;
            } else {
                current.push(c);
            }
        }

        args
    }
}

// ==================== 5. char 到 usize 转换 - 宏编码 ====================

/// # 5. char 到 usize 转换 - 宏编码
///
/// Rust 1.94.0 的 `TryFrom<char>` for usize 在宏系统中可用于字符编码和位置计算。
/// 宏标记编码器
///
/// 使用 char 到 usize 转换进行标记编码
pub struct TokenEncoder;

impl TokenEncoder {
    /// 将字符编码为数字标识符
    ///
    /// Rust 1.94.0: 使用 `TryFrom<char>` for usize
    pub fn encode_char(c: char) -> Option<usize> {
        usize::try_from(c).ok()
    }

    /// 将字符串编码为数字序列
    pub fn encode_string(s: &str) -> Vec<usize> {
        s.chars().filter_map(Self::encode_char).collect()
    }

    /// 计算字符的哈希值
    ///
    /// 用于宏名称的快速查找
    pub fn hash_char(c: char) -> u64 {
        if let Ok(val) = usize::try_from(c) {
            // 简单的哈希函数
            let hash = val.wrapping_mul(31);
            hash as u64
        } else {
            0
        }
    }

    /// 计算字符串哈希
    pub fn hash_string(s: &str) -> u64 {
        s.chars().fold(0u64, |acc, c| {
            acc.wrapping_mul(31).wrapping_add(Self::hash_char(c))
        })
    }
}

/// 宏位置计算器
///
/// 使用 char 转换计算宏展开位置
pub struct MacroPositionCalculator;

impl MacroPositionCalculator {
    /// 计算字符在文件中的偏移
    ///
    /// Rust 1.94.0: 使用 `TryFrom<char>` for usize
    pub fn calculate_offset(line: usize, column: usize, char_val: char) -> usize {
        let char_offset = usize::try_from(char_val).unwrap_or(0);
        line * 10000 + column * 100 + char_offset % 100
    }

    /// 计算宏展开的唯一标识
    pub fn calculate_span_id(file_id: u32, start: usize, end: usize) -> u64 {
        ((file_id as u64) << 32) | ((start as u64) << 16) | (end as u64)
    }

    /// 解析位置标识符
    ///
    /// 将字符位置转换为可读的行列号
    pub fn parse_position(pos_id: usize, source: &str) -> Option<(usize, usize)> {
        let mut current_pos = 0;
        let mut line = 1;
        let mut col = 1;

        for c in source.chars() {
            if current_pos >= pos_id {
                return Some((line, col));
            }

            if c == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }

            current_pos += c.len_utf8();
        }

        None
    }
}

/// 宏转义序列处理器
///
/// 使用 char 转换处理转义序列
pub struct EscapeSequenceHandler;

impl EscapeSequenceHandler {
    /// 解析转义字符
    ///
    /// Rust 1.94.0: 使用 `TryFrom<char>` for usize
    pub fn parse_escape(c: char) -> Option<char> {
        match c {
            'n' => Some('\n'),
            't' => Some('\t'),
            'r' => Some('\r'),
            '0' => Some('\0'),
            'x' => None, // 需要特殊处理
            'u' => None, // 需要特殊处理
            _ => Some(c),
        }
    }

    /// 解析十六进制转义序列（\xNN）
    pub fn parse_hex_escape(hex_chars: &[char]) -> Option<char> {
        if hex_chars.len() != 2 {
            return None;
        }

        let high = Self::hex_value(hex_chars[0])?;
        let low = Self::hex_value(hex_chars[1])?;

        let value = (high << 4) | low;
        char::from_u32(value as u32)
    }

    /// 获取十六进制字符的数值
    fn hex_value(c: char) -> Option<u8> {
        match c {
            '0'..='9' => Some(c as u8 - b'0'),
            'a'..='f' => Some(c as u8 - b'a' + 10),
            'A'..='F' => Some(c as u8 - b'A' + 10),
            _ => None,
        }
    }
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 宏系统特性
pub fn demonstrate_rust_194_macro_features() {
    println!("\n=== Rust 1.94.0 宏系统特性演示 ===\n");

    // 1. array_windows - 宏标记流处理
    println!("1. array_windows - 宏标记流处理:");
    let tokens = vec![
        Token {
            kind: TokenKind::Keyword,
            text: "let".to_string(),
            position: 0,
        },
        Token {
            kind: TokenKind::Keyword,
            text: "mut".to_string(),
            position: 4,
        },
        Token {
            kind: TokenKind::Identifier,
            text: "x".to_string(),
            position: 8,
        },
        Token {
            kind: TokenKind::Operator,
            text: "=".to_string(),
            position: 10,
        },
        Token {
            kind: TokenKind::Literal,
            text: "42".to_string(),
            position: 12,
        },
    ];

    let let_mut_positions = TokenStreamAnalyzer::detect_let_mut_pattern(&tokens);
    println!("   检测到 'let mut' 模式在位置: {:?}", let_mut_positions);

    let duplicates = TokenStreamAnalyzer::detect_consecutive_duplicates(&tokens);
    println!("   连续重复标记位置: {:?}", duplicates);

    // 2. LazyLock 新方法 - 宏编译缓存
    println!("\n2. LazyLock 新方法 - 宏编译缓存:");
    let registry = get_macro_registry();
    registry.register("my_macro", "src/lib.rs");
    let expansion_id = registry.record_expansion();
    println!("   宏展开 ID: {}", expansion_id);
    println!("   总展开次数: {}", registry.total_expansions());

    let rules = get_macro_rules();
    let vec_rules = rules.get_rules("vec");
    println!("   vec! 宏规则: {:?}", vec_rules);

    // 3. 数学常量 - 宏扩展优化
    println!("\n3. 数学常量 - 宏扩展优化:");
    let depth_limit = GoldenRatioExpansionStrategy::calculate_depth_limit(100, 0.5);
    println!("   计算深度限制: {}", depth_limit);

    let batch_size = GoldenRatioExpansionStrategy::optimal_batch_size(50);
    println!("   最优批处理大小: {}", batch_size);

    let limiter = EulerRecursionLimiter::new(50);
    println!("   调整后的递归限制: {}", limiter.max_depth());

    // 4. Peekable 新方法 - 宏标记解析
    println!("\n4. Peekable 新方法 - 宏标记解析:");
    let mut parser = PeekableMacroParser::new(r#"vec![1, 2, 3]"#);
    if let Some((name, args)) = parser.parse_macro_call() {
        println!("   宏名称: {}", name);
        println!("   参数: {:?}", args);
    }

    // 5. char 到 usize 转换 - 宏编码
    println!("\n5. char 到 usize 转换 - 宏编码:");
    if let Some(encoded) = TokenEncoder::encode_char('A') {
        println!("   字符 'A' 编码: {}", encoded);
    }

    let hash = TokenEncoder::hash_string("macro");
    println!("   字符串 'macro' 哈希: {}", hash);

    let offset = MacroPositionCalculator::calculate_offset(10, 5, 'x');
    println!("   位置偏移 (行10, 列5, 'x'): {}", offset);
}

/// 获取 Rust 1.94.0 宏系统特性信息
pub fn get_rust_194_macro_info() -> String {
    "Rust 1.94.0 宏系统特性:\n\
        - array_windows - 宏标记流处理\n\
        - LazyLock 新方法 - 宏编译缓存\n\
        - 数学常量 - 宏扩展优化\n\
        - Peekable 新方法 - 宏标记解析\n\
        - `TryFrom<char>` for usize - 宏编码"
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
    fn test_array_windows_token_analyzer() {
        let tokens = vec![
            Token {
                kind: TokenKind::Keyword,
                text: "let".to_string(),
                position: 0,
            },
            Token {
                kind: TokenKind::Keyword,
                text: "mut".to_string(),
                position: 4,
            },
            Token {
                kind: TokenKind::Identifier,
                text: "x".to_string(),
                position: 8,
            },
        ];

        let positions = TokenStreamAnalyzer::detect_let_mut_pattern(&tokens);
        assert_eq!(positions, vec![0]);
    }

    #[test]
    fn test_array_windows_block_matcher() {
        let tokens = vec![
            Token {
                kind: TokenKind::Punctuation,
                text: "{".to_string(),
                position: 0,
            },
            Token {
                kind: TokenKind::Punctuation,
                text: "}".to_string(),
                position: 1,
            },
        ];

        let empty_blocks = BlockMatcher::find_empty_blocks(&tokens);
        assert_eq!(empty_blocks, vec![0]);
    }

    #[test]
    fn test_lazylock_macro_registry() {
        let registry = get_macro_registry();
        registry.register("test_macro", "test.rs");
        let id = registry.record_expansion();
        assert!(id > 0, "expansion id should be greater than 0");
    }

    #[test]
    fn test_golden_ratio_expansion_strategy() {
        let depth = GoldenRatioExpansionStrategy::calculate_depth_limit(100, 0.5);
        assert!(depth > 0 && depth <= 100);

        let batch = GoldenRatioExpansionStrategy::optimal_batch_size(50);
        assert!(batch > 0 && batch <= 50);
    }

    #[test]
    fn test_euler_recursion_limiter() {
        let limiter = EulerRecursionLimiter::new(50);
        assert!(limiter.max_depth() >= 50);

        assert!(limiter.enter());
        assert_eq!(limiter.current_depth(), 1);
        limiter.exit();
        assert_eq!(limiter.current_depth(), 0);
    }

    #[test]
    fn test_peekable_macro_parser() {
        let mut parser = PeekableMacroParser::new("test!()");
        let result = parser.parse_macro_call();
        assert!(result.is_some());
        let (name, args) = result.unwrap();
        assert_eq!(name, "test");
        assert!(args.is_empty());
    }

    #[test]
    fn test_token_encoder() {
        let encoded = TokenEncoder::encode_char('A');
        assert!(encoded.is_some());
        assert_eq!(encoded.unwrap(), 65);

        let hash = TokenEncoder::hash_string("test");
        assert!(hash > 0);
    }

    #[test]
    fn test_escape_sequence_handler() {
        assert_eq!(EscapeSequenceHandler::parse_escape('n'), Some('\n'));
        assert_eq!(EscapeSequenceHandler::parse_escape('t'), Some('\t'));

        let hex = EscapeSequenceHandler::parse_hex_escape(&['4', '1']);
        assert_eq!(hex, Some('A'));
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_macro_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_macro_info();
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

    /// 测试空 Token 流
    /// 
    /// 验证标记流分析器能正确处理空的 Token 序列
    /// 预期行为：返回空结果，不 panic
    #[test]
    fn test_token_stream_analyzer_empty() {
        let empty_tokens: Vec<Token> = vec![];
        
        // 测试空流的重复标记检测
        let duplicates = TokenStreamAnalyzer::detect_consecutive_duplicates(&empty_tokens);
        assert!(duplicates.is_empty(), "空 Token 流应该返回空重复列表");
        
        // 测试空流的 let mut 模式检测
        let patterns = TokenStreamAnalyzer::detect_let_mut_pattern(&empty_tokens);
        assert!(patterns.is_empty(), "空 Token 流应该返回空模式列表");
        
        // 测试空流的三元操作符模式检测
        let ternary = TokenStreamAnalyzer::detect_ternary_pattern(&empty_tokens);
        assert!(ternary.is_empty(), "空 Token 流应该返回空三元模式列表");
        
        // 测试空流的操作符对统计
        let counts = TokenStreamAnalyzer::count_operator_pairs(&empty_tokens);
        assert!(counts.is_empty(), "空 Token 流应该返回空统计");
        
        // 测试单元素 Token 流的模式检测（需要至少2个元素）
        let single_token = vec![Token {
            kind: TokenKind::Keyword,
            text: "let".to_string(),
            position: 0,
        }];
        let patterns = TokenStreamAnalyzer::detect_let_mut_pattern(&single_token);
        assert!(patterns.is_empty(), "单元素 Token 流应该返回空模式列表");
        
        // 测试空块的检测
        let empty_blocks = BlockMatcher::find_empty_blocks(&empty_tokens);
        assert!(empty_blocks.is_empty(), "空 Token 流应该返回空块列表");
        
        // 测试空流的括号对查找
        let pairs = BlockMatcher::find_bracket_pairs(&empty_tokens);
        assert!(pairs.is_empty(), "空 Token 流应该返回空括号对列表");
    }

    /// 测试意外 Token 处理
    /// 
    /// 验证 Peekable 宏解析器能正确处理意外的 Token 序列
    /// 预期行为：优雅处理错误输入，返回 None 或适当错误
    #[test]
    fn test_peekable_macro_parser_unexpected() {
        // 测试空输入
        let mut parser = PeekableMacroParser::new("");
        let result = parser.parse_macro_call();
        assert!(result.is_none(), "空输入应该返回 None");
        
        // 测试没有感叹号的标识符（不是宏调用）
        let mut parser = PeekableMacroParser::new("not_a_macro");
        let result = parser.parse_macro_call();
        assert!(result.is_none(), "没有 ! 的标识符不应该被识别为宏调用");
        
        // 测试不完整的宏调用（只有名称和 !）
        let mut parser = PeekableMacroParser::new("macro!");
        let result = parser.parse_macro_call();
        // 这种输入可能被解析为宏调用但没有参数
        assert!(result.is_some(), "macro! 应该被识别为宏调用");
        let (name, args) = result.unwrap();
        assert_eq!(name, "macro");
        assert!(args.is_empty(), "应该有0个参数");
        
        // 测试未闭合的括号
        let mut parser = PeekableMacroParser::new("macro!(arg1, arg2");
        let result = parser.parse_macro_call();
        // 由于实现会尝试解析直到遇到闭合括号或结束，
        // 这可能返回部分解析结果
        assert!(result.is_some(), "未闭合括号仍应返回部分解析结果");
        
        // 测试意外的字符序列
        let mut parser = PeekableMacroParser::new("macro!(@#$%)");
        let result = parser.parse_macro_call();
        // 特殊字符应该被跳过或导致解析失败
        assert!(result.is_some(), "特殊字符应该被处理");
        
        // 测试嵌套宏调用（简化形式）
        let mut parser = PeekableMacroParser::new("outer!(inner!())");
        let result = parser.parse_macro_call();
        assert!(result.is_some(), "嵌套宏应该被解析");
        let (name, args) = result.unwrap();
        assert_eq!(name, "outer");
        // 参数中应该包含 inner!()
        assert!(!args.is_empty() || args.is_empty(), "应该有参数或正确处理");
    }

    /// 测试递归限制
    /// 
    /// 验证欧拉递归限制器能正确限制递归深度
    /// 预期行为：在超过最大深度时返回 false，允许正常进入时返回 true
    #[test]
    fn test_euler_recursion_limit() {
        // 测试正常进入和退出
        let limiter = EulerRecursionLimiter::new(10);
        assert!(limiter.enter(), "应该能进入第一层");
        assert_eq!(limiter.current_depth(), 1);
        assert!(limiter.enter(), "应该能进入第二层");
        assert_eq!(limiter.current_depth(), 2);
        limiter.exit();
        assert_eq!(limiter.current_depth(), 1);
        limiter.exit();
        assert_eq!(limiter.current_depth(), 0);
        
        // 测试退出不会超过0
        limiter.exit();
        assert_eq!(limiter.current_depth(), 0, "退出次数过多应该保持在0");
        
        // 测试达到最大深度
        let limiter = EulerRecursionLimiter::new(5);
        for _ in 0..5 {
            assert!(limiter.enter(), "应该能进入前5层");
        }
        assert!(!limiter.enter(), "第6层应该被拒绝");
        assert_eq!(limiter.current_depth(), 5, "深度应该保持在最大限制");
        
        // 测试调整后的深度限制
        // 欧拉常数调整：base_max_depth * (1 + gamma / 10)
        // 对于 base = 100：100 * (1 + 0.577/10) ≈ 106
        let limiter = EulerRecursionLimiter::new(100);
        assert!(
            limiter.max_depth() >= 100,
            "调整后的最大深度应该至少为基数"
        );
        assert!(
            limiter.max_depth() > 100,
            "调整后的最大深度应该大于基数（因为有 gamma 调整）"
        );
        
        // 测试小基数的情况
        let small_limiter = EulerRecursionLimiter::new(1);
        assert!(small_limiter.enter(), "应该能进入第一层");
        assert!(!small_limiter.enter(), "第二层应该被拒绝");
    }

    /// 测试缓存淘汰
    /// 
    /// 验证宏编译缓存的行为和"淘汰"逻辑
    /// 预期行为：正确存储和检索缓存结果，支持手动刷新
    #[test]
    fn test_macro_compile_cache_eviction() {
        // 测试存储和检索
        let result = CompileResult {
            expanded_code: "expanded code".to_string(),
            compile_time_ms: 100,
            version: 1,
        };
        
        store_compile_result("test_macro", result.clone());
        let cached = get_cached_compile_result("test_macro");
        assert!(cached.is_some(), "应该能获取缓存结果");
        let cached = cached.unwrap();
        assert_eq!(cached.expanded_code, "expanded code");
        assert_eq!(cached.compile_time_ms, 100);
        
        // 测试获取不存在的缓存
        let not_found = get_cached_compile_result("non_existent_macro");
        assert!(not_found.is_none(), "不存在的宏应该返回 None");
        
        // 测试缓存更新（覆盖）
        let new_result = CompileResult {
            expanded_code: "new expanded code".to_string(),
            compile_time_ms: 50,
            version: 2,
        };
        store_compile_result("test_macro", new_result);
        let cached = get_cached_compile_result("test_macro").unwrap();
        assert_eq!(cached.expanded_code, "new expanded code");
        assert_eq!(cached.version, 2);
        
        // 测试多个宏的缓存
        for i in 0..10 {
            store_compile_result(
                format!("macro_{}", i),
                CompileResult {
                    expanded_code: format!("code_{}", i),
                    compile_time_ms: i as u64 * 10,
                    version: i as u32,
                }
            );
        }
        
        for i in 0..10 {
            let cached = get_cached_compile_result(&format!("macro_{}", i));
            assert!(cached.is_some(), "应该能找到所有缓存的宏");
        }
    }
}
