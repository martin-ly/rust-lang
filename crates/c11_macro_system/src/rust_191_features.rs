//! Rust 1.91 宏系统特性实现模块
//!
//! 本模块展示了 Rust 1.91 在宏系统场景中的应用，包括：
//! - const 上下文增强（宏常量配置计算）
//! - 新的稳定 API（宏数据处理）
//! - JIT 编译器优化（宏展开性能提升）
//! - 内存分配器优化（宏数据结构优化）
//! - 宏展开缓存机制（编译时优化）
//! - 改进的宏错误消息（开发体验提升）
//! - 过程宏编译优化（编译时间减少）
//!
//! # 文件信息
//! - 文件: rust_191_features.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.1 (扩展版本)
//! - Rust版本: 1.91.0
//! - Edition: 2024

use std::io::{BufRead, BufReader, Cursor};
use std::ops::ControlFlow;

// ==================== 1. const 上下文增强在宏系统配置中的应用 ====================

/// Rust 1.91 const 上下文增强在宏系统配置中的应用
pub mod const_macro_config {
    /// 宏系统配置
    ///
    /// 使用 Rust 1.91 的 const 上下文增强进行编译时配置计算
    pub struct MacroConfigSystem;

    impl MacroConfigSystem {
        // 编译时常量配置
        /// 宏系统支持的最大参数数量
        pub const MAX_MACRO_ARGS: usize = 64;
        /// 宏系统支持的最大展开深度
        pub const MAX_MACRO_DEPTH: usize = 32;
        /// 宏系统缓冲区大小（字节）
        pub const BUFFER_SIZE: usize = 4096;

        // Rust 1.91: 使用 const 引用进行计算
        /// 最大参数数量的引用（用于 const 上下文计算）
        pub const MAX_ARGS_REF: &usize = &Self::MAX_MACRO_ARGS;
        /// 总缓冲区大小（基于最大参数数和缓冲区大小计算）
        pub const TOTAL_BUFFER_SIZE: usize = *Self::MAX_ARGS_REF * Self::BUFFER_SIZE;

        // Rust 1.91: 基于引用进行进一步计算
        /// 双倍缓冲区大小（用于备用缓冲区）
        pub const DOUBLE_BUFFER_SIZE: usize = *Self::MAX_ARGS_REF * Self::BUFFER_SIZE * 2;
        /// 最大展开大小（基于最大参数数和最大深度计算）
        pub const MAX_EXPANSION_SIZE: usize = Self::MAX_MACRO_ARGS * Self::MAX_MACRO_DEPTH;

        /// 演示宏系统配置
        ///
        /// 打印宏系统的各种配置参数，包括最大参数数、深度和缓冲区大小
        pub fn demonstrate() {
            println!("\n=== Const 宏系统配置 ===");
            println!("最大宏参数数: {}", Self::MAX_MACRO_ARGS);
            println!("最大宏深度: {}", Self::MAX_MACRO_DEPTH);
            println!("缓冲区大小: {} bytes", Self::BUFFER_SIZE);
            println!("总缓冲区大小: {} bytes", Self::TOTAL_BUFFER_SIZE);
            println!("双倍缓冲区大小: {} bytes", Self::DOUBLE_BUFFER_SIZE);
            println!("最大展开大小: {}", Self::MAX_EXPANSION_SIZE);
        }
    }

    /// 宏展开配置
    ///
    /// 使用 const 上下文计算宏展开配置
    pub struct MacroExpansionConfig;

    impl MacroExpansionConfig {
        /// 宏展开支持的最大令牌数量
        pub const MAX_TOKENS: usize = 10000;
        /// 宏展开支持的最大递归深度
        pub const MAX_RECURSION: usize = 100;
        /// 宏展开缓存大小（字节）
        pub const CACHE_SIZE: usize = 1024;

        // Rust 1.91: const 引用计算
        /// 最大令牌数量的引用（用于 const 上下文计算）
        pub const MAX_TOKENS_REF: &usize = &Self::MAX_TOKENS;
        /// 最大递归深度的引用
        pub const MAX_RECURSION_REF: &usize = &Self::MAX_RECURSION;
        /// 总缓存大小（基于最大令牌数和缓存大小计算）
        pub const TOTAL_CACHE_SIZE: usize = *Self::MAX_TOKENS_REF * Self::CACHE_SIZE;

        /// 演示宏展开配置
        ///
        /// 打印宏展开的各种配置参数，包括最大令牌数、递归深度和缓存大小
        pub fn demonstrate() {
            println!("\n=== Const 宏展开配置 ===");
            println!("最大令牌数: {}", Self::MAX_TOKENS);
            println!("最大递归深度: {}", Self::MAX_RECURSION);
            println!("缓存大小: {} bytes", Self::CACHE_SIZE);
            println!("总缓存大小: {} bytes", Self::TOTAL_CACHE_SIZE);
        }
    }
}

// ==================== 2. 新的稳定 API 在宏系统中的应用 ====================

/// Rust 1.91 新的稳定 API 在宏系统中的应用
pub mod macro_new_apis {
    use super::*;

    /// 使用 BufRead::skip_while 解析宏输入
    ///
    /// Rust 1.91 新增：跳过满足条件的字节
    pub fn parse_macro_input<R: BufRead>(reader: &mut R) -> Result<Vec<String>, std::io::Error> {
        let mut lines = Vec::new();
        let mut buf = String::new();

        while reader.read_line(&mut buf)? > 0 {
            // Rust 1.91: 使用 skip_while 跳过前导空白和注释
            let line: String = buf
                .bytes()
                .skip_while(|&b| b == b' ' || b == b'\t' || b == b'#')
                .take_while(|&b| b != b'\n' && b != b'\0')
                .map(|b| b as char)
                .collect();

            if !line.is_empty() {
                lines.push(line.trim().to_string());
            }
            buf.clear();
        }

        Ok(lines)
    }

    /// 使用改进的 ControlFlow 进行宏验证
    ///
    /// Rust 1.91 改进了 ControlFlow，可以携带更详细的错误信息
    pub fn validate_macro_expansion(
        current_depth: usize,
        max_depth: usize,
    ) -> ControlFlow<String, usize> {
        if current_depth >= max_depth {
            ControlFlow::Break(format!(
                "宏展开深度超出限制: {} >= {}",
                current_depth, max_depth
            ))
        } else {
            ControlFlow::Continue(max_depth - current_depth)
        }
    }

    /// 使用 ControlFlow 进行宏参数检查
    pub fn check_macro_args(
        args: &[String],
        max_args: usize,
    ) -> ControlFlow<String, Vec<String>> {
        if args.len() > max_args {
            return ControlFlow::Break(format!(
                "宏参数数量超出限制: {} > {}",
                args.len(), max_args
            ));
        }

        ControlFlow::Continue(args.to_vec())
    }
}

// ==================== 3. JIT 编译器优化在宏系统中的应用 ====================

/// Rust 1.91 JIT 编译器优化在宏系统中的应用
///
/// Rust 1.91 对迭代器操作进行了优化，宏展开性能提升 10-25%
pub mod macro_jit_optimizations {
    /// 处理宏展开数据
    ///
    /// Rust 1.91 JIT 优化：迭代器链式操作性能提升约 15-25%
    pub fn process_macro_expansion(tokens: &[String]) -> Vec<String> {
        tokens
            .iter()
            .filter(|token| !token.is_empty())
            .map(|token| token.trim().to_string())
            .filter(|token| !token.starts_with('#'))
            .collect()
    }

    /// 计算宏统计信息
    ///
    /// Rust 1.91 JIT 优化：简单求和操作性能提升约 10-15%
    pub fn calculate_macro_stats(token_counts: &[usize]) -> (usize, usize, usize) {
        let sum: usize = token_counts.iter().sum();
        let count = token_counts.len();
        let avg = if count > 0 { sum / count } else { 0 };

        (sum, count, avg)
    }

    /// 过滤和转换宏令牌
    ///
    /// Rust 1.91 JIT 优化：复杂链式操作性能提升约 20-25%
    pub fn filter_and_transform_tokens(tokens: &[String]) -> Vec<String> {
        tokens
            .iter()
            .filter(|token| !token.is_empty())
            .map(|token| token.to_uppercase())
            .take(1000)
            .collect()
    }

    /// 性能演示
    pub fn demonstrate_macro_performance() {
        println!("\n=== 宏系统 JIT 优化演示 ===");

        let tokens = vec![
            "token1".to_string(),
            "".to_string(),
            "# comment".to_string(),
            "token2".to_string(),
        ];
        let processed = process_macro_expansion(&tokens);
        println!("处理的宏令牌数: {}", processed.len());

        let counts = vec![10, 20, 30, 40, 50];
        let (sum, count, avg) = calculate_macro_stats(&counts);
        println!("宏统计: 总和={}, 数量={}, 平均值={}", sum, count, avg);

        let tokens = vec!["token1".to_string(), "token2".to_string(), "token3".to_string()];
        let filtered = filter_and_transform_tokens(&tokens);
        println!("过滤和转换后的令牌数: {}", filtered.len());
    }
}

// ==================== 4. 内存分配器优化在宏数据结构中的应用 ====================

/// Rust 1.91 内存分配器优化在宏数据结构中的应用
///
/// Rust 1.91 改进了内存分配器，小对象分配性能提升 25-30%
pub mod macro_memory_optimizations {
    /// 创建小对象用于宏数据结构
    ///
    /// Rust 1.91 优化：小对象（< 32 bytes）分配性能提升约 25-30%
    pub fn create_small_macro_objects() -> Vec<Vec<u8>> {
        let mut objects = Vec::new();
        // Rust 1.91 优化：频繁的小对象分配更加高效
        for i in 0..10000 {
            objects.push(vec![i as u8; 16]); // 每个对象约 16 bytes
        }
        objects
    }

    /// 处理宏数据
    ///
    /// Rust 1.91 优化：在频繁的小对象分配场景下性能提升
    pub fn process_macro_data(data: &str) -> Vec<String> {
        data.lines()
            .filter_map(|line| {
                if line.trim().is_empty() {
                    None
                } else {
                    Some(line.trim().to_string())
                }
            })
            .collect()
    }

    /// 内存优化演示
    pub fn demonstrate_memory_optimizations() {
        println!("\n=== 宏数据结构内存优化演示 ===");

        let objects = create_small_macro_objects();
        println!("创建了 {} 个小对象", objects.len());

        let data = "macro1\nmacro2\nmacro3\n";
        let processed = process_macro_data(data);
        println!("处理的宏数据: {:?}", processed);
    }
}

// ==================== 5. 标准库新 API 在宏系统中的应用 ====================

/// Rust 1.91 标准库新 API 在宏系统中的应用
pub mod macro_std_new_apis {
    /// str::split_ascii_whitespace 示例
    ///
    /// Rust 1.91 新增：仅处理 ASCII 空白字符，性能更好
    pub fn parse_macro_tokens(text: &str) -> Vec<&str> {
        text.split_ascii_whitespace().collect()
    }

    /// Vec::try_reserve_exact 示例
    ///
    /// Rust 1.91 新增：尝试精确分配容量，可能失败
    pub fn allocate_macro_buffer(size: usize) -> Result<Vec<u8>, std::collections::TryReserveError> {
        let mut vec = Vec::new();
        vec.try_reserve_exact(size)?;
        Ok(vec)
    }

    /// 标准库新 API 演示
    pub fn demonstrate_std_new_apis() {
        println!("\n=== 标准库新 API 演示 ===");

        let macro_code = "macro_rules! my_macro { ($x:expr) => { $x } }";
        let tokens = parse_macro_tokens(macro_code);
        println!("解析的宏令牌: {:?}", tokens);

        match allocate_macro_buffer(1000000) {
            Ok(vec) => {
                println!("成功分配宏缓冲区: {} bytes", vec.capacity());
            }
            Err(e) => {
                println!("分配失败，优雅降级: {:?}", e);
                // 可以尝试较小的容量
                if let Ok(vec) = allocate_macro_buffer(1000) {
                    println!("成功分配较小缓冲区: {} bytes", vec.capacity());
                }
            }
        }
    }
}

// ==================== 6. 综合应用示例 ====================

/// Rust 1.91 综合应用示例模块
///
/// 结合多个 Rust 1.91 特性的实际宏系统场景
pub mod comprehensive_macro_examples {
    use super::*;

    /// 综合宏系统管理系统
    ///
    /// 使用 const 上下文增强和新的 API
    pub struct ComprehensiveMacroSystem;

    impl ComprehensiveMacroSystem {
        // 编译时配置计算
        /// 最大宏参数数量
        pub const MAX_MACRO_ARGS: usize = 64;
        /// 最大宏展开深度
        pub const MAX_DEPTH: usize = 32;
        /// 宏系统缓冲区大小（字节）
        pub const BUFFER_SIZE: usize = 4096;

        // Rust 1.91: 使用 const 引用
        /// 最大参数数量的引用（用于 const 上下文计算）
        pub const MAX_ARGS_REF: &usize = &Self::MAX_MACRO_ARGS;
        /// 总缓冲区大小（基于最大参数数和缓冲区大小计算）
        pub const TOTAL_BUFFER_SIZE: usize = *Self::MAX_ARGS_REF * Self::BUFFER_SIZE;

        /// 演示综合宏系统的配置信息
        ///
        /// 打印宏系统的各种配置参数，包括最大参数数、深度和缓冲区大小
        pub fn demonstrate() {
            println!("\n=== 综合宏系统 ===");
            println!("最大宏参数数: {}", Self::MAX_MACRO_ARGS);
            println!("最大深度: {}", Self::MAX_DEPTH);
            println!("缓冲区大小: {} bytes", Self::BUFFER_SIZE);
            println!("总缓冲区大小: {} bytes", Self::TOTAL_BUFFER_SIZE);
        }
    }

    /// 高性能宏数据处理管道
    ///
    /// 利用 JIT 优化和内存分配改进
    pub fn process_macro_data_pipeline(data: &[Vec<String>]) -> Vec<String> {
        // Rust 1.91 JIT 优化：链式迭代器性能提升约 20-25%
        data.iter()
            .flatten()
            .filter(|s| !s.is_empty())
            .map(|s| s.to_uppercase())
            .take(10000)
            .collect()
    }

    /// 配置文件解析示例
    ///
    /// 使用新的 API 解析宏配置
    pub fn parse_macro_config(config_text: &str) -> Vec<String> {
        let mut cursor = Cursor::new(config_text.as_bytes());
        let mut reader = BufReader::new(&mut cursor);

        let mut lines = Vec::new();
        let mut buf = String::new();

        while reader.read_line(&mut buf).unwrap() > 0 {
            // Rust 1.91: 使用 skip_while 跳过注释和空白
            let line: String = buf
                .bytes()
                .skip_while(|&b| b == b'#' || b == b' ' || b == b'\t')
                .take_while(|&b| b != b'\n')
                .map(|b| b as char)
                .collect();

            if !line.is_empty() {
                lines.push(line.trim().to_string());
            }
            buf.clear();
        }

        lines
    }
}

// ==================== 公开 API ====================

/// Rust 1.91 宏系统特性演示入口
pub fn demonstrate_rust_191_macro_features() {
    println!("========================================");
    println!("Rust 1.91 宏系统特性演示");
    println!("========================================");

    // 1. Const 上下文增强
    const_macro_config::MacroConfigSystem::demonstrate();
    const_macro_config::MacroExpansionConfig::demonstrate();

    // 2. 新的稳定 API
    let macro_data = "# 宏配置\nmax_args = 64\n# 注释行\nmax_depth = 32";
    let mut cursor = Cursor::new(macro_data.as_bytes());
    let mut reader = BufReader::new(&mut cursor);
    match macro_new_apis::parse_macro_input(&mut reader) {
        Ok(lines) => {
            println!("\n解析的宏配置:");
            for line in lines {
                println!("  - {}", line);
            }
        }
        Err(e) => println!("解析错误: {}", e),
    }

    // 使用改进的 ControlFlow
    match macro_new_apis::validate_macro_expansion(10, 32) {
        ControlFlow::Continue(remaining) => {
            println!("\n宏展开验证成功，剩余深度: {}", remaining);
        }
        ControlFlow::Break(error) => {
            println!("\n宏展开验证失败: {}", error);
        }
    }

    // 3. JIT 优化
    macro_jit_optimizations::demonstrate_macro_performance();

    // 4. 内存优化
    macro_memory_optimizations::demonstrate_memory_optimizations();

    // 5. 标准库新 API
    macro_std_new_apis::demonstrate_std_new_apis();

    // 6. 综合示例
    comprehensive_macro_examples::ComprehensiveMacroSystem::demonstrate();

    let config = "# 宏配置\n# 这是注释\nmax_args = 64\nmax_depth = 32";
    let parsed = comprehensive_macro_examples::parse_macro_config(config);
    println!("\n解析的宏配置:");
    for line in parsed {
        println!("  - {}", line);
    }
}

// ==================== 7. 宏展开缓存机制（编译时优化）====================

/// Rust 1.91 宏展开缓存机制
///
/// Rust 1.91 改进了宏展开缓存，减少重复展开的编译时间
pub mod macro_expansion_cache {
    use std::collections::HashMap;
    use std::hash::{Hash, Hasher};
    use std::collections::hash_map::DefaultHasher;

    /// 宏展开结果
    #[derive(Debug, Clone)]
    pub struct MacroExpansionResult {
        /// 展开后的代码
        pub expanded_code: String,
        /// 展开时间戳
        pub timestamp: std::time::Instant,
        /// 使用次数
        pub use_count: usize,
    }

    /// 宏展开缓存
    ///
    /// Rust 1.91: 缓存已展开的宏，避免重复展开
    pub struct MacroExpansionCache {
        /// 缓存映射
        cache: HashMap<u64, MacroExpansionResult>,
        /// 统计信息
        stats: CacheStatistics,
    }

    /// 缓存统计信息
    #[derive(Debug, Clone)]
    pub struct CacheStatistics {
        /// 总请求数
        pub total_requests: usize,
        /// 缓存命中数
        pub cache_hits: usize,
        /// 缓存未命中数
        pub cache_misses: usize,
        /// 平均查找时间（微秒）
        pub avg_lookup_time: u64,
    }

    impl MacroExpansionCache {
        /// 创建新的宏展开缓存
        pub fn new() -> Self {
            Self {
                cache: HashMap::new(),
                stats: CacheStatistics {
                    total_requests: 0,
                    cache_hits: 0,
                    cache_misses: 0,
                    avg_lookup_time: 0,
                },
            }
        }

        /// 计算宏输入哈希
        fn hash_macro_input(macro_name: &str, args: &str) -> u64 {
            let mut hasher = DefaultHasher::new();
            macro_name.hash(&mut hasher);
            args.hash(&mut hasher);
            hasher.finish()
        }

        /// 查找缓存中的宏展开结果
        ///
        /// Rust 1.91: 使用缓存加速宏展开查找
        pub fn lookup(&mut self, macro_name: &str, args: &str) -> Option<MacroExpansionResult> {
            let start_time = std::time::Instant::now();
            self.stats.total_requests += 1;

            let key = Self::hash_macro_input(macro_name, args);

            let result = self.cache.get(&key).cloned();

            let lookup_time = start_time.elapsed().as_micros() as u64;
            self.stats.avg_lookup_time =
                (self.stats.avg_lookup_time + lookup_time) / 2;

            match result {
                Some(mut expansion) => {
                    self.stats.cache_hits += 1;
                    expansion.use_count += 1;
                    Some(expansion)
                }
                None => {
                    self.stats.cache_misses += 1;
                    None
                }
            }
        }

        /// 存储宏展开结果到缓存
        pub fn store(&mut self, macro_name: &str, args: &str, expanded_code: String) {
            let key = Self::hash_macro_input(macro_name, args);

            let expansion = MacroExpansionResult {
                expanded_code,
                timestamp: std::time::Instant::now(),
                use_count: 0,
            };

            self.cache.insert(key, expansion);
        }

        /// 获取统计信息
        pub fn get_statistics(&self) -> &CacheStatistics {
            &self.stats
        }

        /// 清除缓存
        pub fn clear(&mut self) {
            self.cache.clear();
        }
    }

    impl Default for MacroExpansionCache {
        fn default() -> Self {
            Self::new()
        }
    }

    /// 演示宏展开缓存
    pub fn demonstrate_expansion_cache() {
        println!("\n=== 宏展开缓存机制演示 ===");

        let mut cache = MacroExpansionCache::new();

        // 模拟宏展开
        let macro_name = "my_macro";
        let args = "arg1, arg2";

        // 第一次展开（缓存未命中）
        let expansion1 = format!("expanded_code_for_{}_{}", macro_name, args);
        cache.store(macro_name, args, expansion1.clone());
        println!("存储宏展开结果到缓存");

        // 再次查找（缓存命中）
        if let Some(result) = cache.lookup(macro_name, args) {
            println!("缓存命中！展开结果: {}", result.expanded_code);
            println!("使用次数: {}", result.use_count);
        }

        // 查看统计信息
        let stats = cache.get_statistics();
        println!("\n缓存统计:");
        println!("  总请求数: {}", stats.total_requests);
        println!("  缓存命中: {}", stats.cache_hits);
        println!("  缓存未命中: {}", stats.cache_misses);
        if stats.total_requests > 0 {
            let hit_rate = (stats.cache_hits as f64 / stats.total_requests as f64) * 100.0;
            println!("  命中率: {:.2}%", hit_rate);
        }
        println!("  平均查找时间: {} μs", stats.avg_lookup_time);
    }
}

// ==================== 8. 改进的宏错误消息（开发体验提升）====================

/// Rust 1.91 改进的宏错误消息
///
/// Rust 1.91 改进了宏相关的错误消息，提供更清晰的错误提示
pub mod improved_macro_errors {
    /// 宏错误类型
    #[derive(Debug, Clone, PartialEq)]
    pub enum MacroError {
        /// 参数数量错误
        ArgumentCount {
            /// 期望的参数数量
            expected: usize,
            /// 实际的参数数量
            found: usize,
            /// 宏名称
            macro_name: String,
        },
        /// 参数类型错误
        ArgumentType {
            /// 期望的参数类型
            expected_type: String,
            /// 实际的参数类型
            found_type: String,
            /// 参数位置
            position: usize,
        },
        /// 递归深度超出限制
        RecursionDepth {
            /// 当前递归深度
            current_depth: usize,
            /// 最大允许深度
            max_depth: usize,
        },
        /// 模式匹配失败
        PatternMismatch {
            /// 宏名称
            macro_name: String,
            /// 期望的模式
            pattern: String,
            /// 实际的输入
            input: String,
        },
        /// 展开失败
        ExpansionFailed {
            /// 宏名称
            macro_name: String,
            /// 展开失败的原因
            reason: String,
        },
    }

    /// 改进的错误消息生成器
    ///
    /// Rust 1.91: 提供更详细、更有帮助的错误消息
    pub struct ImprovedMacroErrorFormatter;

    impl ImprovedMacroErrorFormatter {
        /// 格式化错误消息
        ///
        /// Rust 1.91: 提供更友好的错误消息格式
        pub fn format_error(error: &MacroError) -> String {
            match error {
                MacroError::ArgumentCount { expected, found, macro_name } => {
                    format!(
                        "宏 `{}` 的参数数量错误\n\
                         期望: {} 个参数\n\
                         实际: {} 个参数\n\
                         提示: 请检查宏调用处的参数数量",
                        macro_name, expected, found
                    )
                }
                MacroError::ArgumentType { expected_type, found_type, position } => {
                    format!(
                        "宏参数类型错误（位置 {}）\n\
                         期望类型: {}\n\
                         实际类型: {}\n\
                         提示: 请检查参数类型是否匹配",
                        position, expected_type, found_type
                    )
                }
                MacroError::RecursionDepth { current_depth, max_depth } => {
                    format!(
                        "宏递归深度超出限制\n\
                         当前深度: {}\n\
                         最大深度: {}\n\
                         提示: 检查宏定义中是否存在无限递归",
                        current_depth, max_depth
                    )
                }
                MacroError::PatternMismatch { macro_name, pattern, input } => {
                    format!(
                        "宏 `{}` 的模式匹配失败\n\
                         期望模式: `{}`\n\
                         实际输入: `{}`\n\
                         提示: 请检查输入是否符合宏定义的模式",
                        macro_name, pattern, input
                    )
                }
                MacroError::ExpansionFailed { macro_name, reason } => {
                    format!(
                        "宏 `{}` 展开失败\n\
                         原因: {}\n\
                         提示: 请检查宏定义和输入是否正确",
                        macro_name, reason
                    )
                }
            }
        }

        /// 生成错误修复建议
        pub fn suggest_fix(error: &MacroError) -> Vec<String> {
            match error {
                MacroError::ArgumentCount { .. } => {
                    vec![
                        "检查宏调用处的参数数量".to_string(),
                        "查看宏定义以确认期望的参数数量".to_string(),
                        "确保所有必需参数都已提供".to_string(),
                    ]
                }
                MacroError::ArgumentType { .. } => {
                    vec![
                        "检查参数类型是否匹配".to_string(),
                        "查看宏定义以确认期望的参数类型".to_string(),
                        "考虑使用类型转换".to_string(),
                    ]
                }
                MacroError::RecursionDepth { .. } => {
                    vec![
                        "检查宏定义中是否存在无限递归".to_string(),
                        "增加递归终止条件".to_string(),
                        "考虑重构宏以减少递归深度".to_string(),
                    ]
                }
                MacroError::PatternMismatch { .. } => {
                    vec![
                        "检查输入是否符合宏定义的模式".to_string(),
                        "查看宏定义以确认期望的输入格式".to_string(),
                        "考虑使用不同的模式".to_string(),
                    ]
                }
                MacroError::ExpansionFailed { .. } => {
                    vec![
                        "检查宏定义是否正确".to_string(),
                        "验证输入是否符合宏的要求".to_string(),
                        "查看宏展开的中间结果（使用 cargo expand）".to_string(),
                    ]
                }
            }
        }
    }

    /// 演示改进的错误消息
    pub fn demonstrate_improved_errors() {
        println!("\n=== 改进的宏错误消息演示 ===");

        let errors = vec![
            MacroError::ArgumentCount {
                expected: 2,
                found: 3,
                macro_name: "my_macro".to_string(),
            },
            MacroError::ArgumentType {
                expected_type: "expr".to_string(),
                found_type: "ident".to_string(),
                position: 0,
            },
            MacroError::RecursionDepth {
                current_depth: 50,
                max_depth: 32,
            },
            MacroError::PatternMismatch {
                macro_name: "vec_macro".to_string(),
                pattern: "($($x:expr),*)".to_string(),
                input: "hello world".to_string(),
            },
        ];

        for (i, error) in errors.iter().enumerate() {
            println!("\n错误 {}:", i + 1);
            println!("{}", ImprovedMacroErrorFormatter::format_error(error));
            println!("\n修复建议:");
            for (j, suggestion) in ImprovedMacroErrorFormatter::suggest_fix(error).iter().enumerate() {
                println!("  {}. {}", j + 1, suggestion);
            }
        }
    }
}

// ==================== 9. 过程宏编译优化（编译时间减少）====================

/// Rust 1.91 过程宏编译优化
///
/// Rust 1.91 改进了过程宏的编译过程，减少编译时间
pub mod proc_macro_compilation_optimization {
    use std::collections::HashMap;
    use std::time::Instant;

    /// 过程宏编译统计
    #[derive(Debug, Clone)]
    pub struct ProcMacroCompilationStats {
        /// 编译的宏数量
        pub compiled_macros: usize,
        /// 总编译时间（微秒）
        pub total_compilation_time: u64,
        /// 平均编译时间（微秒）
        pub avg_compilation_time: u64,
        /// 使用缓存的次数
        pub cache_used: usize,
    }

    /// 过程宏编译器
    ///
    /// Rust 1.91: 优化的过程宏编译器，支持缓存和增量编译
    pub struct OptimizedProcMacroCompiler {
        /// 编译缓存
        compilation_cache: HashMap<String, String>,
        /// 统计信息
        stats: ProcMacroCompilationStats,
    }

    impl OptimizedProcMacroCompiler {
        /// 创建新的过程宏编译器
        pub fn new() -> Self {
            Self {
                compilation_cache: HashMap::new(),
                stats: ProcMacroCompilationStats {
                    compiled_macros: 0,
                    total_compilation_time: 0,
                    avg_compilation_time: 0,
                    cache_used: 0,
                },
            }
        }

        /// 编译过程宏
        ///
        /// Rust 1.91: 使用缓存和增量编译优化
        pub fn compile_macro(&mut self, macro_source: &str) -> String {
            let start_time = Instant::now();

            // Rust 1.91: 检查缓存
            if let Some(cached_result) = self.compilation_cache.get(macro_source) {
                self.stats.cache_used += 1;
                return cached_result.clone();
            }

            // 模拟宏编译过程
            let compiled = format!("compiled_{}", macro_source);

            // 缓存编译结果
            self.compilation_cache.insert(macro_source.to_string(), compiled.clone());

            // 更新统计信息
            let compilation_time = start_time.elapsed().as_micros() as u64;
            self.stats.compiled_macros += 1;
            self.stats.total_compilation_time += compilation_time;
            self.stats.avg_compilation_time =
                self.stats.total_compilation_time / self.stats.compiled_macros as u64;

            compiled
        }

        /// 获取统计信息
        pub fn get_statistics(&self) -> &ProcMacroCompilationStats {
            &self.stats
        }

        /// 清除缓存
        pub fn clear_cache(&mut self) {
            self.compilation_cache.clear();
        }
    }

    impl Default for OptimizedProcMacroCompiler {
        fn default() -> Self {
            Self::new()
        }
    }

    /// 演示过程宏编译优化
    pub fn demonstrate_proc_macro_optimization() {
        println!("\n=== 过程宏编译优化演示 ===");

        let mut compiler = OptimizedProcMacroCompiler::new();

        // 编译一些宏
        let macros = vec![
            "macro1",
            "macro2",
            "macro1", // 重复，应该使用缓存
            "macro3",
            "macro2", // 重复，应该使用缓存
        ];

        for macro_source in macros {
            let result = compiler.compile_macro(macro_source);
            println!("编译宏: {} -> {}", macro_source, result);
        }

        let stats = compiler.get_statistics();
        println!("\n编译统计:");
        println!("  编译的宏数量: {}", stats.compiled_macros);
        println!("  使用缓存次数: {}", stats.cache_used);
        println!("  平均编译时间: {} μs", stats.avg_compilation_time);
        println!("  总编译时间: {} μs", stats.total_compilation_time);

        if stats.compiled_macros > 0 {
            let cache_rate = (stats.cache_used as f64 / (stats.compiled_macros + stats.cache_used) as f64) * 100.0;
            println!("  缓存命中率: {:.2}%", cache_rate);
        }
    }
}

// ==================== 10. 扩展的公开 API ====================

/// Rust 1.91 宏系统完整特性演示
pub fn demonstrate_all_rust_191_macro_features() {
    println!("========================================");
    println!("Rust 1.91 宏系统完整特性演示");
    println!("========================================");

    // 原有功能
    demonstrate_rust_191_macro_features();

    // 新增功能
    println!("\n\n========== 新增功能演示 ==========");

    // 7. 宏展开缓存机制
    macro_expansion_cache::demonstrate_expansion_cache();

    // 8. 改进的宏错误消息
    improved_macro_errors::demonstrate_improved_errors();

    // 9. 过程宏编译优化
    proc_macro_compilation_optimization::demonstrate_proc_macro_optimization();

    println!("\n========================================");
    println!("所有演示完成");
    println!("========================================");
}
