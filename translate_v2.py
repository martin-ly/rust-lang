import os
import re

# Exact match dictionary for common lines
EXACT_DICT = {
    # Markdown headers
    '## 问题描述': '## Problem Description',
    '## 复杂度': '## Complexity',
    '## 复杂度分析': '## Complexity Analysis',
    '## Rust 1.91 特性应用': '## Rust 1.91 Feature Application',
    '## Rust 1.92 特性应用': '## Rust 1.92 Feature Application',
    '## 使用场景': '## Usage Scenarios',
    '## 使用示例': '## Usage Examples',
    '## 包含的经典题目': '## Classic Problems',
    '## 现在': '## Now',
    '## 之前': '## Before',
    '## 限制': '## Constraints',
    '## 核心概念': '## Core Concepts',
    '## 语法': '## Syntax',
    '## 背景': '## Background',
    '## 注意事项': '## Notes',
    '## 形式化规约': '## Formal Specification',
    '## 形式化定义': '## Formal Definition',
    '## 核心特性': '## Core Features',
    '## 异步特性': '## Async Features',
    '# 版本信息': '# Version Info',
    '# 示例': '# Examples',
    '# 文件信息': '# File Info',
    '# 返回值': '# Return Value',
    '# 参数': '# Parameters',
    '# 概述 (Overview)': '# Overview',
    '# 权威来源': '# Authoritative Sources',
    '# 概念定义': '# Concept Definitions',
    '# 参考': '# References',
    '# 综合示例: 运行所有演示': '# Comprehensive Example: Run All Demos',
    '# 执行流程': '# Execution Flow',
    '# 实现原理': '# Implementation Principle',
    '# 概述': '# Overview',
    '# 注意事项': '# Notes',
    '# 开放范围与一元操作符': '# Open Ranges and Unary Operators',
    '# 安全函数的 `#[target_feature]`': '# `#[target_feature]` on Safe Functions',
    '# Trait 中的 `use<...>` Precise Capturing': '# `use<...>` Precise Capturing in Traits',
    '# Trait 对象向上转换': '# Trait Object Upcasting',
    '# Let Chains 稳定化': '# Let Chains Stabilization',
    '# 显式推断 const 参数': '# Explicit Inferred Const Parameters',
    '# 裸函数（Naked Functions）': '# Naked Functions',
    
    # Version info lines
    '- 版本: 1.0': '- Version: 1.0',
    '- Rust 版本: 186.0': '- Rust Version: 186.0',
    '- Rust 版本: 187.0': '- Rust Version: 187.0',
    '- Rust 版本: 188.0': '- Rust Version: 188.0',
    '- Rust 版本: 189.0': '- Rust Version: 189.0',
    '- 稳定日期: 2025-04-03': '- Stable Date: 2025-04-03',
    '- 稳定日期: 2025-05-15': '- Stable Date: 2025-05-15',
    '- 稳定日期: 2025-06-26': '- Stable Date: 2025-06-26',
    '- 稳定日期: 2025-08-07': '- Stable Date: 2025-08-07',
    '- 文件: rust_194_features.rs': '- File: rust_194_features.rs',
    '- 文件: rust_191_features.rs': '- File: rust_191_features.rs',
    '- 文件: rust_192_features.rs': '- File: rust_192_features.rs',
    '- 创建日期: 2026-03-06': '- Creation Date: 2026-03-06',
    '- 创建日期: 2025-01-27': '- Creation Date: 2025-01-27',
    '- 创建日期: 2025-12-11': '- Creation Date: 2025-12-11',
    '- Rust版本: 1.94.0': '- Rust Version: 1.94.0',
    '- Rust版本: 1.91.0': '- Rust Version: 1.91.0',
    '- Rust版本: 1.92.0': '- Rust Version: 1.92.0',
    
    # Complexity lines (exact matches)
    '- 时间复杂度: O(n)': '- Time Complexity: O(n)',
    '- 空间复杂度: O(1)': '- Space Complexity: O(1)',
    '- 空间复杂度: O(n)': '- Space Complexity: O(n)',
    '- 时间复杂度: O(log n)': '- Time Complexity: O(log n)',
    '- 空间复杂度: O(h)': '- Space Complexity: O(h)',
    '- 时间复杂度: O(m * n)': '- Time Complexity: O(m * n)',
    '- 时间复杂度: O(n²)': '- Time Complexity: O(n²)',
    '- 时间复杂度: O(n log n)': '- Time Complexity: O(n log n)',
    '- 时间复杂度: O(n log k)': '- Time Complexity: O(n log k)',
    '- 空间复杂度: O(k)': '- Space Complexity: O(k)',
    '- 时间复杂度: O(n + m)': '- Time Complexity: O(n + m)',
    '- 时间复杂度: O(1)': '- Time Complexity: O(1)',
    
    # JIT optimization lines
    '- **JIT 优化**: 位运算操作性能提升': '- **JIT Optimization**: Bitwise operation performance improvement',
    '- **JIT 优化**: 递归遍历性能提升': '- **JIT Optimization**: Recursive traversal performance improvement',
    '- **JIT 优化**: 回溯递归性能提升': '- **JIT Optimization**: Backtracking recursion performance improvement',
    '- **JIT 优化**: 堆操作性能提升': '- **JIT Optimization**: Heap operation performance improvement',
    '- **JIT 优化**: 双指针遍历性能提升': '- **JIT Optimization**: Two-pointer traversal performance improvement',
    '- **JIT 优化**: 双指针遍历': '- **JIT Optimization**: Two-pointer traversal',
    '- **JIT 优化**: 二分查找性能提升': '- **JIT Optimization**: Binary search performance improvement',
    '- **JIT 优化**: DP 状态转移性能提升': '- **JIT Optimization**: DP state transition performance improvement',
    '- **JIT 优化**: 字符频率统计性能提升': '- **JIT Optimization**: Character frequency statistics performance improvement',
    '- **JIT 优化**: 滑动窗口操作性能提升': '- **JIT Optimization**: Sliding window operation performance improvement',
    '- **JIT 优化**: 迭代器操作性能提升': '- **JIT Optimization**: Iterator operation performance improvement',
    '- **JIT 优化**: DFS 遍历性能提升': '- **JIT Optimization**: DFS traversal performance improvement',
    '- **JIT 优化**: HashMap 操作性能提升': '- **JIT Optimization**: HashMap operation performance improvement',
    
    # Memory optimization lines
    '- **内存优化**: O(1) 空间复杂度': '- **Memory Optimization**: O(1) space complexity',
    '- **内存优化**: 原地操作': '- **Memory Optimization**: In-place operation',
    '- **内存优化**: O(h) 空间复杂度': '- **Memory Optimization**: O(h) space complexity',
    '- **内存优化**: 使用 Vec 存储路径': '- **Memory Optimization**: Use Vec to store paths',
    '- **内存优化**: 使用滚动数组，O(1) 空间复杂度': '- **Memory Optimization**: Use rolling array, O(1) space complexity',
    
    # Simple action lines
    '获取当前值': 'Get current value',
    '获取性能指标': 'Get performance metrics',
    '获取统计信息': 'Get statistics',
    '获取等待者数量': 'Get waiter count',
    '获取最小执行时间': 'Get minimum execution time',
    '获取最大执行时间': 'Get maximum execution time',
    '获取最佳性能的测试用例': 'Get best performance test case',
    '获取当前内存使用量（简化实现）': 'Get current memory usage (simplified implementation)',
    '获取库版本信息': 'Get library version info',
    '获取版本信息': 'Get version info',
    '获取进程信息': 'Get process info',
    '获取所有进程': 'Get all processes',
    '运行基准测试': 'Run benchmark',
    '计算欧几里得距离': 'Compute Euclidean distance',
    '设置值': 'Set value',
    '交换值': 'Swap value',
    '是否已训练': 'Whether trained',
    '任务优先级': 'Task priority',
    '综合演示函数': 'Comprehensive demo function',
    '数据验证管道': 'Data validation pipeline',
    '批量处理带错误控制': 'Batch processing with error control',
    '搜索二维数组，找到目标时提前退出': 'Search 2D array, early exit when target found',
    '尝试获取锁': 'Try to acquire lock',
    '发送消息': 'Send message',
    '接收消息': 'Receive message',
    '注册组件': 'Register component',
    '示例组件实现': 'Example component implementation',
    '配置错误': 'Configuration error',
    '命令处理器': 'Command processor',
    
    # Simple noun phrases
    '异步批处理器': 'Async batch processor',
    '重试策略': 'Retry strategy',
    '异步任务管理器': 'Async task manager',
    '任务状态': 'Task status',
    '性能指标': 'Performance metrics',
    '开始时间': 'Start time',
    '结束时间': 'End time',
    '超时时间': 'Timeout',
    '错误信息': 'Error information',
    '子步骤': 'Sub-steps',
    '上下文数据': 'Context data',
    '上下文信息': 'Context information',
    '是否启用性能监控': 'Whether performance monitoring is enabled',
    '异步到同步转换': 'Async to synchronous conversion',
    '同步到异步转换': 'Synchronous to async conversion',
    '验证等价性': 'Verify equivalence',
    '测试用例': 'Test cases',
    '证明步骤': 'Proof steps',
    '内存优化演示': 'Memory optimization demo',
    '标准库新 API 演示': 'Standard library new API demo',
    '配置文件解析示例': 'Configuration file parsing example',
    'str::split_ascii_whitespace 示例': 'str::split_ascii_whitespace example',
    'Vec::try_reserve_exact 示例': 'Vec::try_reserve_exact example',
    
    # Feature descriptions
    '- `target_feature_safe`: 安全函数上的 `#[target_feature]`': '- `target_feature_safe`: `#[target_feature]` on safe functions',
    '- `use_in_traits`: trait 中 RPIT 的 `use<...>` precise capturing': '- `use_in_traits`: `use<...>` precise capturing in trait RPIT',
    '- `let_chains`: Let Chains 在 2024 Edition 中稳定': '- `let_chains`: Let Chains stabilized in 2024 Edition',
    '- `explicit_inferred_const`: 显式推断 const 参数': '- `explicit_inferred_const`: Explicit inferred const parameters',
    '- `trait_upcasting`: Trait 对象向上转换（dyn Trait + Trait -> dyn Trait）': '- `trait_upcasting`: Trait object upcasting (dyn Trait + Trait -> dyn Trait)',
    '- 仅在 Edition 2024 中可用': '- Only available in Edition 2024',
    '- 不支持 `||`（或）与 `let` 混合（因语义复杂）': '- Does not support `||` (OR) mixed with `let` (due to complex semantics)',
    '- 抽象层解耦：在运行时根据具体类型降级到更通用的 trait 对象': '- Abstraction decoupling: downgrade to more general trait objects at runtime based on specific types',
    '- 插件系统：将特定插件接口转换为通用接口': '- Plugin system: convert specific plugin interfaces to general interfaces',
    
    # Rust version features
    'Rust 1.91 优化：异步迭代器性能提升约 15-20%': 'Rust 1.91 Optimization: Async iterator performance improved by ~15-20%',
    'Rust 1.91 优化：小对象分配性能提升 25-30%': 'Rust 1.91 Optimization: Small object allocation performance improved by 25-30%',
    'Rust 1.91 优化：在频繁的小对象分配场景下性能提升': 'Rust 1.91 Optimization: Performance improvement in frequent small object allocation scenarios',
    'Rust 1.91 优化：小对象（< 32 bytes）分配性能提升约 25-30%': 'Rust 1.91 Optimization: Small object (< 32 bytes) allocation performance improved by ~25-30%',
    'Rust 1.91 新增：跳过满足条件的字节': 'Rust 1.91 New: Skip bytes meeting conditions',
    'Rust 1.91 新增：仅处理 ASCII 空白字符，性能更好': 'Rust 1.91 New: Only process ASCII whitespace, better performance',
    'Rust 1.91 新增：尝试精确分配容量，可能失败': 'Rust 1.91 New: Try exact capacity allocation, may fail',
    'Rust 1.91 改进了内存分配器，小对象分配性能提升 25-30%': 'Rust 1.91 Improved memory allocator, small object allocation performance improved by 25-30%',
    'Rust 1.91 改进了 ControlFlow，可以携带更详细的错误信息': 'Rust 1.91 Improved ControlFlow, can carry more detailed error information',
    'Rust 1.91 JIT 优化：简单求和操作性能提升约 10-15%': 'Rust 1.91 JIT Optimization: Simple summation operation performance improved by ~10-15%',
    'Rust 1.94.0: 使用 Deref': 'Rust 1.94.0: Using Deref',
    'Rust 1.94.0 添加了 EULER_GAMMA 和 GOLDEN_RATIO 常量，': 'Rust 1.94.0 Added EULER_GAMMA and GOLDEN_RATIO constants,',
    'Rust 1.94.0 为 Peekable 添加了 next_if_map 和 next_if_map_mut 方法，': 'Rust 1.94.0 Added next_if_map and next_if_map_mut methods to Peekable,',
    
    # Process-related
    '进程生命周期管理器': 'Process lifecycle manager',
    '创建新的生命周期管理器': 'Create new lifecycle manager',
    '注册进程': 'Register process',
    '更新进程状态': 'Update process status',
    '清理已终止的进程': 'Cleanup terminated processes',
    '进程属性': 'Process attributes',
    '进程控制': 'Process control',
    '进程监控': 'Process monitor',
    '进程池': 'Process pool',
    '进程安全的原子布尔值': 'Process-safe atomic boolean',
    '创建新的原子布尔值': 'Create new atomic boolean',
    '进程安全的原子无符号整数': 'Process-safe atomic unsigned integer',
    '比较并交换': 'Compare and swap',
    '获取并设置': 'Fetch and set',
    '获取或设置': 'Fetch or set',
    '获取异或设置': 'Fetch xor set',
    '获取并添加': 'Fetch and add',
    '获取并减去': 'Fetch and subtract',
    '获取并位与': 'Fetch and bitand',
    '获取并位或': 'Fetch and bitor',
    '获取并位异或': 'Fetch and bitxor',
    '进程安全的屏障': 'Process-safe barrier',
    '屏障模块': 'Barrier module',
    
    # Algorithm-related
    '计算几何：凸包（Andrew）与旋转卡壳直径': 'Computational Geometry: Convex Hull (Andrew) and Rotating Calipers Diameter',
    '凸包：返回按逆时针顺序的顶点（包含共线最外点）': 'Convex Hull: Returns vertices in counter-clockwise order (including outermost collinear points)',
    '高级算法实现模块': 'Advanced Algorithm Implementation Module',
    '并行排序算法实现': 'Parallel Sorting Algorithm Implementation',
    '算法选择决策树': 'Algorithm Selection Decision Tree',
    '排序算法选择': 'Sorting Algorithm Selection',
    '搜索算法选择': 'Searching Algorithm Selection',
    '图算法选择': 'Graph Algorithm Selection',
    '动态规划 vs 贪心': 'Dynamic Programming vs Greedy',
    '并发与并行策略': 'Concurrency and Parallelism Strategy',
    
    # Design patterns
    '数据库系统设计模式应用': 'Database System Design Pattern Application',
    '游戏引擎设计模式应用': 'Game Engine Design Pattern Application',
    '操作系统设计模式应用': 'OS Design Pattern Application',
    '组合模式工程案例': 'Combined Pattern Engineering Cases',
    '函数式编程模式': 'Functional Programming Patterns',
    '高阶函数模式': 'Higher-order Function Pattern',
    'Web 框架设计模式': 'Web Framework Design Patterns',
    '设计模式错误处理': 'Design Pattern Error Handling',
    '设计模式通用错误类型': 'Design Pattern Common Error Type',
    '实体ID类型': 'Entity ID type',
    '组件接口': 'Component interface',
    'HTTP请求': 'HTTP request',
    '请求方法': 'Request method',
    '请求路径': 'Request path',
    '请求头': 'Request headers',
    '系统资源管理器': 'System resource manager',
    '单例模式': 'Singleton pattern',
    '工厂模式': 'Factory pattern',
    '策略模式': 'Strategy pattern',
    
    # Async
    '高级异步调试和日志系统': 'Advanced Async Debugging and Logging System',
    '异步生态系统集成模块': 'Async Ecosystem Integration Module',
    '异步生态系统全面': 'Async Ecosystem Comprehensive',
    'Actor 与 Reactor 模式深度分析': 'Actor and Reactor Patterns Deep Analysis',
    'Actor 模式理论基础': 'Actor Model Theoretical Foundations',
    'CSP 模型对比': 'CSP Model Comparison',
    'CSP 理论基础': 'CSP Theoretical Foundations',
    '异步语义理论': 'Async Semantics Theory',
    '异步递归深度分析': 'Async Recursion Deep Analysis',
    '异步运行时具体示例和组合模式': 'Async Runtime Examples and Combined Patterns',
    '异步运行时': 'Async Runtime',
    '异步集成框架层面分析': 'Async Integration Framework Analysis',
    '异步日志调试和跟踪': 'Async Logging Debugging and Tracing',
    'eBPF + Rust (Aya) 预研模块': 'eBPF + Rust (Aya) Research Module',
    'AFIDT (async fn in dyn trait) 跟踪模块（Nightly）': 'AFIDT (async fn in dyn trait) Tracking Module (Nightly)',
    'AFIDT 当前限制': 'AFIDT Current Limitations',
    'Rust 异步编程全面解析': 'Comprehensive Analysis of Rust Async Programming',
    'Rust 1.96.0 稳定特性演示模块（异步编程）': 'Rust 1.96.0 Stable Features Demo Module (Async Programming)',
    'Rust 1.96 特性跟踪模块（含历史特性复习与 1.96 前瞻）': 'Rust 1.96 Feature Tracking Module (Including Historical Review and 1.96 Preview)',
    'Rust 1.97 异步特性演示': 'Rust 1.97 Async Features Demo',
    'Rust 1.98 Nightly 异步特性前瞻': 'Rust 1.98 Nightly Async Features Preview',
    '高性能异步运行时': 'High-performance Async Runtime',
    '轻量级运行时': 'Lightweight Runtime',
    '流处理模块': 'Stream Processing Module',
    '运行时模块': 'Runtime Module',
    '运行时对比': 'Runtime Comparison',
    '运行时选择': 'Runtime Selection',
    '批处理处理器': 'Batch Processor',
    '重试引擎': 'Retry Engine',
    '任务管理器': 'Task Manager',
    '高级工具模块': 'Advanced Tools Module',
    '退避策略': 'Backoff Strategy',
    'Actix 最小可运行示例：定义消息/Actor，发送并接收响应。': 'Actix Minimum Runnable Example: Define Message/Actor, Send and Receive Response.',
    '同步封装：内部创建并运行 Actix `System`，方便示例/二进制入口直接调用': 'Synchronous Wrapper: Internally create and run Actix `System`, convenient for example/binary entry direct call',
    '库内调用异步版本': 'In-library async call version',
    '需在 Actix 系统/运行时内': 'Must be inside Actix system/runtime',
    '可直接在可执行入口调用同步封装': 'Can directly call synchronous wrapper at executable entry',
    '内部启动并关闭系统': 'Internally start and shutdown system',
    '示例参见': 'See example',
    '注意：此模块需要 futures 依赖': 'Note: This module requires futures dependency',
    
    # Misc
    'Fenwick 树（Binary Indexed Tree）：支持前缀和与点更新，O(log n)': 'Fenwick Tree (Binary Indexed Tree): Supports prefix sum and point update, O(log n)',
    '归档的历史版本特性模块': 'Archived Historical Version Features Module',
    '当前活跃版本为 Rust 1.94，请使用最新模块获取最新特性。': 'Currently active version is Rust 1.94, please use the latest module for newest features.',
    '历史版本特性实现': 'Historical Version Features Implementation',
    '仅供学习参考': 'For learning reference only',
    '⚠️ **历史版本文件** - 本文件仅作为历史参考保留': '⚠️ **Historical Version File** - This file is retained for historical reference only',
    '**当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`': '**Currently Recommended Version**: Rust 1.92.0+ | For latest features, please refer to `rust_192_features.rs`',
    '运行方式:': 'How to run:',
    '其中:': 'Where:',
    
    # Rust 2024/2025 features
    'Rust 2025 新特性在算法中的应用': 'Rust 2025 New Features in Algorithms',
    'Rust 1.92.0 算法特性实现模块': 'Rust 1.92.0 Algorithm Features Implementation Module',
    'Rust 1.94.0 算法特性实现模块': 'Rust 1.94.0 Algorithm Features Implementation Module',
    
    # Process features
    'Rust 1.96.0 特性 — 进程管理与系统编程模块': 'Rust 1.96.0 Features — Process Management and System Programming Module',
    'Rust 1.97 进程/文件系统特性演示': 'Rust 1.97 Process/Filesystem Features Demo',
    'Rust for Linux 2026 趋势': 'Rust for Linux 2026 Trends',
    
    # Design pattern features
    'Rust 1.96.0 特性 — 设计模式': 'Rust 1.96.0 Features — Design Patterns',
    'Rust 1.97 设计模式特性演示': 'Rust 1.97 Design Pattern Features Demo',
    'Rust 中的 Visitor 模式': 'Visitor Pattern in Rust',
    'Rust 核心惯用法': 'Rust Core Idioms',
    '其他 Rust 核心惯用法': 'Other Rust Core Idioms',
    
    # Module descriptions
    '本模块提供了完整的异步调试解决方案，重点解决以下问题：': 'This module provides a complete async debugging solution, focusing on the following problems:',
    '本模块展示了如何集成和组合使用不同的异步运行时和设计模式：': 'This module demonstrates how to integrate and combine different async runtimes and design patterns:',
    '本模块展示了在游戏引擎中应用各种设计模式的实践案例，': 'This module demonstrates practical cases of applying various design patterns in game engines,',
    '包括Component、Observer、State等经典模式。': 'Including classic patterns such as Component, Observer, and State.',
    '本模块包含 Rust 1.90-1.92 版本的历史特性实现，仅供参考学习使用。': 'This module contains historical feature implementations for Rust 1.90-1.92, for reference and learning only.',
    '当前活跃版本为 Rust 1.94，请使用最新模块获取最新特性。': 'Currently active version is Rust 1.94, please use the latest module for the newest features.',
    '本模块展示了 Rust 186.0 (2025-04-03) 的关键语言特性和工具链改进。': 'This module demonstrates key language features and toolchain improvements of Rust 186.0 (2025-04-03).',
    '本模块展示了 Rust 187.0 (2025-05-15) 的关键语言特性和工具链改进。': 'This module demonstrates key language features and toolchain improvements of Rust 187.0 (2025-05-15).',
    '本模块展示了 Rust 188.0 (2025-06-26) 的关键语言特性和工具链改进。': 'This module demonstrates key language features and toolchain improvements of Rust 188.0 (2025-06-26).',
    '本模块展示了 Rust 189.0 (2025-08-07) 的关键语言特性和工具链改进。': 'This module demonstrates key language features and toolchain improvements of Rust 189.0 (2025-08-07).',
    '本模块提供了Rust中的高级算法实现，包括：': 'This module provides advanced algorithm implementations in Rust, including:',
    '本库提供了Rust中各种高级算法的完整实现，完全对齐 Rust 1.95.0 版本特性，': 'This library provides complete implementations of various advanced algorithms in Rust, fully aligned with Rust 1.95.0 features,',
    '包括排序、搜索、图算法、机器学习算法、密码学算法等。': 'Including sorting, searching, graph algorithms, machine learning algorithms, cryptographic algorithms, etc.',
    '本模块展示了在数据库系统中应用各种设计模式的实践案例，': 'This module demonstrates practical cases of applying various design patterns in database systems,',
    '包括DAO、Active Record、Unit of Work等经典模式。': 'Including classic patterns such as DAO, Active Record, and Unit of Work.',
    
    # Sentence fragments
    '1. 多运行时集成策略': '1. Multi-runtime integration strategy',
    '2. 聚合组合设计模式': '2. Aggregate combination design pattern',
    '3. 异步同步转换最佳实践': '3. Async-sync conversion best practices',
    '4. 跨运行时任务调度': '4. Cross-runtime task scheduling',
    '5. 统一异步接口设计': '5. Unified async interface design',
    '1. 异步执行流的同步化跟踪': '1. Synchronous tracking of async execution flows',
    '2. 跨任务上下文传播': '2. Cross-task context propagation',
    '3. 性能瓶颈识别': '3. Performance bottleneck identification',
    '4. 分布式追踪集成': '4. Distributed tracing integration',
    '5. 实时监控和可视化': '5. Real-time monitoring and visualization',
    
    # Formal verification
    '形式化验证示例：设计模式的正确性证明': 'Formal Verification Example: Correctness Proof of Design Patterns',
    '类型级证明': 'Type-level proof',
    '不变量验证': 'Invariant verification',
    '终止性证明': 'Termination proof',
    '并发安全性证明': 'Concurrent safety proof',
    '状态转换正确性': 'State transition correctness',
    '编译时保证状态转换正确性': 'Compile-time guarantee of state transition correctness',
    
    # Miri
    'Miri 测试模块 - 算法内存安全验证': 'Miri Test Module - Algorithm Memory Safety Verification',
    'Miri 测试模块 - 设计模式内存安全验证': 'Miri Test Module - Design Pattern Memory Safety Verification',
    'Miri 测试模块 - 进程管理内存安全验证': 'Miri Test Module - Process Management Memory Safety Verification',
    
    # eBPF
    '⚠️ **警告**: 本模块内容基于 Aya 框架文档，需要 Linux 内核 5.7+ 和特定工具链。': '⚠️ **Warning**: This module content is based on Aya framework documentation, requires Linux kernel 5.7+ and specific toolchain.',
    'eBPF 程序需要 root 权限或 CAP_BPF 能力。': 'eBPF programs require root privileges or CAP_BPF capability.',
    '# 概念定义': '# Concept Definitions',
    '纯 Rust eBPF 开发框架': 'Pure Rust eBPF development framework',
    '允许用 Rust 编写内核态和用户态 eBPF 程序': 'Allows writing kernel-mode and user-mode eBPF programs in Rust',
    '无需 libbpf 或 C': 'Without libbpf or C',
    
    # Native async trait
    '原生 async fn in trait 示例（Rust 1.75.0 / Edition 2021+）': 'Native async fn in trait example (Rust 1.75.0 / Edition 2021+)',
    '教学示例：在公开 trait 中使用 async fn，抑制 lint 提示': 'Teaching example: Using async fn in public trait, suppressing lint warnings',
    '模拟异步工作：无需运行时，这里只示意': 'Simulate async work: No runtime needed, just illustrative here',
    
    # Archive
    '归档模块': 'Archive module',
    '历史特性': 'Historical features',
    '包含的经典题目': 'Included classic problems',
    
    # Cloud native
    '云原生示例': 'Cloud native example',
    '分布式共识示例': 'Distributed consensus example',
    '分布式锁示例': 'Distributed lock example',
    '事件溯源示例': 'Event sourcing example',
    '微服务模式示例': 'Microservice patterns example',
    '简单演示': 'Simple demo',
    
    # Performance
    '性能优化实践示例模块': 'Performance Optimization Practice Example Module',
    '性能基准测试结果': 'Performance benchmark results',
    '性能基准测试模块': 'Performance benchmark module',
    
    # Data structures
    '并查集（DSU/Union-Find）：按秩合并 + 路径压缩': 'Disjoint Set Union (DSU/Union-Find): Union by rank + path compression',
    '线段树': 'Segment Tree',
    '稀疏表': 'Sparse Table',
    '优先队列': 'Priority Queue',
    'LRU缓存': 'LRU Cache',
}


def translate_line(text):
    if not re.search(r'[\u4e00-\u9fff]', text):
        return text
    
    t = text.strip()
    
    # Try exact match
    if t in EXACT_DICT:
        return EXACT_DICT[t]
    
    # Pattern: 本模块提供了... -> This module provides ...
    m = re.match(r'^本模块提供了(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'This module provides ' + rest
    
    m = re.match(r'^本模块展示(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'This module demonstrates ' + rest
    
    m = re.match(r'^本模块实现(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'This module implements ' + rest
    
    m = re.match(r'^本模块包含(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'This module contains ' + rest
    
    m = re.match(r'^本库提供了(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'This library provides ' + rest
    
    m = re.match(r'^本文件(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'This file ' + rest
    
    m = re.match(r'^获取(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Get ' + rest
    
    m = re.match(r'^创建新的?(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Create new ' + rest
    
    m = re.match(r'^更新(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Update ' + rest
    
    m = re.match(r'^注册(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Register ' + rest
    
    m = re.match(r'^清理(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Cleanup ' + rest
    
    m = re.match(r'^计算(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Compute ' + rest
    
    m = re.match(r'^设置(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Set ' + rest
    
    m = re.match(r'^运行(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Run ' + rest
    
    m = re.match(r'^开始(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Start ' + rest
    
    m = re.match(r'^完成(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Complete ' + rest
    
    m = re.match(r'^搜索(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Search ' + rest
    
    m = re.match(r'^测试(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Test ' + rest
    
    m = re.match(r'^验证(.+)$', t)
    if m:
        rest = translate_fragment(m.group(1))
        return 'Verify ' + rest
    
    # Suffix patterns
    m = re.match(r'^(.+)模块$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' module'
    
    m = re.match(r'^(.+)管理器$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' manager'
    
    m = re.match(r'^(.+)接口$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' interface'
    
    m = re.match(r'^(.+)类型$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' type'
    
    m = re.match(r'^(.+)模式$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' pattern'
    
    m = re.match(r'^(.+)系统$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' system'
    
    m = re.match(r'^(.+)函数$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' function'
    
    m = re.match(r'^(.+)方法$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' method'
    
    m = re.match(r'^(.+)结构体$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' struct'
    
    m = re.match(r'^(.+)算法$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' algorithm'
    
    m = re.match(r'^(.+)实现$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' implementation'
    
    m = re.match(r'^(.+)示例$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' example'
    
    m = re.match(r'^(.+)测试$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' test'
    
    m = re.match(r'^(.+)应用$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' application'
    
    m = re.match(r'^(.+)案例$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' case'
    
    m = re.match(r'^(.+)解决方案$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' solution'
    
    m = re.match(r'^(.+)策略$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' strategy'
    
    m = re.match(r'^(.+)引擎$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' engine'
    
    m = re.match(r'^(.+)框架$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' framework'
    
    m = re.match(r'^(.+)运行时$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' runtime'
    
    m = re.match(r'^(.+)分析$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' analysis'
    
    m = re.match(r'^(.+)证明$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' proof'
    
    m = re.match(r'^(.+)验证$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' verification'
    
    m = re.match(r'^(.+)优化$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' optimization'
    
    m = re.match(r'^(.+)处理$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' processing'
    
    m = re.match(r'^(.+)设计$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' design'
    
    m = re.match(r'^(.+)排序$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' sort'
    
    m = re.match(r'^(.+)搜索$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' search'
    
    m = re.match(r'^(.+)遍历$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' traversal'
    
    m = re.match(r'^(.+)操作$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' operation'
    
    m = re.match(r'^(.+)提升$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' improvement'
    
    m = re.match(r'^(.+)性能$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' performance'
    
    m = re.match(r'^(.+)信息$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' information'
    
    m = re.match(r'^(.+)数据$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' data'
    
    m = re.match(r'^(.+)控制$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' control'
    
    m = re.match(r'^(.+)错误$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' error'
    
    m = re.match(r'^(.+)安全$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' safety'
    
    m = re.match(r'^(.+)状态$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' status'
    
    m = re.match(r'^(.+)机制$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' mechanism'
    
    m = re.match(r'^(.+)方式$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' method'
    
    m = re.match(r'^(.+)结果$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' result'
    
    m = re.match(r'^(.+)步骤$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' step'
    
    m = re.match(r'^(.+)流程$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' flow'
    
    m = re.match(r'^(.+)配置$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' configuration'
    
    m = re.match(r'^(.+)对象$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' object'
    
    m = re.match(r'^(.+)值$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' value'
    
    m = re.match(r'^(.+)数量$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' count'
    
    m = re.match(r'^(.+)时间$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' time'
    
    m = re.match(r'^(.+)内存$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' memory'
    
    m = re.match(r'^(.+)空间$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' space'
    
    m = re.match(r'^(.+)资源$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' resource'
    
    m = re.match(r'^(.+)服务$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' service'
    
    m = re.match(r'^(.+)容器$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' container'
    
    m = re.match(r'^(.+)组件$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' component'
    
    m = re.match(r'^(.+)节点$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' node'
    
    m = re.match(r'^(.+)边$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' edge'
    
    m = re.match(r'^(.+)路径$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' path'
    
    m = re.match(r'^(.+)树$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' tree'
    
    m = re.match(r'^(.+)图$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' graph'
    
    m = re.match(r'^(.+)表$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' table'
    
    m = re.match(r'^(.+)数组$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' array'
    
    m = re.match(r'^(.+)队列$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' queue'
    
    m = re.match(r'^(.+)栈$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' stack'
    
    m = re.match(r'^(.+)集合$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' set'
    
    m = re.match(r'^(.+)映射$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' map'
    
    m = re.match(r'^(.+)列表$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' list'
    
    m = re.match(r'^(.+)字符串$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' string'
    
    m = re.match(r'^(.+)指针$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' pointer'
    
    m = re.match(r'^(.+)引用$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' reference'
    
    m = re.match(r'^(.+)切片$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' slice'
    
    m = re.match(r'^(.+)迭代器$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' iterator'
    
    m = re.match(r'^(.+)生成器$', t)
    if m and len(m.group(1)) > 1:
        return translate_fragment(m.group(1)) + ' generator'
    
    # If nothing matched, try fragment translation
    result = translate_fragment(t)
    if result != t:
        return result
    
    # If still no good translation, return empty to indicate skip
    return None


FRAGMENT_DICT = {
    '异步': 'async',
    '同步': 'synchronous',
    '并行': 'parallel',
    '并发': 'concurrent',
    '分布式': 'distributed',
    '调试': 'debugging',
    '日志': 'logging',
    '跟踪': 'tracing',
    '监控': 'monitoring',
    '可视化': 'visualization',
    '集成': 'integration',
    '分析': 'analysis',
    '识别': 'identification',
    '转换': 'conversion',
    '调度': 'scheduling',
    '设计': 'design',
    '模式': 'pattern',
    '应用': 'application',
    '案例': 'cases',
    '实践': 'practice',
    '经典': 'classic',
    '高级': 'advanced',
    '完整': 'complete',
    '全面': 'comprehensive',
    '深入': 'in-depth',
    '重点': 'focus',
    '关键': 'key',
    '语言': 'language',
    '特性': 'features',
    '工具链': 'toolchain',
    '改进': 'improvements',
    '包括': 'including',
    '问题': 'problems',
    '性能': 'performance',
    '瓶颈': 'bottleneck',
    '执行': 'execution',
    '流': 'flow',
    '任务': 'task',
    '上下文': 'context',
    '传播': 'propagation',
    '实时': 'real-time',
    '解决方案': 'solution',
    '系统': 'system',
    '模块': 'module',
    '库': 'library',
    '文件': 'file',
    '函数': 'function',
    '方法': 'method',
    '结构体': 'struct',
    '枚举': 'enum',
    '类型': 'type',
    '泛型': 'generic',
    '生命周期': 'lifetime',
    '所有权': 'ownership',
    '借用': 'borrowing',
    '引用': 'reference',
    '切片': 'slice',
    '向量': 'vector',
    '字符串': 'string',
    '错误': 'error',
    '处理': 'handling',
    '安全': 'safety',
    '线程': 'thread',
    '进程': 'process',
    '运行时': 'runtime',
    '状态机': 'state machine',
    '组合子': 'combinator',
    '机制': 'mechanism',
    '背压': 'backpressure',
    '控制': 'control',
    '轻量级': 'lightweight',
    '获取': 'get',
    '创建': 'create',
    '更新': 'update',
    '注册': 'register',
    '清理': 'cleanup',
    '设置': 'set',
    '计算': 'compute',
    '运行': 'run',
    '开始': 'start',
    '完成': 'complete',
    '搜索': 'search',
    '测试': 'test',
    '验证': 'verify',
    '训练': 'train',
    '管理器': 'manager',
    '管理': 'management',
    '生成器': 'generator',
    '迭代器': 'iterator',
    '指针': 'pointer',
    '列表': 'list',
    '集合': 'set',
    '映射': 'map',
    '数组': 'array',
    '队列': 'queue',
    '栈': 'stack',
    '堆': 'heap',
    '链表': 'linked list',
    '树': 'tree',
    '图': 'graph',
    '表': 'table',
    '节点': 'node',
    '边': 'edge',
    '路径': 'path',
    '顶点': 'vertex',
    '组件': 'component',
    '容器': 'container',
    '服务': 'service',
    '资源': 'resource',
    '配置': 'configuration',
    '对象': 'object',
    '值': 'value',
    '数量': 'count',
    '时间': 'time',
    '内存': 'memory',
    '空间': 'space',
    '数据': 'data',
    '信息': 'information',
    '结果': 'result',
    '状态': 'status',
    '方式': 'method',
    '步骤': 'step',
    '流程': 'flow',
    '优化': 'optimization',
    '提升': 'improvement',
    '操作': 'operation',
    '遍历': 'traversal',
    '查询': 'query',
    '查找': 'search',
    '排序': 'sort',
    '算法': 'algorithm',
    '实现': 'implementation',
    '证明': 'proof',
    '规约': 'specification',
    '复杂度': 'complexity',
    '正确性': 'correctness',
    '终止性': 'termination',
    '不变量': 'invariant',
    '安全性': 'safety',
    '并发性': 'concurrency',
    '并行性': 'parallelism',
    '形式化': 'formal',
    '类型级': 'type-level',
    '编译时': 'compile-time',
    '本地': 'local',
    '全局': 'global',
    '内部': 'internal',
    '外部': 'external',
    '公共': 'public',
    '私有': 'private',
    '静态': 'static',
    '动态': 'dynamic',
    '可变': 'mutable',
    '不可变': 'immutable',
    '常量': 'constant',
    '临时': 'temporary',
    '持久': 'persistent',
    '唯一': 'unique',
    '共享': 'shared',
    '独占': 'exclusive',
    '原始': 'raw',
    '智能': 'smart',
    '裸': 'raw',
    '胖': 'fat',
    '悬垂': 'dangling',
    '空': 'null',
    '野': 'wild',
    '自定义': 'custom',
    '通用': 'generic',
    '标准': 'standard',
    '专用': 'dedicated',
    '灵活': 'flexible',
    '可扩展': 'scalable',
    '可靠': 'reliable',
    '高效': 'efficient',
    '快速': 'fast',
    '高性能': 'high-performance',
    '低延迟': 'low-latency',
    '高吞吐': 'high-throughput',
    '零拷贝': 'zero-copy',
    '零成本抽象': 'zero-cost abstraction',
    '幂等': 'idempotent',
    '原子': 'atomic',
    '确定': 'deterministic',
    '随机': 'random',
    '顺序': 'sequential',
    '串行': 'serial',
    '最佳': 'best',
    '学习': 'learning',
    '参考': 'reference',
    '历史': 'historical',
    '版本': 'version',
    '活跃': 'active',
    '当前': 'current',
    '推荐': 'recommended',
    '最新': 'latest',
    '仅': 'only',
    '供': 'for',
    '保留': 'retained',
    '作为': 'as',
    '已经': 'already',
    '是否': 'whether',
    '启用': 'enable',
    '使用': 'use',
    '提供': 'provide',
    '展示': 'demonstrate',
    '包含': 'contain',
    '支持': 'support',
    '需要': 'need',
    '必须': 'must',
    '应该': 'should',
    '可以': 'can',
    '可能': 'may',
    '最好': 'best',
    '更好': 'better',
    '最大': 'maximum',
    '最小': 'minimum',
    '最快': 'fastest',
    '最慢': 'slowest',
    '最高': 'highest',
    '最低': 'lowest',
    '最早': 'earliest',
    '最终': 'final',
    '最初': 'initial',
    '现有': 'existing',
    '新': 'new',
    '旧': 'old',
    '大': 'large',
    '小': 'small',
    '高': 'high',
    '低': 'low',
    '长': 'long',
    '短': 'short',
    '快': 'fast',
    '慢': 'slow',
    '好': 'good',
    '坏': 'bad',
    '优': 'excellent',
    '劣': 'poor',
    '强': 'strong',
    '弱': 'weak',
    '硬': 'hard',
    '软': 'soft',
    '真': 'true',
    '假': 'false',
    '正': 'positive',
    '负': 'negative',
    '零': 'zero',
    '非空': 'non-empty',
    '有': 'has',
    '无': 'without',
    '多': 'multiple',
    '少': 'few',
    '单': 'single',
    '双': 'double',
    '初': 'initial',
    '末': 'final',
    '内': 'inner',
    '外': 'outer',
    '上': 'upper',
    '下': 'lower',
    '左': 'left',
    '右': 'right',
    '前': 'front',
    '后': 'back',
}


def translate_fragment(text):
    result = []
    i = 0
    while i < len(text):
        matched = False
        for cn in sorted(FRAGMENT_DICT.keys(), key=len, reverse=True):
            if text[i:i+len(cn)] == cn:
                result.append(FRAGMENT_DICT[cn])
                i += len(cn)
                matched = True
                break
        if not matched:
            char = text[i]
            if ord(char) < 128:
                result.append(char)
            i += 1
    
    translated = ''.join(result)
    translated = re.sub(r'  +', ' ', translated).strip()
    if not translated or translated == text:
        return text
    return translated


def process_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    modified = False
    new_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()
        
        if not (stripped.startswith('///') or stripped.startswith('//!')):
            new_lines.append(line)
            i += 1
            continue
        
        comment_text = stripped[3:].rstrip('\n')
        if not re.search(r'[\u4e00-\u9fff]', comment_text):
            new_lines.append(line)
            i += 1
            continue
        
        # Find the next non-empty doc comment line
        next_doc_idx = None
        j = i + 1
        while j < len(lines):
            next_stripped = lines[j].lstrip()
            if next_stripped.startswith('///') or next_stripped.startswith('//!'):
                next_text = next_stripped[3:].rstrip('\n')
                if next_text.strip():
                    next_doc_idx = j
                    break
                # Empty doc comment, keep looking
                j += 1
            else:
                break
        
        translated = translate_line(comment_text)
        
        if translated is None:
            # Skip translation for this line
            new_lines.append(line)
            i += 1
            continue
        
        if next_doc_idx is not None:
            # There's already an English translation - replace it
            next_text = lines[next_doc_idx].lstrip()[3:].rstrip('\n')
            # Only replace if existing translation is bad (contains Chinese or is very different from expected)
            existing_has_chinese = re.search(r'[\u4e00-\u9fff]', next_text)
            existing_is_too_short = len(next_text.strip()) < len(comment_text) * 0.3
            if existing_has_chinese or existing_is_too_short:
                prefix = line[:line.index(stripped[0])]
                if stripped.startswith('///'):
                    new_line = prefix + '/// ' + translated + '\n'
                else:
                    new_line = prefix + '//! ' + translated + '\n'
                new_lines.append(line)
                new_lines.append(new_line)
                modified = True
                i = next_doc_idx + 1
                continue
            else:
                # Existing translation seems OK, keep it
                new_lines.append(line)
                i += 1
                continue
        else:
            # No existing translation - add one
            prefix = line[:line.index(stripped[0])]
            if stripped.startswith('///'):
                new_line = prefix + '/// ' + translated + '\n'
            else:
                new_line = prefix + '//! ' + translated + '\n'
            new_lines.append(line)
            new_lines.append(new_line)
            modified = True
        
        i += 1
    
    if modified:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.writelines(new_lines)
        return True
    return False


crates = [
    'crates/c06_async/src',
    'crates/c07_process/src',
    'crates/c08_algorithms/src',
    'crates/c09_design_pattern/src',
]

modified_files = []
for crate in crates:
    for root, dirs, files in os.walk(crate):
        for f in files:
            if f.endswith('.rs'):
                filepath = os.path.join(root, f)
                if process_file(filepath):
                    modified_files.append(filepath)

print(f'Modified {len(modified_files)} files')
for f in modified_files:
    print(f)
