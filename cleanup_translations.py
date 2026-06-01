import os
import re

# Expanded exact-match dictionary
EXACT_DICT = {
    # Headers
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
    '## 影响': '## Impact',
    '## 快速开始': '## Quick Start',
    '## 等价性证明': '## Equivalence Proof',
    '## 验证发布顺序': '## Verify Publish Order',
    '## 认知必要性': '## Cognitive Necessity',
    '## 实现细节': '## Implementation Details',
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
    '# Cargo 多包发布（Multi-Package Publishing）': '# Cargo Multi-Package Publishing',
    '# 理论基础 (Theoretical Foundations)': '# Theoretical Foundations',
    '# 核心差异': '# Core Differences',
    '# 实现细节': '# Implementation Details',
    '# 预研语法': '# Preview Syntax',
    '# 核心文档 (2025年10月最新)': '# Core Documentation (Latest Oct 2025)',
    '# 示例索引': '# Example Index',
    '### 🌟 必读文档': '### 🌟 Required Reading',
    '### 🎯 2025年核心示例 (强烈推荐)': '### 🎯 2025 Core Examples (Highly Recommended)',
    '### 理论学习路径': '### Theory Learning Path',
    '### 实践应用路径': '### Practice Application Path',
    '### 核心异步原语 (Core Async Primitives)': '### Core Async Primitives',
    '### Actor 模型与消息传递 (Actor Model)': '### Actor Model and Message Passing',
    '### 高级工具与模式 (Advanced Tools)': '### Advanced Tools and Patterns',
    '### Rust 1.95 特性 (Rust 1.95 Features)': '### Rust 1.95 Features',
    '### Rust 1.94 历史特性 (Rust 1.94 Historical Features)': '### Rust 1.94 Historical Features',
    '### 生态系统集成 (Ecosystem Integration)': '### Ecosystem Integration',
    '### 理论基础模块 (Theoretical Foundations)': '### Theoretical Foundations Modules',
    
    # Version info
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
    
    # Complexity
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
    '- 空间复杂度: O(min(n, m))，其中 m 是字符集大小': '- Space Complexity: O(min(n, m)), where m is the character set size',
    '- 空间复杂度: O(|s| + |t|)': '- Space Complexity: O(|s| + |t|)',
    '- 空间复杂度: O(1) 额外空间复杂度': '- Space Complexity: O(1) extra space',
    
    # JIT
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
    
    # Memory
    '- **内存优化**: O(1) 空间复杂度': '- **Memory Optimization**: O(1) space complexity',
    '- **内存优化**: 原地操作': '- **Memory Optimization**: In-place operation',
    '- **内存优化**: O(h) 空间复杂度': '- **Memory Optimization**: O(h) space complexity',
    '- **内存优化**: 使用 Vec 存储路径': '- **Memory Optimization**: Use Vec to store paths',
    '- **内存优化**: 使用滚动数组，O(1) 空间复杂度': '- **Memory Optimization**: Use rolling array, O(1) space complexity',
    
    # Actions
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
    '创建新的缓存': 'Create new cache',
    '获取日志数量': 'Get log count',
    '检查是否为空': 'Check if empty',
    '开始时间': 'Start time',
    '结束时间': 'End time',
    '超时时间': 'Timeout',
    '性能指标': 'Performance metrics',
    '验证等价性': 'Verify equivalence',
    '测试用例': 'Test cases',
    '证明步骤': 'Proof steps',
    '运行方式:': 'How to run:',
    '其中:': 'Where:',
    '特性：': 'Features:',
    '事件类型': 'Event type',
    '异步任务': 'Async task',
    '运行时名称': 'Runtime name',
    '性能特征': 'Performance characteristics',
    '日志级别': 'Log level',
    '完成任务': 'Complete task',
    '取消任务': 'Cancel task',
    '获取任务信息': 'Get task info',
    '清理已完成的任务': 'Cleanup completed tasks',
    '获取队列长度': 'Get queue length',
    '显示系统状态': 'Show system status',
    '获取特性信息': 'Get feature info',
    '添加任务': 'Add task',
    '清空队列': 'Clear queue',
    '执行任务': 'Execute task',
    '执行带重试的异步操作': 'Execute async operation with retry',
    '智能重试引擎': 'Smart retry engine',
    '任务信息': 'Task info',
    '任务统计信息': 'Task statistics',
    '获取任务统计信息': 'Get task statistics',
    '演示并行编译优化': 'Demonstrate parallel compilation optimization',
    '获取库信息': 'Get library info',
    '进程信息结构': 'Process info structure',
    '资源限制结构': 'Resource limit structure',
    '性能演示': 'Performance demo',
    '错误恢复器': 'Error recovery',
    '恢复策略': 'Recovery strategy',
    '异步终止进程': 'Async terminate process',
    '异步获取进程信息': 'Async get process info',
    '带超时等待进程完成': 'Wait for process completion with timeout',
    '处理启动进程命令': 'Handle start process command',
    '处理终止进程命令': 'Handle terminate process command',
    '处理获取进程信息命令': 'Handle get process info command',
    '性能监控循环': 'Performance monitoring loop',
    '初始化进程池': 'Initialize process pool',
    '获取并取最大值': 'Fetch and get maximum',
    '获取并取最小值': 'Fetch and get minimum',
    '获取原语类型': 'Get primitive type',
    '检查是否被锁定': 'Check if locked',
    '检查死锁风险': 'Check deadlock risk',
    '性能分析结果': 'Performance analysis results',
    '获取所有原语名称': 'Get all primitive names',
    '检查原语是否存在': 'Check if primitive exists',
    '获取原语统计信息': 'Get primitive statistics',
    '获取所有原语统计信息': 'Get all primitive statistics',
    '获取读锁': 'Get read lock',
    '获取写锁': 'Get write lock',
    '检查锁是否被持有': 'Check if lock is held',
    '获取锁名称': 'Get lock name',
    '错误类型': 'Error type',
    '检查是否为子进程': 'Check if child process',
    '检查是否为父进程': 'Check if parent process',
    '通道统计信息': 'Channel statistics',
    '获取通道统计信息': 'Get channel statistics',
    '清理所有通道': 'Cleanup all channels',
    '命名管道实现': 'Named pipe implementation',
    '创建新的命名管道': 'Create new named pipe',
    '检查管道是否关闭': 'Check if pipe is closed',
    '解析数字': 'Parse number',
    '演示异步流处理': 'Demonstrate async stream processing',
    '演示如何组合不同的异步运行时': 'Demonstrate combining different async runtimes',
    '展示 smol 的轻量级特性': 'Demonstrate smol lightweight features',
    '轻量级任务调度示例': 'Lightweight task scheduling example',
    '嵌入式友好示例': 'Embedded-friendly example',
    '运行时兼容性示例': 'Runtime compatibility example',
    '零依赖示例': 'Zero-dependency example',
    '标准库兼容性示例': 'Standard library compatibility example',
    '任务管理示例': 'Task management example',
    '标准库风格的异步文件操作': 'Standard library style async file operations',
    '网络客户端示例': 'Network client example',
    '高性能并发处理示例': 'High-performance concurrency example',
    '流处理示例': 'Stream processing example',
    '定时器和调度示例': 'Timer and scheduling example',
    '异步错误处理示例': 'Async error handling example',
    '异步迭代器示例': 'Async iterator example',
    '基础异步函数示例': 'Basic async function example',
    '异步迭代版本': 'Async iteration version',
    
    # Nouns
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
    '内存优化演示': 'Memory optimization demo',
    '标准库新 API 演示': 'Standard library new API demo',
    '配置文件解析示例': 'Configuration file parsing example',
    'str::split_ascii_whitespace 示例': 'str::split_ascii_whitespace example',
    'Vec::try_reserve_exact 示例': 'Vec::try_reserve_exact example',
    '性能分析器': 'Performance profiler',
    '生成性能报告': 'Generate performance report',
    '检查数组是否已排序': 'Check if array is sorted',
    '获取最小内存使用': 'Get minimum memory usage',
    '获取最大内存使用': 'Get maximum memory usage',
    '计算性能稳定性（变异系数）': 'Compute performance stability (coefficient of variation)',
    '基准测试结果': 'Benchmark results',
    '复杂度边界': 'Complexity bounds',
    '搜索算法': 'Search algorithm',
    '验证排序算法的正确性': 'Verify sorting algorithm correctness',
    '证明状态': 'Proof state',
    '约束条件': 'Constraints',
    '时间复杂度': 'Time complexity',
    '空间复杂度': 'Space complexity',
    '实现类型': 'Implementation type',
    '同步实现': 'Synchronous implementation',
    '前置条件': 'Precondition',
    '后置条件': 'Postcondition',
    
    # Features
    '- `target_feature_safe`: 安全函数上的 `#[target_feature]`': '- `target_feature_safe`: `#[target_feature]` on safe functions',
    '- `use_in_traits`: trait 中 RPIT 的 `use<...>` precise capturing': '- `use_in_traits`: `use<...>` precise capturing in trait RPIT',
    '- `let_chains`: Let Chains 在 2024 Edition 中稳定': '- `let_chains`: Let Chains stabilized in 2024 Edition',
    '- `explicit_inferred_const`: 显式推断 const 参数': '- `explicit_inferred_const`: Explicit inferred const parameters',
    '- `trait_upcasting`: Trait 对象向上转换（dyn Trait + Trait -> dyn Trait）': '- `trait_upcasting`: Trait object upcasting (dyn Trait + Trait -> dyn Trait)',
    '- 仅在 Edition 2024 中可用': '- Only available in Edition 2024',
    '- 不支持 `||`（或）与 `let` 混合（因语义复杂）': '- Does not support `||` (OR) mixed with `let` (due to complex semantics)',
    '- 抽象层解耦：在运行时根据具体类型降级到更通用的 trait 对象': '- Abstraction decoupling: downgrade to more general trait objects at runtime based on specific types',
    '- 插件系统：将特定插件接口转换为通用接口': '- Plugin system: convert specific plugin interfaces to general interfaces',
    '- `open_ranges_parsing`: 开放范围 `..EXPR` 可在一元操作符后解析': '- `open_ranges_parsing`: Open ranges `..EXPR` can be parsed after unary operators',
    '- `cargo_multi_publish`: Cargo 多包发布稳定': '- `cargo_multi_publish`: Cargo multi-package publishing stabilized',
    '- 可通过 `-C link-arg=-fuse-ld=gold` 等覆盖': '- Can be overridden via `-C link-arg=-fuse-ld=gold` etc.',
    '无需修改配置，工具链自动处理。': 'No configuration changes needed, toolchain handles automatically.',
    
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
    'Rust 1.91 对异步迭代器进行了优化，性能提升约 15-20%': 'Rust 1.91 optimized async iterators, performance improved by ~15-20%',
    'Rust 1.87.0 修复了开放范围 `..expr` 在一元操作符后的解析问题。': 'Rust 1.87.0 fixed open range `..expr` parsing after unary operators.',
    '`..-5` 会被解析错误，需要写成 `..(-5)`。': '`..-5` was parsed incorrectly, needed to be written as `..(-5)`.',
    '`..-5` 可以直接解析为 `RangeTo { end: -5 }`。': '`..-5` can now be directly parsed as `RangeTo { end: -5 }`.',
    
    # Process
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
    
    # Algorithms
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
    '本模块展示了 Rust 186.0 (2025-04-03) 的关键语言特性和工具链改进。': 'This module demonstrates key language features and toolchain improvements of Rust 186.0 (2025-04-03).',
    '本模块展示了 Rust 187.0 (2025-05-15) 的关键语言特性和工具链改进。': 'This module demonstrates key language features and toolchain improvements of Rust 187.0 (2025-05-15).',
    '本模块展示了 Rust 188.0 (2025-06-26) 的关键语言特性和工具链改进。': 'This module demonstrates key language features and toolchain improvements of Rust 188.0 (2025-06-26).',
    '本模块展示了 Rust 189.0 (2025-08-07) 的关键语言特性和工具链改进。': 'This module demonstrates key language features and toolchain improvements of Rust 189.0 (2025-08-07).',
    '本模块提供了Rust中的高级算法实现，包括：': 'This module provides advanced algorithm implementations in Rust, including:',
    '本库提供了Rust中各种高级算法的完整实现，完全对齐 Rust 1.95.0 版本特性，': 'This library provides complete implementations of various advanced algorithms in Rust, fully aligned with Rust 1.95.0 features,',
    '包括排序、搜索、图算法、机器学习算法、密码学算法等。': 'Including sorting, searching, graph algorithms, machine learning algorithms, cryptographic algorithms, etc.',
    '本模块展示了在数据库系统中应用各种设计模式的实践案例，': 'This module demonstrates practical cases of applying various design patterns in database systems,',
    '包括DAO、Active Record、Unit of Work等经典模式。': 'Including classic patterns such as DAO, Active Record, and Unit of Work.',
    '本库提供了Rust中各种设计模式的完整实现和实际应用案例，': 'This library provides complete implementations and practical application cases of various design patterns in Rust,',
    '包括基础设计模式、高级设计模式以及在特定领域的应用。': 'Including basic design patterns, advanced design patterns, and applications in specific domains.',
    '一个功能完整的 Rust 进程管理和 IPC 通信库。': 'A fully-featured Rust process management and IPC communication library.',
    
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
    
    # Additional common phrases from analysis
    '239. Sliding Window Maximum（滑动窗口最大值）': '239. Sliding Window Maximum',
    '可以直接暴露原始汇编入口。': 'Can directly expose raw assembly entry points.',
    '- 与汇编代码直接交互的回调': '- Callbacks that directly interact with assembly code',
    '- 调用者负责保存/恢复寄存器': '- Caller is responsible for saving/restoring registers',
    '直接暴露原始汇编入口': 'Directly expose raw assembly entry',
    '比较两个运行时的特性': 'Compare runtime features',
    '获取所有运行时状态': 'Get all runtime states',
    '异步运行时管理器': 'Async runtime manager',
    '实现聚合模式，统一管理多个运行时': 'Implement aggregate pattern, uniformly manage multiple runtimes',
    '异步日志记录器接口': 'Async logger interface',
    '简单异步日志记录器实现': 'Simple async logger implementation',
    '异步运行时共性分析': 'Async runtime commonality analysis',
    '分析不同异步运行时的共同特性和设计模式': 'Analyze common features and design patterns of different async runtimes',
    '获取运行时共性分析': 'Get runtime commonality analysis',
    '分析设计模式共性': 'Analyze design pattern commonalities',
    '异步同步转换框架': 'Async-sync conversion framework',
    '提供异步和同步代码之间的转换机制': 'Provide conversion mechanism between async and synchronous code',
    '聚合组合设计模式框架': 'Aggregate combination design pattern framework',
    '提供聚合和组合的设计模式实现': 'Provide aggregate and combination design pattern implementation',
    '综合演示异步集成框架': 'Comprehensive async integration framework demo',
    '异步日志调试和跟踪模块': 'Async logging debugging and tracing module',
    '是否启用结构化日志': 'Whether structured logging is enabled',
    '是否启用分布式追踪': 'Whether distributed tracing is enabled',
    '最大日志文件大小（MB）': 'Maximum log file size (MB)',
    '平均执行时间（纳秒）': 'Average execution time (nanoseconds)',
    '获取所有任务信息': 'Get all task information',
    '清理已完成的任务': 'Cleanup completed tasks',
    '结构化日志记录器': 'Structured logger',
    '调试模式执行任务': 'Debug mode task execution',
    '异步执行流跟踪器': 'Async execution flow tracker',
    '解决异步任务执行流难以跟踪的问题': 'Solve the problem of difficult async task execution flow tracking',
    '异步执行流管理器': 'Async execution flow manager',
    '生成执行流图表（DOT格式）': 'Generate execution flow graph (DOT format)',
    '异步生态系统架构分析': 'Async ecosystem architecture analysis',
    '获取所有运行时分析': 'Get all runtime analysis',
    '模式1：运行时适配器模式': 'Pattern 1: Runtime Adapter Pattern',
    '为不同的异步运行时提供统一的接口': 'Provide unified interface for different async runtimes',
    '模式2：任务组合模式': 'Pattern 2: Task Composition Pattern',
    '模式3：运行时抽象模式': 'Pattern 3: Runtime Abstraction Pattern',
    '通过抽象接口支持不同的异步运行时': 'Support different async runtimes through abstract interfaces',
    '模式4：异步同步转换模式': 'Pattern 4: Async-Sync Conversion Pattern',
    '模式5：聚合组合设计模式': 'Pattern 5: Aggregate Combination Design Pattern',
    '演示聚合和组合的设计模式': 'Demonstrate aggregate and combination design patterns',
    '异步任务调度器': 'Async task scheduler',
    '执行任务': 'Execute task',
    '执行带重试的异步操作': 'Execute async operation with retry',
    '新范式（1.85.0+）：真正的异步闭包': 'New paradigm (1.85.0+): True async closures',
    '中间件模式：HTTP 处理链': 'Middleware pattern: HTTP processing chain',
    '迁移路径说明': 'Migration path description',
    'RTN 语法预览': 'RTN syntax preview',
    '异步递归解决方案': 'Async recursion solution',
    '尾递归优化方案': 'Tail recursion optimization solution',
    '迭代器等价方案': 'Iterator equivalence solution',
    '异步递归深度分析 - 理论基础与实现': 'Async Recursion Deep Analysis - Theory and Implementation',
    '异步递归的形式化定义': 'Formal definition of async recursion',
    '迭代器等价性证明': 'Iterator equivalence proof',
    '异步递归性能分析': 'Async recursion performance analysis',
    'Actor/Reactor 模式对比分析': 'Actor/Reactor Pattern Comparison Analysis',
    'Actor/Reactor 模式对比': 'Actor/Reactor Pattern Comparison',
    'Actor 模式实现': 'Actor Pattern Implementation',
    'Reactor 模式实现': 'Reactor Pattern Implementation',
    '综合对比分析': 'Comprehensive Comparison Analysis',
    '异步生态系统全面分析': 'Async Ecosystem Comprehensive Analysis',
    '异步运行时对比分析': 'Async Runtime Comparison Analysis',
    '异步集成模式分析': 'Async Integration Pattern Analysis',
    '异步同步转换分析': 'Async-Sync Conversion Analysis',
    '设计模式共性分析': 'Design Pattern Commonality Analysis',
    '异步运行时集成框架': 'Async Runtime Integration Framework',
    '简化异步运行时集成框架': 'Simplified Async Runtime Integration Framework',
    '运行时选择器模式': 'Runtime Selector Pattern',
    '运行时适配器模式': 'Runtime Adapter Pattern',
    '运行时桥接模式': 'Runtime Bridge Pattern',
    '聚合组合设计模式服务': 'Aggregate Combination Design Pattern Service',
    '顺序聚合': 'Sequential aggregation',
    '并行聚合': 'Parallel aggregation',
    '混合转换模式': 'Mixed conversion pattern',
    '异步同步转换服务': 'Async-sync conversion service',
    '示例任务实现': 'Example task implementation',
    '异步任务抽象': 'Async task abstraction',
    '运行时配置': 'Runtime configuration',
    '运行时性能指标': 'Runtime performance metrics',
    'CSP 模型对比 (Rust vs Golang)': 'CSP Model Comparison (Rust vs Golang)',
    'CSP 模型对比 (Rust vs Golang)、语义差异': 'CSP Model Comparison (Rust vs Golang), semantic differences',
    'Future 状态机、组合子、调度机制': 'Future state machines, combinators, scheduling mechanisms',
    'Stream 处理、异步迭代器、背压控制': 'Stream handling, async iterators, backpressure control',
    'Tokio runtime 、synchronous 、I/O': 'Tokio runtime, synchronization primitives, I/O',
    'Smol 轻量级运行时': 'Smol lightweight runtime',
    'async-std 运行时（已于 2025-03 停止维护）': 'async-std runtime (maintenance ended 2025-03)',
    '运行时对比与选择': 'Runtime comparison and selection',
    'Actix Actor 框架基础': 'Actix Actor framework basics',
    '重试、超时、限流、熔断、监督树': 'Retry, timeout, rate limiting, circuit breaker, supervision trees',
    '批处理、任务管理、重试引擎': 'Batch processing, task management, retry engines',
    'Rust 1.95 异步新特性': 'Rust 1.95 async new features',
    'if let guards 用于异步状态机匹配': 'if let guards for async state machine matching',
    'bool 转浮点数用于异步数值计算': 'bool to float for async numeric computation',
    'RangeInclusive 优化用于异步迭代': 'RangeInclusive optimization for async iteration',
    'Rust 1.94 异步历史特性': 'Rust 1.94 async historical features',
    'array_windows 用于异步数据流处理': 'array_windows for async data flow processing',
    'LazyCell/LazyLock 用于异步缓存': 'LazyCell/LazyLock for async caching',
    '数学常量用于异步算法': 'Mathematical constants for async algorithms',
    '生态系统全面分析': 'Comprehensive ecosystem analysis',
    '日志与调试': 'Logging and debugging',
    '高级调试技术': 'Advanced debugging techniques',
    '简化集成': 'Simplified integration',
    
    # lib.rs specific fixes
    '## 模块组织': '## Module Organization',
    '## 特性': '## Features',
    '## 使用示例': '## Usage Examples',
    '本 crate 提供 Rust 1.95.0 异步编程的全面、深入的理论与实践指南。': 'This crate provides a comprehensive and in-depth theoretical and practical guide to Rust 1.95.0 async programming.',
    'Rust 1.95.0 高级算法实现库': 'Rust 1.95.0 Advanced Algorithm Implementation Library',
    'Rust设计模式实践案例库': 'Rust Design Pattern Practice Case Library',
    '- **Rust 1.95.0+ 特性对齐**: 完全支持最新语言特性 (Edition 2024)': '- **Rust 1.95.0+ Feature Alignment**: Fully supports latest language features (Edition 2024)',
    '- **对齐日期**: 2026-05-12': '- **Alignment Date**: 2026-05-12',
    '- **LeetCode 分类组织**: 按照 LeetCode 官方分类组织算法': '- **LeetCode Categorized Organization**: Organizes algorithms by LeetCode official categories',
    '- **主题化组织**: 按算法主题分类组织': '- **Thematic Organization**: Organizes by algorithm topics',
    '- **多实现方式**: 同步、并行、异步实现': '- **Multiple Implementation Methods**: Synchronous, parallel, async implementations',
    '- **形式化验证**: 包含算法正确性证明（循环不变量、霍尔逻辑）': '- **Formal Verification**: Includes algorithm correctness proofs (loop invariants, Hoare logic)',
    '- **完整文档**: 详细的算法说明和复杂度分析（主定理、摊还分析）': '- **Complete Documentation**: Detailed algorithm explanations and complexity analysis (master theorem, amortized analysis)',
    '- **异步模式**: Actor/Reactor/CSP三大模式完整实现': '- **Async Patterns**: Complete implementation of Actor/Reactor/CSP三大模式',
    '## 模块组织': '## Module Organization',
    
    # More process-related
    '创建进程管理器': 'Create process manager',
    '创建进程配置': 'Create process configuration',
    '注意：在实际使用中，需要确保程序存在': 'Note: In actual use, ensure the program exists',
    '## 快速开始': '## Quick Start',
}


def translate_line(text):
    if not re.search(r'[\u4e00-\u9fff]', text):
        return None
    
    t = text.strip()
    
    # Try exact match
    if t in EXACT_DICT:
        return EXACT_DICT[t]
    
    return None


def is_bad_translation(cn_text, en_text):
    """Heuristic to detect bad translations."""
    if not en_text.strip():
        return True
    
    # Contains Chinese - definitely bad
    if re.search(r'[\u4e00-\u9fff]', en_text):
        return True
    
    # ASCII art / formatting
    stripped = en_text.strip()
    if stripped.startswith('```') or stripped in ('ignore', 'text', 'rust', 'no_run'):
        return True
    if all(c in ' ├┤┼─┴┬│┌┐└┘═║╒╓╔╕╖╗╘╙╚╛╜╝╞╟╠╡╢╣╤╥╦╧╨╩╪╫╬' or c.isspace() for c in stripped):
        return True
    if all(c in ' ↓↑←→' or c.isspace() for c in stripped):
        return True
    
    # Very short for long Chinese
    cn_chars = len(re.findall(r'[\u4e00-\u9fff]', cn_text))
    words = stripped.split()
    if cn_chars >= 8 and len(words) <= 2:
        return True
    if cn_chars >= 15 and len(words) <= 4:
        return True
    
    # Contains weird artifacts
    if '（）' in stripped and not stripped.replace('（）', '').strip():
        return True
    if stripped.endswith("'s") and len(words) <= 2:
        return True
    
    return False


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
        next_doc_text = None
        j = i + 1
        while j < len(lines):
            next_stripped = lines[j].lstrip()
            if next_stripped.startswith('///') or next_stripped.startswith('//!'):
                next_text = next_stripped[3:].rstrip('\n')
                if next_text.strip():
                    next_doc_idx = j
                    next_doc_text = next_text
                    break
                j += 1
            else:
                break
        
        translated = translate_line(comment_text)
        
        if translated is None:
            # No translation available - check if existing translation is bad
            if next_doc_idx is not None and is_bad_translation(comment_text, next_doc_text):
                # Delete bad translation
                new_lines.append(line)
                modified = True
                i = next_doc_idx + 1
                continue
            else:
                new_lines.append(line)
            i += 1
            continue
        
        prefix = line[:line.index(stripped[0])]
        if stripped.startswith('///'):
            new_line = prefix + '/// ' + translated + '\n'
        else:
            new_line = prefix + '//! ' + translated + '\n'
        
        if next_doc_idx is not None:
            if is_bad_translation(comment_text, next_doc_text):
                # Replace bad translation
                new_lines.append(line)
                new_lines.append(new_line)
                modified = True
                i = next_doc_idx + 1
                continue
            else:
                # Existing translation looks OK, keep it
                new_lines.append(line)
        else:
            # Add new translation
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
