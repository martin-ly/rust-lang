import os
import re

# Translation dictionary - longest keys first for greedy matching
DICT_RAW = {
    # Module descriptors
    '本模块提供了': 'This module provides',
    '本模块展示': 'This module demonstrates',
    '本模块实现': 'This module implements',
    '本模块包含': 'This module contains',
    '本模块是': 'This module is',
    '本模块': 'This module',
    '本库提供了': 'This library provides',
    '本库': 'This library',
    '本文件': 'This file',
    '本章节': 'This section',
    '本例': 'This example',
    '本测试': 'This test',
    '本trait': 'This trait',
    '本结构体': 'This struct',
    '本枚举': 'This enum',
    '本函数': 'This function',
    '本方法': 'This method',
    '本类型': 'This type',
    '本宏': 'This macro',
    '本模式': 'This pattern',
    '本算法': 'This algorithm',
    '本数据': 'This data',
    '本结构': 'This structure',
    '本系统': 'This system',
    '本工具': 'This tool',
    '本框架': 'This framework',
    '本运行时': 'This runtime',
    '本组件': 'This component',
    '本接口': 'This interface',
    '本服务': 'This service',
    '本应用': 'This application',
    '本程序': 'This program',
    '本 crate': 'This crate',

    # Common verbs and phrases
    '提供了': 'provides',
    '提供': 'provides',
    '展示了': 'demonstrates',
    '展示了在': 'demonstrates in',
    '展示': 'demonstrates',
    '实现了': 'implements',
    '实现': 'implementation',
    '包含': 'contains',
    '支持': 'supports',
    '使用': 'uses',
    '用于': 'used for',
    '应用于': 'applied to',
    '的完整': 'complete',
    '完整的': 'complete',
    '完整': 'complete',
    '全面的': 'comprehensive',
    '全面': 'comprehensive',
    '深入的': 'in-depth',
    '深入': 'in-depth',
    '重点解决以下问题': 'focuses on solving the following problems',
    '关键语言特性和工具链改进': 'key language features and toolchain improvements',
    '包括': 'including',
    '等经典模式': 'and other classic patterns',
    '等': 'etc.',

    # Rust/async terms
    '异步编程': 'async programming',
    '异步运行时': 'async runtime',
    '异步调试': 'async debugging',
    '异步执行流': 'async execution flow',
    '异步迭代器': 'async iterator',
    '异步': 'async',
    '同步化跟踪': 'synchronized tracing',
    '同步': 'synchronous',
    '跨任务上下文传播': 'cross-task context propagation',
    '跨任务': 'cross-task',
    '上下文传播': 'context propagation',
    '性能瓶颈识别': 'performance bottleneck identification',
    '性能瓶颈': 'performance bottleneck',
    '瓶颈识别': 'bottleneck identification',
    '分布式追踪集成': 'distributed tracing integration',
    '分布式追踪': 'distributed tracing',
    '实时监控和可视化': 'real-time monitoring and visualization',
    '实时监控': 'real-time monitoring',
    '日志系统': 'logging system',
    '调试和日志': 'debugging and logging',
    '调试解决方案': 'debugging solution',
    '解决方案': 'solution',
    '执行流': 'execution flow',
    '执行流跟踪器': 'execution flow tracker',
    '跟踪器': 'tracker',
    '执行步骤': 'execution step',
    '步骤': 'step',
    '步骤ID': 'step ID',
    '步骤名称': 'step name',
    '步骤类型': 'step type',
    '上下文信息': 'context information',
    '上下文数据': 'context data',
    '上下文': 'context',
    '性能指标': 'performance metrics',
    '错误信息': 'error information',
    '子步骤': 'sub-steps',
    '总执行时间': 'total execution time',
    '异步等待时间': 'async wait time',
    '内存使用峰值': 'peak memory usage',
    '内存使用': 'memory usage',
    '使用率': 'usage rate',
    '开始新的': 'start new',
    '开始新': 'start new',
    '开始执行': 'start execution',
    '开始': 'start',
    '完成执行': 'complete execution',
    '完成': 'complete',

    # Process management
    '进程生命周期管理器': 'process lifecycle manager',
    '进程生命周期': 'process lifecycle',
    '生命周期管理器': 'lifecycle manager',
    '生命周期': 'lifecycle',
    '进程管理': 'process management',
    '进程安全': 'process-safe',
    '进程': 'process',
    '创建新的': 'create new',
    '创建新': 'create new',
    '创建': 'create',
    '注册进程': 'register process',
    '注册': 'register',
    '更新进程状态': 'update process status',
    '更新': 'update',
    '获取进程信息': 'get process info',
    '获取所有进程': 'get all processes',
    '获取': 'get',
    '清理已终止的进程': 'cleanup terminated processes',
    '清理已终止': 'cleanup terminated',
    '清理': 'cleanup',
    '已终止': 'terminated',

    # Algorithm terms
    '高级算法实现模块': 'advanced algorithm implementation module',
    '高级算法': 'advanced algorithms',
    '算法实现': 'algorithm implementation',
    '算法': 'algorithm',
    '并行算法': 'parallel algorithms',
    '并行排序算法': 'parallel sorting algorithm',
    '并行排序': 'parallel sort',
    '并行快速排序': 'parallel quicksort',
    '快速排序': 'quicksort',
    '排序算法': 'sorting algorithm',
    '排序': 'sort',
    '分布式算法': 'distributed algorithms',
    '分布式排序': 'distributed sort',
    '机器学习算法': 'machine learning algorithms',
    '机器学习': 'machine learning',
    '密码学算法': 'cryptographic algorithms',
    '密码学': 'cryptography',
    '图算法': 'graph algorithms',
    '搜索算法': 'search algorithms',
    '搜索': 'search',
    '动态规划': 'dynamic programming',
    '贪心算法': 'greedy algorithm',
    '贪心': 'greedy',
    '分治算法': 'divide and conquer',
    '分治': 'divide and conquer',
    '回溯算法': 'backtracking algorithm',
    '回溯': 'backtracking',
    '组合数学': 'combinatorics',
    '几何算法': 'geometry algorithms',
    '几何': 'geometry',
    '数论算法': 'number theory algorithms',
    '数论': 'number theory',
    '字符串算法': 'string algorithms',
    '字符串': 'string',
    '优化算法': 'optimization algorithms',
    '优化': 'optimization',
    '验证': 'verification',
    '形式化验证': 'formal verification',
    '形式化': 'formal',
    '复杂度分析': 'complexity analysis',
    '复杂度': 'complexity',
    '正确性证明': 'correctness proof',
    '正确性': 'correctness',
    '时间复杂度': 'time complexity',
    '空间复杂度': 'space complexity',
    '原地操作': 'in-place operation',
    '内存优化': 'memory optimization',

    # Design patterns
    '设计模式': 'design pattern',
    '数据库系统设计模式应用': 'database system design pattern application',
    '数据库系统': 'database system',
    '数据库': 'database',
    '游戏引擎设计模式应用': 'game engine design pattern application',
    '游戏引擎': 'game engine',
    '操作系统设计模式应用': 'OS design pattern application',
    '操作系统': 'operating system',
    'Web框架': 'web framework',
    '框架': 'framework',
    '组合模式工程案例': 'combined pattern engineering cases',
    '工程案例': 'engineering cases',
    '实践案例': 'practice cases',
    '实践': 'practice',
    '经典模式': 'classic patterns',
    '经典': 'classic',

    # Data structures
    '数据结构': 'data structure',
    '并查集': 'disjoint set union (DSU)',
    '树状数组': 'Fenwick tree',
    '线段树': 'segment tree',
    '稀疏表': 'sparse table',
    '优先队列': 'priority queue',
    'LRU缓存': 'LRU cache',
    '缓存': 'cache',
    '栈': 'stack',
    '队列': 'queue',
    '堆': 'heap',
    '链表': 'linked list',
    '数组': 'array',
    '向量': 'vector',
    '映射': 'map',
    '集合': 'set',
    '哈希表': 'hash map',

    # LeetCode
    'LeetCode分类': 'LeetCode categories',
    '分类组织': 'categorized organization',
    '按算法主题分类': 'categorized by algorithm topics',
    '主题化': 'thematic',
    '多实现方式': 'multiple implementations',
    '同步实现': 'synchronous implementation',
    '异步实现': 'async implementation',
    '完整文档': 'complete documentation',
    '使用示例': 'usage examples',
    '使用场景': 'usage scenarios',

    # Doc headers
    '问题描述': 'Problem Description',
    '复杂度分析': 'Complexity Analysis',
    '复杂度': 'Complexity',
    '版本信息': 'Version Info',
    '示例': 'Examples',
    '返回值': 'Return Value',
    '参数': 'Parameters',
    '限制': 'Constraints',
    '核心概念': 'Core Concepts',
    '注意事项': 'Notes',
    '形式化规约': 'Formal Specification',
    '背景': 'Background',
    '语法': 'Syntax',
    '之前': 'Before',
    '现在': 'Now',
    '权威来源': 'Authoritative Sources',
    '概述': 'Overview',
    '概念定义': 'Concept Definitions',
    '参考': 'References',
    '文件信息': 'File Info',
    '综合示例': 'Comprehensive Example',
    '证明步骤': 'Proof Steps',
    '测试用例': 'Test Cases',
    '运行方式': 'How to Run',
    '历史参考': 'Historical Reference',
    '实现原理': 'Implementation Principle',
    '实现细节': 'Implementation Details',
    '实际应用示例': 'Practical Application Examples',
    '工作原理': 'Working Principle',
    '处理流程': 'Processing Flow',
    '字段说明': 'Field Descriptions',
    '基础语法': 'Basic Syntax',
    '前提条件': 'Prerequisites',
    '使用前提': 'Prerequisites',

    # Performance
    '性能优化': 'performance optimization',
    '性能提升': 'performance improvement',
    '性能': 'performance',
    '约': 'approximately',
    '提升约': 'improved by approximately',
    '性能提升约': 'performance improved by approximately',
    'JIT优化': 'JIT optimization',
    '迭代器操作': 'iterator operations',
    '位运算操作': 'bitwise operations',
    '递归遍历': 'recursive traversal',
    '回溯递归': 'backtracking recursion',
    '堆操作': 'heap operations',
    '双指针遍历': 'two-pointer traversal',
    '双指针': 'two-pointer',
    '二分查找': 'binary search',
    'DP状态转移': 'DP state transition',
    '滑动窗口操作': 'sliding window operations',
    '滑动窗口': 'sliding window',
    '字符频率统计': 'character frequency statistics',

    # Rust features
    '新特性实现模块': 'new features implementation module',
    '新特性': 'new features',
    '特性应用': 'feature application',
    '特性对齐': 'feature alignment',
    '特性': 'features',
    '稳定日期': 'stable date',
    '稳定': 'stable',
    '创建日期': 'creation date',
    'Rust版本': 'Rust version',
    '历史版本': 'historical version',
    '历史版本特性模块': 'historical version features module',
    '历史特性': 'historical features',
    '归档的历史版本特性模块': 'archived historical version features module',
    '归档': 'archive',
    '当前活跃版本': 'currently active version',
    '活跃版本': 'active version',
    '当前推荐版本': 'currently recommended version',
    '推荐版本': 'recommended version',
    '最新特性': 'latest features',
    '历史参考': 'historical reference',
    '仅供参考学习使用': 'for reference and learning only',
    '请使用最新模块获取最新特性': 'please use the latest module for the newest features',
    '请使用': 'please use',
    '获取最新特性': 'get latest features',

    # Common nouns
    '模块': 'module',
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
    '错误处理': 'error handling',
    '错误': 'error',
    '安全': 'safe',
    '线程安全': 'thread-safe',
    '并发': 'concurrent',
    '并行': 'parallel',
    '运行时': 'runtime',
    '状态机': 'state machine',
    '组合子': 'combinator',
    '调度机制': 'scheduling mechanism',
    '调度': 'scheduling',
    '背压控制': 'backpressure control',
    '背压': 'backpressure',
    'I/O抽象': 'I/O abstraction',
    '轻量级': 'lightweight',

    # Actions
    '获取当前值': 'get current value',
    '获取当前': 'get current',
    '获取统计信息': 'get statistics',
    '获取性能指标': 'get performance metrics',
    '获取等待者数量': 'get waiter count',
    '获取最小执行时间': 'get minimum execution time',
    '获取最大执行时间': 'get maximum execution time',
    '获取最佳性能的测试用例': 'get best performance test case',
    '获取当前内存使用量': 'get current memory usage',
    '获取库版本信息': 'get library version info',
    '获取版本信息': 'get version info',
    '运行基准测试': 'run benchmark',
    '运行所有演示': 'run all demos',
    '计算欧几里得距离': 'compute Euclidean distance',
    '计算': 'compute',
    '设置值': 'set value',
    '训练': 'train',
    '是否已训练': 'whether trained',
    '任务优先级': 'task priority',
    '优先级': 'priority',
    '综合演示函数': 'comprehensive demo function',
    '数据验证管道': 'data validation pipeline',
    '批量处理带错误控制': 'batch processing with error control',
    '搜索二维数组': 'search 2D array',
    '找到目标时提前退出': 'early exit when target found',
    '提前退出': 'early exit',

    # eBPF / system
    'eBPF + Rust (Aya) 预研模块': 'eBPF + Rust (Aya) research module',
    '预研模块': 'research module',
    '警告': 'Warning',
    '本模块内容基于': 'this module content is based on',
    '框架文档': 'framework documentation',
    '需要': 'requires',
    '特定工具链': 'specific toolchain',
    '程序需要': 'program requires',
    'root权限': 'root privileges',
    '能力': 'capability',
    '内核态': 'kernel mode',
    '用户态': 'user mode',
    '无需': 'without',
    '纯Rust': 'pure Rust',
    '开发框架': 'development framework',
    '允许用Rust编写': 'allows writing in Rust',
    '编写': 'write',

    # Machine learning
    '聚类': 'clustering',
    '决策树': 'decision tree',
    'K均值': 'K-means',
    '朴素贝叶斯': 'naive Bayes',
    '神经网络': 'neural network',
    '回归': 'regression',
    '支持向量机': 'support vector machine (SVM)',

    # Formal verification
    '类型级证明': 'type-level proof',
    '类型级': 'type-level',
    '不变量验证': 'invariant verification',
    '不变量': 'invariant',
    '终止性证明': 'termination proof',
    '终止性': 'termination',
    '并发安全性证明': 'concurrent safety proof',
    '并发安全性': 'concurrent safety',
    '状态转换正确性': 'state transition correctness',
    '状态转换': 'state transition',
    '编译时保证': 'compile-time guarantee',
    '编译时': 'compile-time',
    '保证': 'guarantee',
    '正确性': 'correctness',

    # Pattern terms
    'DAO (Data Access Object) 模式': 'DAO (Data Access Object) Pattern',
    '数据访问对象': 'Data Access Object',
    'Active Record': 'Active Record',
    'Unit of Work': 'Unit of Work',
    '数据库连接接口': 'database connection interface',
    '数据库连接': 'database connection',
    '连接接口': 'connection interface',
    '模拟数据库连接': 'mock database connection',
    '模拟': 'mock',
    '用户实体': 'user entity',
    '用户DAO接口': 'user DAO interface',
    '用户DAO实现': 'user DAO implementation',
    '用户': 'user',
    '实体': 'entity',
    '接口': 'interface',
    '实现': 'implementation',

    # Game engine
    '实体ID类型': 'entity ID type',
    '组件接口': 'component interface',
    '组件': 'component',
    'Component 模式': 'Component Pattern',
    'Entity-Component-System': 'Entity-Component-System',
    'Observer 模式': 'Observer Pattern',
    'State 模式': 'State Pattern',

    # Web framework
    'HTTP请求': 'HTTP request',
    '请求方法': 'request method',
    '请求路径': 'request path',
    '请求头': 'request headers',

    # OS patterns
    '系统资源管理器': 'system resource manager',
    '资源管理器': 'resource manager',
    '单例模式': 'singleton pattern',
    '单例': 'singleton',
    '工厂模式': 'factory pattern',
    '策略模式': 'strategy pattern',

    # Functional patterns
    '函数式编程模式': 'functional programming patterns',
    '高阶函数': 'higher-order functions',
    '高阶函数模式': 'higher-order function pattern',
    '接受函数作为参数': 'accepts function as parameter',
    '返回函数': 'returns function',
    'map-reduce 模式': 'map-reduce pattern',

    # Concurrency
    '进程安全的': 'process-safe',
    '进程安全的原子布尔值': 'process-safe atomic boolean',
    '原子布尔值': 'atomic boolean',
    '创建新的原子布尔值': 'create new atomic boolean',
    '进程安全的原子无符号整数': 'process-safe atomic unsigned integer',
    '原子无符号整数': 'atomic unsigned integer',
    '设置值': 'set value',
    '交换值': 'swap value',
    '比较并交换': 'compare and swap',
    '获取并设置': 'fetch and set',
    '获取或设置': 'fetch or set',
    '获取异或设置': 'fetch xor set',
    '获取并添加': 'fetch and add',
    '获取并减去': 'fetch and subtract',
    '获取并位与': 'fetch and bitand',
    '获取并位或': 'fetch and bitor',
    '获取并位异或': 'fetch and bitxor',

    # Barrier / sync primitives
    '屏障模块': 'barrier module',
    '进程安全的屏障': 'process-safe barrier',
    '屏障': 'barrier',
    '条件变量': 'condition variable',
    '互斥锁': 'mutex',
    '读写锁': 'read-write lock',
    '信号量': 'semaphore',

    # IPC
    '进程间通信': 'inter-process communication',
    '消息队列': 'message queue',
    '共享内存': 'shared memory',
    '管道': 'pipe',
    '命名管道': 'named pipe',
    '套接字': 'socket',

    # Fork
    'Fork trait': 'Fork trait',
    '提供跨平台的进程分叉接口': 'provides cross-platform process fork interface',
    '跨平台的': 'cross-platform',
    '进程分叉': 'process fork',
    '分叉接口': 'fork interface',
    '分叉当前进程': 'fork current process',
    '当前进程': 'current process',
    '检查是否为子进程': 'check if child process',
    '子进程': 'child process',
    '检查是否为父进程': 'check if parent process',
    '父进程': 'parent process',
    'Fork结果': 'Fork result',
    '分叉失败': 'fork failed',
    '检查是否失败': 'check if failed',

    # Process attributes
    '进程属性': 'process attributes',
    '进程控制': 'process control',
    '进程监控': 'process monitor',
    '进程池': 'process pool',

    # Performance
    '性能增强': 'performance enhanced',
    '增强的': 'enhanced',
    '性能模块': 'performance module',

    # Shared memory
    '共享内存区域': 'shared memory region',
    '内存区域': 'memory region',
    '区域': 'region',

    # Types
    '类型模块': 'types module',
    '类型定义': 'type definitions',
    '类型别名': 'type alias',

    # SIMD
    'SIMD操作': 'SIMD operations',
    'SIMD': 'SIMD',
    '向量化操作': 'vectorized operations',

    # Number theory
    '最大公约数': 'greatest common divisor (GCD)',
    '最小公倍数': 'least common multiple (LCM)',
    '素数检测': 'prime detection',
    '素数': 'prime',
    '模幂运算': 'modular exponentiation',
    '扩展欧几里得算法': 'extended Euclidean algorithm',

    # Geometry
    '计算几何': 'computational geometry',
    '凸包': 'convex hull',
    'Andrew': 'Andrew',
    '旋转卡壳': 'rotating calipers',
    '直径': 'diameter',
    '逆时针顺序': 'counter-clockwise order',
    '顶点': 'vertices',
    '包含共线最外点': 'including outermost collinear points',
    '共线': 'collinear',
    '最外点': 'outermost points',
    '按': 'in',
    '顺序': 'order',
    '返回': 'returns',
    '返回按': 'returns in',

    # Graph
    '图模块': 'graph module',
    '有向图': 'directed graph',
    '无向图': 'undirected graph',
    '邻接表': 'adjacency list',
    '邻接矩阵': 'adjacency matrix',
    '深度优先搜索': 'depth-first search',
    '广度优先搜索': 'breadth-first search',
    '最短路径': 'shortest path',
    '最小生成树': 'minimum spanning tree',
    '拓扑排序': 'topological sort',
    '强连通分量': 'strongly connected components',

    # Sorting
    '排序模块': 'sorting module',
    '同步排序': 'synchronous sort',
    '并行排序': 'parallel sort',
    '异步排序': 'async sort',
    '分布式排序': 'distributed sort',
    '冒泡排序': 'bubble sort',
    '选择排序': 'selection sort',
    '插入排序': 'insertion sort',
    '归并排序': 'merge sort',
    '堆排序': 'heap sort',
    '计数排序': 'counting sort',
    '基数排序': 'radix sort',
    '桶排序': 'bucket sort',

    # Searching
    '搜索模块': 'searching module',
    '线性搜索': 'linear search',
    '二分搜索': 'binary search',
    '插值搜索': 'interpolation search',
    '指数搜索': 'exponential search',
    '跳跃搜索': 'jump search',

    # Backtracking
    '回溯模块': 'backtracking module',
    'N皇后问题': 'N-Queens problem',
    '全排列': 'full permutation',
    '子集': 'subset',

    # Dynamic programming
    '动态规划模块': 'dynamic programming module',
    '斐波那契数列': 'Fibonacci sequence',
    '最长公共子序列': 'longest common subsequence',
    '最长递增子序列': 'longest increasing subsequence',
    '编辑距离': 'edit distance',
    '背包问题': 'knapsack problem',

    # Divide and conquer
    '分治模块': 'divide and conquer module',
    '归并': 'merge',
    '快速选择': 'quickselect',

    # Greedy
    '贪心模块': 'greedy module',
    '活动选择': 'activity selection',
    '霍夫曼编码': 'Huffman coding',
    '任务调度': 'task scheduling',

    # String algorithms
    '字符串模块': 'string algorithms module',
    'KMP算法': 'KMP algorithm',
    'Rabin-Karp': 'Rabin-Karp',
    '字符串匹配': 'string matching',
    '最长回文子串': 'longest palindromic substring',
    '字典树': 'trie',
    '后缀数组': 'suffix array',

    # Misc
    '错误处理模块': 'error handling module',
    '统一错误处理': 'unified error handling',
    '统一错误类型': 'unified error type',
    '错误类型': 'error type',
    'Miri测试模块': 'Miri test module',
    '内存安全验证': 'memory safety verification',
    '内存安全': 'memory safety',
    '安全验证': 'safety verification',

    # Utils
    '退避策略': 'backoff strategy',
    '退避': 'backoff',
    '重试': 'retry',
    '超时': 'timeout',
    '限流': 'rate limiting',
    '熔断': 'circuit breaker',
    '监督树': 'supervision tree',

    # Actix
    'Actix最小可运行示例': 'Actix minimum runnable example',
    '定义消息': 'define message',
    '发送并接收响应': 'send and receive response',
    '库内调用异步版本': 'in-library async call version',
    '需在Actix系统/运行时内': 'must be inside Actix system/runtime',
    '可直接在可执行入口调用同步封装': 'can directly call synchronous wrapper at executable entry',
    '内部启动并关闭系统': 'internally start and shutdown system',
    '示例参见': 'see example',
    '同步封装': 'synchronous wrapper',
    '内部创建并运行': 'internally create and run',
    '方便示例/二进制入口直接调用': 'convenient for example/binary entry direct call',

    # Async std
    'async-std运行时模块': 'async-std runtime module',
    'async-std': 'async-std',
    '轻量级运行时': 'lightweight runtime',
    '已停止维护': 'discontinued',
    '停止维护': 'discontinued',

    # Streams
    '流处理模块': 'stream processing module',
    '流处理': 'stream processing',
    '异步流': 'async stream',

    # Runtime
    '运行时模块': 'runtime module',
    '运行时对比': 'runtime comparison',
    '运行时选择': 'runtime selection',

    # Advanced tools
    '批处理处理器': 'batch processor',
    '批处理': 'batch processing',
    '重试引擎': 'retry engine',
    '任务管理器': 'task manager',
    '高级工具模块': 'advanced tools module',

    # Archive
    '归档模块': 'archive module',
    '历史特性': 'historical features',
    '包含的经典题目': 'included classic problems',
    '经典题目': 'classic problems',

    # Cloud native
    '云原生示例': 'cloud native example',
    '分布式共识示例': 'distributed consensus example',
    '分布式锁示例': 'distributed lock example',
    '事件溯源示例': 'event sourcing example',
    '微服务模式示例': 'microservice patterns example',
    '简单演示': 'simple demo',

    # Misc phrases
    '仅供': 'for',
    '参考': 'reference',
    '学习': 'learning',
    '使用': 'use',
    '保留': 'retain',
    '作为': 'as',
    '注意': 'Note',
    '注意:': 'Note:',
    '重要': 'Important',
    '提示': 'Tip',
    '建议': 'Suggestion',
    '不推荐': 'Not recommended',
    '推荐': 'Recommended',
    '已弃用': 'Deprecated',
    '实验性': 'Experimental',
    '不稳定': 'Unstable',
    ' nightly ': ' nightly ',
    '预览': 'preview',
    '预研': 'research',

    # Math symbols in text
    '等于': 'equals',
    '大于': 'greater than',
    '小于': 'less than',
    '大于等于': 'greater than or equal to',
    '小于等于': 'less than or equal to',
    '不等于': 'not equal to',
    '加': 'plus',
    '减': 'minus',
    '乘': 'multiply',
    '除': 'divide',
    '取模': 'modulo',
    '幂': 'power',
    '平方': 'square',
    '立方': 'cube',
    '根号': 'square root',
    '绝对值': 'absolute value',
    '最大值': 'maximum',
    '最小值': 'minimum',
    '平均值': 'average',
    '中位数': 'median',
    '标准差': 'standard deviation',
    '方差': 'variance',
    '协方差': 'covariance',
    '相关系数': 'correlation coefficient',

    # Numbers
    '一': 'one',
    '二': 'two',
    '三': 'three',
    '四': 'four',
    '五': 'five',
    '六': 'six',
    '七': 'seven',
    '八': 'eight',
    '九': 'nine',
    '十': 'ten',

    # Common short words (keep near end)
    '的': '',
    '了': '',
    '是': 'is',
    '在': 'in',
    '中': 'in',
    '为': 'for',
    '与': 'and',
    '或': 'or',
    '及': 'and',
    '对': 'for',
    '将': 'will',
    '从': 'from',
    '到': 'to',
    '通过': 'via',
    '基于': 'based on',
    '针对': 'for',
    '关于': 'about',
    '根据': 'according to',
    '按照': 'according to',
    '随着': 'with',
    '由于': 'due to',
    '因为': 'because',
    '所以': 'therefore',
    '因此': 'therefore',
    '但是': 'but',
    '然而': 'however',
    '如果': 'if',
    '否则': 'otherwise',
    '当': 'when',
    '然后': 'then',
    '之后': 'after',
    '之前': 'before',
    '期间': 'during',
    '同时': 'simultaneously',
    '分别': 'respectively',
    '主要': 'main',
    '所有': 'all',
    '部分': 'part',
    '每个': 'each',
    '各种': 'various',
    '不同': 'different',
    '相同': 'same',
    '类似': 'similar',
    '相关': 'related',
    '特定': 'specific',
    '特殊': 'special',
    '一般': 'general',
    '通常': 'usually',
    '可能': 'may',
    '可以': 'can',
    '需要': 'need',
    '必须': 'must',
    '应该': 'should',
    '最好': 'best',
    '更好': 'better',
    '最大': 'maximum',
    '最小': 'minimum',
    '最快': 'fastest',
    '最慢': 'slowest',
    '最高': 'highest',
    '最低': 'lowest',
    '最新': 'latest',
    '最早': 'earliest',
    '最终': 'final',
    '最初': 'initial',
    '当前': 'current',
    '现有': 'existing',
    '新': 'new',
    '旧': 'old',
    '老': 'old',
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
    '空': 'empty',
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
    '东': 'east',
    '西': 'west',
    '南': 'south',
    '北': 'north',

    # Very common technical terms
    '跟踪': 'tracing',
    '追踪': 'tracing',
    '监控': 'monitoring',
    '可视化': 'visualization',
    '集成': 'integration',
    '分析': 'analysis',
    '识别': 'identification',
    '转换': 'conversion',
    '转换最佳实践': 'conversion best practices',
    '最佳实践': 'best practices',
    '调度': 'scheduling',
    '接口设计': 'interface design',
    '接口': 'interface',
    '设计': 'design',
    '模式': 'pattern',
    '应用': 'application',
    '案例': 'cases',
    '展示在': 'demonstrates in',
    '在...中应用': 'applies in',
    '各种': 'various',
    '经典': 'classic',
}

# Build sorted dictionary (longest first)
DICT = dict(sorted(DICT_RAW.items(), key=lambda x: len(x[0]), reverse=True))


def translate_line(text):
    """Translate a Chinese doc comment line to English."""
    if not re.search(r'[\u4e00-\u9fff]', text):
        return text

    result = text
    i = 0
    output = []
    while i < len(result):
        matched = False
        for cn, en in DICT.items():
            if result[i:i+len(cn)] == cn:
                output.append(en)
                i += len(cn)
                matched = True
                break
        if not matched:
            char = result[i]
            # Keep ASCII, digits, spaces, and common punctuation as-is
            if ord(char) < 128:
                output.append(char)
            else:
                # For unknown Chinese characters, keep them
                output.append(char)
            i += 1

    translated = ''.join(output)
    # Clean up multiple spaces
    translated = re.sub(r'  +', ' ', translated)
    translated = translated.strip()
    # If translation is empty or just punctuation, return original
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

        # Check if next line is already a doc comment (might be English translation)
        has_next_doc = False
        if i + 1 < len(lines):
            next_stripped = lines[i+1].lstrip()
            if next_stripped.startswith('///') or next_stripped.startswith('//!'):
                has_next_doc = True

        new_lines.append(line)

        if not has_next_doc:
            translated = translate_line(comment_text)
            if translated != comment_text:
                # Preserve indentation and comment prefix
                prefix = line[:line.index(stripped[0])]
                if stripped.startswith('///'):
                    new_line = prefix + '/// ' + translated + '\n'
                else:
                    new_line = prefix + '//! ' + translated + '\n'
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

print(f'Modified {len(modified_files)} files:')
for f in modified_files:
    print(f)
