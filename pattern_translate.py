import os
import re

PHRASE_DICT = {
    '高级异步调试和日志': 'Advanced async debugging and logging',
    '异步生态系统集成': 'Async ecosystem integration',
    '异步生态系统全面': 'Async ecosystem comprehensive',
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
    '高级异步调试和日志系统': 'Advanced Async Debugging and Logging System',
    '异步调试解决方案': 'Async Debugging Solution',
    '异步执行流的同步化跟踪': 'Async Execution Flow Synchronized Tracing',
    '跨任务上下文传播': 'Cross-task Context Propagation',
    '性能瓶颈识别': 'Performance Bottleneck Identification',
    '分布式追踪集成': 'Distributed Tracing Integration',
    '实时监控和可视化': 'Real-time Monitoring and Visualization',
    'eBPF + Rust (Aya) 预研': 'eBPF + Rust (Aya) Research',
    'AFIDT (async fn in dyn trait) 跟踪': 'AFIDT (async fn in dyn trait) Tracking',
    'Rust 异步编程全面解析': 'Comprehensive Analysis of Rust Async Programming',
    'Rust 异步编程': 'Rust Async Programming',
    'Rust 1.96.0 稳定特性演示': 'Rust 1.96.0 Stable Features Demo',
    'Rust 1.96 特性跟踪': 'Rust 1.96 Feature Tracking',
    'Rust 1.97 异步特性演示': 'Rust 1.97 Async Features Demo',
    'Rust 1.98 Nightly 异步特性前瞻': 'Rust 1.98 Nightly Async Features Preview',
    '进程生命周期管理': 'Process Lifecycle Management',
    '进程生命周期管理器': 'Process Lifecycle Manager',
    '进程属性': 'Process Attributes',
    '进程控制': 'Process Control',
    '进程监控': 'Process Monitor',
    '进程池': 'Process Pool',
    '进程管理': 'Process Management',
    '进程安全': 'Process Safety',
    '进程间通信': 'Inter-process Communication',
    '共享内存区域': 'Shared Memory Region',
    '命名管道': 'Named Pipe',
    '消息队列': 'Message Queue',
    '高性能异步运行时': 'High-performance Async Runtime',
    '轻量级运行时': 'Lightweight Runtime',
    '流处理模块': 'Stream Processing Module',
    '批处理处理器': 'Batch Processor',
    '重试引擎': 'Retry Engine',
    '任务管理器': 'Task Manager',
    '退避策略': 'Backoff Strategy',
    '计算几何': 'Computational Geometry',
    '凸包（Andrew）与旋转卡壳直径': 'Convex Hull (Andrew) and Rotating Calipers Diameter',
    '凸包': 'Convex Hull',
    '旋转卡壳': 'Rotating Calipers',
    '逆时针顺序的顶点': 'Vertices in Counter-clockwise Order',
    '包含共线最外点': 'Including Outermost Collinear Points',
    '高级算法实现': 'Advanced Algorithm Implementation',
    '并行排序算法实现': 'Parallel Sorting Algorithm Implementation',
    '并行快速排序': 'Parallel Quicksort',
    '算法选择决策树': 'Algorithm Selection Decision Tree',
    '排序算法选择': 'Sorting Algorithm Selection',
    '搜索算法选择': 'Searching Algorithm Selection',
    '图算法选择': 'Graph Algorithm Selection',
    '动态规划 vs 贪心': 'Dynamic Programming vs Greedy',
    '并发与并行策略': 'Concurrency and Parallelism Strategy',
    'LeetCode 分类组织算法': 'LeetCode Categorized Algorithms',
    '按算法主题分类': 'Categorized by Algorithm Topics',
    '多实现方式': 'Multiple Implementation Methods',
    '同步、并行、异步实现': 'Synchronous, Parallel, and Async Implementations',
    '形式化验证': 'Formal Verification',
    '完整文档': 'Complete Documentation',
    '算法正确性证明': 'Algorithm Correctness Proof',
    '复杂度分析': 'Complexity Analysis',
    '主定理': 'Master Theorem',
    '摊还分析': 'Amortized Analysis',
    '性能优化实践': 'Performance Optimization Practice',
    '内存优化最佳实践': 'Memory Optimization Best Practices',
    '并发优化': 'Concurrency Optimization',
    '编译时优化': 'Compile-time Optimization',
    '运行时性能分析': 'Runtime Performance Analysis',
    'Miri 测试模块': 'Miri Test Module',
    '内存安全验证': 'Memory Safety Verification',
    '错误处理模块': 'Error Handling Module',
    '统一错误处理': 'Unified Error Handling',
    '数据库系统设计模式应用': 'Database System Design Pattern Application',
    '游戏引擎设计模式应用': 'Game Engine Design Pattern Application',
    '操作系统设计模式应用': 'OS Design Pattern Application',
    '组合模式工程案例': 'Combined Pattern Engineering Cases',
    '函数式编程模式': 'Functional Programming Patterns',
    '高阶函数模式': 'Higher-order Function Pattern',
    'map-reduce 模式': 'Map-reduce Pattern',
    'Web 框架设计模式': 'Web Framework Design Patterns',
    '设计模式错误处理': 'Design Pattern Error Handling',
    '设计模式通用错误类型': 'Design Pattern Common Error Type',
    '形式化验证示例': 'Formal Verification Examples',
    '类型级状态机': 'Type-level State Machine',
    '状态转换正确性': 'State Transition Correctness',
    '并发安全性证明': 'Concurrent Safety Proof',
    '不变量验证': 'Invariant Verification',
    '终止性证明': 'Termination Proof',
    '性能基准测试': 'Performance Benchmark',
    '性能基准测试结果': 'Performance Benchmark Results',
    'Rust 核心惯用法': 'Rust Core Idioms',
    '其他 Rust 核心惯用法': 'Other Rust Core Idioms',
    '单例模式错误': 'Singleton Pattern Error',
    '工厂模式错误': 'Factory Pattern Error',
    '代理模式错误': 'Proxy Pattern Error',
    '享元模式错误': 'Flyweight Pattern Error',
    '责任链模式错误': 'Chain of Responsibility Pattern Error',
    '归档的历史版本特性': 'Archived Historical Version Features',
    '当前活跃版本为': 'Currently Active Version is',
    '请使用最新模块获取最新特性': 'Please Use the Latest Module for Newest Features',
    '历史版本特性实现': 'Historical Version Features Implementation',
    '仅供学习参考': 'For Learning Reference Only',
    '综合演示函数': 'Comprehensive Demo Function',
    '数据验证管道': 'Data Validation Pipeline',
    '批量处理带错误控制': 'Batch Processing with Error Control',
    '搜索二维数组，找到目标时提前退出': 'Search 2D Array, Early Exit When Target Found',
}

WORD_DICT = {
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
    '接口': 'interface',
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
    '实践': 'practices',
    '最佳实践': 'best practices',
    '主定理': 'Master Theorem',
    '摊还分析': 'amortized analysis',
    '循环不变量': 'loop invariant',
    '霍尔逻辑': 'Hoare logic',
    '学习': 'learning',
    '参考': 'reference',
    '历史': 'historical',
    '版本': 'version',
    '活跃': 'active',
    '当前': 'current',
    '推荐': 'recommended',
    '最新': 'latest',
    '获取': 'get',
    '仅': 'only',
    '供': 'for',
    '保留': 'retained',
    '作为': 'as',
    '注意': 'Note',
    '重要': 'Important',
    '提示': 'Tip',
    '建议': 'Suggestion',
    '已弃用': 'Deprecated',
    '实验性': 'Experimental',
    '不稳定': 'Unstable',
    '预览': 'preview',
    '预研': 'research',
    '警告': 'Warning',
    '等于': 'equals',
    '大于': 'greater than',
    '小于': 'less than',
    '加': 'plus',
    '减': 'minus',
    '乘': 'multiply',
    '除': 'divide',
    '平方': 'square',
    '立方': 'cube',
    '根号': 'square root',
    '绝对值': 'absolute value',
    '最大值': 'maximum',
    '最小值': 'minimum',
    '平均值': 'average',
    '中位数': 'median',
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
    '的': 'of',
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
}


def translate_phrase(text):
    if text in PHRASE_DICT:
        return PHRASE_DICT[text]
    
    result = []
    i = 0
    while i < len(text):
        matched = False
        for cn in sorted(PHRASE_DICT.keys(), key=len, reverse=True):
            if text[i:i+len(cn)] == cn:
                result.append(PHRASE_DICT[cn])
                i += len(cn)
                matched = True
                break
        if not matched:
            for cn in sorted(WORD_DICT.keys(), key=len, reverse=True):
                if text[i:i+len(cn)] == cn:
                    result.append(WORD_DICT[cn])
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
    if not translated:
        return text
    return translated


def translate_line(text):
    original = text
    if not re.search(r'[\u4e00-\u9fff]', text):
        return text
    
    t = text.strip()
    
    # Pattern: 本模块提供了... -> This module provides ...
    m = re.match(r'^本模块提供了(.+)$', t)
    if m:
        return 'This module provides ' + translate_phrase(m.group(1))
    
    m = re.match(r'^本模块展示(.+)$', t)
    if m:
        return 'This module demonstrates ' + translate_phrase(m.group(1))
    
    m = re.match(r'^本模块实现(.+)$', t)
    if m:
        return 'This module implements ' + translate_phrase(m.group(1))
    
    m = re.match(r'^本模块包含(.+)$', t)
    if m:
        return 'This module contains ' + translate_phrase(m.group(1))
    
    m = re.match(r'^本模块是(.+)$', t)
    if m:
        return 'This module is ' + translate_phrase(m.group(1))
    
    m = re.match(r'^本库提供了(.+)$', t)
    if m:
        return 'This library provides ' + translate_phrase(m.group(1))
    
    m = re.match(r'^本库展示(.+)$', t)
    if m:
        return 'This library demonstrates ' + translate_phrase(m.group(1))
    
    m = re.match(r'^本文件(.+)$', t)
    if m:
        return 'This file ' + translate_phrase(m.group(1))
    
    m = re.match(r'^获取(.+)$', t)
    if m:
        return 'Get ' + translate_phrase(m.group(1))
    
    m = re.match(r'^创建新的?(.+)$', t)
    if m:
        return 'Create new ' + translate_phrase(m.group(1))
    
    m = re.match(r'^更新(.+)$', t)
    if m:
        return 'Update ' + translate_phrase(m.group(1))
    
    m = re.match(r'^注册(.+)$', t)
    if m:
        return 'Register ' + translate_phrase(m.group(1))
    
    m = re.match(r'^清理(.+)$', t)
    if m:
        return 'Cleanup ' + translate_phrase(m.group(1))
    
    m = re.match(r'^计算(.+)$', t)
    if m:
        return 'Compute ' + translate_phrase(m.group(1))
    
    m = re.match(r'^设置(.+)$', t)
    if m:
        return 'Set ' + translate_phrase(m.group(1))
    
    m = re.match(r'^运行(.+)$', t)
    if m:
        return 'Run ' + translate_phrase(m.group(1))
    
    m = re.match(r'^开始(.+)$', t)
    if m:
        return 'Start ' + translate_phrase(m.group(1))
    
    m = re.match(r'^完成(.+)$', t)
    if m:
        return 'Complete ' + translate_phrase(m.group(1))
    
    m = re.match(r'^搜索(.+)$', t)
    if m:
        return 'Search ' + translate_phrase(m.group(1))
    
    m = re.match(r'^测试(.+)$', t)
    if m:
        return 'Test ' + translate_phrase(m.group(1))
    
    m = re.match(r'^验证(.+)$', t)
    if m:
        return 'Verify ' + translate_phrase(m.group(1))
    
    m = re.match(r'^(.+)模块$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' module'
    
    m = re.match(r'^(.+)实现$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' implementation'
    
    m = re.match(r'^(.+)算法$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' algorithm'
    
    m = re.match(r'^(.+)管理器$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' manager'
    
    m = re.match(r'^(.+)接口$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' interface'
    
    m = re.match(r'^(.+)类型$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' type'
    
    m = re.match(r'^(.+)模式$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' pattern'
    
    m = re.match(r'^(.+)系统$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' system'
    
    m = re.match(r'^(.+)工具$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' tool'
    
    m = re.match(r'^(.+)函数$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' function'
    
    m = re.match(r'^(.+)方法$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' method'
    
    m = re.match(r'^(.+)结构体$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' struct'
    
    m = re.match(r'^(.+)枚举$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' enum'
    
    m = re.match(r'^(.+)示例$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' example'
    
    m = re.match(r'^(.+)测试$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' test'
    
    m = re.match(r'^(.+)应用$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' application'
    
    m = re.match(r'^(.+)案例$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' case'
    
    m = re.match(r'^(.+)解决方案$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' solution'
    
    m = re.match(r'^(.+)策略$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' strategy'
    
    m = re.match(r'^(.+)引擎$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' engine'
    
    m = re.match(r'^(.+)框架$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' framework'
    
    m = re.match(r'^(.+)运行时$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' runtime'
    
    m = re.match(r'^(.+)分析$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' analysis'
    
    m = re.match(r'^(.+)证明$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' proof'
    
    m = re.match(r'^(.+)验证$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' verification'
    
    m = re.match(r'^(.+)优化$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' optimization'
    
    m = re.match(r'^(.+)处理$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' processing'
    
    m = re.match(r'^(.+)设计$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' design'
    
    m = re.match(r'^(.+)排序$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' sort'
    
    m = re.match(r'^(.+)搜索$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' search'
    
    m = re.match(r'^(.+)查找$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' search'
    
    m = re.match(r'^(.+)查询$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' query'
    
    m = re.match(r'^(.+)遍历$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' traversal'
    
    m = re.match(r'^(.+)操作$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' operation'
    
    m = re.match(r'^(.+)提升$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' improvement'
    
    m = re.match(r'^(.+)性能$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' performance'
    
    m = re.match(r'^(.+)信息$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' information'
    
    m = re.match(r'^(.+)数据$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' data'
    
    m = re.match(r'^(.+)控制$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' control'
    
    m = re.match(r'^(.+)错误$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' error'
    
    m = re.match(r'^(.+)安全$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' safety'
    
    m = re.match(r'^(.+)状态$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' status'
    
    m = re.match(r'^(.+)机制$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' mechanism'
    
    m = re.match(r'^(.+)方式$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' method'
    
    m = re.match(r'^(.+)结果$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' result'
    
    m = re.match(r'^(.+)步骤$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' step'
    
    m = re.match(r'^(.+)流程$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' flow'
    
    m = re.match(r'^(.+)配置$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' configuration'
    
    m = re.match(r'^(.+)设置$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' setting'
    
    m = re.match(r'^(.+)对象$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' object'
    
    m = re.match(r'^(.+)值$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' value'
    
    m = re.match(r'^(.+)数量$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' count'
    
    m = re.match(r'^(.+)时间$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' time'
    
    m = re.match(r'^(.+)内存$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' memory'
    
    m = re.match(r'^(.+)空间$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' space'
    
    m = re.match(r'^(.+)资源$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' resource'
    
    m = re.match(r'^(.+)服务$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' service'
    
    m = re.match(r'^(.+)容器$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' container'
    
    m = re.match(r'^(.+)组件$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' component'
    
    m = re.match(r'^(.+)节点$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' node'
    
    m = re.match(r'^(.+)边$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' edge'
    
    m = re.match(r'^(.+)路径$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' path'
    
    m = re.match(r'^(.+)树$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' tree'
    
    m = re.match(r'^(.+)图$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' graph'
    
    m = re.match(r'^(.+)表$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' table'
    
    m = re.match(r'^(.+)数组$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' array'
    
    m = re.match(r'^(.+)队列$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' queue'
    
    m = re.match(r'^(.+)栈$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' stack'
    
    m = re.match(r'^(.+)集合$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' set'
    
    m = re.match(r'^(.+)映射$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' map'
    
    m = re.match(r'^(.+)列表$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' list'
    
    m = re.match(r'^(.+)字符串$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' string'
    
    m = re.match(r'^(.+)指针$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' pointer'
    
    m = re.match(r'^(.+)引用$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' reference'
    
    m = re.match(r'^(.+)切片$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' slice'
    
    m = re.match(r'^(.+)迭代器$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' iterator'
    
    m = re.match(r'^(.+)生成器$', t)
    if m and len(m.group(1)) > 1:
        return translate_phrase(m.group(1)) + ' generator'
    
    return translate_phrase(t)


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
        
        has_next_doc = False
        if i + 1 < len(lines):
            next_stripped = lines[i+1].lstrip()
            if next_stripped.startswith('///') or next_stripped.startswith('//!'):
                has_next_doc = True
        
        new_lines.append(line)
        
        if not has_next_doc:
            translated = translate_line(comment_text)
            if translated != comment_text:
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

print(f'Modified {len(modified_files)} files')
for f in modified_files:
    print(f)
