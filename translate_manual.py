#!/usr/bin/env python3
"""
Manual pattern-based translation of Chinese doc comments.
"""

import os
import re

# ============================================================================
# EXACT BLOCK TRANSLATIONS
# ============================================================================
EXACT_TRANSLATIONS = {
    "/// 安全相关错误": "/// Security-related errors",
    "/// 错误统计": "/// Error statistics",
    "/// 延迟初始化的协议处理器注册表": "/// Lazily initialized protocol handler registry",
    "/// 注册协议处理器": "/// Register protocol handler",
    "/// 服务器权重": "/// Server weight",
    "/// 批量处理带错误控制": "/// Batch processing with error control",
    "/// 池化字节": "/// Pooled bytes",
    "/// 吞吐量统计": "/// Throughput statistics",
    "/// 批量处理器": "/// Batch processor",
    "/// 连接统计信息": "/// Connection statistics",
    "/// 导出格式": "/// Export format",
    "/// 语义违规": "/// Semantic violations",
    "/// 语义验证器": "/// Semantic validator",
    "/// 语义模型": "/// Semantic model",
    "/// 虚拟模型检查器": "/// Virtual model checker",
    "/// 模型检查器": "/// Model checker",
    "/// 覆盖度统计": "/// Coverage statistics",
    "/// 避免名称冲突的模式": "/// Patterns to avoid name conflicts",
    "/// 静态注册表宏": "/// Static registry macro",
    "/// 单元测试简化宏": "/// Unit test simplification macro",
    "/// 宏调试信息": "/// Macro debug information",
    "/// 以太网帧头": "/// Ethernet frame header",
    "/// 获取导出信息": "/// Get export information",
    "/// 添加预打开目录": "/// Add pre-opened directory",
    "/// 获取预打开目录列表": "/// Get pre-opened directory list",
    "/// 安全的寄存器读取": "/// Safe register read",
    "/// 门状态": "/// Gate state",
    "/// 事件": "/// Event",
    "/// 异步返回一个数字的平方": "/// Asynchronously return the square of a number",
    "/// 异步计算两个数字的和": "/// Asynchronously compute the sum of two numbers",
    "/// 顺序执行两个异步操作并返回结果之和": "/// Sequentially execute two async operations and return the sum of results",
    "/// 并发计算多个数字的平方": "/// Concurrently compute the squares of multiple numbers",
    "/// 矩形": "/// Rectangle",
    "/// 配置错误": "/// Configuration error",
    "/// 返回面积最大的形状名称": "/// Return the name of the shape with the largest area",
    "/// 返回每种灯的持续时间（秒）": "/// Return the duration (in seconds) for each type of light",
    "/// 返回字符串的长度，同时保持原字符串可用": "/// Return the length of a string while keeping the original string available",
    "/// 返回字符串的第一个单词": "/// Return the first word of a string",
    "/// 返回字符串的字符数": "/// Return the character count of a string",
    "/// 返回切片中的最大元素": "/// Return the maximum element in a slice",
    "/// 返回先完成的 Future 的结果": "/// Return the result of the Future that completes first",
    "/// 返回以空格分割后的第一个字段": "/// Return the first field after splitting by whitespace",
    "/// 返回两个字符串切片中较长的一个": "/// Return the longer of two string slices",
    "/// 返回两个值中较大者的描述": "/// Return a description of the larger of two values",
    "/// 返回一个指向局部变量的原始指针": "/// Return a raw pointer to a local variable",
    "/// 返回一个固定的 C 字符串字面量": "/// Return a fixed C string literal",
    "/// 链式计算：先解析字符串，再计算平方根，最后加倍": "/// Chained computation: parse string, then compute square root, then double",
    "/// 链式操作：先解析，再检查范围，最后加倍": "/// Chained operations: parse first, then check range, then double",
    "/// 输入是一个 `Option<String>`：": "/// Input is an `Option<String>`:",
    "/// 验证配置项": "/// Validate configuration item",
    "/// 黄金分割搜索用于网络参数优化": "/// Golden-section search for network parameter optimization",
    "/// 验证配置": "/// Validate configuration",
    "/// 预期结果: 应该正确解析并访问 octets": "/// Expected result: should correctly parse and access octets",
    "/// 预期结果: 应该正确管理读写位置": "/// Expected result: should correctly manage read/write position",
    "/// 预期结果: 应该正确管理状态": "/// Expected result: should correctly manage state",
    "/// 预期结果: 应该正确提取各部分": "/// Expected result: should correctly extract each part",
    "/// 预期结果: 应该正确创建和访问": "/// Expected result: should correctly create and access",
    "/// 预期结果: 使用 addr_of! 和 read_unaligned 应该安全访问": "/// Expected result: should safely access using addr_of! and read_unaligned",
    "/// 需要使用嵌套 `if let` 或 `match`。": "/// Requires nested `if let` or `match`.",
    "/// 零拷贝缓冲区": "/// Zero-copy buffer",
    "/// 错误恢复策略": "/// Error recovery strategy",
    "/// 错误上下文扩展": "/// Error context extension",
    "/// 遥测配置": "/// Telemetry configuration",
    "/// 遥测守卫": "/// Telemetry guard",
    "/// 逻辑操作符": "/// Logical operators",
    "/// 连接统计信息": "/// Connection statistics",
    "/// 连接结构": "/// Connection structure",
    "/// 性能监控器": "/// Performance monitor",
    "/// 性能指标": "/// Performance metrics",
    "/// 性能报告": "/// Performance report",
    "/// 缓存统计信息": "/// Cache statistics",
    "/// 缓存实现": "/// Cache implementation",
    "/// 数据包序列化器": "/// Packet serializer",
    "/// 数据包解析器": "/// Packet parser",
}

# ============================================================================
# LINE-BY-LINE PHRASE TRANSLATIONS
# ============================================================================
PHRASE_MAP = {
    # Common nouns and phrases
    "网络编程": "network programming",
    "错误处理": "error handling",
    "模块": "module",
    "本模块": "this module",
    "本库": "this library",
    "本 crate": "this crate",
    "本文件": "this file",
    "提供了": "provides",
    "提供": "provides",
    "包含": "contains",
    "展示了": "demonstrates",
    "展示": "demonstrates",
    "定义了": "defines",
    "定义": "defines",
    "涵盖": "covering",
    "练习": "exercises",
    "道练习题": " exercises",
    "当前完成": "currently completed",
    "涵盖：": "covering:",
    "关键语言特性": "key language features",
    "工具链改进": "toolchain improvements",
    "新特性": "new features",
    "实现模块": "implementation module",
    "特性": "features",
    "示例代码": "example code",
    "核心示例": "core examples",
    "学习模块": "learning module",
    "编程练习库": "programming exercise library",
    "按主题分类": "categorized by topic",
    "覆盖": "covering",
    "核心概念": "core concepts",
    "每道练习题": "each exercise",
    "说明文档": "documentation",
    "测试用例": "test cases",
    "对应": "corresponds to",
    "下的": "under",
    "和": "and",
    "与": "and",
    "或": "or",
    "的": " ",
    "了": " ",
    "在": "in",
    "中": "in",
    "上": "on",
    "下": "under",
    "为": "for",
    "从": "from",
    "到": "to",
    "通过": "through",
    "使用": "using",
    "基于": "based on",
    "包括": "including",
    "如": "such as",
    "等": "etc.",
    "以及": "and",
    "及": "and",
    "并": "and",
    "可以": "can",
    "能够": "can",
    "需要": "needs",
    "必须": "must",
    "应该": "should",
    "将": "will",
    "会": "will",
    "已": "already",
    "已经": "already",
    "未": "not",
    "不": "not",
    "无": "no",
    "有": "has",
    "具有": "has",
    "用于": "used for",
    "用作": "used as",
    "作为": "as",
    "成为": "become",
    "表示": "represents",
    "代表": "represents",
    "描述": "describes",
    "说明": "describes",
    "介绍": "introduces",
    "解释": "explains",
    "展示": "shows",
    "显示": "shows",
    "演示": "demonstrates",
    "实现": "implementation",
    "方法": "method",
    "函数": "function",
    "结构体": "struct",
    "枚举": "enum",
    "特质": "trait",
    "类型": "type",
    "变量": "variable",
    "常量": "constant",
    "参数": "parameters",
    "返回值": "return value",
    "返回": "return",
    "获取": "get",
    "设置": "set",
    "创建": "create",
    "删除": "delete",
    "更新": "update",
    "读取": "read",
    "写入": "write",
    "计算": "compute",
    "处理": "process",
    "分析": "analyze",
    "检查": "check",
    "验证": "validate",
    "测试": "test",
    "运行": "run",
    "执行": "execute",
    "调用": "invoke",
    "引用": "reference",
    "借用": "borrow",
    "所有权": "ownership",
    "生命周期": "lifetime",
    "泛型": "generics",
    "模式匹配": "pattern matching",
    "闭包": "closure",
    "迭代器": "iterator",
    "异步": "async",
    "并发": "concurrency",
    "线程": "thread",
    "通道": "channel",
    "锁": "lock",
    "原子": "atomic",
    "指针": "pointer",
    "引用计数": "reference counting",
    "智能指针": "smart pointer",
    "不安全": "unsafe",
    "安全": "safe",
    "内存": "memory",
    "性能": "performance",
    "优化": "optimization",
    "效率": "efficiency",
    "速度": "speed",
    "缓存": "cache",
    "缓冲区": "buffer",
    "序列化": "serialization",
    "反序列化": "deserialization",
    "编码": "encoding",
    "解码": "decoding",
    "压缩": "compression",
    "加密": "encryption",
    "解密": "decryption",
    "哈希": "hash",
    "签名": "signature",
    "证书": "certificate",
    "协议": "protocol",
    "连接": "connection",
    "断开": "disconnect",
    "重连": "reconnect",
    "超时": "timeout",
    "重试": "retry",
    "心跳": "heartbeat",
    "负载均衡": "load balancing",
    "流量控制": "flow control",
    "拥塞控制": "congestion control",
    "路由": "routing",
    "转发": "forwarding",
    "代理": "proxy",
    "网关": "gateway",
    "防火墙": "firewall",
    "过滤器": "filter",
    "中间件": "middleware",
    "拦截器": "interceptor",
    "处理器": "handler",
    "适配器": "adapter",
    "转换器": "converter",
    "包装器": "wrapper",
    "装饰器": "decorator",
    "工厂": "factory",
    "构建器": "builder",
    "单例": "singleton",
    "观察者": "observer",
    "发布订阅": "pub/sub",
    "生产者": "producer",
    "消费者": "consumer",
    "队列": "queue",
    "栈": "stack",
    "堆": "heap",
    "树": "tree",
    "图": "graph",
    "表": "table",
    "映射": "map",
    "集合": "set",
    "列表": "list",
    "数组": "array",
    "向量": "vector",
    "切片": "slice",
    "字符串": "string",
    "字节": "bytes",
    "字符": "character",
    "整数": "integer",
    "浮点数": "floating point",
    "布尔": "boolean",
    "空": "empty",
    "可选": "optional",
    "结果": "result",
    "错误": "error",
    "异常": "exception",
    "恐慌": "panic",
    "断言": "assertion",
    "假设": "assumption",
    "前提": "precondition",
    "后置条件": "postcondition",
    "不变量": "invariant",
    "约束": "constraint",
    "限制": "limitation",
    "边界": "boundary",
    "范围": "range",
    "域": "domain",
    "作用域": "scope",
    "上下文": "context",
    "环境": "environment",
    "状态": "state",
    "事件": "event",
    "动作": "action",
    "操作": "operation",
    "行为": "behavior",
    "属性": "property",
    "字段": "field",
    "成员": "member",
    "元素": "element",
    "项": "item",
    "条目": "entry",
    "记录": "record",
    "日志": "log",
    "跟踪": "trace",
    "调试": "debug",
    "信息": "information",
    "消息": "message",
    "通知": "notification",
    "警告": "warning",
    "致命": "fatal",
    "严重": "critical",
    "重要": "important",
    "主要": "main",
    "次要": "secondary",
    "辅助": "auxiliary",
    "基础": "basic",
    "基本": "basic",
    "高级": "advanced",
    "初级": "beginner",
    "中级": "intermediate",
    "专家": "expert",
    "简单": "simple",
    "复杂": "complex",
    "困难": "difficult",
    "容易": "easy",
    "快速": "fast",
    "慢速": "slow",
    "大": "large",
    "小": "small",
    "长": "long",
    "短": "short",
    "高": "high",
    "低": "low",
    "多": "many",
    "少": "few",
    "全部": "all",
    "部分": "partial",
    "完整": "complete",
    "不完整": "incomplete",
    "正确": "correct",
    "错误": "incorrect",
    "有效": "valid",
    "无效": "invalid",
    "成功": "success",
    "失败": "failure",
    "正常": "normal",
    "异常": "abnormal",
    "标准": "standard",
    "规范": "specification",
    "格式": "format",
    "模板": "template",
    "模式": "pattern",
    "实例": "instance",
    "示例": "example",
    "样例": "sample",
    "案例": "case",
    "用例": "use case",
    "场景": "scenario",
    "情况": "situation",
    "条件": "condition",
    "配置": "configuration",
    "选项": "option",
    "设置": "settings",
    "默认值": "default value",
    "初始值": "initial value",
    "当前值": "current value",
    "旧值": "old value",
    "新值": "new value",
    "最大值": "maximum value",
    "最小值": "minimum value",
    "平均值": "average value",
    "总和": "sum",
    "数量": "count",
    "长度": "length",
    "大小": "size",
    "容量": "capacity",
    "宽度": "width",
    "高度": "height",
    "深度": "depth",
    "比例": "ratio",
    "百分比": "percentage",
    "频率": "frequency",
    "速率": "rate",
    "比例": "proportion",
    "分布": "distribution",
    "密度": "density",
    "浓度": "concentration",
    "精度": "precision",
    "准确度": "accuracy",
    "容错": "fault tolerance",
    "可靠": "reliable",
    "可用": "available",
    "可扩展": "scalable",
    "可维护": "maintainable",
    "可测试": "testable",
    "可移植": "portable",
    "兼容": "compatible",
    "互操作": "interoperable",
    "独立": "independent",
    "依赖": "dependent",
    "耦合": "coupled",
    "解耦": "decoupled",
    "内聚": "cohesive",
    "松散": "loose",
    "紧密": "tight",
    "灵活": "flexible",
    "僵硬": "rigid",
    "动态": "dynamic",
    "静态": "static",
    "全局": "global",
    "局部": "local",
    "内部": "internal",
    "外部": "external",
    "公开": "public",
    "私有": "private",
    "保护": "protected",
    "继承": "inheritance",
    "多态": "polymorphism",
    "封装": "encapsulation",
    "抽象": "abstraction",
    "接口": "interface",
    "实现": "implementation",
    "具体": "concrete",
    "虚拟": "virtual",
    "覆盖": "override",
    "重载": "overload",
    "隐藏": "hide",
    "暴露": "expose",
    "访问": "access",
    "修改": "modify",
    "只读": "read-only",
    "只写": "write-only",
    "读写": "read-write",
    "同步": "synchronous",
    "阻塞": "blocking",
    "非阻塞": "non-blocking",
    "等待": "wait",
    "通知": "notify",
    "唤醒": "wake",
    "休眠": "sleep",
    "暂停": "pause",
    "恢复": "resume",
    "停止": "stop",
    "开始": "start",
    "启动": "launch",
    "关闭": "shutdown",
    "初始化": "initialize",
    "清理": "cleanup",
    "释放": "release",
    "分配": "allocate",
    "回收": "reclaim",
    "重用": "reuse",
    "复制": "copy",
    "克隆": "clone",
    "移动": "move",
    "交换": "swap",
    "替换": "replace",
    "合并": "merge",
    "拆分": "split",
    "连接": "join",
    "分离": "separate",
    "排序": "sort",
    "搜索": "search",
    "查找": "find",
    "匹配": "match",
    "比较": "compare",
    "排序": "ordering",
    "过滤": "filter",
    "映射": "map",
    "归约": "reduce",
    "折叠": "fold",
    "扫描": "scan",
    "收集": "collect",
    "生成": "generate",
    "构造": "construct",
    "解构": "deconstruct",
    "转换": "transform",
    "映射": "mapping",
    "投影": "projection",
    "选择": "selection",
    "聚合": "aggregation",
    "分组": "grouping",
    "分区": "partitioning",
    "切片": "slicing",
    "索引": "indexing",
    "定位": "positioning",
    "偏移": "offset",
    "对齐": "alignment",
    "填充": "padding",
    "打包": "packing",
    "解包": "unpacking",
    "序列": "sequence",
    "流": "stream",
    "管道": "pipeline",
    "通道": "channel",
    "套接字": "socket",
    "端口": "port",
    "地址": "address",
    "主机": "host",
    "客户端": "client",
    "服务器": "server",
    "服务端": "server",
    "请求": "request",
    "响应": "response",
    "头部": "header",
    "主体": "body",
    "负载": "payload",
    "内容": "content",
    "数据": "data",
    "元数据": "metadata",
    "原始数据": "raw data",
    "二进制": "binary",
    "文本": "text",
    "JSON": "JSON",
    "XML": "XML",
    "YAML": "YAML",
    "CSV": "CSV",
    "HTML": "HTML",
    "URL": "URL",
    "URI": "URI",
    "IP": "IP",
    "TCP": "TCP",
    "UDP": "UDP",
    "HTTP": "HTTP",
    "HTTPS": "HTTPS",
    "WebSocket": "WebSocket",
    "gRPC": "gRPC",
    "REST": "REST",
    "API": "API",
    "SDK": "SDK",
    "CLI": "CLI",
    "GUI": "GUI",
    "UI": "UI",
    "UX": "UX",
    "OS": "OS",
    "CPU": "CPU",
    "GPU": "GPU",
    "RAM": "RAM",
    "ROM": "ROM",
    "SSD": "SSD",
    "HDD": "HDD",
    "I/O": "I/O",
    "输入": "input",
    "输出": "output",
    "标准输入": "standard input",
    "标准输出": "standard output",
    "标准错误": "standard error",
    "文件系统": "file system",
    "目录": "directory",
    "路径": "path",
    "文件名": "filename",
    "扩展名": "extension",
    "权限": "permissions",
    "所有者": "owner",
    "组": "group",
    "用户": "user",
    "系统": "system",
    "内核": "kernel",
    "驱动": "driver",
    "固件": "firmware",
    "硬件": "hardware",
    "软件": "software",
    "应用": "application",
    "程序": "program",
    "进程": "process",
    "服务": "service",
    "守护进程": "daemon",
    "容器": "container",
    "镜像": "image",
    "虚拟机": "virtual machine",
    "集群": "cluster",
    "节点": "node",
    "副本": "replica",
    "分片": "shard",
    "分区": "partition",
    "命名空间": "namespace",
    "资源": "resource",
    "配额": "quota",
    "限制": "limit",
    "预留": "reserve",
    "预留接口": "reserved interface",
    "抽象": "abstraction",
    "抽象（预留接口）": "abstraction (reserved interface)",
    "可达性": "reachability",
    "端口映射": "port mapping",
    "身份": "identity",
    "密钥管理": "key management",
    "节点": "node",
    "节点身份": "node identity",
    "节点发现": "node discovery",
    "发布订阅": "publish-subscribe",
    "抓包": "packet capture",
    "流量分析": "traffic analysis",
    "入口": "entry",
    "工具": "tools",
    "辅助工具": "utilities",
    "开发辅助工具": "development utilities",
    "地址工具": "address tools",
    "协议层": "protocol layer",
    "跨平台": "cross-platform",
    "说明": "description",
    "高性能": "high-performance",
    "现代": "modern",
    "安全传输": "secure transport",
    "传输协议": "transport protocol",
    "实时中断": "real-time interrupt",
    "驱动并发": "driven concurrency",
    "实时中断驱动并发": "real-time interrupt-driven concurrency",
    "硬件抽象层": "hardware abstraction layer",
    "设计模式": "design patterns",
    "内存映射": "memory-mapped",
    "寄存器": "registers",
    "中断处理": "interrupt handling",
    "启动代码": "startup code",
    "panic handler": "panic handler",
    "全局分配器": "global allocator",
    "概念说明": "concept description",
    "概念": "concept",
    "作用": "purpose",
    "启动序列": "startup sequence",
    "序列描述": "sequence description",
    "复位": "reset",
    "初始化": "initialization",
    "复制": "copy",
    "清零": "zero",
    "调用": "call",
    "无限循环": "infinite loop",
    "硬件复位": "hardware reset",
    "看门狗": "watchdog",
    "调试": "debugging",
    "串口": "serial port",
    "LED": "LED",
    "闪烁": "blinking",
    "写入": "write",
    "触发": "trigger",
    "发散函数": "diverging function",
    "永不返回": "never returns",
    "向量表": "vector table",
    "栈指针": "stack pointer",
    "Flash": "Flash",
    "RAM": "RAM",
    "全局变量": "global variables",
    "已初始化": "initialized",
    "未初始化": "uninitialized",
    "复位向量": "reset vector",
    "启动代码": "startup code",
    "用户代码": "user code",
    "Cortex-M": "Cortex-M",
    "异步嵌入式框架": "async embedded framework",
    "异步框架": "async framework",
    "嵌入式框架": "embedded framework",
    "Bare-metal": "Bare-metal",
    "基础概念": "basic concepts",
    "演示": "demonstrates",
    "表示": "represents",
    "不使用": "does not use",
    "标准库": "standard library",
    "核心": "core",
    "启动": "startup",
    "接管": "take over",
    "由...接管": "taken over by",
    "启动代码或": "startup code or",
    "自动处理": "automatically handles",
    "这些步骤": "these steps",
    "负责": "responsible for",
    "没有操作系统加载器": "no OS loader",
    "直接从": "directly from",
    "开始执行": "starts execution",
    "提供": "provides",
    "必须": "must",
    "一个": "a",
    "在...环境中": "in ... environment",
    "真实硬件上": "on real hardware",
    "通常进入": "usually enters",
    "或触发": "or triggers",
    "因为": "because",
    "系统无法恢复": "system cannot recover",
    "常用的": "commonly used",
    "通过": "through",
    "输出到": "output to",
    "调试器": "debugger",
    "仅 Cortex-M": "Cortex-M only",
    "ITM": "ITM",
    "输出调试信息": "output debug information",
    " semihosting ": " semihosting ",
    "如果需要使用": "if you need to use",
    "必须提供": "must provide",
    "全局分配器": "global allocator",
    "等": "etc.",
    "可选": "optional",
}

# Sort by length descending for greedy matching
PHRASES_SORTED = sorted(PHRASE_MAP.items(), key=lambda x: len(x[0]), reverse=True)


def translate_line(line):
    """Translate a single doc comment line using phrase dictionary."""
    # Skip non-doc-comment lines
    if not line.startswith("///") and not line.startswith("//!"):
        return line

    prefix = "///" if line.startswith("///") else "//!"
    rest = line[len(prefix):]
    if rest.startswith(" "):
        rest = rest[1:]

    # Skip empty lines and code blocks
    if not rest.strip() or rest.strip().startswith("```") or rest.strip().startswith("|"):
        return line

    # Skip lines that are mostly English already
    if len(re.findall(r'[a-zA-Z]', rest)) > len(re.findall(r'[\u4e00-\u9fff]', rest)) * 2:
        return line

    # Skip markdown headers that are already English
    if rest.strip().startswith("#") and len(re.findall(r'[\u4e00-\u9fff]', rest)) == 0:
        return line

    translated = rest
    for ch, en in PHRASES_SORTED:
        translated = translated.replace(ch, en)

    # Clean up extra spaces
    translated = re.sub(r'  +', ' ', translated).strip()

    # If translation didn't change anything and still has Chinese, skip
    if translated == rest and re.search(r'[\u4e00-\u9fff]', translated):
        return None  # Can't translate

    return prefix + " " + translated


def translate_block(block_text):
    """Translate a doc comment block."""
    lines = block_text.split("\n")
    translated_lines = []
    has_translation = False

    for line in lines:
        exact_match = EXACT_TRANSLATIONS.get(line.strip())
        if exact_match:
            translated_lines.append(exact_match)
            has_translation = True
        else:
            translated = translate_line(line)
            if translated and translated != line:
                translated_lines.append(translated)
                has_translation = True
            elif translated is None:
                # Can't translate this line, skip the whole block
                return None
            else:
                translated_lines.append(line)

    if has_translation:
        return "\n".join(translated_lines)
    return None


def process_file(filepath):
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    lines = content.split("\n")
    new_lines = []
    i = 0
    modified = False
    skipped_blocks = []

    while i < len(lines):
        line = lines[i]
        if line.startswith("///") or line.startswith("//!"):
            block_type = "///" if line.startswith("///") else "//!"
            block_lines = []
            while i < len(lines) and lines[i].startswith(block_type):
                block_lines.append(lines[i])
                i += 1
            block_text = "\n".join(block_lines)

            if re.search(r"[\u4e00-\u9fff]", block_text):
                # Check if next block is English
                already_english = False
                if i < len(lines) and lines[i].startswith(block_type):
                    next_lines = []
                    next_i = i
                    while next_i < len(lines) and lines[next_i].startswith(block_type):
                        next_lines.append(lines[next_i])
                        next_i += 1
                    next_text = "\n".join(next_lines)
                    if not re.search(r"[\u4e00-\u9fff]", next_text):
                        already_english = True

                if not already_english:
                    translated = translate_block(block_text)
                    if translated:
                        new_lines.extend(block_lines)
                        new_lines.extend(translated.split("\n"))
                        modified = True
                    else:
                        skipped_blocks.append((filepath, block_text))
                        new_lines.extend(block_lines)
                else:
                    new_lines.extend(block_lines)
            else:
                new_lines.extend(block_lines)
        else:
            new_lines.append(line)
            i += 1

    if modified:
        with open(filepath, "w", encoding="utf-8") as f:
            f.write("\n".join(new_lines))

    return modified, skipped_blocks


def main():
    directories = [
        "crates/c10_networks/src",
        "crates/c11_macro_system/src",
        "crates/c11_macro_system_proc/src",
        "crates/c12_wasm/src",
        "crates/c13_embedded/src",
        "exercises/src",
    ]

    modified_files = []
    all_skipped = []

    for d in directories:
        if not os.path.exists(d):
            continue
        for root, _, files in os.walk(d):
            for fname in files:
                if fname.endswith(".rs"):
                    filepath = os.path.join(root, fname)
                    modified, skipped = process_file(filepath)
                    if modified:
                        modified_files.append(filepath)
                    all_skipped.extend(skipped)

    print(f"Modified {len(modified_files)} files")
    for f in modified_files:
        print(f"  {f}")

    if all_skipped:
        print(f"\nSkipped {len(all_skipped)} blocks:")
        for fp, block in all_skipped[:50]:
            print(f"  {fp}: {block[:80].replace(chr(10), ' | ')}")


if __name__ == "__main__":
    main()
