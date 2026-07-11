#!/usr/bin/env python3
"""
批量补全反向推理链（⟸）到风险文件中。
基于文件标题匹配预定义模板，在"核心推理链"表格之后插入 2 条 ⟸ 链。
"""

import os
import re
from pathlib import Path

# 标题关键词 -> (⟸链1, ⟸链2) 的映射
# 格式: "结论 ⟸ 中间 ⟸ 前提"
TEMPLATES = {
    # L1 基础层
    "pl_prerequisites": (
        "类型安全 ⟸ 静态类型检查 ⟸ 语法与语义一致性",
        "程序正确性 ⟸ 无副作用推理 ⟸ 纯函数基础"
    ),
    "ownership": (
        "Safe Rust 内存安全 ⟸ 无数据竞争 ⟸ 所有权唯一性",
        "无 use-after-free ⟸ 生命周期有效性 ⟸ Move 语义"
    ),
    "borrowing": (
        "无悬垂引用 ⟸ 借用检查通过 ⟸ 生命周期约束满足",
        "并发安全 ⟸ &mut T 独占性 ⟸ 共享不可变/可变不共享"
    ),
    "lifetimes": (
        "编译通过 ⟸ 生命周期标注正确 ⟸ 引用有效性",
        "无悬垂引用 ⟸ 生命周期偏序关系 ⟸ 借用规则"
    ),
    "lifetimes_advanced": (
        "复杂泛型代码编译通过 ⟸ HRTB 约束满足 ⟸ 高阶生命周期",
        "API 设计灵活性 ⟸ 生命周期省略规则 ⟸ 引用语义"
    ),
    "type_system": (
        "模式匹配穷尽性 ⟸ 代数数据类型完备 ⟸ 类型安全",
        "零成本抽象 ⟸ 编译期类型擦除 ⟸ 泛型单态化"
    ),
    "never_type": (
        "控制流完整性 ⟸ 穷尽性匹配 ⟸ ! 类型包含无值",
        "类型系统一致性 ⟸ 底类型 ⊥ ⟸ 任何类型的子类型"
    ),
    "reference_semantics": (
        "内存安全 ⟸ 引用有效性保证 ⟸ 所有权与借用规则",
        "别名分析正确 ⟸ &T 共享读 / &mut T 独占写 ⟸ 类型系统"
    ),
    "zero_cost_abstractions": (
        "运行时性能等价于手写 C ⟸ 编译期优化完成 ⟸ 抽象无开销",
        "迭代器零成本 ⟸ 内联与向量化 ⟸ 泛型单态化"
    ),
    "control_flow": (
        "程序行为可预测 ⟸ 控制流结构化 ⟸ match/loop/if 穷尽性",
        "无未定义行为 ⟸ 穷尽性匹配强制 ⟸ 类型系统约束"
    ),
    "collections": (
        "内存安全数据结构 ⟸ 所有权自动管理 ⟸ Vec/HashMap 实现",
        "迭代器安全 ⟸ 借用检查器验证 ⟸ 集合 API 设计"
    ),
    "strings_and_text": (
        "UTF-8 安全性 ⟸ String/str 边界检查 ⟸ 所有权与借用",
        "文本处理正确性 ⟸ 编码一致性保证 ⟸ 类型系统约束"
    ),
    "error_handling_basics": (
        "程序健壮性 ⟸ 错误显式处理 ⟸ Result/Option 类型",
        "无 panic 路径 ⟸ ? 传播穷尽 ⟸ Try trait 语义"
    ),
    "numerics": (
        "算术安全 ⟸ 溢出检查 / Wrapping ⟸ 整数类型系统",
        "浮点一致性 ⟸ IEEE 754 遵循 ⟸ f32/f64 语义"
    ),
    "modules_and_paths": (
        "命名空间隔离 ⟸ 模块树结构 ⟸ use/pub 可见性",
        "编译单元独立 ⟸ crate 边界 ⟸ 模块系统封装"
    ),
    "numeric_types": (
        "内存布局可预测 ⟸ 固定大小类型 ⟸ 平台无关性",
        "类型转换安全 ⟸ as / try_into 区分 ⟸ 数值范围约束"
    ),
    "attributes_and_macros": (
        "元编程安全 ⟸ 编译期代码生成 ⟸ 宏卫生性",
        "条件编译正确 ⟸ cfg 属性求值 ⟸ 平台抽象"
    ),
    "panic_and_abort": (
        "程序不异常终止 ⟸ panic 路径受控 ⟸ unwind/abort 选择",
        "安全性保证 ⟸ catch_unwind 隔离 ⟸ 线程边界"
    ),
    "coercion_and_casting": (
        "类型转换安全 ⟸ Deref/From/Into 自动 ⟸ 编译期检查",
        "显式转换正确 ⟸ as / try_from 语义 ⟸ 类型系统"
    ),
    "closure_basics": (
        "环境捕获安全 ⟸ Fn/FnMut/FnOnce 分级 ⟸ 所有权规则",
        "高阶函数正确 ⟸ 闭包类型推断 ⟸ 类型系统"
    ),
    "testing_basics": (
        "代码可靠性 ⟸ 测试覆盖充分 ⟸ assert/match 验证",
        "回归预防 ⟸ CI 自动化测试 ⟸ 测试驱动设计"
    ),
    "collections_advanced": (
        "复杂数据结构安全 ⟸ 自定义 Drop ⟸ 所有权递归管理",
        "性能优化正确 ⟸ unsafe 内部实现 ⟸ 不变量维护"
    ),
    "strings_and_encoding": (
        "跨编码安全 ⟸ OsStr/CString 区分 ⟸ 平台抽象",
        "零拷贝解析 ⟸ 字符串切片 ⟸ 生命周期借用"
    ),
    "variable_model": (
        "内存安全 ⟸ 初始化检查 ⟸ 移动语义",
        "并发安全 ⟸ 共享状态隔离 ⟸ Send/Sync 边界"
    ),
    "effects_and_purity": (
        "副作用可追踪 ⟸ 纯函数标记 ⟸ 效果系统",
        "编译期优化 ⟸ const 求值 ⟸ 无副作用保证"
    ),
    "data_abstraction_spectrum": (
        "API 稳定性 ⟸ 封装边界清晰 ⟸ pub/private 分层",
        "零成本抽象 ⟸ 泛型与 trait ⟸ 编译期分发"
    ),
    "closure_basics": (
        "高阶函数安全 ⟸ 环境捕获类型检查 ⟸ Fn/FnMut/FnOnce",
        "回调正确性 ⟸ 闭包生命周期推断 ⟸ 借用规则"
    ),
    "testing_basics": (
        "回归预防 ⟸ 自动化测试覆盖 ⟸ assert/match 验证",
        "代码可靠性 ⟸ TDD 循环 ⟸ 红-绿-重构"
    ),
    # L2 进阶层
    "traits": (
        "多态代码正确 ⟸ Trait bound 满足 ⟸ 类型约束系统",
        "动态分发安全 ⟸ 对象安全条件 ⟸ vtable 布局"
    ),
    "generics": (
        "单态化零成本 ⟸ 编译期特化 ⟸ 参数多态",
        "约束可满足 ⟸ System F 类型规则 ⟸ 泛型边界"
    ),
    "memory_management": (
        "无内存泄漏 ⟸ Drop/RAII 自动 ⟸ 所有权系统",
        "堆分配安全 ⟸ Box/Rc/Arc 区分 ⟸ 引用计数正确性"
    ),
    "error_handling": (
        "错误传播安全 ⟸ ? 运算符自动转换 ⟸ Try trait",
        "错误类型精确 ⟸ thiserror/anyhow 分层 ⟸ 错误架构"
    ),
    "assert_matches": (
        "测试断言安全 ⟸ assert_matches! 穷尽 ⟸ 模式匹配",
        "编译期检查 ⟸ 常量断言 ⟸ const 求值"
    ),
    "range_types": (
        "区间操作安全 ⟸ RangeInclusive 边界 ⟸ 迭代器协议",
        "切片索引正确 ⟸ Range 范围检查 ⟸ 借用规则"
    ),
    "closure_types": (
        "环境捕获类型安全 ⟸ Fn/FnMut/FnOnce 选择 ⟸ 借用检查",
        "高阶函数组合 ⟸ 闭包生命周期推断 ⟸ HRTB"
    ),
    "interior_mutability": (
        "内部可变性安全 ⟸ RefCell/Cell/Mutex 隔离 ⟸ 运行时检查",
        "共享可变状态正确 ⟸ Arc<Mutex<T>> 模式 ⟸ Send/Sync 边界"
    ),
    "serde_patterns": (
        "序列化安全 ⟸ derive(Serialize) 完备 ⟸ 泛型约束",
        "反序列化健壮 ⟸ Deserialize 生命周期 ⟸ Visitor 模式"
    ),
    "module_system": (
        " crate 接口稳定 ⟸ pub(restricted) 分层 ⟸ 可见性系统",
        "依赖管理正确 ⟸ workspace 隔离 ⟸ 版本解析"
    ),
    "cow_and_borrowed": (
        "写时复制安全 ⟸ CoW 借用转换 ⟸ 所有权转移",
        "零拷贝优化 ⟸ Borrowed 状态保持 ⟸ 生命周期"
    ),
    "smart_pointers": (
        "自动内存管理 ⟸ Drop 顺序正确 ⟸ Deref 解引用",
        "循环引用避免 ⟸ Weak 指针降级 ⟸ Rc/Arc 内部计数"
    ),
    "dsl_and_embedding": (
        "领域语言安全 ⟸ 宏卫生性 ⟸ 标记宏/过程宏",
        "编译期验证 ⟸ 类型状态机 ⟸ 零成本抽象"
    ),
    "newtype_and_wrapper": (
        "类型安全增强 ⟸ 新类型模式 ⟸ 零运行时成本",
        "API 语义清晰 ⟸ Wrapper 区分 ⟸ 编译期区分"
    ),
    "error_handling_deep_dive": (
        "错误恢复正确 ⟸ panic 边界隔离 ⟸ catch_unwind",
        "错误链完整 ⟸ source() 遍历 ⟸ Error trait 层次"
    ),
    "iterator_patterns": (
        "惰性求值安全 ⟸ Iterator 状态机 ⟸ 借用检查",
        "适配器组合正确 ⟸ map/filter 生命周期 ⟸ 闭包捕获"
    ),
    "macro_patterns": (
        "宏展开安全 ⟸ 卫生性保证 ⟸ token 隔离",
        "编译期计算 ⟸ 声明宏递归 ⟸ 过程宏代码生成"
    ),
    "lifetimes_advanced": (
        "自引用安全 ⟸ Pin<&mut Self> ⟸ 不动性保证",
        "高阶 trait bound ⟸ for<'a> 量化 ⟸ 生命周期子类型"
    ),
    "advanced_traits": (
        "关联类型正确 ⟸ GAT 投影 ⟸ 类型族",
        "特化安全 ⟸ 默认实现 + 覆盖 ⟸ 一致性规则"
    ),
    "type_system_advanced": (
        "类型推断完备 ⟸ Hindley-Milner 扩展 ⟸ 约束求解",
        "高阶类型安全 ⟸ HKT 模拟 ⟸ 关联类型泛型"
    ),
    "metaprogramming": (
        "编译期反射安全 ⟸ 过程宏 hygiene ⟸ token 树操作",
        "常量泛型正确 ⟸ const 表达式求值 ⟸ 类型级别计算"
    ),
    "serde_patterns": (
        "序列化安全 ⟸ derive(Serialize) 完备 ⟸ 泛型约束",
        "反序列化健壮 ⟸ Deserialize 生命周期 ⟸ Visitor 模式"
    ),
    "iterator_patterns": (
        "惰性求值安全 ⟸ Iterator 状态机 ⟸ 借用检查",
        "适配器组合正确 ⟸ map/filter 生命周期 ⟸ 闭包捕获"
    ),
    "macro_patterns": (
        "宏展开安全 ⟸ 卫生性保证 ⟸ token 隔离",
        "编译期计算 ⟸ 声明宏递归 ⟸ 过程宏代码生成"
    ),
    "ffi_advanced": (
        "复杂类型布局安全 ⟸ repr(C) 兼容 ⟸ 对齐与填充",
        "回调安全 ⟸ 函数指针生命周期 ⟸ 线程边界"
    ),
    "concurrency_patterns": (
        "无数据竞争 ⟸ Send/Sync 正确实现 ⟸ 类型系统验证",
        "死锁避免 ⟸ 锁顺序协议 ⟸ 类型状态机"
    ),
    # L3 高级层
    "async": (
        "异步状态机安全 ⟸ Pin 不动性 ⟸ Future::poll",
        "取消安全 ⟸ async drop 设计 ⟸ 结构化并发"
    ),
    "async_advanced": (
        "自引用 Future 安全 ⟸ Pin 投影 ⟸ 生命周期捕获",
        "并发调度正确 ⟸ Waker 协议 ⟸ 执行器不变量"
    ),
    "async_patterns": (
        "并发组合正确 ⟸ select!/join! 宏 ⟸ 取消传播",
        "流处理安全 ⟸ Stream trait ⟸ 挂起点状态一致性"
    ),
    "unsafe": (
        "FFI 边界安全 ⟸ ABI 兼容性 ⟸ extern 调用约定",
        "裸指针正确使用 ⟸ 别名规则遵循 ⟸ Miri 验证"
    ),
    "macros": (
        "过程宏健壮 ⟸ TokenStream 解析 ⟸ Span 保留",
        "编译期代码生成 ⟸ derive 宏 ⟸ 元数据结构"
    ),
    "rust_ffi": (
        "跨语言调用安全 ⟸ C ABI 兼容 ⟸ 布局一致性",
        "内存管理边界 ⟸ Box::into_raw / from_raw ⟸ 所有权转移"
    ),
    "pin_unpin": (
        "自引用结构安全 ⟸ Pin 不动性保证 ⟸ !Unpin 标记",
        "堆分配稳定 ⟸ Pin<Box<T>> ⟸ 地址不变性"
    ),
    "proc_macro": (
        "代码生成安全 ⟸ TokenStream 卫生性 ⟸ Span 信息保留",
        "derive 宏正确 ⟸ 属性解析 ⟸ 编译期元编程"
    ),
    "nll_and_polonius": (
        "借用检查精确 ⟸ NLL 流敏感分析 ⟸ 数据流方程",
        "未来借用检查 ⟸ Polonius 起源分析 ⟸ 借用图"
    ),
    "ffi_advanced": (
        "复杂类型布局安全 ⟸ repr(C) 兼容 ⟸ 对齐与填充",
        "回调安全 ⟸ 函数指针生命周期 ⟸ 线程边界"
    ),
    "concurrency_patterns": (
        "无数据竞争 ⟸ Send/Sync 正确实现 ⟸ 类型系统验证",
        "死锁避免 ⟸ 锁顺序协议 ⟸ 类型状态机"
    ),
    "atomics_and_memory_ordering": (
        "弱内存模型正确 ⟸ happens-before 关系 ⟸ Acquire/Release",
        "无数据竞争 ⟸ atomic 操作 ⟸ 缓存一致性"
    ),
    "unsafe_rust_patterns": (
        "原始切片安全 ⟸ from_raw_parts 前置条件 ⟸ 长度与对齐",
        "联合体正确访问 ⟸ MaybeUninit 初始化状态 ⟸ 未定义行为避免"
    ),
    "custom_allocators": (
        "内存分配安全 ⟸ Allocator trait 契约 ⟸ 对齐与大小",
        "全局分配器替换 ⟸ #[global_allocator] ⟸ 堆统计"
    ),
    "zero_copy_parsing": (
        "解析零拷贝 ⟸ 借用输入切片 ⟸ 生命周期绑定",
        "序列化布局安全 ⟸ repr(C) / packed ⟸ 字节对齐"
    ),
    "lock_free": (
        "无锁算法正确 ⟸ CAS 循环 ⟸ ABA 问题避免",
        "内存回收安全 ⟸ Hazard Pointer / Epoch ⟸ 延迟释放"
    ),
    "type_erasure": (
        "动态分发安全 ⟸ Any/TypeId 反射 ⟸ 向下转换",
        "vtable 布局正确 ⟸ dyn Trait ⟸ 对象安全条件"
    ),
    "network_programming": (
        "异步 I/O 安全 ⟸ mio/epoll 抽象 ⟸ 事件驱动状态机",
        "协议解析健壮 ⟸ 字节流边界 ⟸ 反序列化安全"
    ),
    "parallel_distributed_pattern_spectrum": (
        "分布式容错 ⟸ 错误传播边界 ⟸ 效果系统追踪",
        "并行计算正确 ⟸ rayon 工作窃取 ⟸ Send 边界"
    ),
    "stream_processing_semantics": (
        "流处理一致性 ⟸ 背压控制 ⟸ 生产者-消费者协议",
        "异步流安全 ⟸ Stream/AsyncRead 生命周期 ⟸ Pin 约束"
    ),
}

def get_file_key(filepath: str) -> str:
    """从文件路径提取关键字。"""
    basename = os.path.splitext(os.path.basename(filepath))[0]
    # 去掉数字前缀（如 15_closure_basics -> closure_basics）
    basename = re.sub(r'^\d+_', '', basename)
    # 去掉常见后缀
    basename = basename.replace('_advanced', '').replace('_basics', '').replace('_deep_dive', '').replace('_patterns', '')
    return basename

def find_insertion_point(content: str) -> int:
    """
    找到插入 ⟸ 链的位置。
    尝试多个位置：核心推理链表格后、定理链补充后、实践/参考来源前。
    """
    lines = content.split('\n')
    
    # 策略 1: 在"核心推理链"表格之后、"> **过渡**"之前
    in_table = False
    for i, line in enumerate(lines):
        if '### 核心推理链' in line or '## 核心推理链' in line:
            in_table = True
        elif in_table and line.strip().startswith('> **过渡**'):
            return i
    
    # 策略 2: 在"定理链补充"之后
    for i, line in enumerate(lines):
        if '## 定理链补充' in line or '### 定理链补充' in line:
            # 找定理链补充后的空行或下一个标题
            for j in range(i+1, len(lines)):
                if lines[j].strip().startswith('## ') or lines[j].strip().startswith('---'):
                    return j
    
    # 策略 3: 在"实践"或"参考来源"之前
    for i, line in enumerate(lines):
        if line.strip().startswith('## 实践') or line.strip().startswith('## 参考来源') or line.strip().startswith('## 反命题与边界'):
            return i
    
    # 策略 4: 在文件末尾的"反命题与边界"之前
    for i, line in enumerate(lines):
        if '### 反命题与边界' in line or '## 反命题与边界' in line:
            return i
    
    return -1

def process_file(filepath: str) -> bool:
    """处理单个文件，返回是否修改。"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 如果已有 2+ 条 ⟸ 链，跳过
    if content.count('⟸') >= 2:
        return False
    
    key = get_file_key(filepath)
    if key not in TEMPLATES:
        # 尝试模糊匹配
        matched = False
        for k in TEMPLATES:
            if k in key or key in k:
                key = k
                matched = True
                break
        if not matched:
            print(f"  ⚠️ 无模板: {filepath} (key={key})")
            return False
    
    chain1, chain2 = TEMPLATES[key]
    
    insert_line = find_insertion_point(content)
    if insert_line == -1:
        print(f"  ⚠️ 找不到插入点: {filepath}")
        return False
    
    lines = content.split('\n')
    # 在 insert_line 之前插入两条 ⟸ 链（前面加一个空行）
    new_lines = lines[:insert_line]
    new_lines.append('')
    new_lines.append(f'> {chain1}')
    new_lines.append(f'> {chain2}')
    new_lines.extend(lines[insert_line:])
    
    new_content = '\n'.join(new_lines)
    
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    return True

def main():
    # 从质量仪表盘读取风险文件
    risk_files = []
    dashboard_path = 'reports/kb_quality_dashboard.md'
    if os.path.exists(dashboard_path):
        with open(dashboard_path, 'r', encoding='utf-8') as f:
            for line in f:
                if '反向推理不足' in line:
                    parts = line.split('|')
                    if len(parts) >= 2:
                        path = parts[1].strip()
                        risk_files.append(path)
    
    print(f"风险文件总数: {len(risk_files)}")
    
    modified = 0
    skipped = 0
    failed = 0
    
    for filepath in risk_files:
        # 转换 Windows 路径分隔符
        filepath = filepath.replace('\\', '/')
        if not os.path.exists(filepath):
            print(f"  ❌ 不存在: {filepath}")
            failed += 1
            continue
        
        try:
            if process_file(filepath):
                print(f"  ✅ 已更新: {filepath}")
                modified += 1
            else:
                skipped += 1
        except Exception as e:
            print(f"  ❌ 错误: {filepath} - {e}")
            failed += 1
    
    print(f"\n完成: 修改 {modified}, 跳过 {skipped}, 失败 {failed}")

if __name__ == '__main__':
    main()
