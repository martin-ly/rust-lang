import os

exercises = [
    ("ownership_borrowing", "ex01_borrow_checker_fix", "修复借用检查错误", "Easy", "理解所有权转移与借用规则，修复函数使其通过编译。"),
    ("ownership_borrowing", "ex02_string_slice", "字符串 Slice", "Easy", "掌握字符串 slice 的使用，实现 first_word 函数。"),
    ("ownership_borrowing", "ex03_mutable_borrow", "可变引用规则", "Easy", "理解可变引用的排他性，实现字符串修改与读取。"),
    ("ownership_borrowing", "ex04_lifetime_basic", "基础生命周期标注", "Medium", "为函数添加显式生命周期参数，使其能够编译。"),
    ("ownership_borrowing", "ex05_smart_pointer_rc", "Rc 智能指针共享所有权", "Medium", "使用 Rc<T> 实现共享配置项，理解引用计数。"),
    ("type_system", "ex01_enum_pattern_match", "枚举与模式匹配", "Easy", "定义 TrafficLight 枚举，实现 match 表达式。"),
    ("type_system", "ex02_struct_methods", "结构体与方法", "Easy", "实现 Rectangle 结构体，包含面积计算和缩放方法。"),
    ("type_system", "ex03_type_conversion", "类型转换", "Easy", "为自定义温度类型实现 From/Into 特质。"),
    ("type_system", "ex04_generics_intro", "泛型入门", "Medium", "实现泛型二分查找和切片最大值函数。"),
    ("type_system", "ex05_trait_object", "特质对象", "Medium", "使用 dyn Trait 实现多态图形渲染系统。"),
    ("generics_traits", "ex01_trait_bounds", "特质约束", "Easy", "使用 trait bound 和 where 子句限制泛型类型。"),
    ("generics_traits", "ex02_associated_types", "关联类型", "Medium", "定义 Container 特质，使用关联类型表示元素类型。"),
    ("generics_traits", "ex03_operator_overload", "运算符重载", "Medium", "为二维向量实现 Add 和 Sub 运算符。"),
    ("generics_traits", "ex04_default_trait", "Default 特质", "Easy", "为 ServerConfig 实现 Default，使用 struct update syntax。"),
    ("generics_traits", "ex05_trait_composition", "特质组合", "Hard", "使用 supertrait 组合 Display 和 PartialOrd。"),
    ("concurrency", "ex01_thread_spawn", "创建线程", "Easy", "创建线程并发计算数字的平方。"),
    ("concurrency", "ex02_mutex_counter", "Mutex 计数器", "Medium", "使用 Arc<Mutex<T>> 实现线程安全计数器。"),
    ("concurrency", "ex03_channel_mpsc", "MPSC 通道", "Easy", "使用 mpsc 通道在线程间传递消息。"),
    ("concurrency", "ex04_rwlock_shared", "RwLock 共享状态", "Medium", "使用 RwLock 实现并发缓存，支持多读单写。"),
    ("concurrency", "ex05_arc_atomic", "Arc + Atomic", "Medium", "使用 AtomicUsize 实现无锁计数器。"),
    ("async_programming", "ex01_basic_async", "基础 async/await", "Easy", "实现简单的异步函数，理解 .await 用法。"),
    ("async_programming", "ex02_future_combinator", "Future 组合", "Medium", "使用 join、join_all 并发执行多个 Future。"),
    ("async_programming", "ex03_tokio_task", "Tokio 任务", "Medium", "使用 tokio::spawn 并发执行异步任务。"),
    ("async_programming", "ex04_async_channel", "异步通道", "Medium", "使用 tokio::sync::mpsc 进行异步消息传递。"),
    ("async_programming", "ex05_timeout_retry", "超时与重试", "Hard", "实现带有超时和重试机制的异步操作。"),
    ("error_handling", "ex01_result_option", "Result 与 Option", "Easy", "掌握 Result 和 Option 的基本操作与转换。"),
    ("error_handling", "ex02_custom_error", "自定义错误类型", "Medium", "为配置验证定义专门的错误枚举。"),
    ("error_handling", "ex03_error_propagation", "错误传播", "Medium", "使用 ? 运算符和 map_err 在多层调用中传播错误。"),
    ("macros", "ex01_declarative_macro", "声明宏", "Medium", "编写 set!、ok_or_return!、timed! 宏。"),
    ("macros", "ex02_derive_macro_stub", "派生宏框架", "Hard", "理解过程宏概念，手动实现 Describe 特质。"),
]

hints = {
    "ex01_borrow_checker_fix": "使用 &String 借用而不是转移所有权。函数签名已经要求 &String。",
    "ex02_string_slice": "find(' ') 返回 Option<usize>，使用 match 或 if let 处理。返回 &str 避免所有权转移。",
    "ex03_mutable_borrow": "先完成所有不可变借用，再进行可变借用。或者调整操作顺序。",
    "ex04_lifetime_basic": "当函数返回引用时，返回的生命周期必须等于输入参数的生命周期之一。",
    "ex05_smart_pointer_rc": "Rc::clone 不会深拷贝数据，只是增加引用计数。使用 Rc::strong_count 查看计数。",
    "ex01_enum_pattern_match": "match 必须覆盖所有变体。Option 可以用 map、filter 等组合子操作。",
    "ex02_struct_methods": "impl 块中的 &self 表示不可变借用，&mut self 表示可变借用。",
    "ex03_type_conversion": "实现 From<A> for B 会自动获得 Into<B> for A。注意浮点数精度。",
    "ex04_generics_intro": "Ord trait 提供 cmp 方法。swap 可以使用 std::mem::swap。",
    "ex05_trait_object": "Box<dyn Shape> 允许在运行时动态分发。注意 trait object 有大小限制（object safe）。",
    "ex01_trait_bounds": "使用 <T: Display + PartialOrd> 或 where T: Display + PartialOrd。",
    "ex02_associated_types": "关联类型与泛型参数的区别：每个实现只能有一种关联类型。",
    "ex03_operator_overload": "实现 std::ops::Add 等 trait，注意 type Output = Self。",
    "ex04_default_trait": "使用 ..Default::default() 语法可以只覆盖部分字段。",
    "ex05_trait_composition": "supertrait 自动为实现了子 trait 的类型提供方法。",
    "ex01_thread_spawn": "thread::spawn 返回 JoinHandle，必须调用 join() 等待完成。",
    "ex02_mutex_counter": "Arc::clone 增加引用计数，Mutex::lock() 返回 MutexGuard。",
    "ex03_channel_mpsc": "mpsc::channel 返回 (Sender, Receiver)。Sender 可以 clone。",
    "ex04_rwlock_shared": "RwLock 允许多个读锁或单个写锁。注意死锁风险。",
    "ex05_arc_atomic": "AtomicUsize 的 fetch_add 是线程安全的。Ordering::SeqCst 是最保守的内存序。",
    "ex01_basic_async": "async fn 返回一个 Future，需要 .await 才能执行。",
    "ex02_future_combinator": "futures::future::join 可以并发等待两个 Future。",
    "ex03_tokio_task": "tokio::spawn 需要 tokio 运行时。测试使用 #[tokio::test]。",
    "ex04_async_channel": "tokio::sync::mpsc 是异步的，send 和 recv 都是 async 方法。",
    "ex05_timeout_retry": "tokio::time::timeout 包装一个 Future，如果超时返回 Err。",
    "ex01_result_option": "? 运算符只能在返回 Result 或 Option 的函数中使用。",
    "ex02_custom_error": "实现 std::fmt::Display 和 std::error::Error 是自定义错误的基础。",
    "ex03_error_propagation": "map_err 可以转换错误类型，同时保留原始错误信息。",
    "ex01_declarative_macro": "macro_rules! 使用 \\$name:expr 匹配表达式，\$(...)* 表示重复。",
    "ex02_derive_macro_stub": "过程宏需要单独的 proc-macro crate，本练习为手动实现版本。",
}

for topic, exid, title, level, desc in exercises:
    readme_path = f"exercises/docs/{topic}/{exid}.md"
    hint_path = f"exercises/docs/{topic}/{exid}_hint.md"

    readme = f"""# {title}

**主题**: {topic.replace("_", " ").title()}  
**难度**: {level}  
**练习编号**: {exid}

---

## 题目描述

{desc}

## 代码位置

- 代码框架: `exercises/src/{topic}/{exid}.rs`
- 测试用例: 同一文件内的 `#[cfg(test)]` 模块

## 学习目标

- 理解 {topic.replace("_", "/")} 的核心概念
- 能够独立编写通过测试的实现
- 掌握相关的 Rust 语法和惯用法

## 运行测试

```bash
cd exercises
cargo test {topic}::{exid}
```

或运行整个主题的测试：

```bash
cd exercises
cargo test {topic}::
```
"""

    hint = f"""# 提示: {title}

{hints.get(exid, "暂无提示，请尝试独立完成。")}

## 相关阅读

- 项目内对应模块: `crates/` 下的相关源码
- 速查卡: `docs/02_reference/quick_reference/`
"""

    os.makedirs(os.path.dirname(readme_path), exist_ok=True)
    with open(readme_path, "w", encoding="utf-8") as f:
        f.write(readme)
    with open(hint_path, "w", encoding="utf-8") as f:
        f.write(hint)

print(f"已生成 {len(exercises)} 道练习的 README 和 hint 文件")
