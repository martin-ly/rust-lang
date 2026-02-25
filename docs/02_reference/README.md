# 参考与速查

> **创建日期**: 2025-12-11
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 语法/模式/边界/错误码速查；20 速查卡 + 边界特例 + 错误码映射
> **判定目标**: 速查完整、边界可查、错误码可落点
> **完整结构**: [DOCS_STRUCTURE_OVERVIEW](../DOCS_STRUCTURE_OVERVIEW.md) § 2.2
> **概念说明**: 参考与速查文档提供 Rust 语法、标准库 API、边界特例和错误码的快速查找，包含 20 个主题速查卡，支持开发者快速定位问题和解决方案。

---

## 快速查找示例

```rust
// 常用类型速查
// Option<T> - 可能不存在的值
let maybe: Option<i32> = Some(42);
let value = maybe.unwrap_or(0);  // 42

// Result<T, E> - 可能失败的计算
let result: Result<i32, &str> = Ok(42);
let value = result.unwrap_or(0);  // 42

// 迭代器常用方法
let nums = vec![1, 2, 3, 4, 5];
let sum: i32 = nums.iter().sum();           // 15
let evens: Vec<_> = nums.iter().filter(|&&x| x % 2 == 0).collect();  // [2, 4]
let doubled: Vec<_> = nums.iter().map(|&x| x * 2).collect();  // [2, 4, 6, 8, 10]

// 智能指针
use std::rc::Rc;
use std::sync::Arc;
use std::cell::RefCell;

let shared = Rc::new(RefCell::new(5));  // 单线程引用计数 + 内部可变性
let atomic = Arc::new(5);                // 多线程原子引用计数
```

---

## 文档列表

| 文档 | 描述 | 适用场景 |
| :--- | :--- | :--- |
| [quick_reference/](./quick_reference/) | 20 个速查卡（含 AI/ML） | 快速查找语法和模式 |
| [ALIGNMENT_GUIDE.md](./ALIGNMENT_GUIDE.md) | 对齐知识综合（内存/格式化/unsafe/缓存行） | 内存布局优化 |
| [EDGE_CASES_AND_SPECIAL_CASES.md](./EDGE_CASES_AND_SPECIAL_CASES.md) | 边界特例 | 处理特殊情况 |
| [STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md](./STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md) | 标准库分析 | 标准库深入理解 |
| [CROSS_LANGUAGE_COMPARISON.md](./CROSS_LANGUAGE_COMPARISON.md) | 跨语言对比 | 从其他语言迁移 |

---

## 速查卡主题

| 主题 | 文件 | 描述 |
| :--- | :--- | :--- |
| **所有权与借用** | ownership_cheatsheet.md | 所有权规则、生命周期 |
| **类型系统** | type_system.md | 泛型、trait、类型转换 |
| **异步编程** | async_cheatsheet.md | async/await、Future |
| **并发** | concurrency_cheatsheet.md | 线程、同步、Send/Sync |
| **宏系统** | macros_cheatsheet.md | 声明宏、过程宏 |
| **错误处理** | error_handling_cheatsheet.md | Result、panic、? 运算符 |
| **泛型** | generics_cheatsheet.md | 泛型约束、关联类型 |
| **迭代器** | iterators_cheatsheet.md | Iterator trait、适配器 |
| **测试** | testing_cheatsheet.md | 单元测试、mock、基准测试 |
| **Unsafe** | unsafe_cheatsheet.md | 原始指针、FFI |
| **智能指针** | smart_pointers_cheatsheet.md | Box、Rc、Arc、RefCell |
| **生命周期** | lifetimes_cheatsheet.md | 生命周期省略、高阶 trait bound |
| **闭包** | closures_cheatsheet.md | Fn、FnMut、FnOnce |
| **模式匹配** | pattern_matching_cheatsheet.md | match、if let、while let |
| **模块系统** | modules_cheatsheet.md | mod、use、pub |
| **字符串** | strings_cheatsheet.md | &str、String、编码 |
| **集合** | collections_cheatsheet.md | Vec、HashMap、BTreeMap |
| **I/O** | io_cheatsheet.md | Read、Write、BufRead |
| **WASM** | wasm_cheatsheet.md | WebAssembly 开发 |
| **AI/ML** | ai_ml_cheatsheet.md | Rust AI/ML 生态 |

---

## 边界特例示例

```rust
// 整数溢出
let max = u8::MAX;
// let overflow = max + 1;  // Debug: panic, Release: wrap

// 安全处理
let (result, overflowed) = max.overflowing_add(1);
assert!(overflowed);

// 浮点数特例
let nan = f64::NAN;
assert!(nan != nan);  // NaN != NaN

// 空切片
let empty: &[i32] = &[];
assert!(empty.first().is_none());

// 递归类型需要装箱
// 错误： enum List { Cons(i32, List), Nil }
// 正确：
enum List {
    Cons(i32, Box<List>),
    Nil,
}
```

---

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../research_notes/formal_methods/README.md](../research_notes/formal_methods/README.md) |
| 类型系统形式化 | 类型理论数学定义 | [../research_notes/type_theory/type_system_foundations.md](../research_notes/type_theory/type_system_foundations.md) |
| 证明索引 | 形式化证明集合 | [../research_notes/PROOF_INDEX.md](../research_notes/PROOF_INDEX.md) |

---

## 主索引

[00_MASTER_INDEX.md](../00_MASTER_INDEX.md)

---

[返回文档中心](../README.md)
