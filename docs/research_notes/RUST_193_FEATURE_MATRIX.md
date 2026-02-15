# Rust 1.93 特性族多维概念矩阵

> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-13
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **目标**: 按特性族展开「概念-公理-定理-证明方法-反例」五维矩阵，便于逐特性查找
> **上位文档**: [UNIFIED_SYSTEMATIC_FRAMEWORK](UNIFIED_SYSTEMATIC_FRAMEWORK.md)、[RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md)

---

## 📊 目录

- [Rust 1.93 特性族多维概念矩阵](#rust-193-特性族多维概念矩阵)
  - [目录](#目录)
  - [1. 内存与所有权族](#1-内存与所有权族)
  - [2. 类型系统族](#2-类型系统族)
  - [3. Trait 与多态族](#3-trait-与多态族)
  - [4. 控制流与模式匹配族](#4-控制流与模式匹配族)
  - [5. 并发与异步族](#5-并发与异步族)
  - [6. 宏与元编程族](#6-宏与元编程族)
  - [7. 模块与可见性族](#7-模块与可见性族)
  - [8. 常量与编译期族](#8-常量与编译期族)
  - [9. FFI 与不安全族](#9-ffi-与不安全族)
  - [10. Rust 1.93 新增/变更族](#10-rust-193-新增变更族)
  - [相关文档](#相关文档)

---

## 1. 内存与所有权族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 所有权 | 每值恰一所有者 | 规则 1–3, Def 1.1–1.3 | T2 唯一性, T3 内存安全 | 结构归纳、反证 | 使用已移动值 |
| 借用 | 不可变可多、可变独占 | 规则 5–8 | T1 数据竞争自由 | 规则归纳 | 双重可变借用 |
| 生命周期 | 引用有效性约束 | $\ell \subseteq \text{lft}$ | T2 引用有效性 | 三步骤 | 返回局部引用 |
| Pin | 非 Unpin 位置稳定 | Def 1.1–2.2 | T1–T3 | 类型系统 | 非 Unpin 用 Pin::new |
| Box | 堆分配、单一所有权 | BOX1 | BOX-T1 | ownership_model | 使用已移动 Box |
| Rc/Arc | 共享所有权 | RC1/ARC1 | RC-T1 | ownership_model | 跨线程用 Rc |
| Cell/RefCell | 内部可变性 | CELL1/REFCELL1 | REFCELL-T1 | ownership_model | Cell 跨线程共享 |
| MaybeUninit | 延迟初始化 | MAYBEUNINIT1 | MAYBEUNINIT-T1 | ownership_model | 未初始化 assume_init |
| 智能指针 | Deref/Drop 语义 | DROP1/DEREF1 | DROP-T1/DEREF-T1 | ownership_model | 违反 Drop 顺序 |
| 裸指针 | FFI、unsafe 底层 | RAW1 | RAW-T1 | borrow_checker_proof | 解引用空指针 |
| 引用 | 借用、零成本 | &T、&mut T | borrow_checker | 悬垂引用 |
| 内存布局 | 与 C 互操作 | REPR1 | REPR-T1 | ownership_model | 错误布局导致 UB |

---

## 2. 类型系统族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 基本类型 | 机器字、数值、布尔 | - | 进展性 T1、保持性 T2 | type_system_foundations | 溢出（debug panic） |
| 结构体 | 命名字段聚合 | struct | - | - | - |
| 枚举 | tagged union | enum | - | - | - |
| Never (!) | 不可达、发散 | BOT1 | BOT-T1 | type_system_foundations | 1.92 Lint 严格化 |
| Option/Result | 可选值、错误处理 | 构造性 | - | - | unwrap 空值 |
| 型变 | 子类型在泛型中传递 | Def 1.1–3.1 | T1–T4 | variance_theory | &mut 协变 |
| 类型推断 | 减少注解 | 局部推断 | - | - | 歧义时报错 |
| 类型别名 | 简化复杂类型 | type Alias = T | - | - | - |
| 单元类型 () | 无返回值 | 唯一值 () | - | - | - |
| 数组/切片 | 连续内存 | [T; N]、[T] | - | - | 越界 panic |
| str | UTF-8 字符串 | &str、String | - | - | 非 UTF-8 |
| impl Trait | 匿名泛型返回值 | 存在类型 | DYN-T1 | trait_system_formalization | - |
| dyn Trait | 运行时多态 | vtable、对象安全 | - | trait_system_formalization | Clone 非对象安全 |
| Sized | 编译时已知大小 | 默认约束 | - | - | 未 Sized 的 DST |
| Clone/Copy | 显式复制语义 | Copy 位复制 | - | ownership_model | 1.93 Copy 不再 specialization |

---

## 3. Trait 与多态族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Trait | 行为抽象、多态 | trait、impl for | COH-T1 | trait_system_formalization | - |
| 泛型 | 编译时多态 | 单态化 | - | - | 歧义 impl |
| 关联类型 | Trait 内类型抽象 | type Item | - | - | - |
| GATs | 泛型关联类型 | type Item<'a> | AT-L1 | advanced_types | 约束违反 |
| const 泛型 | 编译时常量参数 | [T; N] | - | advanced_types | 非 const 作参数 |
| Trait 对象 | 运行时多态 | dyn Trait | - | trait_system | 对象安全违规 |
| Send/Sync | 跨线程安全 | Send=可转移、Sync=可共享 | T6.1–T6.3 | async_state_machine | Rc 非 Send |
| Unpin | Pin 的反面 | Def 2.2 | T1–T3 | pin_self_referential | 非 Unpin 栈固定 |
| blanket impl | 泛型实现 | impl<T: Trait> Foo for T | - | - | 冲突 impl |
| Trait 继承 | Trait 组合 | trait B: A | - | - | - |

---

## 4. 控制流与模式匹配族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| if/else | 条件分支 | 表达式 | - | - | - |
| match | 穷尽模式匹配 | MATCH1 | MATCH-T1 | borrow_checker_proof | 非穷尽 match |
| if let | 单模式匹配 | - | - | - | - |
| loop | 无限循环 | loop、break 返回值 | - | - | - |
| while | 条件循环 | - | - | - | - |
| for | 迭代 | FOR1 | FOR-T1 | borrow_checker_proof | 迭代中修改集合 |
| ? 操作符 | 错误传播 | QUERY1 | QUERY-T1 | borrow_checker_proof | 非 Result 类型 |
| 模式 | 解构、绑定 | ref、mut、@、.. | - | - | 非穷尽 |

---

## 5. 并发与异步族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 线程 | 多核并行 | SPAWN1 | SPAWN-T1 | async_state_machine | 非 Send 跨线程 |
| Future | 异步 I/O | Def 4.1–5.2 | T6.1–T6.3 | async_state_machine | 未 Pin 自引用 |
| async/await | 异步语法糖 | 生成状态机 | - | async_state_machine | 非 Send 跨 await |
| Pin | Future 位置稳定 | 见内存族 | - | pin_self_referential | - |
| Send/Sync | 见 Trait 族 | - | - | async_state_machine | - |
| 通道 | 消息传递 | CHAN1 | CHAN-T1 | borrow_checker_proof | 发送端 drop 后接收 |
| Mutex/RwLock | 共享可变 | MUTEX1 | MUTEX-T1 | borrow_checker_proof | 死锁 |
| 原子操作 | 无锁并发 | ATOMIC1 | ATOMIC-T1 | ownership_model | 错误内存顺序 |

---

## 6. 宏与元编程族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 声明宏 | 代码生成、DSL | macro_rules! | - | - | 意外捕获 |
| 过程宏 | 编译器扩展 | derive、attr、function | - | - | 非卫生导致冲突 |
| 属性宏 | 标注语法 | #[attribute] | - | - | 无效位置 |
| derive 宏 | 自动实现 | #[derive(Clone)] | - | - | 自定义 derive 错误 |
| cfg | 条件编译 | #[cfg(...)] | - | - | 1.93 关键词作谓词报错 |

---

## 7. 模块与可见性族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| mod | 代码组织 | mod、文件即模块 | - | - | 循环依赖 |
| use | 导入简写 | use、pub use | - | - | 私有项导出 |
| pub | 可见性 | pub、pub(crate) | - | - | 越权访问 |
| crate | 包边界 | crate 根 | - | - | - |

---

## 8. 常量与编译期族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| const | 编译期常量 | const X: T = ... | - | advanced_types | 非常量表达式 |
| const fn | 编译期可求值 | 受限操作 | - | advanced_types | 非 const 操作 |
| const 泛型 | 见 Trait 族 | - | - | - | - |
| const 中 mutable ref | 1.93 允许 | const 含 &mut static | CONST-MUT1 | advanced_types | const_item_interior_mutations |
| const-eval | 编译期求值 | 1.93 指针字节复制 | - | - | - |
| inline | 内联提示 | #[inline] | - | - | - |

---

## 9. FFI 与不安全族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| unsafe | 绕过借用、类型检查 | UNSAFE1 | UNSAFE-T1/T2 | borrow_checker_proof | 违反契约 UB |
| extern | C/FFI 互操作 | EXTERN1 | EXTERN-T1 | borrow_checker_proof | ABI 不匹配 |
| C variadic | 1.93 C 风格可变参数 | CVARIADIC1 | - | borrow_checker_proof | 非 system ABI |
| 裸指针 | 见内存族 | RAW1 | - | - | deref_nullptr 1.93 deny |
| union | C 互操作 | UNION1 | - | ownership_model | 非活动字段读取 |
| transmute | 类型重解释 | TRANSMUTE1 | TRANSMUTE-T1 | ownership_model | 大小/对齐不匹配 |

---

## 10. Rust 1.93 新增/变更族

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| s390x vector | s390x SIMD | is_s390x_feature_detected! | - | toolchain | 非 s390x 架构 |
| C variadic | printf 等 FFI | extern "system" fn(..., ...) | - | toolchain | 非 system ABI |
| cfg 关键词 | 避免误用 | 关键词作 cfg 谓词报错 | - | toolchain | - |
| asm_cfg | 条件汇编 | #[cfg] 在 asm! 行上 | - | toolchain | - |
| LUB coercion | 类型推断正确性 | 修正函数项、安全性 | LUB-T1 | type_system_foundations | - |
| const &mut static | 允许特定 const | 非常 unsafe | CONST-MUT1 | advanced_types | const_item_interior_mutations |
| const_item_interior_mutations | 安全警示 | warn-by-default lint | - | toolchain | - |
| function_casts_as_integer | 可移植性 | warn-by-default | - | toolchain | - |
| deref_nullptr | 安全 | deny-by-default | DEREF-NULL1 | type_system_foundations | 解引用空指针 |
| Copy specialization 移除 | 生命周期安全 | 不再内部 specialization | COP-T1 | type_system_foundations | 可能性能回归 |
| 全局分配器 thread_local | 避免重入 | 允许 thread_local! | - | toolchain | - |

---

## 相关文档

| 文档 | 用途 |
| :--- | :--- |
| [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) | 92 项特性完整分析 |
| [UNIFIED_SYSTEMATIC_FRAMEWORK](UNIFIED_SYSTEMATIC_FRAMEWORK.md) | 全局统一框架、五维矩阵总览 |
| [PROOF_INDEX](PROOF_INDEX.md) | 形式化证明索引 |
| [toolchain/07_rust_1.93_full_changelog](../06_toolchain/07_rust_1.93_full_changelog.md) | Rust 1.93 完整变更清单 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-13
**状态**: ✅ 100% 完成（10 特性族 × 五维矩阵）
