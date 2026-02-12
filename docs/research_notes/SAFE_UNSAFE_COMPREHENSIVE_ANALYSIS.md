# Rust 安全与非安全全面论证与分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: 🔄 持续完善直至 100%
> **目标**: 全面、完整、充分地论证「安全 Rust」与「unsafe Rust」的边界、契约、保证与 UB

---

## 📋 目录

- [Rust 安全与非安全全面论证与分析](#rust-安全与非安全全面论证与分析)
  - [📋 目录](#-目录)
  - [🎯 文档宗旨](#-文档宗旨)
  - [一、安全与非安全定义与边界](#一安全与非安全定义与边界)
    - [1.1 形式化定义](#11-形式化定义)
    - [1.2 边界图示](#12-边界图示)
    - [1.3 为何需要 unsafe？](#13-为何需要-unsafe)
  - [二、安全保证的形式化论证](#二安全保证的形式化论证)
    - [2.1 安全保证定理汇总](#21-安全保证定理汇总)
    - [2.2 安全保证依赖链](#22-安全保证依赖链)
  - [三、unsafe 契约体系](#三unsafe-契约体系)
    - [3.1 契约形式](#31-契约形式)
    - [3.2 典型 unsafe 操作契约表](#32-典型-unsafe-操作契约表)
    - [3.3 契约违反后果](#33-契约违反后果)
  - [四、UB 分类与反例](#四ub-分类与反例)
    - [4.1 UB 分类](#41-ub-分类)
    - [4.2 反例表](#42-反例表)
    - [4.3 1.93 相关变更](#43-193-相关变更)
  - [五、安全抽象论证](#五安全抽象论证)
    - [5.1 定义](#51-定义)
    - [5.2 论证结构](#52-论证结构)
    - [5.3 典型安全抽象](#53-典型安全抽象)
    - [5.4 安全抽象决策树](#54-安全抽象决策树)
  - [六、安全 vs 非安全多维矩阵](#六安全-vs-非安全多维矩阵)
    - [6.1 按维度](#61-按维度)
    - [6.2 按操作类型](#62-按操作类型)
  - [📚 相关文档](#-相关文档)

---

## 🎯 文档宗旨

本文档针对「安全与非安全缺乏全面论证和分析」的缺口，系统化补全：

1. **定义与边界**：安全子集、unsafe 边界、跨越方式
2. **形式化论证**：各安全保证的定理与证明引用
3. **unsafe 契约**：前置/后置条件、典型操作契约
4. **UB 分类**：内存、类型、并发、FFI 等 UB 及反例
5. **安全抽象**：不变式、边界、正确性论证

---

## 一、安全与非安全定义与边界

### 1.1 形式化定义

**定义 1.1（安全 Rust）**
安全 Rust 指仅使用安全 API（无 `unsafe` 块、无 `unsafe fn` 调用、无 `unsafe trait` 实现）的代码子集。编译器对此子集提供**静态保证**。

**定义 1.2（unsafe Rust）**
unsafe Rust 指包含 `unsafe` 块、调用 `unsafe fn` 或实现 `unsafe trait` 的代码。程序员须**manually 保证**契约满足，否则可能导致 UB。

**定义 1.3（安全边界）**
安全边界 = 编译器可静态验证的保证范围。跨越边界即需程序员契约。

### 1.2 边界图示

```text
┌──────────────────────────────────────────────────────────┐
│                     安全子集 (Safe Rust)                   │
│  ┌────────────────────────────────────────────────────┐  │
│  │  所有权、借用、生命周期、类型系统、Send/Sync、Pin   │  │
│  │  编译器静态验证 → 无 UB（在安全代码内）             │  │
│  └────────────────────────────────────────────────────┘  │
└──────────────────────────┬───────────────────────────────┘
                           │ 安全边界
                           ▼
┌──────────────────────────────────────────────────────────┐
│                    unsafe 边界                             │
│  unsafe { ... } / unsafe fn / unsafe trait impl           │
│  契约：{P} op {Q} —— 程序员保证 P                         │
└──────────────────────────┬───────────────────────────────┘
                           │
                           ▼
┌──────────────────────────────────────────────────────────┐
│                  非安全操作 (可导致 UB)                     │
│  裸指针、MaybeUninit、transmute、union、FFI、asm!         │
└──────────────────────────────────────────────────────────┘
```

### 1.3 为何需要 unsafe？

| 需求 | 安全子集 | unsafe 用途 |
|------|----------|-------------|
| 性能 | 零成本抽象 | 绕过不必要的检查 |
| FFI | 无 | 与 C/系统交互 |
| 未初始化内存 | MaybeUninit（需 assume_init） | 延迟初始化、零成本 |
| 自引用 | Pin（堆固定） | 底层实现、自定义集合 |
| 类型转换 | as 等有限转换 | transmute、union |
| 内联汇编 | 无 | asm! |
| 实现不安全 trait | 无 | unsafe trait impl |

---

## 二、安全保证的形式化论证

### 2.1 安全保证定理汇总

| 保证 | 机制 | 定理 | 文档 |
|------|------|------|------|
| 无悬垂引用 | 生命周期、借用 | lifetime T2、ownership T3 | lifetime_formalization、ownership_model |
| 无双重释放 | 所有权 | ownership T2,T3 | ownership_model |
| 无内存泄漏 | RAII、所有权 | ownership T3 | ownership_model |
| 数据竞争自由 | 借用、Send/Sync | borrow T1、async T6.2 | borrow_checker_proof、async_state_machine |
| 类型安全 | 类型系统 | type_system T1–T3 | type_system_foundations |
| 引用有效性 | 生命周期 | lifetime T2 | lifetime_formalization |
| 型变安全 | 协变/逆变/不变 | variance T1–T4 | variance_theory |
| 自引用安全 | Pin | pin T1–T3 | pin_self_referential |

### 2.2 安全保证依赖链

```text
所有权规则 1–3 ──→ 唯一性 T2 ──→ 内存安全 T3（无悬垂、无双重释放、无泄漏）
        │
        └──→ 借用规则 5–8 ──→ 数据竞争自由 T1

生命周期约束 ──→ 引用有效性 T2

typing rules ──→ 进展性 T1、保持性 T2 ──→ 类型安全 T3

型变 Def 1.1–3.1 ──→ 协变/逆变/不变 T1–T4

Pin Def + Future Def ──→ Pin 保证 T1、自引用安全 T2、并发安全 T6.2
```

---

## 三、unsafe 契约体系

### 3.1 契约形式

**Hoare 三元组**：$\{P\}\; \text{unsafe\_op} \;\{Q\}$

- $P$：前置条件（程序员必须保证）
- $Q$：后置条件（编译器信任）

### 3.2 典型 unsafe 操作契约表

| 操作 | 前置 P | 后置 Q | 说明 |
|------|--------|--------|------|
| `*ptr` | 非空、对齐、有效、无别名可变引用 | 访问有效 | [Rustonomicon](https://doc.rust-lang.org/nomicon/) |
| `MaybeUninit::assume_init` | 内存已初始化 | 返回有效 T | 1.93 文档化 |
| `MaybeUninit::assume_init_drop` | 内存已初始化 | 调用 drop、内存未初始化 | 1.93 新 API |
| `ptr::read` | 指针有效、对齐 | 返回值副本 | - |
| `ptr::write` | 指针有效、对齐、可写 | 写入完成 | - |
| `ptr::copy` | 非重叠或正确顺序 | 复制完成 | - |
| `mem::transmute` | 大小相等、对齐兼容 | 类型转换正确 | - |
| `mem::transmute_copy` | 大小兼容 | 按位复制 | - |
| union 字段读 | 该字段为活动字段 | 读取有效 | - |
| `Send` impl | 跨线程传递安全 | - | unsafe trait |
| `Sync` impl | 共享引用安全 | - | unsafe trait |
| `Pin::new`（非 Unpin） | 调用者不移动 | 位置稳定 | - |
| `Pin::get_unchecked_mut` | 满足 Unpin 或投影安全 | 可变引用 | - |

### 3.3 契约违反后果

违反前置条件 → **未定义行为 (UB)**。编译器可假设前置条件成立，故可能产生任意优化、任意结果。

---

## 四、UB 分类与反例

### 4.1 UB 分类

| 类别 | 说明 | 典型原因 |
|------|------|----------|
| **内存 UB** | 无效内存操作 | 悬垂、双重释放、越界、未初始化读取 |
| **类型 UB** | 无效类型操作 | 错误 transmute、无效 union 读 |
| **并发 UB** | 数据竞争、错误同步 | 非 Send 跨线程、原子顺序错误 |
| **FFI UB** | 外部 ABI 违反 | 错误 extern 签名、abi 不匹配 |
| **未指定** | 实现定义 | 有符号溢出（release 可 wrap） |

### 4.2 反例表

| 反例 | 违反契约 | 后果 |
|------|----------|------|
| 解引用空指针 | *ptr 前置（非空） | 内存 UB |
| assume_init 未初始化 | assume_init 前置 | 内存 UB |
| transmute 大小不等 | transmute 前置 | 类型 UB |
| 非 Send 跨线程 | Send 契约 | 并发 UB |
| 移动未 Pin 自引用 | Pin 保证 | 悬垂、内存 UB |
| 双重可变借用 | 借用规则 | 编译错误（安全子集内） |
| 返回局部引用 | 生命周期 | 编译错误（安全子集内） |

### 4.3 1.93 相关变更

| 变更 | 影响 | 文档 |
|------|------|------|
| deref_nullptr deny-by-default | 解引用空指针编译失败 | 09_rust_1.93_compatibility_deep_dive |
| MaybeUninit 文档化 | 契约明确 | 07_rust_1.93_full_changelog |
| const_item_interior_mutations | const 内部可变警告 | 07_rust_1.93 |

---

## 五、安全抽象论证

### 5.1 定义

**安全抽象**：内部使用 unsafe，对外仅暴露安全 API，且若调用者仅用安全 API，则不会触发 UB。

### 5.2 论证结构

1. **不变式**：抽象维持的不变式（如 Vec: len ≤ capacity）
2. **安全 API 边界**：不暴露可破坏不变式的操作
3. **unsafe 正确性**：所有 unsafe 均在前置条件满足下调用
4. **结论**：安全抽象正确 ⟺ 不变式 + 边界 + 正确 unsafe

### 5.3 典型安全抽象

| 抽象 | 内部 unsafe | 不变式 | 安全 API |
|------|-------------|--------|----------|
| Vec<T> | 裸指针、realloc | len ≤ capacity | push、pop、index |
| Box<T> | 堆分配、释放 | 单一所有权 | new、drop |
| Rc<T> | 原子引用计数 | 计数一致 | clone、strong_count |
| Mutex<T> | 锁、内部可变 | 互斥 | lock、try_lock |
| String | 与 Vec 类似 | UTF-8 | 所有 &str 方法 |

### 5.4 安全抽象决策树

```text
需要提供底层能力？
├── 有现成安全抽象？ → 使用（Vec、Box、Mutex 等）
└── 需自定义？
    ├── 定义不变式
    ├── 文档化前置/后置条件（对 unsafe 块）
    ├── 最小化 unsafe 范围
    ├── 用安全 API 封装
    └── 验证（Miri、测试、形式化）
```

---

## 六、安全 vs 非安全多维矩阵

### 6.1 按维度

| 维度 | 安全子集 | unsafe 拓展 | 边界 |
|------|----------|-------------|------|
| **内存** | 所有权、借用、RAII | 裸指针、MaybeUninit、手动分配 | 编译器可验证 vs 程序员契约 |
| **类型** | 类型系统、泛型 | transmute、union | 类型安全 vs 重解释 |
| **并发** | Send/Sync、借用 | 裸原子、无锁 | 数据竞争自由 vs 手动同步 |
| **引用** | 生命周期、NLL | 裸指针无生命周期 | 引用有效性 vs 手动保证 |
| **FFI** | 无 | extern、extern "C" | 无 vs 完全手动 |

### 6.2 按操作类型

| 操作类型 | 安全 | unsafe | 说明 |
|----------|------|--------|------|
| 所有权转移 | 移动、Copy | - | 安全子集涵盖 |
| 借用 | &T、&mut T | - | 安全子集涵盖 |
| 裸指针 | - | *const、*mut | 需 unsafe |
| 未初始化 | - | MaybeUninit | assume_init 需契约 |
| 类型转换 | as、From | transmute | 后者需 unsafe |
| 锁 | Mutex、RwLock | - | 安全抽象 |
| 原子 | AtomicUsize 等 | - | 安全抽象 |
| FFI | - | extern | 需 unsafe |

---

## 📚 相关文档

| 文档 | 用途 |
|------|------|
| [THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md) | 理论体系、论证体系、安全边界总览 |
| [LANGUAGE_SEMANTICS_EXPRESSIVENESS](LANGUAGE_SEMANTICS_EXPRESSIVENESS.md) | 公理语义、unsafe 契约 |
| [UNSAFE_RUST_GUIDE](../UNSAFE_RUST_GUIDE.md) | Unsafe Rust 专题指南 |
| [ownership_model](formal_methods/ownership_model.md) | 内存安全定理 |
| [borrow_checker_proof](formal_methods/borrow_checker_proof.md) | 数据竞争自由定理 |
| [Rustonomicon](https://doc.rust-lang.org/nomicon/) | 官方 unsafe 权威 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-12
**状态**: ✅ **100% 完成**（安全与非安全全面论证）
