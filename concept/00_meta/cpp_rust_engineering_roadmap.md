# C/C++ → Rust 工程层对比路线图
>
> **EN**: C/C++ to Rust Engineering Comparison Roadmap
> **Summary**: A unified roadmap and index for all C/C++ engineering-level comparison files, helping C++ programmers migrate to Rust through structured topic clusters.
>
> **受众**: [进阶]
> **层级**: L2-L5 跨层导航
> **A/S/P 标记**: C+S — Comparison + Structure
> **双维定位**: C×Ana / C×Eva
> **前置概念**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md) · [Variable Model](../01_foundation/20_variable_model.md)
> **后置概念**: [Pattern Semantic Space Index](./pattern_semantic_space_index.md) · [C++ ABI Object Model](../05_comparative/02_cpp_abi_object_model.md)
> **主要来源**: [Rust Foundation Interop Initiative] · [Brown University CRP Phrasebook] · [simplifycpp.org C++_Rust.pdf]
---

> **Bloom 层级**: 理解 → 分析 → 评价

## 一、核心命题

> **C++ 程序员学习 Rust 的最大障碍不是语法，而是"同一工程问题在两门语言中的本体论差异"。
> 本路线图将 C/C++ → Rust 的对比内容组织为五个主题簇：内存模型、类型系统、错误处理、构造与元编程、ABI 与运行时，
> 帮助学习者按自己的知识缺口定位文件，而不是按文件编号顺序阅读。**

---

## 二、主题簇地图

### 2.1 内存模型簇

| C++ 概念 | Rust 对应 | 文件 |
|:---|:---|:---|
| 所有权 / 智能指针 | 所有权系统 / `Box`/`Rc`/`Arc` | [Rust vs C++ §7](../05_comparative/01_rust_vs_cpp.md) · [Ownership](../01_foundation/01_ownership.md) |
| 借用 / 引用 | `&T` / `&mut T` / 生命周期 | [Borrowing](../01_foundation/02_borrowing.md) · [Lifetimes](../01_foundation/03_lifetimes.md) |
| Move 语义 | 所有权转移 / `Copy` / `Clone` | [Rust vs C++ §7.3](../05_comparative/01_rust_vs_cpp.md) · [Variable Model](../01_foundation/20_variable_model.md) |
| RAII / 析构函数 | `Drop` trait | [Variable Model](../01_foundation/20_variable_model.md) |
| 值类别（lvalue/xvalue/prvalue） | place / value expression | [Variable Model](../01_foundation/20_variable_model.md) |

### 2.2 类型系统簇

| C++ 概念 | Rust 对应 | 文件 |
|:---|:---|:---|
| 模板 / 泛型 | Generics / Trait Bounds | [Generics](../02_intermediate/02_generics.md) · [Traits](../02_intermediate/01_traits.md) |
| SFINAE / `enable_if` | Trait Bounds / `where` | [Traits §5.8](../02_intermediate/01_traits.md) |
| C++20 Concepts | Trait + Bound | [Traits §5.8.5](../02_intermediate/01_traits.md) |
| 模板特化 / 偏特化 | Orphan Rule / Specialization | [Traits §5.8.3](../02_intermediate/01_traits.md) · [Advanced Traits](../02_intermediate/19_advanced_traits.md) |
| 运算符重载 | `std::ops` trait | [Type System §12](../01_foundation/04_type_system.md) · [Surface Features §3](../05_comparative/16_cpp_rust_surface_features.md) |

### 2.3 错误处理簇

| C++ 概念 | Rust 对应 | 文件 |
|:---|:---|:---|
| 异常 / `try` / `catch` | `Result<T, E>` / `?` | [Error Handling](../02_intermediate/04_error_handling.md) |
| 异常安全保证 | 类型系统 + `Result` | [Exception Safety](../02_intermediate/27_exception_safety_rust_cpp.md) |
| `std::expected` (C++23) | `Result<T, E>` | [Exception Safety §6](../02_intermediate/27_exception_safety_rust_cpp.md) |
| `noexcept` | `panic` / abort | [Exception Safety §5](../02_intermediate/27_exception_safety_rust_cpp.md) |

### 2.4 构造与元编程簇

| C++ 概念 | Rust 对应 | 文件 |
|:---|:---|:---|
| 构造函数 / 初始化列表 | 结构体字面量 / `new` 约定 | [Construction](../02_intermediate/28_construction_and_initialization.md) |
| 默认构造 / `constexpr` | `Default` / `const fn` | [Construction](../02_intermediate/28_construction_and_initialization.md) |
| 三/五/零法则 | `Copy` / `Clone` / `Drop` | [Construction §5](../02_intermediate/28_construction_and_initialization.md) |
| 预处理器 / `#define` | `macro_rules!` / `#[cfg]` | [Preprocessor vs Macros](../02_intermediate/26_c_preprocessor_vs_rust_macros.md) |
| 模板元编程 / `constexpr` | `const fn` / 类型级状态机 | [Traits §5.8.4](../02_intermediate/01_traits.md) |

### 2.5 ABI 与运行时簇

| C++ 概念 | Rust 对应 | 文件 |
|:---|:---|:---|
| ABI / 对象布局 | `repr(C)` / 默认 ABI | [C++ ABI Object Model](../05_comparative/02_cpp_abi_object_model.md) |
| vtable / 虚函数 | `dyn Trait` 胖指针 | [C++ ABI Object Model](../05_comparative/02_cpp_abi_object_model.md) |
| RTTI / `dynamic_cast` | `Any` / `TypeId` | [RTTI](../02_intermediate/25_rtti_and_dynamic_typing.md) |
| `friend` | 模块可见性 | [Friend vs Module Privacy](../02_intermediate/29_friend_vs_module_privacy.md) |
| FFI / `extern "C"` | `extern "C"` / `unsafe` | [Rust FFI](../03_advanced/05_rust_ffi.md) |

---

## 三、推荐学习路径

### 路径 A：C++ 系统程序员快速迁移

```text
Rust vs C++（总体本体论）
    ↓
Variable Model（理解所有权 = 存储模型 + 线性约束）
    ↓
Construction（结构体字面量替代构造函数）
    ↓
Exception Safety（Result 替代异常）
    ↓
C++ ABI Object Model（FFI 必备）
    ↓
RTTI / Friend / Preprocessor（逐个主题扫尾）
```

### 路径 B：按问题域切入

| 你来自 C++ 的哪个领域 | 起点 | 延伸阅读 |
|:---|:---|:---|
| 底层系统 / 嵌入式 | [C++ ABI Object Model](../05_comparative/02_cpp_abi_object_model.md) | [Rust FFI](../03_advanced/05_rust_ffi.md) |
| 游戏 / 高性能计算 | [Variable Model](../01_foundation/20_variable_model.md) | [Move 语义](../05_comparative/01_rust_vs_cpp.md) |
| 企业后端 | [Exception Safety](../02_intermediate/27_exception_safety_rust_cpp.md) | [Error Handling](../02_intermediate/04_error_handling.md) |
| 编译器 / 元编程 | [Preprocessor vs Macros](../02_intermediate/26_c_preprocessor_vs_rust_macros.md) | [Macros](../03_advanced/04_macros.md) |

---

## 四、与 Phase B 计划的衔接

本路线图属于 **Phase B（C/C++ 工程层对比）** 的导航层。审计报告 [SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md](../../reports/SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md) 指出的 Phase B 缺口包括：

- ABI 与对象模型 ✅ [C++ ABI Object Model](../05_comparative/02_cpp_abi_object_model.md)
- Move 语义系统对比 ✅ [Rust vs C++ §7.3](../05_comparative/01_rust_vs_cpp.md)
- 异常安全深度 ✅ [Exception Safety](../02_intermediate/27_exception_safety_rust_cpp.md)
- SFINAE / 模板元编程 ✅ [Traits §5.8](../02_intermediate/01_traits.md)
- 构造/初始化/运算符/RTTI/友元 ✅ [Surface Features](../05_comparative/16_cpp_rust_surface_features.md) + 专门文件
- 预处理器 vs 宏 ✅ [Preprocessor vs Macros](../02_intermediate/26_c_preprocessor_vs_rust_macros.md)

---

## 五、L1 / L2 / L3 总结

| 层级 | 要点 |
|:---|:---|
| **L1** | C++ 与 Rust 在内存、类型、错误、构造、ABI 五个维度上都有可映射的对应概念。 |
| **L2** | Rust 通过类型系统、trait、模块可见性替代了 C++ 的构造函数、异常、friend、SFINAE 等语言内建机制。 |
| **L3** | 迁移的核心不是"找等价语法"，而是理解 Rust 如何通过去语法化和显式约束，把 C++ 中的隐式规则和特权语法转化为可静态检查的结构。 |

---

## 六、延伸阅读

- [Rust Foundation Interop Initiative](https://github.com/rustfoundation/interop-initiative)
- [Brown University C++↔Rust Phrasebook](https://cel.cs.brown.edu/crp/)
- [simplifycpp.org — C++ vs Rust](https://simplifycpp.org/books/cpp/CPP_Rust.pdf)
- [Tangram Vision — C++ Rust Generics](https://www.tangramvision.com/blog/c-rust-generics-and-specialization)

---

> **Checklist**: 已建立 C/C++ → Rust 工程层对比的主题簇地图 / 提供学习路径 / 衔接 Phase B 审计计划。
