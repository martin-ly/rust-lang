# L2 进阶概念层（Intermediate）

> **定位**：在掌握 L1 基础后，理解 Rust 的模块化、泛型、错误处理等进阶机制。本层内容对齐 TRPL 第 10-15 章、Microsoft RustTraining 进阶部分。

---

## 一、本层概念图谱

```mermaid
graph TD
    A[L2 进阶概念层] --> B[01 Traits]
    A --> C[02 Generics]
    A --> D[03 Memory Management]
    A --> E[04 Error Handling]

    B --> B1[Trait Definition]
    B --> B2[Trait Bounds]
    B --> B3[Orphan Rule]
    B --> B4[Associated Types]

    C --> C1[Monomorphization]
    C --> C2[Const Generics]
    C --> C3[GATs]

    D --> D1[Smart Pointers]
    D --> D2[Interior Mutability]
    D --> D3[Custom Allocators]

    E --> E1[Option / Result]
    E --> E2[? Operator]
    E --> E3[Custom Errors]

    B -.->|依赖| C
    C -.->|依赖| D
    B -.->|依赖| E
```

---

## 二、文件索引

| 文件 | 概念 | 核心内容 | 状态 |
|:---|:---|:---|:---|
| `01_traits.md` | Trait 系统 | 定义、约束、Orphan Rule、关联类型、Supertrait | ✅ v1.0 |
| `02_generics.md` | 泛型系统 | 单态化、约束、Const Generics、GATs | ✅ v1.0 |
| `03_memory_management.md` | 内存管理 | Box/Rc/Arc、RefCell/Mutex、自定义分配器 | ✅ v1.0 |
| `04_error_handling.md` | 错误处理 | Result/Option、`?`、自定义错误、Error trait | ✅ v1.0 |

---

## 三、学习路径建议

```
L1 Foundation
    ↓
Traits ←────→ Generics
    ↓             ↓
Error Handling ← Memory Management
    ↓
L3 Advanced
```

---

## 四、待创建内容（按 Phase 2 计划）

详见 [PLAN.md](../PLAN.md) Phase 2 部分。
