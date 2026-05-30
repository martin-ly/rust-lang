<!-- ARCHIVED: 内容简略，待补充后解档 -->

> **分级**: [C]
<details>
<summary>📦 归档内容（点击展开）— 待补充实质内容</summary>

# 01 - 核心概念

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **Rust所有权系统核心机制详解**

---

## 目录说明
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

本目录深入讲解Rust所有权系统的五大核心概念，从实践和理论两个维度进行形式化分析。

---

## 文档列表
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

| # | 文档 | 核心内容 | 定理数量 |
|:---:|:---|:---|:---:|
| 01-01 | [所有权规则](./01-01-ownership-rules.md) | 所有权转移、Drop、RAII | 10+ |
| **01-01-deep** | [**所有权规则深度解析**](./01-01-ownership-rules-deep.md) | 形式语义、18+反例、定理证明 | 8+ |
| 01-02 | [借用系统](./01-02-borrowing-system.md) | 共享借用vs可变借用 | 8+ |
| 01-03 | [生命周期](./01-03-lifetimes.md) | 生命周期标注、省略规则 | 6+ |
| 01-04 | [运行时vs编译时](./01-04-runtime-vs-compile-time.md) | 检查时机对比 | 5+ |
| 01-05 | [内部可变性](./01-05-interior-mutability.md) | Cell/RefCell/Mutex | 8+ |

### 深度解析文档
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

📘 **[所有权规则深度解析 (01-01-ownership-rules-deep.md)](./01-01-ownership-rules-deep.md)**

本深度文档提供Rust所有权系统的完整形式化分析，包含：

- **形式语义**: 基于分离逻辑和RustBelt的数学基础
- **8+ 定理与证明**: 所有权唯一性、移动线性性、精确释放等
- **18个深度反例**: Use-after-move、Pin交互、Vec重新分配等
- **高级模式**: Builder模式、状态机、零拷贝
- **Vec案例研究**: 原始指针所有权、重新分配安全
- **Rust 1.95特性**: if let guards、use<..> 精确捕获、bool 转浮点数
- **Rust 1.94历史特性**: 精确大小迭代器、内联const

适合希望深入理解所有权系统底层机制的开发者和研究人员。

---

## 核心定理预览

```text
Thm OWNERSHIP-UNIQUENESS: 任意时刻，一个值只有一个所有者

Thm BORROW-XOR-MUT: 不能同时存在可变借用和不可变借用

Thm LIFETIME-SUBSET: 引用生命周期 ⊆ 被引用值生命周期
```

---

**维护者**: Rust Core Concepts Team
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

</details>

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**
