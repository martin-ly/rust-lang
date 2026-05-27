<!-- ARCHIVED: 内容简略，待补充后解档 -->

<details>
<summary>📦 归档内容（点击展开）— 待补充实质内容</summary>

# 05 - 对比研究

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **与其他类型系统的对比分析**

---

## 目录说明
>
> **[来源: Rust Official Docs]**

本目录对比Rust所有权系统与其他编程语言的类型系统，分析各自的优劣和适用场景。

---

## 文档列表
>
> **[来源: Rust Official Docs]**

| # | 文档 | 对比对象 |
|:---:|:---|:---|
| 05-01 | [线性vs仿射](./05-01-linear-vs-affine.md) | 线性类型 vs 仿射类型 |
| 05-02 | [Rust vs C++]

> 📝 待补充：对比分析 | 内存安全与性能对比 |
| 05-03 | [Rust vs Go](./05-03-rust-vs-go.md) | 并发与工程效率对比 |
| 05-04 | [Rust vs Java](./05-04-rust-vs-java.md) | 内存管理与类型系统 |
| 05-05 | [Rust vs Swift](./05-05-rust-vs-swift.md) | 所有权 vs ARC |

---

## 对比维度
>
> **[来源: Rust Official Docs]**

| 维度 | 线性类型 | 仿射类型 | Rust |
|:---:|:---:|:---:|:---:|
| 使用次数 | 恰好1次 | ≤1次 | ≤1次 (允许丢弃) |
| 复制 | 禁止 | 禁止 | Copy trait允许 |
| 交换律 | 有 | 有 | 有 |
| 弱化 | 无 | 有 | 有 |

---

**维护者**: Rust Comparative Study Team
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

</details>

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**
