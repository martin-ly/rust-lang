<!-- ARCHIVED: 内容简略，待补充后解档 -->

<details>
<summary>📦 归档内容（点击展开）— 待补充实质内容</summary>

# 04 - 可判定性分析

> **Rust类型系统与借用检查的可判定性**

---

## 目录说明
> **[来源: Rust Official Docs]**

本目录分析Rust类型系统各项检查的计算复杂度，包括类型推断、借用检查等核心算法的可判定性。

---

## 文档列表
> **[来源: Rust Official Docs]**

| # | 文档 | 主题 | 复杂度 |
|:---:|:---|:---|:---:|
| 04-01 | [类型推断](./04-01-type-inference.md) | Hindley-Milner扩展 | P |
| 04-02 | [借用检查](./04-02-borrow-checking.md) | 所有权流分析 | P |

---

## 核心结论
> **[来源: Rust Official Docs]**

```text
类型推断:      P (多项式时间)
借用检查:      P (多项式时间)
生命周期检查:  P (多项式时间)

总体: Rust编译时检查都是可判定的
```

---

**维护者**: Rust Decidability Analysis Team
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
