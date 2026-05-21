<!-- ARCHIVED: 内容简略，待补充后解档 -->

<details>
<summary>📦 归档内容（点击展开）— 待补充实质内容</summary>

# Rust 特有设计模式

这些模式利用 Rust 的所有权、生命周期和类型系统特性。

---

## 模式列表
> **[来源: Rust Official Docs]**

| 模式 | 文件 | 描述 | 难度 |
|-----|------|------|------|
| **RAII Guard** | [raii-guard.md](./raii-guard.md) | 资源自动管理 | 🟢 |
| **Newtype** | [newtype.md](./newtype.md) | 类型包装 | 🟢 |
| **Type State** | [../11-03-type-state-pattern.md](../11-03-type-state-pattern.md) | 编译时状态机 | 🟡 |

---

## 核心 Rust 特性
> **[来源: Rust Official Docs]**

- **所有权**: 确保资源管理正确性
- **生命周期**: 编译时引用验证
- **零成本抽象**: 模式无运行时开销
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)


</details>
