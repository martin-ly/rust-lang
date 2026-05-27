<!-- ARCHIVED: 内容简略，待补充后解档 -->

<details>
<summary>📦 归档内容（点击展开）— 待补充实质内容</summary>

# 结构型设计模式 (Structural Patterns)

> **Bloom 层级**: L5-L6 (分析/评价/创造)

结构型模式关注如何组合类和对象以形成更大的结构。

---

## 模式列表
>
> **[来源: Rust Official Docs]**

| 模式 | 文件 | 描述 | 难度 |
|-----|------|------|------|
| **Adapter** | [adapter.md](./adapter.md) | 接口适配 | 🟢 |
| **Decorator** | [decorator.md](./decorator.md) | 动态添加功能 | 🟡 |
| **Proxy** | [proxy.md](./proxy.md) | 访问控制 | 🟡 |

---

## 选择指南
>
> **[来源: Rust Official Docs]**

```
需要改变接口?
├── 是 → Adapter
└── 否 → 需要添加功能而不改变原类?
         ├── 是 → Decorator
         └── 否 → 需要控制访问?
                  ├── 是 → Proxy
                  └── 否 → 直接组合
```

---

## Rust 特性利用
>
> **[来源: Rust Official Docs]**

- **泛型**: 零成本装饰者和代理
- **Deref**: 智能指针模式
- **Trait**: 接口抽象

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

> **[来源: Wikipedia - Design Pattern]**

> **[来源: Rust API Guidelines]**

> **[来源: Gang of Four - Design Patterns]**

> **[来源: ACM - Software Design Patterns]**
