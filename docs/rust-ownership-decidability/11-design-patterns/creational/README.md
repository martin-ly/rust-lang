<!-- ARCHIVED: 内容简略，待补充后解档 -->

<details>
<summary>📦 归档内容（点击展开）— 待补充实质内容</summary>

# 创建型设计模式 (Creational Patterns)

创建型模式关注对象的创建机制，提供创建对象的灵活性。

---

## 模式列表
>
> **[来源: Rust Official Docs]**

| 模式 | 文件 | 描述 | 难度 |
|-----|------|------|------|
| **Singleton** | singleton.md (待补充) | 确保全局唯一实例 | 🟡 |
| **Builder** | [builder.md](./builder.md) | 逐步构建复杂对象 | 🟡 |
| **Factory** | [factory.md](./factory.md) | 封装对象创建逻辑 | 🟢 |

---

## 选择指南
>
> **[来源: Rust Official Docs]**

```
需要全局唯一实例?
├── 是 → Singleton
└── 否 → 需要逐步配置对象?
         ├── 是 → Builder
         └── 否 → 需要运行时决定类型?
                  ├── 是 → Factory
                  └── 否 → 直接构造
```

---

## Rust 特殊考虑
>
> **[来源: Rust Official Docs]**

- **所有权系统**: 影响单例的可变性设计
- **Type State**: Rust 独特的编译时验证构建者模式
- **零成本抽象**: 泛型工厂避免动态分派开销

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
