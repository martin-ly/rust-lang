# 所有权系统思维导图

```mermaid
graph TD
    A[所有权 Ownership] --> B[核心规则]
    A --> C[操作类型]
    A --> D[理论基础]
    A --> E[编译时检查]

    B --> B1[唯一性: 单所有者]
    B --> B2[可转移: Move语义]
    B --> B3[作用域: RAII]
    B --> B4[Drop: 自动释放]

    C --> C1[Move: 所有权转移]
    C --> C2[Borrow: 临时访问]
    C --> C3[Copy: 值复制]
    C --> C4[Clone: 深拷贝]

    C2 --> C2a[不可变借用 &T]
    C2 --> C2b[可变借用 &mut T]

    D --> D1[线性逻辑]
    D --> D2[仿射逻辑]
    D --> D3[分离逻辑]
    D --> D4[区域理论]

    E --> E1[借用检查器]
    E --> E2[生命周期检查]
    E --> E3[Send/Sync检查]
```

## 📑 目录
>
- [所有权系统思维导图](#所有权系统思维导图)
  - [📑 目录](#-目录)
  - [ASCII版本](#ascii版本)
  - [相关概念](#相关概念)

## ASCII版本
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```
                            ┌─────────────┐
                            │   所有权    │
                            │  Ownership  │
                            └──────┬──────┘
                                   │
        ┌──────────────────────────┼──────────────────────────┐
        │                          │                          │
        ▼                          ▼                          ▼
┌───────────────┐        ┌─────────────────┐        ┌─────────────────┐
│   核心规则    │        │    操作类型     │        │    理论基础     │
└───────┬───────┘        └────────┬────────┘        └────────┬────────┘
        │                         │                          │
   ┌────┴────┐              ┌─────┴──────┐            ┌─────┴──────┐
   │• 唯一性 │              │• Move      │            │• 线性逻辑  │
   │• 可转移 │              │• Borrow    │            │• 仿射逻辑  │
   │• 作用域 │              │• Copy      │            │• 分离逻辑  │
   │• Drop  │              │• Clone     │            │• 区域理论  │
   └─────────┘              └─────┬──────┘            └────────────┘
                                  │
                           ┌──────┴──────┐
                           │• &T 不可变  │
                           │• &mut T可变 │
                           └─────────────┘
```

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念

- [visualizations 目录](./README.md)
- [上级目录](../README.md)


---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**
