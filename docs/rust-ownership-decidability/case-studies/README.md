<!-- ARCHIVED: 内容简略，待补充后解档 -->

<details>
<summary>📦 归档内容（点击展开）— 待补充实质内容</summary>

# 案例研究

> **生产级Rust项目深度分析**

---

## 目录说明
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

本目录包含对著名Rust开源库和框架的深度案例分析，从形式化角度分析其设计和实现。

---

## 专题案例
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 综合分析专题
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

位于 `comprehensive-analysis/case-studies/`

| 案例 | 内容 |
|:---|:---|
| Tokio运行时 | 调度器、IO驱动、性能分析 |
| Embassy嵌入式 | 无堆分配、实时性分析 |

### Actor专题

位于 `actor-specialty/case-studies/`

| 案例 | 内容 |
|:---|:---|
| Actix-web | 生产环境架构分析 |

---

## 案例分析维度

每个案例分析包含:

1. **项目概览** - 基本信息、定位
2. **架构分析** - 整体架构、关键组件
3. **形式化分析** - 安全定理、证明
4. **性能分析** - 基准测试、优化
5. **最佳实践** - 生产环境建议

---

## 分类索引

| 类别 | 案例 |
|:---|:---|
| 异步运行时 | Tokio, async-std |
| Web框架 | Actix-web, Axum |
| 嵌入式 | Embassy, RTIC |
| Actor系统 | Actix, Bastion |
| 数据库 | Diesel, SQLx |
| 序列化 | Serde, Rkyv |

---

**维护者**: Rust Case Study Team
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

## 相关概念

- [区块链/Web3](./blockchain/README.md)
- [CLI 工具](./cli/README.md)
- [云计算](./cloud/README.md)
- [数据库](./database/README.md)
- [嵌入式](./embedded/README.md)
- [游戏开发](./gamedev/README.md)
- [媒体处理](./media/README.md)
- [ML/AI](./ml-ai/README.md)
- [网络安全](./security/README.md)
- [WebAssembly](./wasm/README.md)
- [领域覆盖索引](./COMPLETE_DOMAIN_COVERAGE_INDEX.md)
- [所有权可判定性总览](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**
