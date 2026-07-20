> **内容分级**: 归档级

> **⚠️ 历史文档提示**：本文档包含 `async-std`、`wasm32-wasi` 等已归档或已重命名的生态引用。
> 其中技术观点反映了对应时间点的社区状态，可能与当前（Rust 1.96+）推荐实践不一致。
> 学习时请以 `concept/`、`knowledge/` 及官方文档为准。
>
> - `async-std` 已进入维护模式，新项目建议优先考虑 Tokio / smol。
> - `wasm32-wasi` 已重命名为 `wasm32-wasip1`；WASI Preview 2 目标为 `wasm32-wasip2`。

---

<!-- ARCHIVED: 内容简略，待补充后解档 -->

> **分级**: [C]
<details>
<summary>📦 归档内容（点击展开）— 待补充实质内容</summary>

# 案例研究

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **生产级Rust项目深度分析**

---

## 目录说明
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

本目录包含对著名Rust开源库和框架的深度案例分析，从形式化角度分析其设计和实现。

---

## 专题案例
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### 综合分析专题
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

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
| 异步运行时 | Tokio, async-std [已归档] |
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
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

</details>

---

## 相关概念

- [区块链/Web3](blockchain/README.md)
- [CLI 工具](cli/README.md)
- [云计算](cloud/README.md)
- [数据库](database/README.md)
- [嵌入式](embedded/README.md)
- [游戏开发](gamedev/README.md)
- [媒体处理](media/README.md)
- [ML/AI](ml-ai/README.md)
- [网络安全](security/README.md)
- [WebAssembly](wasm/README.md)
- [领域覆盖索引](COMPLETE_DOMAIN_COVERAGE_INDEX.md)
- [所有权可判定性总览](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**

> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**

> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**
