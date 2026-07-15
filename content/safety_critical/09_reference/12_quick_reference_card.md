# Rust安全关键系统快速参考卡片

**EN**: Quick Reference Card
**Summary**: Rust安全关键系统快速参考卡片 Quick Reference Card.

> **权威来源**: 本文件为 `content/` 专题深度内容入口；通用 Rust 概念解释请见 [`concept/00_meta/04_navigation/11_quick_reference.md`](../../../concept/00_meta/04_navigation/11_quick_reference.md)。若 `concept/` 已覆盖相同主题，本文仅保留应用场景、案例与决策树，不重复概念推导。
> **Bloom 层级**: L4-L6
>
> 本文内容迁移自历史归档，已按 `AGENTS.md` 规则保留为安全关键领域专题实践。

## 速查命令
>
> **[来源: Rust Official Docs]**

### 日常开发

> **[来源: Wikipedia - Rust (programming language)]**
>
> **[来源: Rust Official Docs]**

```bash
# 构建和测试
cargo build --release
cargo test
cargo clippy -- -D warnings

# 安全审计
cargo audit
cargo outdated

# 高级验证
cargo miri test
cargo kani
cargo tarpaulin

# 格式化
cargo fmt
cargo doc --no-deps
```

### 依赖管理
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```bash
# 更新依赖
cargo update

# 查看依赖树
cargo tree
cargo tree -d  # 查看重复依赖

# 检查许可证
cargo license

# 漏洞扫描
cargo audit
```

### 嵌入式
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```bash
# 添加目标
rustup target add thumbv7em-none-eabihf

# 交叉编译
cargo build --target thumbv7em-none-eabihf

# 烧录
cargo flash --chip STM32F407VG

# 调试
cargo embed
```

---

## 关键资源链接
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 资源 | URL |
|------|-----|
| Rust Book | <https://doc.rust-lang.org/book/> |
| Rust Reference | <https://doc.rust-lang.org/reference/> |
| Embedded Book | <https://docs.rust-embedded.org/book/> |
| High Assurance Rust | <https://highassurance.rs> |
| Ferrocene | <https://ferrocene.dev> |
| Rust Safety WG | <https://rust-lang.org/governance> |

---

将此卡片打印并放在工作台上，随时查阅

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: ISO 26262 - Functional Safety]**
> **[来源: IEC 61508 - Safety Standards]**
> **[来源: MISRA Rust Guidelines]**
> **[来源: Ferrocene Language Specification]**

---
