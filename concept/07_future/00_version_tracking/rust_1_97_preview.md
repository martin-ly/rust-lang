# Rust 1.97.0 前沿特性预览（已归档）

> **内容重叠提示**: 本文不再重复 1.97.0 已稳定内容；`concept/` 版本为项目权威主轨。
> **代码状态**: [设计级 — 仅跟踪未稳定条目]
>
> **EN**: Rust 1.97.0 Preview Archive
> **Summary**: Rust 1.97.0 已于 2026-07-09 进入 stable。本文件保留**未进入 1.97.0 stable** 的候选特性，作为 1.98+ 预览入口；已稳定内容请参见 `rust_1_97_stabilized.md`。
> **Rust 版本**: 1.97.0 (Edition 2024) 预览归档
>
> **受众**: [进阶]
> **Bloom 层级**: L2-L3
> **内容分级**: [参考级]
> **权威来源**: 本文件为 `concept/` 权威页。
> **状态**: ✅ Rust 1.97.0 已 stable；本文件仅跟踪未稳定候选
> **跟踪版本**: Rust 1.98+ nightly
> **Rust 属性标记**: `#[unstable]` / `#[nightly_only]`
>
> **前置依赖**: [Rust 1.96 稳定特性](rust_1_96_stabilized.md) · [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md)
> **后置概念**: [Rust 1.97.0 稳定特性](rust_1_97_stabilized.md) · [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)

---

> **来源**: [Rust 1.97.0 Release Notes](https://releases.rs/docs/1.97.0/) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/)

---

## 一、说明

Rust 1.97.0 已按计划在 2026-07-09 发布 stable。官方 1.97.0 包含的语言、标准库、Cargo、Rustdoc 与平台变更已全部迁移到 [`rust_1_97_stabilized.md`](rust_1_97_stabilized.md)。

本文件保留**曾在 1.97 周期讨论但最终错过 1.97.0 stable** 的条目，以及后续仍处 nightly/RFC 阶段的特性，作为进入 [`rust_1_98_preview.md`](rust_1_98_preview.md) 的过渡入口。

---

## 二、从 1.97 推迟到 1.98+ 的标准库 API

以下 API 原被讨论为 1.97 候选，但因错过 beta cutoff（2026-05-22）进入 1.98 列车：

| 特性 | 说明 | 跟踪 |
|:---|:---|:---|
| `VecDeque::truncate_front` | 从队列前端截断元素 | [#151973](https://github.com/rust-lang/rust/pull/151973) |
| `VecDeque::retain_back` | 从后端按条件保留元素 | [#151973](https://github.com/rust-lang/rust/pull/151973) |
| `Vec::into_non_null` / `Box::into_non_null` | 将 `Vec<T>` / `Box<T>` 转换为 `NonNull<T>` | [#130364](https://github.com/rust-lang/rust/issues/130364) |

```rust,ignore
// 以下代码在 1.97.0 stable 上尚不可用，预计 1.98+ 稳定
#![feature(vec_deque_truncate_front, vec_deque_retain_back, box_vec_non_null)]

use std::collections::VecDeque;
use std::ptr::NonNull;

fn demo() {
    let mut dq = VecDeque::from([1, 2, 3, 4]);
    // dq.truncate_front(2);
    // dq.retain_back(|x| *x > 1);

    let v = vec![1, 2, 3];
    // let _ptr: NonNull<i32> = v.into_non_null();
}
```

---

## 三、仍在评审中的 1.98+ 候选

更完整的跟踪请参见 [`rust_1_98_preview.md`](rust_1_98_preview.md)。本节仅列出与 1.97 周期高度相关的条目：

| 特性 | 状态 | 说明 |
|:---|:---|:---|
| `core::range::{legacy, RangeFull, RangeTo}` | 已合并，1.98 | RFC 3550 range 类型补全 |
| `NonZero<T>::from_str_radix` | 已合并，1.98 | 非零整数按进制解析 |
| `float_algebraic` | 已合并，1.98 | 浮点代数运算 intrinsics |
| `int_format_into` | 已合并，1.98 | 整数零分配格式化到缓冲区 |
| `PathBuf::into_string` | 已合并，1.98 | `PathBuf` 零成本转 `String` |
| `Result::map_or_default` / `Option::map_or_default` | 已合并，1.98 | 便捷默认值映射 |
| `RandomSource` / `DefaultRandomSource` | 等待评审 | 可插拔随机数源抽象 |
| `#[optimize]` | PFCP | 函数级优化属性 |
| `size_of_val_raw` / `align_of_val_raw` | 等待评审 | 裸值尺寸/对齐计算 |
| C-variadic 函数定义 | PFCP | 安全 Rust 中定义 C 可变参数函数 |
| `derive(CoercePointee)` | FCP finished | 智能指针自动类型强制 |
| `never_type` (`!`) | FCP finished / blocked | 底类型最终稳定化 |

---

## 四、形式化与生态前瞻

与 1.97 周期相关的长期项目仍在继续：

- **Pin Ergonomics / Reborrow Traits**: Project Goals 2026 旗舰目标 "Beyond the &"，预计 1.99+。
- **Field Projections**: `field_of!` 宏与 FRTs 已合并，逐步推进。
- **BorrowSanitizer**: 运行时（Runtime） Tree Borrows 违规检测，LLVM RFC 已发布。
- **Safety Tags**: unsafe 契约的机器可读标注，RFC 讨论中。

---

## 五、关联文档

- [Rust 1.97.0 稳定特性摘要](rust_1_97_stabilized.md)
- [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)
- [Rust 形式模型演进跟踪](05_rust_version_tracking.md)

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Matsushita, Denis, Jourdan & Dreyer: RustHornBelt — A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code（POPL 2022, arXiv:2203.00944）](https://arxiv.org/abs/2203.00944)（2026-07-12 验证 HTTP 200）
- **P2 生态/社区**: [docs.rs/futures — 生态权威 API 文档](https://docs.rs/futures) · [docs.rs/hyper — 生态权威 API 文档](https://docs.rs/hyper)
