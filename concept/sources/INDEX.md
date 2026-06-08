> **内容分级**: [综述级]
> **受众**: [研究者]
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
# 权威来源索引库
>
> **EN**: 权威来源索引库 (Chinese)
> **Summary**:
>
> | 标识符 | 全称 | 根 URL | 更新频率 | 建议引用格式 |
> | :--- | :--- | :--- | :--- | :--- |
> | `REF` | Rust Reference | <https://doc.rust-lang.org/reference/> | 与 stable 同步 | `[来源: REF — §章节]` |
> | `TRPL` | The Rust Programming Language | <https://doc.rust-lang.org/book/> | 每 Edition 更新 | `[来源: TRPL — 第X章]` |
> | `NOM` |
>
> **定位**: 本项目所有 `[来源: ...]` 标注的**单一真相源（Single Source of Truth）**。
> **原则**: 每个来源必须指向**具体章节或锚点**，禁止仅使用根 URL。
> **维护**: 新增来源必须先在此索引注册，获取唯一标识符，然后在概念文件中引用。

---

## 一级来源：官方规范与设计文档

| 标识符 | 全称 | 根 URL | 更新频率 | 建议引用格式 |
| :--- | :--- | :--- | :--- | :--- |
| `REF` | Rust Reference | <https://doc.rust-lang.org/reference/> | 与 stable 同步 | `[来源: REF — §章节]` |
| `TRPL` | The Rust Programming Language | <https://doc.rust-lang.org/book/> | 每 Edition 更新 | `[来源: TRPL — 第X章]` |
| `NOM` | The Rustonomicon | <https://doc.rust-lang.org/nomicon/> | 持续维护 | `[来源: NOM — 章节名]` |
| `RBE` | Rust by Example | <https://doc.rust-lang.org/rust-by-example/> | 与 stable 同步 | `[来源: RBE — 示例名]` |
| `RFC` | Rust RFCs | <https://rust-lang.github.io/rfcs/> | 持续活跃 | `[来源: RFC XXXX]` |
| `EDG` | Rust Edition Guide | <https://doc.rust-lang.org/edition-guide/> | 每 Edition 更新 | `[来源: EDG — 章节]` |
| `ASB` | Asynchronous Programming in Rust (Async Book) | <https://rust-lang.github.io/async-book/> | 重写中 | `[来源: ASB — 章节]` |
| `CAR` | The Cargo Book | <https://doc.rust-lang.org/cargo/> | 持续维护 | `[来源: CAR — 章节]` |
| `RUC` | The rustc Book | <https://doc.rust-lang.org/rustc/> | 持续维护 | `[来源: RUC — 章节]` |
| `UNB` | The Unstable Book | <https://doc.rust-lang.org/nightly/unstable-book/> | nightly | `[来源: UNB — 特性名]` |
| `STD` | Rust Standard Library | <https://doc.rust-lang.org/std/> | 与 stable 同步 | `[来源: STD — 模块::项]` |
| `FOR` | Rust Forge | <https://forge.rust-lang.org/> | 持续维护 | `[来源: FOR — 页面]` |

### REF — Rust Reference 精确章节映射（常用）

| 概念 | 精确章节 URL |
| :--- | :--- |
| 所有权与移动语义 | REF — §4.1.8 Ownership and moves |
| 借用与引用 | REF — §4.1.9 Borrowing |
| 生命周期 | REF — §4.1.10 Lifetimes |
| 类型系统 | REF — §4.2 Types |
| 泛型 | REF — §4.2.4 Generic parameters |
| Trait | REF — §4.2.5 Trait objects |
| 内存模型 | REF — §6.9 Memory model |
| Unsafe | REF — §7.9 Unsafe functions and blocks |
| 宏 | REF — §3.2 Macros |
| 模式 | REF — §4.3 Patterns |
| 常量求值 | REF — §4.4 Constant evaluation |
| 内联汇编 | REF — §7.10 Inline assembly |
| 链接 | REF — §7.3 Linkage |
| ABI | REF — §7.4 ABI |
| 内联属性 | REF — §7.5.2 The `inline` attribute |

### RFC — 关键 RFC 索引

| RFC 编号 | 标题 | 状态 | 稳定版本 |
| :--- | :--- | :---: | :--- |
| [RFC 0001](https://rust-lang.github.io/rfcs/0001.html) | RFC 流程本身 | Accepted | — |
| [RFC 0243](https://rust-lang.github.io/rfcs/0243.html) | Trait-based exception handling (Try trait) | Accepted | 1.26 |
| [RFC 1210](https://rust-lang.github.io/rfcs/1210.html) | Specialization | Accepted | nightly (min_specialization) |
| [RFC 1598](https://rust-lang.github.io/rfcs/1598.html) | Generic Associated Types (GATs) | Accepted | 1.65 |
| [RFC 2000](https://rust-lang.github.io/rfcs/2000.html) | Const Generics | Accepted | 1.51 (基础) |
| [RFC 2094](https://rust-lang.github.io/rfcs/2094.html) | Non-lexical lifetimes (NLL) | Accepted | 1.31 |
| [RFC 2349](https://rust-lang.github.io/rfcs/2349.html) | Pin API | Accepted | 1.33 |
| [RFC 2394](https://rust-lang.github.io/rfcs/2394.html) | async/await | Accepted | 1.39 |
| [RFC 2497](https://rust-lang.github.io/rfcs/2497.html) | if-let chains | Accepted | 1.88 |
| [RFC 2582](https://rust-lang.github.io/rfcs/2582.html) | raw reference operators (`&raw`) | Accepted | 1.82 |
| [RFC 2592](https://rust-lang.github.io/rfcs/2592.html) | futures | Accepted | 1.36 |
| [RFC 2857](https://rust-lang.github.io/rfcs/2857.html) | Orphan rules | Accepted | — |
| [RFC 2930](https://rust-lang.github.io/rfcs/2930.html) | Readiness and waking for async I/O | Accepted | 1.36 |
| [RFC 3501](https://rust-lang.github.io/rfcs/3501.html) | Edition 2024 | Accepted | 1.85 |
| [RFC 3627](https://rust-lang.github.io/rfcs/3627.html) | Return type notation (RTN) | Accepted | nightly |

> **完整 RFC 索引**: 见 [./RFC_INDEX.md](./RFC_INDEX.md)（建设中，目标覆盖 50+ 关键 RFC）

---

## 二级来源：学术论文与形式化验证

| 标识符 | 全称 | 类型 | 建议引用格式 |
| :--- | :--- | :--- | :--- |
| `RB18` | RustBelt: Securing the Foundations of the Rust Programming Language (POPL 2018) | 论文 | `[来源: RB18 — §章节]` |
| `Jung21` | Stacked Borrows: An Aliasing Model for Rust (POPL 2021) | 论文 | `[来源: Jung21]` |
| `Jung23` | Tree Borrows: An Aliasing Model for Rust (arXiv 2023) | 论文 | `[来源: Jung23]` |
| `Wadler89` | Theorems for Free! (POPL 1989) | 论文 | `[来源: Wadler89]` |
| `TAPL` | Types and Programming Languages (Pierce 2002) | 教材 | `[来源: TAPL — 章节]` |
| `LL87` | Linear Logic (Girard 1987) | 论文 | `[来源: LL87]` |
| `Reynolds02` | Separation Logic (Reynolds 2002) | 论文 | `[来源: Reynolds02]` |
| `Iris` | Iris Framework | 工具 | `[来源: Iris]` |
| `Viper` | Viper Verification Infrastructure | 工具 | `[来源: Viper]` |
| `Kani` | Kani Rust Verifier | 工具 | `[来源: Kani — 文档章节]` |
| `Miri` | Miri (Rust interpreter) | 工具 | `[来源: Miri]` |

---

## 三级来源：社区与工业资源

| 标识符 | 全称 | 类型 | 建议引用格式 |
| :--- | :--- | :--- | :--- |
| `CR` | Comprehensive Rust (Google) | 培训 | `[来源: CR — 章节]` |
| `RI` | Rust Internals (internals.rust-lang.org) | 论坛 | `[来源: RI — 帖子标题]` |
| `TWiR` | This Week in Rust | 周报 | `[来源: TWiR — 期号]` |
| `BE` | Bevy Engine 文档 | 生态 | `[来源: BE]` |
| `TK` | Tokio 文档 | 生态 | `[来源: TK — 章节]` |
| `WG` | Rust GameDev Working Group | 社区 | `[来源: WG]` |
| `COR` | corrode.dev | 博客 | `[来源: COR — 文章]` |
| `BOATS` | without.boats 博客 | 博客 | `[来源: BOATS — 文章]` |

---

## 来源使用规范

### 禁止行为

1. ❌ **仅使用根 URL**: `[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]` — 无法定位到具体章节
2. ❌ **重复堆砌来源**: 同一来源在目录中重复 10+ 次
3. ❌ **混淆来源层级**: 将博客文章标注为一级来源
4. ❌ **过时来源未标注**: 使用已废弃或过时的 RFC/文档未标注状态

### 推荐行为

1. ✅ **精确到章节**: `[来源: REF — §4.1.9 Borrowing]` 或 `[来源: TRPL — 第4章]`
2. ✅ **标注来源状态**: 对 nightly/unstable 特性标注 `[来源: UNB — gen_blocks] (nightly, 1.95+)`
3. ✅ **区分原创与引用**: `[来源: 💡 原创分析]` 仅用于有实质原创洞见的段落
4. ✅ **论文引用完整**: `[来源: Jung21 — Stacked Borrows, POPL 2021, §3.2]`

---

## 变更日志

| 日期 | 变更 | 操作者 |
| :--- | :--- | :--- |
| 2026-05-24 | 建立初始索引库，覆盖 12 个一级来源、11 个二级来源、8 个三级来源 | Kimi Code CLI |
