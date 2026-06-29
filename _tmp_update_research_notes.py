#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Upgrade docs/research_notes/ target files with authoritative international content."""

from pathlib import Path
import re

ROOT = Path("e:/_src/rust-lang/docs/research_notes")

# ---------- Common patterns ----------
OLD_HEADER_STATUS = (
    "> **创建日期**: 2025-01-27\n"
    "> **最后更新**: 2026-02-28\n"
    "> **Rust 版本**: 1.96.0+ (Edition 2024)\n"
    "> **状态**: ✅ 已完成"
)
NEW_HEADER_STATUS = (
    "> **创建日期**: 2025-01-27\n"
    "> **最后更新**: 2026-06-29\n"
    "> **Rust 版本**: 1.96.0+ (Edition 2024)\n"
    "> **状态**: ✅ 完成"
)

OLD_HEADER_STATUS_METH = (
    "> **创建日期**: 2025-01-27\n"
    "> **最后更新**: 2026-02-28\n"
    "> **Rust 版本**: 1.96.0+ (Edition 2024) ✅\n"
    "> **状态**: ✅ 已完成 (100%)"
)


def read_file(path: Path) -> str:
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def write_file(path: Path, text: str) -> None:
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


# ============================================================
# File 1: 10_research_methodology.md
# ============================================================
f1 = ROOT / "10_research_methodology.md"
t1 = read_file(f1)

# header
t1 = t1.replace(OLD_HEADER_STATUS_METH, NEW_HEADER_STATUS)

# maintenance block before old 1.94 section
t1 = t1.replace(
    "**维护者**: Rust Research Methodology Group\n"
    "**最后更新**: 2026-01-26\n"
    "**状态**: ✅ 已完成 (100%)",
    "**维护者**: Rust Research Methodology Group\n"
    "**最后更新**: 2026-06-29\n"
    "**状态**: ✅ 完成",
)

# Insert authoritative formal-methods section before "### 相关概念"
t1 = t1.replace(
    "Qed.\n```\n\n### 相关概念",
    """Qed.
```

### Rust 形式化方法的国际论文与工具链
>
> **来源**: [Iris Project](https://iris-project.org/)
>
> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)

在形式化研究 Rust 时，以下国际论文与项目构成了当前的主流方法：

- **RustBelt** (Jung et al., POPL 2018): 使用 Iris 高阶并发分离逻辑，对 Rust 的核心类型系统和 `unsafe` 库给出了第一个机器检查的安全证明。官方论文 PDF: <https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf>。
- **Aeneas** (Ho & Protzenko, ICFP 2022): 通过 LLBC（Low-Level Borrow Calculus）将安全 Rust 函数式翻译到 F\\*/Coq/Lean，消除了显式内存推理。项目主页: <https://aeneas-verif.github.io/aeneas/>，源码: <https://github.com/AeneasVerif/aeneas>。
- **RustHorn** (Matsushita et al., ESOP 2020 / TOPLAS 2021): 基于约束 Horn 子句（CHC）的 Rust 程序验证，利用所有权信息消除指针与堆。论文 PDF: <https://www.kb.is.s.u-tokyo.ac.jp/old-users/yskm24t/web/papers/esop2020-rust-horn.pdf>。
- **RustHornBelt** (Matsushita, Denis, Jourdan, Dreyer, PLDI 2022): 扩展 RustBelt，为带 `unsafe` 代码的 Rust 程序功能正确性提供语义基础。论文 PDF: <https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf>。
- **Iris** (Jung et al., POPL 2015 / JFP 2018): 高阶并发分离逻辑框架，RustBelt 的证明基础。主页: <https://iris-project.org/>，Coq 实现: <https://gitlab.mpi-sws.org/iris/iris>。
- **λRust** (RustBelt 的 Coq 形式化): RustBelt 在 Iris 中的操作语义与类型解释。源码: <https://gitlab.mpi-sws.org/iris/lambda-rust>。

### Iris/RustBelt 风格 Coq 示例
>
> **来源**: [Iris Project](https://iris-project.org/)

下面的 Coq 片段展示 Iris 分离逻辑中 "points-to" 断言如何表达所有权（与 RustBelt 对 `Box`/`&mut` 的解释一致）:

```coq
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.

(* 位置 l 拥有值 v，对应 RustBelt 中 Box/唯一所有权的资源解释 *)
Definition own_box (l: loc) (v: val) : iProp Σ := l ↦ v.

Lemma own_box_write `{!heapG Σ} (l: loc) (v w: val) :
  l ↦ v -∗ (l ↦ w -∗ Φ) -∗ WP (Write (LitV (LitLoc l)) (LitV w)) {{ v, Φ }}.
Proof.
  iIntros "Hl Hk". wp_write. iApply "Hk". iFrame.
Qed.
```

> 说明：上述示例为示意性 Iris/Coq 代码，展示 RustBelt 如何将所有权建模为分离逻辑资源。完整可机器检查的证明请参考 [λRust](https://gitlab.mpi-sws.org/iris/lambda-rust) 与 [RustBelt 论文](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)。

### Lean 4 / Aeneas 后端示例
>
> **来源**: [Aeneas](https://aeneas-verif.github.io/aeneas/)

Aeneas 将 Rust 的安全子集提取为 Lean 4（或 F\\*/Coq/HOL4）中的纯函数，利用 Rust 借用检查保证消除内存推理：

```lean4
-- Aeneas 生成的 Lean 4 函数签名示例（Result monad 区分 ok/fail/div）
def take_max (a b : U32) : Result U32 :=
  if a ≥ b then ok a else ok b
```

> 说明：Aeneas 的 Lean 后端要求使用 Charon 生成 `.llbc` 文件，再在 Aeneas 中选择 `-backend lean`。详见 [Aeneas 文档](https://aeneas-verif.github.io/aeneas/) 与 [Charon](https://github.com/AeneasVerif/charon)。

### 相关概念""",
)

# References - method papers
t1 = t1.replace(
    """### 方法论文献
>
> **[来源: [crates.io](https://crates.io/)]**

- [研究方法索引](../rust-formal-engineering-system/09_research_agenda/04_research_methods/README.md)
- [研究工具指南](../rust-formal-engineering-system/09_research_agenda/04_research_methods/README.md)""",
    """### 方法论文献
>
> **[来源: [Iris Project](https://iris-project.org/)]**

- [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf) (Jung et al., POPL 2018) — Rust 核心安全性的 Iris/Coq 机器检查证明。
- [Iris from the Ground Up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf) (Jung et al., JFP 2018) — 高阶并发分离逻辑基础。
- [Aeneas: Rust Verification by Functional Translation](https://zenodo.org/records/6672939) (Ho & Protzenko, ICFP 2022) — 基于 LLBC 的函数式翻译验证。
- [Sound Borrow-Checking for Rust via Symbolic Semantics](https://dl.acm.org/doi/pdf/10.1145/3547647) (Ho & Protzenko, ICFP 2024) — Aeneas 符号执行与借用检查的形式化。
- [RustHorn: CHC-based Verification for Rust Programs](https://www.kb.is.s.u-tokyo.ac.jp/old-users/yskm24t/web/papers/esop2020-rust-horn.pdf) (Matsushita et al., ESOP 2020 / TOPLAS 2021) — CHC 自动验证。
- [RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf) (Matsushita et al., PLDI 2022) — 带 `unsafe` 代码的功能正确性基础。
- [λRust Coq Development](https://gitlab.mpi-sws.org/iris/lambda-rust) — RustBelt 在 Iris 中的操作语义与类型解释。""",
)

# References - tool docs
t1 = t1.replace(
    """### 工具文档
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [研究工具使用指南](10_tools_guide.md) - 详细的工具安装和使用方法
- Criterion.rs 文档
- [Miri 文档](https://github.com/rust-lang/miri)
- Prusti 文档""",
    """### 工具文档
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [研究工具使用指南](10_tools_guide.md) - 详细的工具安装和使用方法
- [Kani Rust Verifier](https://model-checking.github.io/kani/) — 模型检查器
- [Prusti User Guide](https://viperproject.github.io/prusti-dev/user-guide/) — 基于 Viper 的演绎验证器
- [Miri](https://github.com/rust-lang/miri) — Rust MIR 解释器与 UB 检测
- [Creusot](https://creusot-rs.github.io/) — 基于 Why3/SMT 的 Rust 演绎验证
- [Aeneas](https://aeneas-verif.github.io/aeneas/) — 函数式翻译验证工具链
- [Verus](https://verus-lang.github.io/verus/) — 面向系统代码的 SMT 验证器
- [Criterion.rs](https://bheisler.github.io/criterion.rs/book/) — 统计驱动基准测试""",
)

# References - best practices
t1 = t1.replace(
    """### 最佳实践
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

- Rust 研究最佳实践
- 性能研究指南
- [形式化验证指南](https://doc.rust-lang.org/book/ch19-00-advanced-topics.html)""",
    """### 最佳实践
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) — 官方 API 设计指南
- [Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html) — 官方 lint 文档
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) — 高级与 unsafe Rust 指南
- [The Rust Programming Language](https://doc.rust-lang.org/book/) — 官方 Rust 教程
- 性能研究指南
- [形式化验证指南](https://doc.rust-lang.org/book/ch19-00-advanced-topics.html)""",
)

# Replace old 1.94 section + final meta before "## 相关概念"
t1_new_section = """## 🆕 权威国际化内容升级 (Rust 1.96.0+)
>
> **来源**: [Rust Research Methodology Group]

> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本次升级要点

- 补充 Rust 形式化方法的国际权威论文索引：RustBelt、Aeneas、RustHorn、RustHornBelt、Iris。
- Coq/Lean 示例对齐 Iris/RustBelt 的分离逻辑与生命周期逻辑。
- 方法论文献与工具文档增加官方 PDF、GitHub、项目主页链接。
- 删除旧版 Rust 1.94 模板内容，状态更新为 ✅ 完成。

---

**维护者**: Rust Research Methodology Group
**最后更新**: 2026-06-29 (权威国际化内容升级)
**状态**: ✅ 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf), [Iris Project](https://iris-project.org/), [Aeneas](https://aeneas-verif.github.io/aeneas/), [RustHorn](https://www.kb.is.s.u-tokyo.ac.jp/old-users/yskm24t/web/papers/esop2020-rust-horn.pdf)
>
> **权威来源对齐变更日志**: 2026-06-29 新增 RustBelt、Aeneas、RustHorn、Iris 等国际形式化方法来源 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.2
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 相关概念"""

t1 = re.sub(
    r"## 🆕 Rust 1\.94 深度整合更新.*?---\n\n## 相关概念",
    t1_new_section,
    t1,
    count=1,
    flags=re.DOTALL,
)

write_file(f1, t1)
print(f"Updated {f1.name}")


# ============================================================
# File 2: 10_tools_guide.md
# ============================================================
f2 = ROOT / "10_tools_guide.md"
t2 = read_file(f2)

t2 = t2.replace(OLD_HEADER_STATUS, NEW_HEADER_STATUS)

# maintenance block
t2 = t2.replace(
    "**维护团队**: Rust Research Community\n"
    "**最后更新**: 2026-01-26\n"
    "**状态**: ✅ **Rust 1.93.1+ 更新完成**",
    "**维护团队**: Rust Research Community\n"
    "**最后更新**: 2026-06-29\n"
    "**状态**: ✅ 完成",
)

# Prusti resources
t2 = t2.replace(
    """**相关资源**:

- Prusti 文档
- Prusti 用户指南
- [Prusti 教程](https://viperproject.github.io/prusti-dev/user-guide/getting-started.html)""",
    """**版本与官方资源**:

- 最新版本：跟随 [Prusti GitHub Releases](https://github.com/viperproject/prusti-dev/releases) 发布；VS Code 用户推荐通过 [Prusti Assistant](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant) 获取最新版。
- [Prusti 用户指南](https://viperproject.github.io/prusti-dev/user-guide/)
- [Prusti 教程 - Getting Started](https://viperproject.github.io/prusti-dev/user-guide/getting-started.html)
- [Prusti GitHub](https://github.com/viperproject/prusti-dev)
- [Prusti 论文：The Prusti Project](https://pm.inf.ethz.ch/publications/AstrauskasBilyFialaGrannanMathejaMuellerPoliSummers22.pdf)""",
)

# Kani resources
t2 = t2.replace(
    """**相关资源**:

- [Kani 文档](https://github.com/model-checking/kani)
- Kani 用户指南
- [Kani 教程](https://model-checking.github.io/kani/tutorial.html)""",
    """**版本与官方资源**:

- 推荐版本：**0.67.0+**（截至 2026-04，以 [Kani GitHub Releases](https://github.com/model-checking/kani/releases) 最新 tag 为准）。
- [Kani 官方文档 / The Kani Rust Verifier](https://model-checking.github.io/kani/)
- [Kani API Docs (docs.rs)](https://docs.rs/kani-verifier/latest)
- [Kani GitHub](https://github.com/model-checking/kani)
- [Kani 教程](https://model-checking.github.io/kani/tutorial.html)
- 安装命令：`cargo install --locked kani-verifier && cargo kani setup`""",
)

# Miri resources
t2 = t2.replace(
    """**相关资源**:

- [Miri 文档](https://github.com/rust-lang/miri)
- [Miri 用户指南](https://github.com/rust-lang/miri#usage)""",
    """**版本与官方资源**:

- 版本：通过 `rustup component add miri` 安装，版本跟随当前工具链（nightly 优先）。
- [Miri GitHub](https://github.com/rust-lang/miri)
- [Miri 使用指南](https://github.com/rust-lang/miri#usage)
- [rustc dev guide - Miri](https://rustc-dev-guide.rust-lang.org/miri.html)
- 推荐标志：`-Zmiri-tag-raw-pointers`、`-Zmiri-disable-isolation`（视测试场景而定）""",
)

# Add Creusot/Aeneas/Verus before Coq/Lean optional
t2 = t2.replace(
    "### 可选进阶：Coq/Lean",
    """### Creusot

> **来源**: [Creusot](https://creusot-rs.github.io/)
>
> **来源**: [Why3](http://why3.lri.fr/)

**用途**: 基于 Why3/SMT 的 Rust 演绎验证器，支持函数契约（pre/post）、循环不变式与 ghost 代码。

**安装**:
```bash
# 需要 OPAM、Why3、Alt-Ergo 等辅助工具
git clone https://github.com/creusot-rs/creusot.git
cd creusot
cargo install --path creusot-rustc
cargo install --path cargo-creusot
cargo creusot setup install
```

**基本使用**:
```rust,ignore
use creusot_contracts::*;

#[requires(x >= 0)]
#[ensures(result >= x)]
fn increment(x: i32) -> i32 {
    x + 1
}
```

**版本与官方资源**:
- 推荐版本：**0.1.1+**（以 [Creusot GitHub Releases](https://github.com/creusot-rs/creusot/releases) 为准）；依赖特定 nightly Rust。
- [Creusot 主页](https://creusot-rs.github.io/)
- [Creusot GitHub](https://github.com/creusot-rs/creusot)
- [CreuSAT - 经 Creusot 验证的 SAT 求解器](https://github.com/sarsko/CreuSAT)

---

### Aeneas

> **来源**: [Aeneas](https://aeneas-verif.github.io/aeneas/)
>
> **来源**: [Charon](https://github.com/AeneasVerif/charon)

**用途**: 将安全 Rust 通过 LLBC 函数式翻译到 F\\*/Coq/Lean/HOL4，消除显式内存推理。

**安装与使用**:
```bash
# 1. 用 Charon 生成 .llbc
charon cargo --preset=aeneas
# 2. 用 Aeneas 翻译到目标证明助手
./bin/aeneas -backend lean|coq|fstar|hol4 file.llbc
```

**版本与官方资源**:
- 推荐版本：以 [Aeneas GitHub](https://github.com/AeneasVerif/aeneas) 最新 commit 为准；与 Charon 版本需匹配。
- [Aeneas 文档](https://aeneas-verif.github.io/aeneas/)
- [Aeneas GitHub](https://github.com/AeneasVerif/aeneas)
- [Charon GitHub](https://github.com/AeneasVerif/charon)
- [Aeneas 论文 (ICFP 2022)](https://zenodo.org/records/6672939)

---

### Verus

> **来源**: [Verus](https://verus-lang.github.io/verus/)

**用途**: 面向低层系统代码的 Rust 验证器，使用 SMT 求解器静态检查可执行 Rust 代码是否满足规约。

**安装**:
```bash
git clone https://github.com/verus-lang/verus.git
cd verus/source
# 按仓库 README 安装依赖并运行 vargo build
```

**基本使用**:
```rust,ignore
use vstd::prelude::*;

verus! {
    fn increment(x: u32) -> (y: u32)
        requires x < u32::MAX,
        ensures y == x + 1,
    {
        x + 1
    }
}
```

**版本与官方资源**:
- 推荐版本：以 [Verus GitHub](https://github.com/verus-lang/verus) 最新 commit / release 为准。
- [Verus 官方文档](https://verus-lang.github.io/verus/)
- [Verus GitHub](https://github.com/verus-lang/verus)
- [Verus 教程与参考](https://verus-lang.github.io/verus/guide/)
- [Verus 标准库 API](https://verus-lang.github.io/verus/verusdoc/vstd/)

---

### 可选进阶：Coq/Lean""",
)

# Expand related resources and add Cargo/rustc section
t2 = t2.replace(
    """## 🔗 相关资源 {#-相关资源}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [研究方法论](10_research_methodology.md) - 研究方法概述
- [实验研究索引](experiments/README.md) - 实验研究工具
- [形式化方法索引](formal_methods/README.md) - 形式化工具""",
    """## 🔗 相关资源 {#-相关资源}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [研究方法论](10_research_methodology.md) - 研究方法概述
- [实验研究索引](experiments/README.md) - 实验研究工具
- [形式化方法索引](formal_methods/README.md) - 形式化工具
- [Rust 异步编程](https://rust-lang.github.io/async-book/)
- [Rust 性能指南](https://nnethercote.github.io/perf-book/)

## 📚 Cargo Book 与 rustc dev guide 权威章节

> **来源**: [The Cargo Book](https://doc.rust-lang.org/cargo/)
>
> **来源**: [rustc dev guide](https://rustc-dev-guide.rust-lang.org/)

### Cargo Book 重点章节

| 章节 | 链接 | 用途 |
| :--- | :--- | :--- |
| 指定依赖 | [specifying-dependencies.html](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) | 语义版本、git/path 依赖、features |
| 工作空间 | [workspaces.html](https://doc.rust-lang.org/cargo/reference/workspaces.html) | 多 crate 管理与统一构建 |
| 编译配置 (Profiles) | [profiles.html](https://doc.rust-lang.org/cargo/reference/profiles.html) | `dev`/`release`、`opt-level`、`lto` |
| 构建脚本 | [build-scripts.html](https://doc.rust-lang.org/cargo/reference/build-scripts.html) | `build.rs` 与 FFI/代码生成 |
| 发布到 crates.io | [publishing.html](https://doc.rust-lang.org/cargo/reference/publishing.html) | 版本发布与元数据 |
| 环境变量 | [environment-variables.html](https://doc.rust-lang.org/cargo/reference/environment-variables.html) | `CARGO_*` 与构建环境 |

### rustc dev guide 重点章节

| 章节 | 链接 | 用途 |
| :--- | :--- | :--- |
| 编译器概览 | [overview.html](https://rustc-dev-guide.rust-lang.org/overview.html) | 编译管线与查询系统 |
| HIR | [hir.html](https://rustc-dev-guide.rust-lang.org/hir.html) | 高级中间表示 |
| MIR | [mir/index.html](https://rustc-dev-guide.rust-lang.org/mir/index.html) | 中阶中间表示，借用检查与优化的基础 |
| 借用检查 | [borrow_check.html](https://rustc-dev-guide.rust-lang.org/borrow_check.html) | NLL/Polonius 与生命周期检查 |
| 类型推断 | [type-inference.html](https://rustc-dev-guide.rust-lang.org/type-inference.html) | 类型系统实现 |
| trait 系统 | [traits/resolution.html](https://rustc-dev-guide.rust-lang.org/traits/resolution.html) | trait 解析与 coherence |
| 代码生成 | [backend/index.html](https://rustc-dev-guide.rust-lang.org/backend/index.html) | LLVM 后端与目标平台 |
| Miri | [miri.html](https://rustc-dev-guide.rust-lang.org/miri.html) | Miri 解释器架构 |""",
)

# Replace old 1.94 section + final meta
t2_new_section = """## 🆕 权威国际化内容升级 (Rust 1.96.0+)
>
> **来源**: [Rust Research Community]

> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本次升级要点

- 补充 Kani、Prusti、Miri、Creusot、Aeneas、Verus 的官方文档链接与版本信息。
- 新增 Cargo Book、rustc dev guide 重点章节索引。
- 删除旧版 Rust 1.94 模板内容，状态更新为 ✅ 完成。

---

**维护者**: Rust Research Community
**最后更新**: 2026-06-29 (权威国际化内容升级)
**状态**: ✅ 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [The Cargo Book](https://doc.rust-lang.org/cargo/), [rustc dev guide](https://rustc-dev-guide.rust-lang.org/)
>
> **权威来源对齐变更日志**: 2026-06-29 新增 Cargo Book、rustc dev guide、Kani/Prusti/Miri/Creusot/Aeneas/Verus 官方文档与版本信息 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.2
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 相关概念"""

t2 = re.sub(
    r"## 🆕 Rust 1\.94 深度整合更新.*?---\n\n## 相关概念",
    t2_new_section,
    t2,
    count=1,
    flags=re.DOTALL,
)

write_file(f2, t2)
print(f"Updated {f2.name}")


# ============================================================
# File 3: 10_research_roadmap.md
# ============================================================
f3 = ROOT / "10_research_roadmap.md"
t3 = read_file(f3)

t3 = t3.replace(OLD_HEADER_STATUS, NEW_HEADER_STATUS)

# Insert roadmap sync section before "## 🔄 研究优先级"
t3 = t3.replace(
    "---\n\n## 🔄 研究优先级 {#-研究优先级}",
    """---

## 🌐 与 Rust 官方发布路线图的同步
>
> **来源**: [Rust Blog](https://blog.rust-lang.org/)
>
> **来源**: [releases.rs](https://releases.rs/)
>
> **来源**: [Rust RFCs](https://github.com/rust-lang/rfcs)
>
> **来源**: [Rust Forge](https://forge.rust-lang.org/)

本路线图与 Rust 官方发布节奏、RFC 进程及 Forge 治理文档保持同步：

| 官方来源 | 链接 | 在本路线图中的用途 |
| :--- | :--- | :--- |
| Rust Blog | <https://blog.rust-lang.org/> | 跟踪稳定版发布、Edition 演进与安全公告 |
| releases.rs | <https://releases.rs/> | 查看最新/下一个稳定版特性与发布日期 |
| Rust RFCs | <https://github.com/rust-lang/rfcs> | 对照语言特性设计（如 RFC 2394 async/await、RFC 2094 NLL、RFC 1522/1951 impl Trait） |
| Rust Forge | <https://forge.rust-lang.org/> | 团队治理、发布流程、平台支持策略 |
| Rust Reference | <https://doc.rust-lang.org/reference/> | 阶段一类型理论与阶段二形式化证明的权威语义依据 |

**同步说明**：
- 阶段一（类型系统基础）参考 Rust Reference 与 RFC 738（型变）、RFC 141（生命周期省略）等。
- 阶段二（形式化验证）对照 RustBelt/Aeneas 论文与 RFC 1966（unsafe 指针改革）等。
- 阶段三（实验研究）结合 Rust Blog 的性能发布说明与 rustc dev guide 的编译器章节。
- 阶段四（综合应用）依据 Rust API Guidelines、Nomicon 与 RFC 流程落地最佳实践。

---

## 🔄 研究优先级 {#-研究优先级}""",
)

# maintenance block
t3 = t3.replace(
    "**维护团队**: Rust Research Community\n"
    "**最后更新**: 2026-02-28\n"
    "**状态**: ✅ **路线图 17/17 项已 100% 完成**（含 formal_methods 2.5 完备性缺口）",
    "**维护团队**: Rust Research Community\n"
    "**最后更新**: 2026-06-29\n"
    "**状态**: ✅ 完成",
)

# Replace old 1.94 section + final meta
t3_new_section = """## 🆕 权威国际化内容升级 (Rust 1.96.0+)
>
> **来源**: [Rust Research Community]

> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本次升级要点

- 新增「与 Rust 官方发布路线图的同步」章节，引用 Rust Blog、releases.rs、RFCs、Rust Forge。
- 删除旧版 Rust 1.94 模板内容，状态更新为 ✅ 完成。

---

**维护者**: Rust Research Community
**最后更新**: 2026-06-29 (权威国际化内容升级)
**状态**: ✅ 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Blog](https://blog.rust-lang.org/), [releases.rs](https://releases.rs/), [Rust RFCs](https://github.com/rust-lang/rfcs), [Rust Forge](https://forge.rust-lang.org/)
>
> **权威来源对齐变更日志**: 2026-06-29 新增 Rust Blog、releases.rs、RFCs、Rust Forge 官方路线图来源 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.2
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 相关概念"""

t3 = re.sub(
    r"## 🆕 Rust 1\.94 深度整合更新.*?---\n\n## 相关概念",
    t3_new_section,
    t3,
    count=1,
    flags=re.DOTALL,
)

write_file(f3, t3)
print(f"Updated {f3.name}")


# ============================================================
# File 4: 10_best_practices.md
# ============================================================
f4 = ROOT / "10_best_practices.md"
t4 = read_file(f4)

t4 = t4.replace(OLD_HEADER_STATUS, NEW_HEADER_STATUS)

# Insert alignment section before "## 🔗 相关资源 {#-相关资源}"
t4 = t4.replace(
    "---\n\n## 🔗 相关资源 {#-相关资源}",
    """---

## 🎯 与 Rust 官方规范的对齐
>
> **来源**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
>
> **来源**: [Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html)
>
> **来源**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)

研究笔记的代码示例、API 设计与安全讨论应与以下官方规范保持一致：

### Rust API Guidelines

- **C-CASE**: 命名符合 RFC 430（类型 CamelCase、函数 snake_case）。
- **C-CONV**: 转换方法使用 `as_`（免费/借用）、`to_`（昂贵）、`into_`（消耗）。
- **C-GETTER**: Getter 省略 `get_` 前缀，直接使用字段名。
- **C-COMMON-TRAITS**: 公共类型尽早实现 `Copy、Clone、Eq、PartialEq、Ord、PartialOrd、Hash、Debug、Display、Default`。
- **C-SEND-SYNC**: 类型应尽可能实现 `Send`/`Sync`（手动实现为 unsafe，需严格论证）。
- **C-GOOD-ERR**: 错误类型实现 `std::error::Error + Send + Sync`，并提供清晰 `Display`。
- 完整清单见 [Rust API Guidelines Checklist](https://rust-lang.github.io/api-guidelines/checklist.html)。

### Clippy lint 文档

- **correctness**: 可能产生错误结果的代码（如 `absurd_extreme_comparisons`）。
- **suspicious**: 很可能是 bug 的代码（如 `double_must_use`）。
- **style**: 不符合 Rust 风格的写法（如 `needless_return`）。
- **complexity**: 过度复杂的写法（如 `too_many_arguments`）。
- **perf**: 性能反模式（如 `vec_init_then_push`）。
- 完整 lint 列表与示例见 [Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html)。

### Nomicon 重点章节

| 主题 | Nomicon 章节 | 说明 |
| :--- | :--- | :--- |
| Unsafe 能力边界 | [what-unsafe-does.html](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) | `unsafe` 允许的五种额外操作 |
| 行为 considered UB | [what-unsafe-does.html#behavior-considered-undefined](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) | 语言层面的未定义行为清单 |
| 生命周期省略 | [lifetime-elision.html](https://doc.rust-lang.org/nomicon/lifetime-elision.html) | 函数签名中的生命周期推断 |
| 子类型与型变 | [subtyping-and-variance.html](https://doc.rust-lang.org/nomicon/subtyping-and-variance.html) | 协变/逆变/不变与内存安全 |
| 发送与同步 | [send-and-sync.html](https://doc.rust-lang.org/nomicon/send-and-sync.html) | `Send`/`Sync` 的语义与手动实现 |
| 未初始化内存 | [uninitialized.html](https://doc.rust-lang.org/nomicon/uninitialized.html) | `MaybeUninit` 与 unsafe 初始化 |

### Rust Book 重点章节

| 主题 | Rust Book 章节 | 说明 |
| :--- | :--- | :--- |
| 所有权与借用 | [ch04-00-understanding-ownership.html](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) | 所有权、借用、slice |
| 泛型与 trait | [ch10-00-generics.html](https://doc.rust-lang.org/book/ch10-00-generics.html) | 泛型、trait、生命周期 |
| 迭代器与闭包 | [ch13-00-functional-features.html](https://doc.rust-lang.org/book/ch13-00-functional-features.html) | 闭包、迭代器 |
| 并发编程 | [ch16-00-concurrency.html](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | 线程、`Mutex`、`Arc`、Send/Sync |
| 高级 trait / unsafe | [ch19-00-advanced-features.html](https://doc.rust-lang.org/book/ch19-00-advanced-features.html) | 不安全 Rust、高级 trait、宏 |

> 实践建议：在编写研究笔记的代码示例时，先运行 `cargo clippy -- -W clippy::all`，并对 unsafe 段落给出对应 Nomicon 章节的引用。

---

## 🔗 相关资源 {#-相关资源}""",
)

# maintenance block
t4 = t4.replace(
    "**维护团队**: Rust Research Community\n"
    "**最后更新**: 2026-02-12\n"
    "**状态**: ✅ **100% 完成**（含形式化衔接、实质内容检查表、Rust 示例与定理对应）",
    "**维护团队**: Rust Research Community\n"
    "**最后更新**: 2026-06-29\n"
    "**状态**: ✅ 完成",
)

# Replace from first "Rust 1.94 研究更新" through final meta
t4_new_section = """## 🆕 权威国际化内容升级 (Rust 1.96.0+)
>
> **来源**: [Rust Research Community]

> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本次升级要点

- 新增「与 Rust 官方规范的对齐」章节，系统引用 Rust API Guidelines、Clippy lint 文档、Nomicon、Rust Book 具体章节。
- 删除旧版 Rust 1.94 模板内容，状态更新为 ✅ 完成。

---

**维护者**: Rust Research Community
**最后更新**: 2026-06-29 (权威国际化内容升级)
**状态**: ✅ 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/), [Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html), [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-06-29 新增 Rust API Guidelines、Clippy、Nomicon、Rust Book 章节对齐 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.2
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 相关概念"""

t4 = re.sub(
    r"## 🆕 Rust 1\.94 研究更新.*?---\n\n## 相关概念",
    t4_new_section,
    t4,
    count=1,
    flags=re.DOTALL,
)

write_file(f4, t4)
print(f"Updated {f4.name}")


# ============================================================
# File 5: 10_practical_applications.md
# ============================================================
f5 = ROOT / "10_practical_applications.md"
t5 = read_file(f5)

t5 = t5.replace(OLD_HEADER_STATUS, NEW_HEADER_STATUS)

# References - actual projects
t5 = t5.replace(
    """### 实际项目
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [Tokio](https://tokio.rs/) - 异步运行时
- [Actix-web](https://actix.rs/) - Web 框架
- [Rocket](https://rocket.rs/) - Web 框架""",
    """### 实际项目
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [Redox OS](https://www.redox-os.org/) - 类 Unix 操作系统
- [Tokio](https://tokio.rs/) - 异步运行时
- [Actix-web](https://actix.rs/) - Web 框架
- [Linkerd](https://linkerd.io/) - 服务网格
- [TiKV](https://tikv.org/) - 分布式键值存储
- [ScyllaDB Rust Driver](https://rust-driver.docs.scylladb.com/) - NoSQL 驱动
- [Tock](https://www.tockos.org/) - 嵌入式操作系统
- [Drone](https://book.drone-os.com/) - 实时操作系统框架
- [Firecracker](https://firecracker-microvm.github.io/) - 微虚拟机
- [Axum](https://docs.rs/axum/) - 模块化 Web 框架
- [Rocket](https://rocket.rs/) - Web 框架""",
)

# References - related docs
t5 = t5.replace(
    """### 相关文档
>
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

- [Rust 异步编程](https://rust-lang.github.io/async-book/)
- [Rust 性能指南](https://nnethercote.github.io/perf-book/)""",
    """### 相关文档
>
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

- [Rust 异步编程](https://rust-lang.github.io/async-book/)
- [Rust 性能指南](https://nnethercote.github.io/perf-book/)
- [TechEmpower Framework Benchmarks](https://www.techempower.com/benchmarks/)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)""",
)

# Insert official docs/benchmarks + mechanism mapping before "## 📖 参考文献"
t5 = t5.replace(
    "---\n\n## 📖 参考文献 {#-参考文献}",
    """---

## 🌐 案例官方文档、源码与基准索引
>
> **来源**: [Rust Official Docs](https://doc.rust-lang.org/)

为便于复现与深入研究，每个案例应链接到官方文档、源码仓库及公开基准：

| 案例 | 官方文档 | 源码仓库 | 性能基准 / 案例研究 |
| :--- | :--- | :--- | :--- |
| Redox OS | [redox-os.org](https://www.redox-os.org/) | [redox-os/redox](https://gitlab.redox-os.org/redox-os/redox) | 系统调用与微内核评估见项目文档 |
| Tokio | [tokio.rs](https://tokio.rs/) | [tokio-rs/tokio](https://github.com/tokio-rs/tokio) | [TechEmpower](https://www.techempower.com/benchmarks/)、仓库内 `benches/` |
| Actix-web | [actix.rs](https://actix.rs/) | [actix/actix-web](https://github.com/actix/actix-web) | [TechEmpower](https://www.techempower.com/benchmarks/)、仓库 `benches/` |
| Linkerd | [linkerd.io](https://linkerd.io/) | [linkerd2-proxy](https://github.com/linkerd2/linkerd2-proxy) | 官方性能报告与负载测试文档 |
| TiKV | [tikv.org](https://tikv.org/) | [tikv/tikv](https://github.com/tikv/tikv) | 仓库 `benches/`、[TiKV 性能白皮书](https://tikv.org/) |
| ScyllaDB Rust 驱动 | [Rust Driver Docs](https://rust-driver.docs.scylladb.com/) | [scylladb/scylla-rust-driver](https://github.com/scylladb/scylla-rust-driver) | 官方 benchmark 与 examples |
| Tock | [tockos.org](https://www.tockos.org/) | [tock/tock](https://github.com/tock/tock) | 嵌入式评估与论文 |
| Drone | [Drone OS Book](https://book.drone-os.com/) | [drone-os/drone](https://github.com/drone-os/drone) | 实时性评估见文档 |
| Firecracker | [firecracker-microvm.github.io](https://firecracker-microvm.github.io/) | [firecracker-microvm/firecracker](https://github.com/firecracker-microvm/firecracker) | 官方 microVM 启动与密度基准 |
| Axum (案例 1) | [docs.rs/axum](https://docs.rs/axum/) | [tokio-rs/axum](https://github.com/tokio-rs/axum) | [TechEmpower](https://www.techempower.com/benchmarks/) |

> 建议：在引用性能数据时，应注明测试版本、硬件环境与负载模型；优先使用 TechEmpower 或项目官方 `benches/` 的可复现结果。

## 🧭 Rust 机制与官方文档对照
>
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **来源**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **来源**: [Rust RFCs](https://github.com/rust-lang/rfcs)

案例分析中涉及的 Rust 机制可对照以下官方章节与 RFC：

| 机制 | Rust Book | Nomicon | RFC |
| :--- | :--- | :--- | :--- |
| 所有权与移动 | [ch04](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) | [ownership.html](https://doc.rust-lang.org/nomicon/ownership.html) | 核心语言设计 |
| 借用与生命周期 | [ch10](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) | [lifetimes.html](https://doc.rust-lang.org/nomicon/lifetimes.html)、[lifetime-elision.html](https://doc.rust-lang.org/nomicon/lifetime-elision.html) | [RFC 141](https://rust-lang.github.io/rfcs/0141-lifetime-elision.html) |
| 异步 / Future | [ch17](https://doc.rust-lang.org/book/ch17-00-async-await.html) | [async-await.html](https://doc.rust-lang.org/nomicon/async-await.html) | [RFC 2394](https://rust-lang.github.io/rfcs/2394-async_await.html) |
| 并发 / Send/Sync | [ch16](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | [send-and-sync.html](https://doc.rust-lang.org/nomicon/send-and-sync.html) | 核心语言设计 |
| Unsafe / 原始指针 | [ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) | [what-unsafe-does.html](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) | [RFC 1966](https://rust-lang.github.io/rfcs/1966-unsafe-pointer-reform.html) |
| impl Trait / 泛型 | [ch10](https://doc.rust-lang.org/book/ch10-02-traits.html) | — | [RFC 1522](https://rust-lang.github.io/rfcs/1522-conservative-impl-trait.html)、[RFC 1951](https://rust-lang.github.io/rfcs/1951-expand-impl-trait.html) |
| 型变 | [ch19.3](https://doc.rust-lang.org/book/ch19-03-advanced-traits.html) | [subtyping-and-variance.html](https://doc.rust-lang.org/nomicon/subtyping-and-variance.html) | [RFC 738](https://rust-lang.github.io/rfcs/0738-variance.html) |
| Error 处理 | [ch09](https://doc.rust-lang.org/book/ch09-00-error-handling.html) | — | [RFC 1859](https://rust-lang.github.io/rfcs/1859-try-trait.html)（`Try` trait） |

---

## 📖 参考文献 {#-参考文献}""",
)

# maintenance block
t5 = t5.replace(
    "**维护者**: Rust Application Research Team\n"
    "**最后更新**: 2026-01-26\n"
    "**状态**: ✅ **已完成** (100%)",
    "**维护者**: Rust Application Research Team\n"
    "**最后更新**: 2026-06-29\n"
    "**状态**: ✅ 完成",
)

# Replace old 1.94 section + final meta
t5_new_section = """## 🆕 权威国际化内容升级 (Rust 1.96.0+)
>
> **来源**: [Rust Application Research Team]

> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本次升级要点

- 补充各案例官方文档、源码仓库与性能基准引用。
- 新增 Rust 机制与 Rust Book、Nomicon、RFCs 的对照表。
- 删除旧版 Rust 1.94 模板内容，状态更新为 ✅ 完成。

---

**维护者**: Rust Application Research Team
**最后更新**: 2026-06-29 (权威国际化内容升级)
**状态**: ✅ 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [The Rustonomicon](https://doc.rust-lang.org/nomicon/), [Rust RFCs](https://github.com/rust-lang/rfcs), [TechEmpower](https://www.techempower.com/benchmarks/)
>
> **权威来源对齐变更日志**: 2026-06-29 新增项目官方文档、源码、性能基准与 Rust 机制对照 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.2
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 相关概念"""

t5 = re.sub(
    r"## 🆕 Rust 1\.94 深度整合更新.*?---\n\n## 相关概念",
    t5_new_section,
    t5,
    count=1,
    flags=re.DOTALL,
)

write_file(f5, t5)
print(f"Updated {f5.name}")

print("\nAll target files updated.")
