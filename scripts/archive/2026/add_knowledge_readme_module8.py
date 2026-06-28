#!/usr/bin/env python3
"""为 knowledge/ 下尚未包含模块 8 的 README.md 补充国际化对齐来源。"""

from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "knowledge"
SECTION_HEADER = "## 📚 模块 8: 国际化对齐"


def table(title: str, rows: list[tuple[str, str]]) -> str:
    lines = [f"### {title}", "", "| 来源 | 说明 |", "|:---|:---|"]
    for link, desc in rows:
        lines.append(f"| {link} | {desc} |")
    return "\n".join(lines)


MODULE8_BLOCKS: dict[str, str] = {
    "00_start/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Rust Programming Language — Ch1](https://doc.rust-lang.org/book/ch01-00-getting-started.html) | 官方入门书第 1 章 |
| [Rust 官方安装指南](https://www.rust-lang.org/tools/install) | 工具链安装 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | 官方示例驱动教程 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Rust 所有权与内存安全形式化基础 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/) | 可视化交互式 Rust 教程 |
| [Rustlings](https://github.com/rust-lang/rustlings) | 官方交互式练习 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 |
""",
    "01_fundamentals/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Rust Programming Language — Ch4](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) | 所有权与借用 |
| [Rust Reference — Types](https://doc.rust-lang.org/reference/types.html) | 类型系统规范 |
| [Rust Standard Library](https://doc.rust-lang.org/std/) | 标准库 API |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | 所有权语义形式化 |
| [Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/) | 别名模型 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/) | 可视化所有权教学 |
| [Rustlings](https://github.com/rust-lang/rustlings) | 基础练习 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | 示例驱动学习 |
""",
    "02_intermediate/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Rust Programming Language — Ch10](https://doc.rust-lang.org/book/ch10-00-generics.html) | 泛型、Trait 与生命周期 |
| [Rust Reference — Traits](https://doc.rust-lang.org/reference/items/traits.html) | Trait 规范 |
| [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | API 设计指南 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Trait 对象与泛型语义 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/) | 常用编程模式 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | 中级示例 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区动态 |
""",
    "03_advanced/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rustonomicon](https://doc.rust-lang.org/nomicon/) | Unsafe Rust 权威指南 |
| [The Rust Async Book](https://rust-lang.github.io/async-book/) | 异步编程官方教程 |
| [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) | 内联汇编规范 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Unsafe / Send / Sync 语义 |
| [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) | 别名模型 |
| [Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/) | Miri 默认别名模型 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Tokio Documentation](https://tokio.rs/) | 异步运行时 |
| [Rust for Linux](https://rust-for-linux.com/) | 内核开发 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 |
""",
    "03_advanced/async/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Rust Async Book](https://rust-lang.github.io/async-book/) | 异步编程官方教程 |
| [TRPL Ch17 — Async/Await](https://doc.rust-lang.org/book/ch17-00-async-await.html) | async/await 语法 |
| [Rust Reference — Async Functions](https://doc.rust-lang.org/reference/items/functions.html#async-functions) | async fn 规范 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Future / Pin 语义基础 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Tokio Documentation](https://tokio.rs/) | 主流异步运行时 |
| [smol](https://github.com/smol-rs/smol) | 轻量异步运行时 |
| [Embassy](https://embassy.dev/) | 嵌入式异步框架 |
""",
    "03_advanced/concurrency/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [TRPL Ch16 — Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | 并发基础 |
| [Rustonomicon — Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html) | 并发高级话题 |
| [std::sync](https://doc.rust-lang.org/std/sync/) | 同步原语 API |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Send / Sync 语义 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rayon Documentation](https://docs.rs/rayon/latest/rayon/) | 数据并行 |
| [Crossbeam](https://github.com/crossbeam-rs/crossbeam) | 并发原语库 |
| [Rust Cookbook — Concurrency](https://rust-lang-nursery.github.io/rust-cookbook/concurrency.html) | 并发模式 |
""",
    "03_advanced/macros/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html) | 宏系统规范 |
| [Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html) | 过程宏规范 |
| [Rust By Example — Macros](https://doc.rust-lang.org/rust-by-example/macros.html) | 宏示例 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RFC 1584 — Macros Literal Matcher](https://rust-lang.github.io/rfcs/1584-macros.html) | 宏字面量匹配 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [The Little Book of Rust Macros](https://veykril.github.io/tlborm/) | 宏进阶教程 |
| [Rust Cookbook — Macros](https://rust-lang-nursery.github.io/rust-cookbook/) | 宏模式 |
""",
    "03_advanced/unsafe/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rustonomicon](https://doc.rust-lang.org/nomicon/) | Unsafe Rust 权威指南 |
| [Rust Reference — Unsafe Blocks](https://doc.rust-lang.org/reference/unsafe-blocks.html) | unsafe 块规范 |
| [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) | UB 列表 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Unsafe 边界语义 |
| [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) | 别名模型 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rust for Linux](https://rust-for-linux.com/) | 内核 Unsafe 实践 |
| [Miri](https://github.com/rust-lang/miri) | UB 检测工具 |
""",
    "04_expert/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) | 编译器开发指南 |
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言参考 |
| [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/) | 项目目标 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Rust 形式化基础 |
| [Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/) | 别名模型 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rust Internals Forum](https://internals.rust-lang.org/) | 设计与 RFC 讨论 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 |
""",
    "04_expert/academic/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言规范 |
| [Rust RFCs](https://github.com/rust-lang/rfcs) | 语言演进 RFC |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Rust 形式化基础 |
| [Iris Project](https://iris-project.org/) | 高阶并发分离逻辑框架 |
| [Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/) | 别名模型 |
| [Kani](https://model-checking.github.io/kani/) | 模型检查工具 |
| [Verus](https://verus-lang.github.io/verus/) | 自动证明生态 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Aeneas](https://github.com/AeneasVerif/aeneas) | Rust 形式化验证器 |
| [Rust Formal Methods Interest Group](https://rust-formal-methods.github.io/) | 形式化社区 |
""",
    "04_expert/miri/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Miri](https://github.com/rust-lang/miri) | Miri 解释器仓库 |
| [Rustc Dev Guide — MIRI](https://rustc-dev-guide.rust-lang.org/miri.html) | Miri 在编译器中的位置 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [Stacked Borrows — POPL 2021](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) | 旧默认别名模型 |
| [Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/) | 新默认别名模型 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Miri Book](https://github.com/rust-lang/miri) | Miri 文档 |
| [Rust Internals — Miri](https://internals.rust-lang.org/) | 讨论区 |
""",
    "04_expert/safety_critical/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言规范 |
| [Rust Project Goals — Safety-Critical Rust](https://rust-lang.github.io/rust-project-goals/2026/) | 安全关键领域目标 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [Ferrocene](https://ferrocene.dev/) | Rust 安全关键工具链 |
| [Rust for Linux](https://rust-for-linux.com/) | 内核应用 |
| [seL4](https://sel4.systems/) | 形式化验证操作系统微内核 |
| [MISRA C](https://www.misra.org.uk/) | 安全关键 C 编码标准 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Safety-Critical Rust Community](https://rust-safety-critical.org/) | 安全关键 Rust 社区 |
| [Rust Foundation](https://foundation.rust-lang.org/) | 基金会动态 |
""",
    "05_reference/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言参考 |
| [Rust Standard Library](https://doc.rust-lang.org/std/) | 标准库 API |
| [The Rust Programming Language](https://doc.rust-lang.org/book/) | 官方教程 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | 语义基础 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rust Cheat Sheet](https://cheats.rs/) | 速查表 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | 示例 |
""",
    "06_ecosystem/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Cargo Book](https://doc.rust-lang.org/cargo/) | Cargo 官方文档 |
| [crates.io](https://crates.io/) | 官方包注册表 |
| [docs.rs](https://docs.rs/) | 文档托管 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [SemVer 规范](https://semver.org/) | 语义化版本 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [lib.rs](https://lib.rs/) | 生态索引 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 |
| [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/) | 常用模式 |
""",
    "06_ecosystem/databases/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言规范 |
| [The Cargo Book](https://doc.rust-lang.org/cargo/) | Cargo 依赖管理 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [SQLx](https://github.com/launchbadge/sqlx) | 异步 SQL 工具包 |
| [Diesel](https://diesel.rs/) | 类型安全 ORM |
| [SeaORM](https://www.sea-ql.org/SeaORM/) | 异步 ORM |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rust Database Drivers Working Group](https://github.com/rust-db) | 数据库驱动工作组 |
| [Crates.io — Database](https://crates.io/categories/database) | 数据库分类索引 |
""",
    "06_ecosystem/deep_dives/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言规范 |
| [The Cargo Book](https://doc.rust-lang.org/cargo/) | Cargo 构建与依赖 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [Tokio](https://tokio.rs/) | 异步运行时 |
| [Axum](https://docs.rs/axum/latest/axum/) | Web 框架 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rust Web Framework Benchmarks](https://web-frameworks-benchmark.netlify.app/) | Web 框架基准 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 |
""",
    "06_ecosystem/deployment/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Cargo Book — Profiles](https://doc.rust-lang.org/cargo/reference/profiles.html) | 编译配置 |
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言规范 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [Kubernetes](https://kubernetes.io/) | 容器编排平台 |
| [Docker](https://docs.docker.com/) | 容器化平台 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Shuttle](https://www.shuttle.rs/) | Rust 原生部署平台 |
| [Render — Rust](https://render.com/docs/rust) | 云部署指南 |
| [Fly.io — Rust](https://fly.io/docs/rust/) | 边缘部署指南 |
""",
    "06_ecosystem/emerging/README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rust Blog](https://blog.rust-lang.org/) | 官方博客 |
| [Rust RFCs](https://github.com/rust-lang/rfcs) | 语言演进 RFC |
| [releases.rs](https://releases.rs/) | 版本发布跟踪 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/) | 项目目标 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rust Internals Forum](https://internals.rust-lang.org/) | 设计与 RFC 讨论 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 |
""",
    "README.md": """## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Rust Programming Language](https://doc.rust-lang.org/book/) | 官方教程 |
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言参考 |
| [Rust Standard Library](https://doc.rust-lang.org/std/) | 标准库 API |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Rust 形式化基础 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 |
| [Rustlings](https://github.com/rust-lang/rustlings) | 交互式练习 |
| [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/) | 可视化教学 |
""",
}


def main():
    for rel, block in MODULE8_BLOCKS.items():
        path = ROOT / rel
        if not path.exists():
            print(f"skip (missing): {path}")
            continue
        text = path.read_text(encoding="utf-8")
        if SECTION_HEADER in text:
            print(f"skip (already has module 8): {rel}")
            continue
        # append two blank lines + block
        path.write_text(text.rstrip() + "\n\n\n" + block + "\n", encoding="utf-8")
        print(f"updated: {rel}")


if __name__ == "__main__":
    main()
