> **内容分级**: [综述级]
> **本节关键术语**: rustc_driver · rustc_interface · `run_compiler` · Callbacks · `rustc_private` · Stable MIR · `rustc_public` · Compiler Session — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
# rustc Driver、Interface 与 Stable MIR

> **EN**: rustc Driver, rustc_interface, and Stable MIR
> **Summary**: Explains how to drive the Rust compiler programmatically via `rustc_driver` and `rustc_interface`, the `rustc_private` feature, and the goals of Stable MIR (`rustc_public`).
> **受众**: [专家 / 研究者]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **F** — Formal
> **双维定位**: F×Inf — 编译器基础设施与工具接口
> **定位**: 把“如何把 rustc 当库用”讲清楚：driver 的回调机制、interface 的低级 API、以及面向外部工具的 Stable MIR（rustc_public）愿景。
> **前置概念**: [安全边界](../../05_comparative/03_domain_comparisons/04_safety_boundaries.md)
> **后置概念**: [Compiler Infrastructure](47_compiler_infrastructure.md) · [Compiler Diagnostics and UI Tests](69_compiler_diagnostics_and_ui_tests.md)（待补）
> **来源**: [Rustc Dev Guide — rustc_driver](https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html) · [Stable MIR](https://github.com/rust-lang/project-stable-mir) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

> **来源**: [Rustc Dev Guide — rustc_driver and rustc_interface](https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html) ·
> [Rustc Dev Guide — External rustc_drivers](https://rustc-dev-guide.rust-lang.org/rustc-driver/external-rustc-drivers.html) ·
> [Rustc Dev Guide — Interacting with the AST](https://rustc-dev-guide.rust-lang.org/rustc-driver/interacting-with-the-ast.html) ·
> [Rust Project Goals — StableMIR](https://rust-lang.github.io/rust-project-goals/2025h1/stable-mir.html)

---

> **过渡**: 从 rustc Driver、Interface 与 Stabl 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 rustc Driver、Interface 与 Stabl 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 rustc Driver、Interface 与 Stabl 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: rustc Driver、Interface 与 Stabl 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 rustc Driver、Interface 与 Stabl 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 rustc Driver、Interface 与 Stabl 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

## 📑 目录

- [rustc Driver、Interface 与 Stable MIR](#rustc-driverinterface-与-stable-mir)
  - [📑 目录](#-目录)
  - [一、为什么要把 rustc 当库用](#一为什么要把-rustc-当库用)
  - [二、`rustc_driver`：高级入口](#二rustc_driver高级入口)
  - [三、`rustc_interface`：低级控制](#三rustc_interface低级控制)
  - [四、`rustc_private` 与外部 Driver](#四rustc_private-与外部-driver)
  - [五、Stable MIR / `rustc_public`](#五stable-mir--rustc_public)
    - [5.1 问题](#51-问题)
    - [5.2 解决方案](#52-解决方案)
  - [六、典型应用场景](#六典型应用场景)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：`rustc_driver` 和 `rustc_interface` 的主要区别是什么？](#测验-1rustc_driver-和-rustc_interface-的主要区别是什么)
    - [测验 2：外部 crate 使用 `rustc_driver` 需要什么 nightly feature 和组件？](#测验-2外部-crate-使用-rustc_driver-需要什么-nightly-feature-和组件)
    - [测验 3：Stable MIR（rustc\_public）试图解决什么问题？](#测验-3stable-mirrustc_public试图解决什么问题)
    - [测验 4：为什么 rustdoc 更适合用 `rustc_interface` 而不是 `rustc_driver`？](#测验-4为什么-rustdoc-更适合用-rustc_interface-而不是-rustc_driver)
  - [权威来源索引](#权威来源索引)

---

## 一、为什么要把 rustc 当库用

`rustc` 不仅是命令行编译器，它的内部 crate 也可以被外部工具复用：

- **Clippy**: 在编译流程中插入自定义 lint；
- **rustdoc**: 利用 `rustc_interface` 解析和类型检查代码，再提取文档；
- **Miri**: 解释执行 MIR 做 UB 检测；
- **自定义分析工具**: 提取类型、调用图、控制流等信息。

> **关键洞察**: `rustc_driver` 提供“开箱即用”的高级 API；`rustc_interface` 提供可精细控制的低级 API；Stable MIR 则试图提供**不依赖内部 API** 的长期稳定接口。
>
> [Rustc Dev Guide — rustc_driver and rustc_interface](https://rustc-dev-guide.rust-lang.org/rustc-driver.html)(<https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html>)

---

## 二、`rustc_driver`：高级入口

`rustc_driver::run_compiler` 等价于命令行 `rustc` 的 `main` 函数：

```rust,ignore
#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Config;

struct MyCallbacks;

impl Callbacks for MyCallbacks {
    fn config(&mut self, config: &mut Config) {
        // 在这里修改 Compiler 配置
    }

    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        // 在分析阶段后执行自定义逻辑
        Compilation::Stop
    }
}

fn main() {
    run_compiler(
        &["ignored".to_string(), "main.rs".to_string()],
        &mut MyCallbacks,
    );
}
```

`Callbacks` trait 的关键钩子：

| 钩子 | 触发时机 |
|:---|:---|
| `config` | 编译器配置构建后 |
| `after_crate_root_parsing` | 根 crate 解析完成后 |
| `after_expansion` | 宏（Macro）展开完成后 |
| `after_analysis` | 类型检查/借用（Borrowing）检查后 |
| `after_codegen` | 代码生成后 |

---

## 三、`rustc_interface`：低级控制

`rustc_interface` 允许你手动驱动编译的每个阶段：

```rust,ignore
use rustc_interface::interface;

interface::run_compiler(config, |compiler| {
    // 获取 Compiler 后可调用不同阶段函数
    compiler.enter(|queries| {
        queries.parse().unwrap();
        queries.global_ctxt().unwrap();
        // ...
    });
});
```

适合 `rustc_driver` 不够灵活的场景，例如 rustdoc 需要拿到分析结果但不生成二进制。

> **警告**: 这些内部 API 永远不稳定，升级 Rust 版本时可能需要同步修改。
>
> [Rustc Dev Guide — rustc_interface](https://rustc-dev-guide.rust-lang.org/rustc-driver.html)(<https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html#rustc_interface>)

---

## 四、`rustc_private` 与外部 Driver

要在 crate 外部使用 rustc 内部 API，需要启用 `#![feature(rustc_private)]` 并安装额外组件：

```bash
rustup component add rustc-dev llvm-tools
```

| 组件 | 作用 |
|:---|:---|
| `rustc-dev` | 提供 rustc 内部库（如 `rustc_driver`、`rustc_interface`） |
| `llvm-tools` | 提供链接所需的 LLVM 库 |

> **常见错误**: 缺少 `llvm-tools` 时链接会报 `-lLLVM-{version}` 找不到。
>
> [Rustc Dev Guide — External rustc_drivers](https://rustc-dev-guide.rust-lang.org/rustc-driver.html)(<https://rustc-dev-guide.rust-lang.org/rustc-driver/external-rustc-drivers.html>)

---

## 五、Stable MIR / `rustc_public`

### 5.1 问题

直接使用 `rustc_middle::mir` 等内部 API 构建工具的问题是：

- MIR 结构每个版本都可能变化；
- 工具必须锁定 rustc 版本；
- 学习曲线陡峭。

### 5.2 解决方案

**Stable MIR**（项目现更名为 **`rustc_public`**）旨在提供：

- 基于 MIR 的**语义稳定 API**；
- SemVer 版本控制；
- 最终发布到 crates.io，使工具无需依赖 `rustc_private`。

目前仍在 nightly 迭代，预计会先发布 crate 到 crates.io（Rust Project Goal 2025 H1）。

> [Rust Project Goals — StableMIR](https://rust-lang.github.io/rust-project-goals/2025h1/stable-mir.html)(<https://rust-lang.github.io/rust-project-goals/2025h1/stable-mir.html>)

---

## 六、典型应用场景

| 工具 | 使用方式 |
|:---|:---|
| **Clippy** | 通过 `rustc_driver::Callbacks` 注册自定义 lint pass |
| **rustdoc** | 使用 `rustc_interface` 驱动到类型检查阶段，收集文档 |
| **Miri** | 复用 MIR 解释器做动态检查 |
| **Kani** | 基于 Stable MIR 提取模型检测所需信息 |

---

## 嵌入式测验

### 测验 1：`rustc_driver` 和 `rustc_interface` 的主要区别是什么？

<details>
<summary>✅ 答案与解析</summary>

`rustc_driver` 是高级入口，按默认顺序驱动编译并提供 Callbacks 钩子；`rustc_interface` 是低级 API，允许手动控制各个编译阶段。

</details>

---

### 测验 2：外部 crate 使用 `rustc_driver` 需要什么 nightly feature 和组件？

<details>
<summary>✅ 答案与解析</summary>

需要 `#![feature(rustc_private)]`，并安装 `rustc-dev` 和 `llvm-tools` 组件。

</details>

---

### 测验 3：Stable MIR（rustc_public）试图解决什么问题？

<details>
<summary>✅ 答案与解析</summary>

内部 rustc API 不稳定，导致分析工具需要锁定编译器版本。Stable MIR 提供语义稳定、SemVer 管理的 MIR API，降低工具维护成本。

</details>

---

### 测验 4：为什么 rustdoc 更适合用 `rustc_interface` 而不是 `rustc_driver`？

<details>
<summary>✅ 答案与解析</summary>

rustdoc 需要拿到类型检查结果来生成文档，但不需要生成二进制；`rustc_interface` 允许在分析阶段后停止并复用结果，更灵活。

</details>

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rustc Dev Guide — rustc_driver and rustc_interface](https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html) | ✅ 一级 | Driver/Interface 官方文档 |
| [Rustc Dev Guide — External rustc_drivers](https://rustc-dev-guide.rust-lang.org/rustc-driver/external-rustc-drivers.html) | ✅ 一级 | `rustc_private` 官方文档 |
| [Rustc Dev Guide — Interacting with the AST](https://rustc-dev-guide.rust-lang.org/rustc-driver/interacting-with-the-ast.html) | ✅ 一级 | 外部 driver 示例 |
| [Rust Project Goals — StableMIR](https://rust-lang.github.io/rust-project-goals/2025h1/stable-mir.html) | ✅ 一级 | Stable MIR 项目目标 |

---

> **权威来源**: [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/), [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/)
> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.97.0 / rustc_driver / Stable MIR 项目目标

**文档版本**: 1.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-06-21
**状态**: ✅ 已对齐 Rustc Dev Guide driver/interface 文档
