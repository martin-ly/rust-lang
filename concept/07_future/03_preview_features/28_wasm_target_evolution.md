> **生态状态提示**：
>
> 本文档提及 `async-std` 与/或 `wasm32-wasi`。请注意：
>
> - `async-std` 项目已进入维护模式，2024 年后不再活跃开发；新项目建议优先评估 **Tokio** 或 **smol**。
> - `wasm32-wasi` 旧目标名已重命名为 **`wasm32-wasip1`**；WASI Preview 2 对应目标为 **`wasm32-wasip2`**。
> - 截至 2026-07-09：`wasm32-wasip2` 自 Rust 1.82 起为 **Tier 2** 目标；旧 `wasm32-wasi` 目标已在 Rust 1.84 移除；当前 stable Rust 1.97.0 仍同时提供 `wasm32-wasip1` 与 `wasm32-wasip2`。
> **前置概念**: N/A
>
---

# WASM Target Evolution Preview

> **代码状态**: [伪代码（示意）] — 示例面向 wasm target 与组件模型工具链，未在 rustc 1.97 host target 单文件场景独立编译验证
>
> **EN**: WebAssembly Target Evolution Preview
> **Summary**: Preview of Rust WebAssembly target evolution, including WASI p1/p2, component model, SIMD, threads, GC, and exception handling proposals.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: 🧪 部分 target 已稳定；部分提案仍在实验阶段
> **Rust 属性标记**: `#[stable_target]`（`wasm32-unknown-unknown`、`wasm32-wasip1`）`#[experimental]`（`wasm32-wasip2`、新提案）
> **跟踪版本**: stable 1.82.0+（`wasm32-wasip2` Tier 2）；stable 1.84.0（移除旧 `wasm32-wasi`）
> **预计稳定**: 随 WebAssembly 提案逐步推进
>
> **受众**: [专家]
> **内容分级**: [综述级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A+S** — Application + Structure
> **双维定位**: P×Ana — 分析 WASM 目标的演进方向
> **前置依赖**: [WASI](../../06_ecosystem/05_systems_and_embedded/01_wasi.md) · [WebAssembly](../../06_ecosystem/11_domain_applications/03_webassembly.md) · [Cross Compilation](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md)
> **后置延伸**: [Rust for WebAssembly](../04_research_and_experimental/06_rust_for_webassembly.md)
> **来源**: [Rust Compiler Repository](https://github.com/rust-lang/rust) · [WebAssembly Spec](https://webassembly.github.io/spec/) · [WASI Preview 2](https://github.com/WebAssembly/WASI/blob/main/specifications/wasi-0.2.4/Overview.md) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>

## 一、功能动机：WASM 目标为什么需要演进？

WebAssembly（WASM）本身在不断扩展：从 MVP 到 SIMD、线程、GC、异常处理、组件模型等。Rust 作为 WASM 生态的核心语言，需要跟踪这些提案并调整 target 命名与能力模型。

当前 Rust 的 WASM 目标已经从单一的 `wasm32-unknown-unknown` 演进为一个矩阵：

| Target | 用途 | 状态 |
|:---|:---|:---|
| `wasm32-unknown-unknown` | 浏览器、最小依赖 | 稳定 Tier 2 |
| `wasm32-wasip1` | WASI Preview 1，类 POSIX | 稳定 Tier 2 |
| `wasm32-wasip2` | WASI Preview 2，组件模型 | 稳定 Tier 2（1.82+） |
| `wasm64-unknown-unknown` | 64-bit 线性内存 | 实验性 |

WASM Target Evolution 关注这些 target 的迁移路径、能力差异以及未来提案对 Rust 编译器的影响。

---

## 二、核心概念：target 命名与能力模型

WASM target 命名编码两层信息：**指令目标**（wasm32/wasm64）与**系统接口能力**：

| target | 系统接口 | std 可用性 | 典型宿主 |
|:---|:---|:---|:---|
| `wasm32-unknown-unknown` | 无（裸模块） | `std` 子集（无 I/O、无线程、无时钟） | 浏览器、嵌入式 JS |
| `wasm32-wasip1` | WASI Preview 1（类 POSIX：fd、时钟、随机） | 接近完整 `std` | wasmtime、wasmer |
| `wasm32-wasip2` | WASI Preview 2（组件模型，wit 接口类型） | `std` + 组件世界导入导出 | 组件模型运行时 |

命名演进要点：旧的 `wasm32-wasi` 已重命名为 `wasm32-wasip1`，以给组件模型让出版本化命名空间；`p1`/`p2` 后缀即 WASI 预览版本号。能力模型判定顺序：先问"宿主提供哪些 WASI 世界"，再选 target，而不是反过来。

### 2.1 `wasm32-unknown-unknown`

```bash
# 浏览器端 WASM，无系统接口
cargo build --target wasm32-unknown-unknown
```

这是 Rust 最早的 WASM target，适合浏览器环境，配合 `wasm-bindgen` 与 JavaScript 交互。它没有文件系统、网络、环境变量等能力。

### 2.2 `wasm32-wasip1`（旧 `wasm32-wasi`）

```bash
# WASI Preview 1：类 POSIX 能力
cargo build --target wasm32-wasip1
```

WASI Preview 1 提供文件系统、时钟、随机数等系统接口，但使用 capability-based security 模型：

```bash
wasmtime --dir=/tmp myapp.wasm
```

### 2.3 `wasm32-wasip2`

```bash
# WASI Preview 2：组件模型（Component Model）
cargo build --target wasm32-wasip2
```

WASI Preview 2 引入组件模型，支持：

- 更强的模块（Module）化与接口定义（WIT）；
- 跨语言组件组合；
- 更细粒度的 capability 管理。

---

## 三、未来提案对 Rust 的影响

| 提案 | 状态 | 对 Rust 的影响 |
|:---|:---|:---|
| Threads | 标准化中 | `std::thread` 可在 WASM 中运行 |
| SIMD128 | 已标准化 | `std::simd` 可映射到 WASM SIMD |
| GC | 提案阶段 | 可能减少 Rust/WASM 二进制体积 |
| Exception Handling | 标准化中 | panic 传播更高效 |
| Component Model | Preview 2 | `wasm32-wasip2` 目标 |

### 3.1 启用 target feature 示例

```bash
# 启用 SIMD128
cargo rustc --target wasm32-unknown-unknown -- -C target-feature=+simd128
```

---

## 四、与稳定 Rust 的对比及迁移建议

| 旧用法 | 推荐迁移 |
|:---|:---|
| `wasm32-wasi` | `wasm32-wasip1`（Rust 1.84+ 旧目标已移除） |
| 仅浏览器 WASM | 继续 `wasm32-unknown-unknown` |
| 需要系统接口 | 评估 `wasm32-wasip1` 或 `wasm32-wasip2` |
| 跨语言组件 | `wasm32-wasip2` + `wasm-tools` |

### 4.1 迁移建议

1. **立即替换 `wasm32-wasi`**：Rust 1.84 已移除该目标，CI 和文档应更新为 `wasm32-wasip1`；
2. **新 WASI 项目考虑 `wasm32-wasip2`**：特别是需要组件模型和更严格 capability 管理的场景；
3. **浏览器项目保持 `wasm32-unknown-unknown`**：这是最小、最成熟的路径；
4. **跟踪 `wasm-bindgen` 和 `wasm-tools` 版本**：新 target 需要配套工具链支持。

> **版本说明**：`wasm32-wasip1` 和 `wasm32-wasip2` 在 stable Rust 1.82+ 中可用；旧 `wasm32-wasi` 目标于 Rust 1.84 移除。Threads、SIMD128 等提案通过 `-C target-feature` 控制，成熟度各不相同。

---

## 五、边界测试：WASI 的 capability-based security 与文件系统访问（运行时拒绝）

```rust,ignore
// WASI 程序需要显式 capability
use std::fs;

fn main() {
    // ❌ 运行时拒绝: WASI 默认无文件系统访问权限
    // 需运行时用 --dir 参数授予目录权限
    let contents = fs::read_to_string("/etc/passwd").unwrap();
    println!("{}", contents);
}
```

> **修正**:
> **WASI**（WebAssembly System Interface）的**capability-based security**：
>
> 1) 程序不能随意访问文件系统，需运行时（Runtime）显式授予（`wasmtime --dir=/tmp`）；
> 2) 类似能力模型：程序持有"capability"（文件描述符），而非拥有全局权限；
> 3) 沙箱化：即使代码被入侵，攻击者只能访问授权资源。
>
> 对比 POSIX：
>
> 1) POSIX 进程拥有用户所有权（Ownership）限（一旦运行，可访问用户的全部文件）；
> 2) WASI 的 capability 更细粒度（per-directory、per-file）；
> 3) 未来：网络、环境变量的 capability。
>
> Rust 的 WASI target：`wasm32-wasip1`（旧名 `wasm32-wasi`）→ `wasm32-wasip2`（组件模型）。
> 这与浏览器的同源策略（类似 capability，但基于 origin）或 Android 的权限模型（安装时授予，运行时（Runtime）检查）不同——WASI 的 capability 是传递给运行时的，程序本身声明需要的能力。
> [来源: [WASI](https://wasi.dev/)] ·
> [来源: [Wasmtime](https://docs.wasmtime.dev/)]
> **后置概念**: [Rust Specification](https://www.rust-lang.org/) ·
> [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **WASM Target Evolution Preview** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| WASM Target Evolution Preview 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| WASM Target Evolution Preview 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| WASM Target Evolution Preview 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

## 嵌入式测验（Embedded Quiz）

测验按"命名→机制→演进"递进：前两题检验 target 三元组与 WASI 预览版本的对应关系（记忆层），中间两题检验 Threads/GC 提案对 Rust 内存模型的影响（分析层），末题检验异常处理提案与 `panic` 策略的交互（综合层）。作答建议：涉及"某提案是否已可用"的题目，以 `rustup target list` 与 WASI 官方文档为准——WASM 目标的 tier 与默认组件支持随版本快速变化。

### 测验 1：WASM 的 target 命名为什么从 `wasm32-unknown-unknown` 演进为更多变体？（理解层）

**题目**: WASM 的 target 命名为什么从 `wasm32-unknown-unknown` 演进为更多变体？

<details>
<summary>✅ 答案与解析</summary>

随着 WASM 能力扩展（线程、SIMD、GC、异常处理），需要不同的 target 来启用/禁用这些特性，如 `wasm32-wasip1` 和未来的 `wasm64-unknown-unknown`。
</details>

---

### 测验 2：WASM 的多线程提案（Threads）对 Rust 有什么意义？（理解层）

**题目**: WASM 的多线程提案（Threads）对 Rust 有什么意义？

<details>
<summary>✅ 答案与解析</summary>

允许 Rust 的 `std::thread` 在 WASM 中运行，共享内存通过 `SharedArrayBuffer` 实现。这使 Rust 可以编译使用真正并行的应用到 WASM。
</details>

---

### 测验 3：WASM GC 提案对 Rust 的 `Rc<T>` / `Arc<T>` 有什么潜在影响？（理解层）

**题目**: WASM GC 提案对 Rust 的 `Rc<T>` / `Arc<T>` 有什么潜在影响？

<details>
<summary>✅ 答案与解析</summary>

WASM GC 提供托管对象支持。Rust 目前不使用 WASM GC（线性内存 + 手动管理），未来可能选择性集成以减少二进制体积。
</details>

---

### 测验 4：WASM 的 Exception Handling 提案如何影响 Rust 的 panic 处理？（理解层）

**题目**: WASM 的 Exception Handling 提案如何影响 Rust 的 panic 处理？

<details>
<summary>✅ 答案与解析</summary>

允许 WASM 使用零成本异常机制传递 panic，替代当前的 `unwind` 库实现。可能减小二进制体积并提高 panic 处理性能。
</details>

---

### 测验 5：Rust 编译器如何跟踪 WASM 提案的稳定化状态？（理解层）

**题目**: Rust 编译器如何跟踪 WASM 提案的稳定化状态？

<details>
<summary>✅ 答案与解析</summary>

通过 target feature flags（`-C target-feature=+simd128`）和 `wasm-bindgen` 的功能检测。随着提案成熟，feature 逐渐默认启用。
</details>

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/wasm-bindgen — 生态权威 API 文档](https://docs.rs/wasm-bindgen) · [docs.rs/wasmtime — 生态权威 API 文档](https://docs.rs/wasmtime)
