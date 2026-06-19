> **生态状态提示**：本文档提及 `async-std` 与/或 `wasm32-wasi`。请注意：
>
> - `async-std` 项目已进入维护模式，2024 年后不再活跃开发；新项目建议优先评估 **Tokio** 或 **smol**。
> - `wasm32-wasi` 旧目标名已重命名为 **`wasm32-wasip1`**；WASI Preview 2 对应目标为 **`wasm32-wasip2`**。

---

# WASM Target Evolution Preview

> **代码状态**: [综述级 — 待补充代码]

>
> **EN**: WASM Target Evolution Preview (Chinese)
> **Summary**: WASM Target Evolution Preview (Chinese). 10.4 边界测试：WASI 的 capability-based security 与文件系统访问（运行时拒绝）.
>
> **受众**: [专家]
> **内容分级**: [综述级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **A+S** — Application + Structure
> **双维定位**: P×Ana — 分析 WASM 目标的演进方向
> **前置依赖**: [WASI](../06_ecosystem/08_wasi.md) · [WebAssembly](../06_ecosystem/11_webassembly.md)
> **后置延伸**: [Rust for WebAssembly](./28_rust_for_webassembly.md)
> **来源**: [WebAssembly Spec](https://webassembly.github.io/spec/) · [WASI Preview 2](https://github.com/WebAssembly/WASI/blob/main/preview2/README.md)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>

## 10.4 边界测试：WASI 的 capability-based security 与文件系统访问（运行时拒绝）

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
> 1) 程序不能随意访问文件系统，需运行时显式授予（`wasmtime --dir=/tmp`）；
> 2) 类似能力模型：程序持有"capability"（文件描述符），而非拥有全局权限；
> 3) 沙箱化：即使代码被入侵，攻击者只能访问授权资源。
>
> 对比 POSIX：
>
> 1) POSIX 进程拥有用户所有权限（一旦运行，可访问用户的全部文件）；
> 2) WASI 的 capability 更细粒度（per-directory、per-file）；
> 3) 未来：网络、环境变量的 capability。
>
> Rust 的 WASI target：`wasm32-wasip1`（旧名 `wasm32-wasi`）→ `wasm32-wasip2`（组件模型）。
> 这与浏览器的同源策略（类似 capability，但基于 origin）或 Android 的权限模型（安装时授予，运行时检查）不同——WASI 的 capability 是传递给运行时的，程序本身声明需要的能力。
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

> **过渡**: 掌握 WASM Target Evolution Preview 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 WASM Target Evolution Preview 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: WASM Target Evolution Preview 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "WASM Target Evolution Preview 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。

## 嵌入式测验（Embedded Quiz）

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
