# WASM Target Evolution Preview
>
> **受众**: [专家]
> **内容分级**: [综述级]

> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **A+S** — Application + Structure
> **双维定位**: P×Ana — 分析 WASM 目标的演进方向
> **前置依赖**: [WASI](../06_ecosystem/08_wasi.md) · [WebAssembly](../06_ecosystem/11_webassembly.md)
> **后置延伸**: [Rust for WebAssembly](./28_rust_for_webassembly.md)

> **来源**: [WebAssembly Spec](https://webassembly.github.io/spec/) · [WASI Preview 2](https://github.com/WebAssembly/WASI/blob/main/preview2/README.md)

### 10.4 边界测试：WASI 的 capability-based security 与文件系统访问（运行时拒绝）

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

> **修正**: **WASI**（WebAssembly System Interface）的**capability-based security**：1) 程序不能随意访问文件系统，需运行时显式授予（`wasmtime --dir=/tmp`）；2) 类似能力模型：程序持有"capability"（文件描述符），而非拥有全局权限；3) 沙箱化：即使代码被入侵，攻击者只能访问授权资源。对比 POSIX：1) POSIX 进程拥有用户所有权限（一旦运行，可访问用户的全部文件）；2) WASI 的 capability 更细粒度（per-directory、per-file）；3) 未来：网络、环境变量的 capability。Rust 的 WASI target：``wasm32-wasip1` 或 `wasm32-wasip2``（旧）→ ``wasm32-wasip1` 或 `wasm32-wasip2`p1`/``wasm32-wasip1` 或 `wasm32-wasip2`p2`（组件模型）。这与浏览器的同源策略（类似 capability，但基于 origin）或 Android 的权限模型（安装时授予，运行时检查）不同——WASI 的 capability 是传递给运行时的，程序本身声明需要的能力。[来源: [WASI](https://wasi.dev/)] · [来源: [Wasmtime](https://docs.wasmtime.dev/)]
