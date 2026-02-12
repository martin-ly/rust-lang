# 支持 vs 不支持边界矩阵

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)

---

## 形式化定义与公理

**Def 1.1（支持边界）**:

设 $F$ 为待实现的功能或模式。定义支持边界函数 $\mathit{SuppB}(F) \in \{\mathrm{Native},\, \mathrm{Lib},\, \mathrm{FFI}\}$：

- **原生支持**：$\mathit{SuppB}(F) = \mathrm{Native}$ 当且仅当 $F$ 可仅用 `std`/`core` 实现，无需 `extern crate`
- **库支持**：$\mathit{SuppB}(F) = \mathrm{Lib}$ 当且仅当 $F$ 需第三方 crate（如 tokio、rayon）
- **需 FFI**：$\mathit{SuppB}(F) = \mathrm{FFI}$ 当且仅当 $F$ 需 `extern` 调用 C/外部库

**Def 1.2（依赖闭包）**:

设 $\mathit{deps}(C)$ 为 crate $C$ 的传递依赖集。若 $\mathit{std} \in \mathit{deps}(C)$ 或 $\mathit{core} \in \mathit{deps}(C)$ 且无其他 crate，则 $\mathit{SuppB}(C) = \mathrm{Native}$。

**Axiom SUM1**：`core` 为 `no_std` 最小子集；`std` 为 `core` 之上扩展（分配、I/O、线程）。

**Axiom SUM2**：`std` 为语言标准库，随编译器分发；第三方 crate 需单独声明。

**定理 SUM-T1**：若模式 $X$ 仅用 `trait`、`impl`、`struct`、`enum`、`Box`、`Vec`、`Option`、`Result` 等，则 $\mathit{SuppB}(X) = \mathrm{Native}$。

*证明*：由 Axiom SUM1、SUM2。上述类型均为 `std`/`core` 提供；无需 `extern crate`。依 Def 1.1，$\mathit{SuppB}(X) = \mathrm{Native}$。∎

**定理 SUM-T2**：若 $F$ 涉及异步运行时、线程池或通信，则 $\mathit{SuppB}(F) \in \{\mathrm{Native},\, \mathrm{Lib}\}$；`std` 提供 `thread`、`mpsc`，但 `tokio`/`rayon` 为 Lib。

*证明*：由 Def 1.1。异步运行时（Waker、Executor）不由 `std` 提供，需 tokio/async-std；线程与 mpsc 由 `std` 提供；故为 Native 或 Lib。∎

**引理 SUM-L1**：若 $C$ 为 `no_std` crate 且 $\mathit{deps}(C) \subseteq \{\mathrm{core},\, \mathrm{alloc}\}$，则 $\mathit{SuppB}(C) \in \{\mathrm{Native},\, \mathrm{Lib}\}$。

*证明*：`core`、`alloc` 随编译器分发；由 Axiom SUM1。∎

**推论 SUM-C1**：GoF 23 种设计模式中，除需网络/异步/并行的 Observer、分布式扩展外，其余均为 Native。

**引理 SUM-L2（no_std 边界）**：若 $F$ 需 `Vec`、`String`、`Box`，则 $\mathit{SuppB}(F) \in \{\mathrm{Native},\, \mathrm{Lib}\}$；`std` 或 `alloc` 提供。

*证明*：`core` 为 `no_std` 最小子集；`std` 扩展 `alloc`；由 Axiom SUM1。∎

**推论 SUM-C2**：组合模式 $C = M_1 \oplus \cdots \oplus M_n$ 的 $\mathit{SuppB}(C) = \max_i \mathit{SuppB}(M_i)$；取依赖最重者。

---

## 反例：违反支持边界

| 反例 | 后果 | 论证 |
| :--- | :--- | :--- |
| 假设 `std` 提供 tokio 功能 | 编译失败；`tokio` 需 `extern crate` | 由 Axiom SUM2 |
| 在 `no_std` 下使用 `Vec` 无 `alloc` | 编译失败 | 由 Def 1.2、Axiom SUM1 |
| 裸机环境用 `std::fs` | 链接失败；无 syscall 实现 | 由 Def 1.1 |

---

## 定义（非形式化对照）

| 分类 | 定义 |
| :--- | :--- |
| **原生支持** | 语言/标准库直接提供，无需第三方 crate |
| **库支持** | 需第三方 crate（如 tokio、rayon、actix） |
| **需 FFI** | 需通过 `extern` 调用 C/外部库 |

---

## 设计模式 × 支持边界

### 创建型（5）

| 模式 | 支持边界 | 说明 |
| :--- | :--- | :--- |
| Factory Method | 原生支持 | trait + impl |
| Abstract Factory | 原生支持 | 枚举/结构体 |
| Builder | 原生支持 | 方法链 |
| Prototype | 原生支持 | Clone trait |
| Singleton | 原生支持 | OnceLock、LazyLock（std） |

### 结构型（7）

| 模式 | 支持边界 | 说明 |
| :--- | :--- | :--- |
| Adapter | 原生支持 | 结构体包装 |
| Bridge | 原生支持 | trait |
| Composite | 原生支持 | Box、Vec、枚举 |
| Decorator | 原生支持 | 结构体委托 |
| Facade | 原生支持 | 模块系统 |
| Flyweight | 原生支持 | Arc、Rc |
| Proxy | 原生支持 | 委托 |

### 行为型（11）

| 模式 | 支持边界 | 说明 |
| :--- | :--- | :--- |
| Chain of Responsibility | 原生支持 | Option、链表 |
| Command | 原生支持 | Fn、闭包 |
| Interpreter | 原生支持 | match、枚举 |
| Iterator | 原生支持 | Iterator trait |
| Mediator | 原生支持 | 结构体 |
| Memento | 原生支持 | serde、Clone |
| Observer | 原生支持 | mpsc、broadcast（std） |
| State | 原生支持 | 枚举、类型状态 |
| Strategy | 原生支持 | trait |
| Template Method | 原生支持 | trait 默认方法 |
| Visitor | 原生支持 | match、trait |

---

## 执行模型 × 支持边界

| 模型 | 支持边界 | 说明 |
| :--- | :--- | :--- |
| 同步 | 原生支持 | 默认执行模型 |
| 异步 | 库支持 | 需 tokio/async-std 等运行时 |
| 并发 | 原生支持 | std::thread、mpsc、Mutex |
| 并行 | 库支持 | rayon（推荐）；std 提供 thread + join |
| 分布式 | 库支持 | tonic、actix、surge 等 |

---

## 决策树：判定支持边界

```text
实现某模式/功能时，是否需要第三方 crate？
├── 否 → 原生支持（std、core）
└── 是 → 是否涉及 extern/C FFI？
    ├── 否 → 库支持（crates.io）
    └── 是 → 需 FFI（unsafe 封装）
```

---

## 典型 crate 映射

| 支持边界 | 设计模式/执行模型 | 典型 crate |
| :--- | :--- | :--- |
| 原生 | 绝大多数 GoF 23 | std、core |
| 库 | 异步 | tokio、async-std |
| 库 | 并行 | rayon |
| 库 | 分布式 RPC | tonic、surge |
| 库 | ORM/数据访问 | diesel、sqlx |
| FFI | 系统调用、C 库 | libc、windows-sys |

---

## 选型建议

| 需求 | 建议 |
| :--- | :--- |
| 零依赖 | 用原生支持；GoF 23 均可用 std |
| 异步 | 加 tokio/async-std；库支持 |
| 并行 | 加 rayon；库支持 |
| 分布式 | 加 tonic/actix；库支持 |
| FFI | 封装 unsafe；最小化暴露 |

---

## `no_std` 与嵌入式支持

| 环境 | 支持边界 | 说明 |
| :--- | :--- | :--- |
| `std` | 全功能 | 标准库、线程、文件、网络 |
| `core` | `no_std` | 无分配、无 I/O；需 `alloc` 做堆 |
| `alloc` | `no_std` + 分配 | `Vec`、`String`、`Box` |
| 裸机 | `no_std` | 无 libc、自定义 panic/alloc |

**设计模式在 no_std**：Factory、Strategy、Adapter 等多数仅用 `core`；Flyweight 需 `alloc`；Observer 需 channel 或自定义。

---

## Cargo 特性与可选依赖

| 依赖类型 | 说明 |
| :--- | :--- |
| 默认 | 必需功能 |
| 可选 `[features]` | 按需启用，如 `tokio/full` |
| `optional = true` | 可选 crate，配合 feature 启用 |

---

## 版本兼容性

| 策略 | 说明 |
| :--- | :--- |
| 语义化版本 | 主版本变更可能有破坏性 |
| 最小版本 | `cargo update -Z minimal-versions` |
| MSRV | 最低 Rust 版本 |

---

## 场景化决策示例（层次推进）

### 示例 1：是否需要第三方 crate

**场景**：实现 Web API 服务。

**决策**：需异步运行时 → 库支持（tokio）；$\mathit{SuppB} = \mathrm{Lib}$。

```rust
// Cargo.toml: tokio = { version = "1", features = ["full"] }
use tokio::net::TcpListener;
async fn serve() {
    let listener = TcpListener::bind("0.0.0.0:8080").await.unwrap();
    // ...
}
```

### 示例 2：no_std 嵌入式

**场景**：裸机无 libc。

**决策**：仅 `core` + `alloc` → $\mathit{SuppB} \in \{\mathrm{Native},\, \mathrm{Lib}\}$；Factory、Strategy、Adapter 等可用。

### 示例 3：FFI 绑定 C 库

**场景**：调用 OpenSSL。

**决策**：需 `extern crate openssl` 或 `libc` → $\mathit{SuppB} = \mathrm{FFI}$；封装为 Safe trait。

---

## 引用

- [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](../../RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md)
- [DESIGN_PATTERNS_USAGE_GUIDE](../../../DESIGN_PATTERNS_USAGE_GUIDE.md)
