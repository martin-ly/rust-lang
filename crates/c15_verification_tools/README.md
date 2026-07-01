# 验证工具实战示例

> 本 crate 提供 [Kani](https://github.com/model-checking/kani)、[Aeneas](https://github.com/AeneasVerif/aeneas)、[Prusti](https://github.com/viperproject/prusti-dev) 的入门示例与反例边界。
>
> - **Rust 版本**: 1.96.0+
> - **Edition**: 2024
> - **状态**: 普通 `cargo check` 可通过；验证需单独安装对应工具。

---

## 目录

- [验证工具实战示例](#验证工具实战示例)
  - [目录](#目录)
  - [Kani](#kani)
    - [示例覆盖点](#示例覆盖点)
  - [Aeneas](#aeneas)
    - [示例覆盖点](#示例覆盖点-1)
    - [当前限制（注释说明）](#当前限制注释说明)
  - [Prusti](#prusti)
    - [示例覆盖点](#示例覆盖点-2)
  - [文件结构](#文件结构)
  - [普通编译检查](#普通编译检查)

---

## Kani

Kani 是基于 [CBMC](https://github.com/diffblue/cbmc) 的 Rust 模型检查器，适合发现溢出、越界、panic 等边界反例。

- **官方文档**: <https://model-checking.github.io/kani/>
- **仓库**: <https://github.com/model-checking/kani>
- **安装**: `cargo install kani-verifier && cargo kani setup`
- **运行示例**: `cargo kani --example kani_example`
- **示例文件**: [examples/kani_example.rs](examples/kani_example.rs)

### 示例覆盖点

- `safe_add` 溢出检查（有界输入下无溢出、越界输入下 `checked_add` 返回 `None`）。
- `index_bounds` 数组越界检查（合法下标可访问、越界下标触发 panic）。

---

## Aeneas

Aeneas 将安全的 Rust 子集翻译为纯函数式语言，用于在 Lean/Coq 中证明正确性。

- **官方文档**: <https://aeneas-verification.github.io/>
- **仓库**: <https://github.com/AeneasVerif/aeneas>
- **运行示例**: `aeneas -backend lean crates/c15_verification_tools/examples/aeneas_example.rs`（具体命令随版本变化）
- **示例文件**: [examples/aeneas_example.rs](examples/aeneas_example.rs)

### 示例覆盖点

- 递归函数 `sum`：对不可变借用链表求和。
- 纯函数 `insert`：在有序链表中插入元素并返回新链表。

### 当前限制（注释说明）

- Aeneas 对 `trait`、泛型、循环的支持仍在演进，示例使用简单递归。
- `unsafe`、裸指针、多线程通常不在 Aeneas 的验证范围内。

---

## Prusti

Prusti 是基于 [Viper](https://www.pm.inf.ethz.ch/research/viper.html) 的 Rust 合约验证工具，通过前置/后置条件验证函数正确性。

- **官方文档**: <https://www.pm.inf.ethz.ch/research/prusti.html>
- **仓库**: <https://github.com/viperproject/prusti-dev>
- **运行示例**: `prusti-rustc crates/c15_verification_tools/examples/prusti_example.rs`（或通过 VS Code 插件）
- **示例文件**: [examples/prusti_example.rs](examples/prusti_example.rs)

### 示例覆盖点

- `abs`：前置条件排除 `i32::MIN` 溢出，后置条件保证结果非负。
- `max`：后置条件保证结果等于其中一个输入且不小于任一输入。
- `sum`：后置条件保证结果等于输入之和。

---

## 文件结构

```text
crates/c15_verification_tools/
├── Cargo.toml
├── README.md
├── src/lib.rs
└── examples/
    ├── kani_example.rs
    ├── aeneas_example.rs
    └── prusti_example.rs
```
---

## 普通编译检查

不安装任何验证工具时，crate 仍可正常编译：

```bash
cargo check -p c15_verification_tools
```
