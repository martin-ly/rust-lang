# 插件架构模式（Plugin Architecture）

> **概念族**: 软件设计 / 组合工程 / 插件架构
>
> **内容分级**: [归档级]
>
> **分级**: [B]
>
> **Bloom 层级**: L4-L6 (分析/评价/创造)
>
> **创建日期**: 2026-06-29
>
> **最后更新**: 2026-06-29
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
>
> **状态**: ✅ 已完成
>
> **对齐说明**: 本文档按 [Rust Reference – FFI](https://doc.rust-lang.org/reference/items/external-blocks.html)、[libloading docs](https://docs.rs/libloading/latest/libloading/)、[Cargo Book – crate-type](https://doc.rust-lang.org/cargo/reference/cargo-targets.html#the-crate-type-field)、[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) 与 [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) 组织。
>
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [libloading docs](https://docs.rs/libloading/latest/libloading/) | [Cargo Book](https://doc.rust-lang.org/cargo/reference/) | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | [Rustonomicon](https://doc.rust-lang.org/nomicon/)

---

## 📑 目录

- [插件架构模式（Plugin Architecture）](#插件架构模式plugin-architecture)
  - [📑 目录](#-目录)
  - [一、动机与应用场景](#一动机与应用场景)
  - [二、静态注册 vs 动态加载](#二静态注册-vs-动态加载)
    - [2.1 静态注册表（Static Registry）](#21-静态注册表static-registry)
    - [2.2 动态加载（Dynamic Loading）](#22-动态加载dynamic-loading)
  - [三、Trait + Registry 设计模式](#三trait--registry-设计模式)
  - [四、Rust 实现方案](#四rust-实现方案)
    - [4.1 共享插件接口 crate](#41-共享插件接口-crate)
    - [4.2 静态注册表示例](#42-静态注册表示例)
    - [4.3 动态加载示例](#43-动态加载示例)
  - [五、代码示例](#五代码示例)
    - [示例 1：静态 Trait Registry](#示例-1静态-trait-registry)
    - [示例 2：使用 libloading 的动态插件](#示例-2使用-libloading-的动态插件)
  - [六、反例边界](#六反例边界)
    - [6.1 ABI 不稳定](#61-abi-不稳定)
    - [6.2 生命周期管理](#62-生命周期管理)
    - [6.3 版本兼容性](#63-版本兼容性)
  - [七、验证清单](#七验证清单)
  - [八、权威来源索引](#八权威来源索引)
  - [九、相关概念](#九相关概念)

---

## 一、动机与应用场景

> **来源: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)**

插件架构（Plugin Architecture）通过**运行时或编译期扩展点**，允许核心系统在不修改自身代码的情况下加载、替换或卸载功能模块。

典型动机：

| 动机 | 说明 | Rust 映射 |
| :--- | :--- | :--- |
| 开闭原则 | 核心稳定，扩展可变 | `trait` + `impl` |
| 延迟加载 | 仅在实际需要时加载模块 | `libloading::Library` |
| 独立发布 | 插件与主程序分开发布、独立版本 | Cargo workspace / `crate-type = ["cdylib"]` |
| 多语言协作 | 通过 C ABI 与外部插件互操作 | `extern "C"` + `#[no_mangle]` |

适用场景：编辑器扩展、Web 服务器中间件、游戏模组（mod）、CLI 工具子命令、数据处理流水线等。

---

## 二、静态注册 vs 动态加载

> **来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)**

### 2.1 静态注册表（Static Registry）

所有插件在**编译期**确定，通过 `inventory`、`linkme` 等 crate 或手工注册表收集。

| 维度 | 静态注册 |
| :--- | :--- |
| 加载时机 | 编译期 / 启动期 |
| 类型安全 | 完全由 Rust 类型系统保证 |
| 性能 | 零额外开销（单态化、内联） |
| 部署 | 与主程序一起打包 |
| 代表 crate | `inventory`、`linkme`、`ctor` |

### 2.2 动态加载（Dynamic Loading）

插件编译为动态库（`.so` / `.dll` / `.dylib`），主程序在**运行时**通过 `dlopen`/`dlsym` 加载。

| 维度 | 动态加载 |
| :--- | :--- |
| 加载时机 | 运行时按需加载 |
| 类型安全 | 跨越 FFI 边界后需显式 ABI 契约保证 |
| 性能 | 函数指针间接调用 + 边界检查 |
| 部署 | 插件独立分发 |
| 代表 crate | `libloading` |

---

## 三、Trait + Registry 设计模式

> **来源: [Rust Reference – Traits](https://doc.rust-lang.org/reference/items/traits.html)**

Rust 中最自然的插件抽象是 **trait**：

```rust
pub trait Plugin: Send + Sync {
    fn name(&self) -> &'static str;
    fn execute(&self, input: &str) -> String;
}
```

注册表负责持有 `Box<dyn Plugin>` 并提供查询/调度接口：

```rust
pub struct PluginRegistry {
    plugins: Vec<Box<dyn Plugin>>,
}

impl PluginRegistry {
    pub fn new() -> Self { Self { plugins: Vec::new() } }
    pub fn register(&mut self, plugin: Box<dyn Plugin>) { self.plugins.push(plugin); }
    pub fn run_all(&self, input: &str) -> Vec<String> {
        self.plugins.iter().map(|p| p.execute(input)).collect()
    }
}
```

该模式满足 [04_compositional_engineering README](README.md) 中的 **Def CE-ARCH1**：跨边界时，所有权与 `Send/Sync` 沿 `Box<dyn Plugin>` 传递。

---

## 四、Rust 实现方案

> **来源: [Cargo Book – crate-type](https://doc.rust-lang.org/cargo/reference/cargo-targets.html#the-crate-type-field)**

### 4.1 共享插件接口 crate

为同时服务静态与动态方案，推荐将插件接口提取到独立的 **接口 crate**（interface crate）：

```toml
[package]
name = "plugin_api"
version = "0.1.0"
edition = "2024"
```

```rust
// plugin_api/src/lib.rs
use std::ffi::{c_char, CStr, CString};

pub trait Plugin: Send + Sync {
    fn name(&self) -> &'static str;
    fn execute(&self, input: &str) -> String;
}

/// 用于动态库的 C ABI 入口。
#[repr(C)]
pub struct RawPlugin {
    pub name: extern "C" fn() -> *const c_char,
    pub execute: extern "C" fn(*const c_char) -> *mut c_char,
    pub free_string: extern "C" fn(*mut c_char),
}

pub const PLUGIN_ENTRY_NAME: &[u8] = b"plugin_entry\0";
```

### 4.2 静态注册表示例

```rust
// host/src/main.rs
use plugin_api::{Plugin, PluginRegistry};

struct UpperPlugin;
impl Plugin for UpperPlugin {
    fn name(&self) -> &'static str { "upper" }
    fn execute(&self, input: &str) -> String { input.to_uppercase() }
}

fn main() {
    let mut registry = PluginRegistry::new();
    registry.register(Box::new(UpperPlugin));
    for out in registry.run_all("hello") {
        println!("{}", out);
    }
}
```

### 4.3 动态加载示例

```rust,ignore
// host/src/main.rs
use libloading::{Library, Symbol};
use plugin_api::{RawPlugin, PLUGIN_ENTRY_NAME};
use std::ffi::{CStr, CString};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    unsafe {
        let lib = Library::new("target/debug/libdemo_plugin.so")?;
        let entry: Symbol<extern "C" fn() -> *const RawPlugin> =
            lib.get(PLUGIN_ENTRY_NAME)?;
        let raw = &*entry();

        let name = CStr::from_ptr((raw.name)()).to_str()?.to_string();
        let input = CString::new("hello")?;
        let out_ptr = (raw.execute)(input.as_ptr());
        let out = CStr::from_ptr(out_ptr).to_str()?.to_string();
        (raw.free_string)(out_ptr);

        println!("{} -> {}", name, out);
    }
    Ok(())
}
```

完整可运行版本见 [crates/c09_design_pattern/examples/plugin_static_registry.rs](../../../../crates/c09_design_pattern/examples/plugin_static_registry.rs) 与 [crates/c09_design_pattern/examples/plugin_dynamic_loading.rs](../../../../crates/c09_design_pattern/examples/plugin_dynamic_loading.rs)。

---

## 五、代码示例

> **来源: [libloading docs](https://docs.rs/libloading/latest/libloading/)**

### 示例 1：静态 Trait Registry

```rust
// 文件：crates/c09_design_pattern/examples/plugin_static_registry.rs
pub trait GreetPlugin: Send + Sync {
    fn name(&self) -> &'static str;
    fn greet(&self, name: &str) -> String;
}

pub struct PluginRegistry {
    plugins: Vec<Box<dyn GreetPlugin>>,
}

impl PluginRegistry {
    pub fn new() -> Self { Self { plugins: Vec::new() } }
    pub fn register(&mut self, p: Box<dyn GreetPlugin>) { self.plugins.push(p); }
    pub fn greetings(&self, name: &str) -> Vec<String> {
        self.plugins.iter().map(|p| p.greet(name)).collect()
    }
}

struct English;
impl GreetPlugin for English {
    fn name(&self) -> &'static str { "english" }
    fn greet(&self, name: &str) -> String { format!("Hello, {}!", name) }
}

struct Spanish;
impl GreetPlugin for Spanish {
    fn name(&self) -> &'static str { "spanish" }
    fn greet(&self, name: &str) -> String { format!("¡Hola, {}!", name) }
}

fn main() {
    let mut registry = PluginRegistry::new();
    registry.register(Box::new(English));
    registry.register(Box::new(Spanish));
    for g in registry.greetings("Rust") {
        println!("{}", g);
    }
}
```

### 示例 2：使用 libloading 的动态插件

```rust,ignore
// 文件：crates/c09_design_pattern/examples/plugin_dynamic_loading.rs
use std::ffi::{c_char, CStr, CString};
use libloading::{Library, Symbol};

#[repr(C)]
pub struct RawPlugin {
    pub name: extern "C" fn() -> *const c_char,
    pub execute: extern "C" fn(*const c_char) -> *mut c_char,
    pub free_string: extern "C" fn(*mut c_char),
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    unsafe {
        let lib = Library::new("target/debug/libdemo_plugin.so")?;
        let entry: Symbol<extern "C" fn() -> *const RawPlugin> =
            lib.get(b"plugin_entry\0")?;
        let raw = &*entry();

        let name = CStr::from_ptr((raw.name)()).to_str()?.to_string();
        let input = CString::new("world")?;
        let out_ptr = (raw.execute)(input.as_ptr());
        let out = CStr::from_ptr(out_ptr).to_str()?.to_string();
        (raw.free_string)(out_ptr);

        println!("plugin {}: {}", name, out);
    }
    Ok(())
}
```

> **注意**：动态示例依赖外部 `.so` 文件，默认以 `ignore` 标注；实际运行时需先构建动态库插件。

---

## 六、反例边界

> **来源: [Rustonomicon – FFI](https://doc.rust-lang.org/nomicon/ffi.html)**

### 6.1 ABI 不稳定

Rust 没有稳定的**类型布局 ABI**（struct 字段顺序、`dyn Trait` vtable 布局等）。跨动态库传递 `Box<dyn Trait>` 或自定义 `struct` 指针而不加 `#[repr(C)]` 会导致未定义行为。

| 错误做法 | 正确做法 |
| :--- | :--- |
| `pub struct Point { x: f64, y: f64 }` 跨动态库传递 | `#[repr(C)] pub struct Point { x: f64, y: f64 }` |
| 直接传递 `Box<dyn Plugin>` | 仅传递 `extern "C"` 函数指针与原始指针 |

### 6.2 生命周期管理

动态库卸载后，若主程序仍持有库分配的指针，将形成悬垂指针。

```rust,ignore
// 反例：库已 drop，但 ptr 仍被使用
let ptr: *const c_char;
{
    let lib = Library::new("libplugin.so")?;
    let sym: Symbol<fn() -> *const c_char> = lib.get(b"get_name\0")?;
    ptr = sym();
} // lib 在此 drop，ptr 悬垂
println!("{}", CStr::from_ptr(ptr).to_str()?); // UB
```

正确做法：确保 `Library` 句柄的生命周期覆盖所有从库中获取的指针，或使用拷贝后的值。

### 6.3 版本兼容性

插件与主程序分别编译时，若插件接口 crate 的语义版本不兼容，可能出现链接或运行时错误。

| 风险 | 缓解 |
| :--- | :--- |
| trait 新增方法 | 接口 crate 遵循 SemVer；主版本号升级 |
| `RawPlugin` 字段变更 | 使用版本号字段 + 向后兼容的 vtable |
| Rust 编译器版本差异 | 统一 `rustc` 版本；避免跨版本动态库 |

---

## 七、验证清单

> **来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)**

- [ ] 静态注册：`cargo check -p c09_design_pattern --examples` 通过。
- [ ] 动态加载：插件 crate 设置 `crate-type = ["cdylib"]`。
- [ ] 跨动态库结构体使用 `#[repr(C)]`。
- [ ] 动态入口函数使用 `extern "C"` 与 `#[no_mangle]`。
- [ ] 接口 crate 遵循 SemVer。
- [ ] `Library` 句柄生命周期覆盖所有从库中借用的资源。

---

## 八、权威来源索引

> **来源优先级说明**：
>
> - **P0**：官方规范与核心库文档，必须对齐。
> - **P1**：社区权威指南与成熟 crate 文档，强烈建议对齐。
> - **P2**：深入原理与工程实践参考，用于边界与反例分析。

| 优先级 | 来源 | 链接 | 对应章节 |
| :--- | :--- | :--- | :--- |
| P0 | Rust Reference – External Blocks | <https://doc.rust-lang.org/reference/items/external-blocks.html> | FFI 函数声明 |
| P0 | Cargo Book – crate-type | <https://doc.rust-lang.org/cargo/reference/cargo-targets.html#the-crate-type-field> | 动态库目标 |
| P0 | libloading docs | <https://docs.rs/libloading/latest/libloading/> | 动态加载 API |
| P1 | Rust API Guidelines | <https://rust-lang.github.io/api-guidelines/> | 接口设计、SemVer |
| P1 | Rust Design Patterns | <https://rust-unofficial.github.io/patterns/> | 插件与策略模式 |
| P2 | Rustonomicon – FFI | <https://doc.rust-lang.org/nomicon/ffi.html> | ABI、生命周期、UB |
| P2 | Cargo Book – SemVer | <https://doc.rust-lang.org/cargo/reference/semver.html> | 版本兼容性 |

---

## 九、相关概念

| 概念 | 关系 | 文档 |
| :--- | :--- | :--- |
| Trait 对象 | 静态注册的核心多态机制 | [type_theory/10_trait_system_formalization.md](../../type_theory/10_trait_system_formalization.md) |
| Strategy 模式 | 插件是策略模式的运行时/编译期扩展 | [software_design_theory/01_design_patterns_formal/03_behavioral/10_strategy.md](../01_design_patterns_formal/03_behavioral/10_strategy.md) |
| 组合有效性 CE-T1–T3 | 插件系统仍需满足所有权、Send/Sync、类型安全 | [02_effectiveness_proofs.md](02_effectiveness_proofs.md) |
| FFI / unsafe | 动态加载跨越 FFI 边界，需 unsafe | [formal_methods/10_safe_unsafe_comprehensive_analysis.md](../../10_safe_unsafe_comprehensive_analysis.md) |
| SemVer / API 稳定性 | 插件接口 crate 的版本管理 | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](../07_crate_architectures/00_crate_architecture_master_index.md) |

---

> **创建日期**: 2026-06-29
>
> **最后更新**: 2026-06-29
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
>
> **状态**: ✅ 已完成
