//! Rust 1.95 特性 —— WASM/WASI 场景
//!
//! # 概述
//!
//! Rust 1.95 带来了 WASM 生态的重要更新：
//! - **WASI Preview 1/2** 目标稳定化 (`wasm32-wasip1`, `wasm32-wasip2`)
//! - **wasm-bindgen 0.2.120** 新特性
//! - **WebAssembly Component Model** 进展
//! - **`wasm32v1-none` 目标** — 纯 WebAssembly，无宿主接口
//!
//! # WASI 目标变更 (1.84.0+)
//!
//! | 旧目标 (已移除) | 新目标 | 说明 |
//! |----------------|--------|------|
//! | `wasm32-wasi` | `wasm32-wasip1` | WASI Preview 1 (legacy) |
//! | — | `wasm32-wasip2` | WASI Preview 2 (组件模型) |
//! | — | `wasm32v1-none` | 纯 WASM，无标准库 |
//!
//! # 参考
//! - [WASI Preview 2](https://github.com/WebAssembly/WASI/tree/main/preview2)
//! - [Component Model](https://component-model.bytecodealliance.org/)
//! - [wasm-bindgen changelog](https://github.com/rustwasm/wasm-bindgen/blob/main/CHANGELOG.md)

// =========================================================================
// 1. WASI Preview 1 → Preview 2 迁移
// =========================================================================

/// # WASI 目标三元组变更
///
// Rust 1.84.0 移除了 `wasm32-wasi` 目标，替换为更精确的变体：
//
// ```sh
// # 旧方式（1.83 及更早）
// rustup target add wasm32-wasi  # ❌ 已移除
// cargo build --target wasm32-wasi
//
// # 新方式（1.84+）
// rustup target add wasm32-wasip1  # ✅ WASI Preview 1
// rustup target add wasm32-wasip2  # ✅ WASI Preview 2
// cargo build --target wasm32-wasip1
// ```
///
/// # 差异对比
///
// | 特性 | wasip1 | wasip2 |
// |------|--------|--------|
// | 接口 | 能力驱动 (capsicum) | 组件模型 (WIT) |
// | 模块化 | 单体 | 可组合组件 |
// | 资源类型 | 文件描述符 | 句柄类型 |
// | 虚拟化 | wasmtime 适配器 | 原生支持 |
// | 生产就绪 | ✅ 成熟 | 🧪 快速迭代中 |
pub struct WasiTargetMigration;

impl WasiTargetMigration {
    /// 展示 Cargo.toml 目标配置更新
    pub fn cargo_config_update() -> &'static str {
        r#"
# .cargo/config.toml — WASI 目标配置更新

[build]
# 旧配置
target = "wasm32-wasi"  # ❌ 已弃用

# 新配置 — WASI Preview 1
target = "wasm32-wasip1"

# 或 Preview 2 (实验性)
# target = "wasm32-wasip2"

[target.wasm32-wasip1]
runner = "wasmtime run --dir ."

[target.wasm32-wasip2]
runner = "wasmtime serve"
"#
    }

    /// 条件编译适配
    pub fn cfg_migration() -> &'static str {
        r#"
// 代码中的条件编译适配

// 旧方式（1.83 及更早）
#[cfg(target_os = "wasi")]
mod wasi_impl {
    // ...
}

// 新方式（1.84+）— 同时兼容新旧
#[cfg(any(
    target_os = "wasi",
    target_env = "wasip1",
    target_env = "wasip2",
))]
mod wasi_impl {
    // 使用 wasi:: 接口
    pub fn read_file(path: &str) -> Vec<u8> {
        std::fs::read(path).unwrap()
    }
}
"#
    }

    /// wasi: Command 和 Reactor 的区别
    pub fn command_vs_reactor() -> &'static str {
        r#"
WASI Preview 2 — Command vs Reactor:

1. Command (命令式):
   - 有 main() 入口
   - 运行一次后退出
   - 类似传统 CLI 程序
   - 默认 cargo build 输出

2. Reactor (反应式):
   - 无 main()，导出函数供宿主调用
   - 长期运行，响应事件
   - 类似库/插件
   - 需要显式配置:
     [package.metadata.component]
     package = "my:component"
     
     [[package.metadata.component.exports]]
     name = "my-interface"

选择建议:
- 可执行程序 → Command
- 库/插件 → Reactor
"#
    }
}

// =========================================================================
// 2. WebAssembly Component Model
// =========================================================================

/// # Component Model (WASI Preview 2 核心)
///
// [WebAssembly Component Model](https://component-model.bytecodealliance.org/)
// 是 WASI Preview 2 的基石，提供了：
// - **接口定义** (WIT — WebAssembly Interface Types)
// - **跨语言组合** — Rust、Python、JS 组件互操作
// - **能力安全** — 显式声明所需的系统能力
///
// # WIT 示例
// ```wit
// package my:calculator;
//
// interface operations {
//     add: func(a: s32, b: s32) -> s32;
//     sub: func(a: s32, b: s32) -> s32;
// }
//
// world calculator {
//     export operations;
// }
// ```
pub struct WasmComponentModel;

impl WasmComponentModel {
    /// Rust 绑定生成
    pub fn rust_bindings_example() -> &'static str {
        r#"
// 由 wit-bindgen 生成的 Rust 绑定

// WIT 接口:
// interface operations {
//     add: func(a: s32, b: s32) -> s32;
// }

// 生成的 Rust trait:
#[allow(dead_code)]
pub trait Operations {
    fn add(a: i32, b: i32) -> i32;
    fn sub(a: i32, b: i32) -> i32;
}

// 实现接口
pub struct Calculator;

impl Operations for Calculator {
    fn add(a: i32, b: i32) -> i32 { a + b }
    fn sub(a: i32, b: i32) -> i32 { a - b }
}

// 导出为 WASM 组件
// wit_bindgen::generate!({
//     path: "../wit/calculator.wit",
//     world: "calculator",
// });
"#
    }

    /// 跨语言调用概念
    pub fn cross_language_concept() -> &'static str {
        r#"
Component Model 跨语言互操作:

1. Rust → Python:
   // Rust 编译为 .wasm 组件
   // Python 使用 wasmtime-py 加载
   
   import wasmtime
   store = wasmtime.Store(engine)
   component = wasmtime.Component.from_file(engine, "calculator.wasm")
   instance = wasmtime.Instance(store, component, [])
   result = instance.exports(store).add(1, 2)

2. Rust → JavaScript (Web):
   // 浏览器原生支持组件模型（Chrome 125+）
   const component = await WebAssembly.Component(
       await fetch('calculator.wasm')
   );
   const { add } = await component.exports;
   console.log(add(1, 2));

3. 组合性:
   // 组件 A 使用组件 B 的接口
   // 无需重新编译，链接时解析
"#
    }
}

// =========================================================================
// 3. wasm32v1-none 目标
// =========================================================================

/// # `wasm32v1-none` — 纯 WebAssembly
///
// 1.95 新增的 `wasm32v1-none` 目标是一个**纯 WebAssembly** 目标：
// - 无标准库（`no_std`）
// - 无 WASI 接口
// - 无宿主函数
// - 完全自包含
///
// # 适用场景
// - 区块链智能合约（需要确定性执行）
// - 自定义宿主环境（游戏引擎、插件系统）
// - 最小化部署体积
///
// ```sh
// rustup target add wasm32v1-none
// cargo build --target wasm32v1-none -Zbuild-std=core,alloc
// ```
pub struct Wasm32v1None;

impl Wasm32v1None {
    pub fn target_description() -> &'static str {
        r#"
wasm32v1-none 目标特性:

- 架构: WebAssembly 1.0 Core Spec
- OS: none
- 环境: none
- std: 不可用 (必须使用 no_std + alloc)
- 浮点: 依赖硬件 (或软件模拟)
- SIMD: 可选 (WebAssembly SIMD 128)

典型配置:

[unstable]
build-std = ["core", "alloc"]

[build]
target = "wasm32v1-none"

rustflags = [
    "-C", "link-arg=--no-entry",
    "-C", "link-arg=--export-dynamic",
]
"#
    }

    /// 自定义宿主接口
    pub fn custom_host_functions() -> &'static str {
        r#"
// wasm32v1-none + 自定义宿主接口
// 主机提供 extern 函数，WASM 模块调用

#[no_mangle]
pub extern "C" fn add(a: i32, b: i32) -> i32 {
    // 调用宿主提供的日志函数
    unsafe { host_log(b"Adding numbers") };
    a + b
}

// 宿主函数声明（由主机实现）
extern "C" {
    fn host_log(msg: *const u8);
    fn host_storage_read(key: *const u8, value: *mut u8, len: usize) -> usize;
}
"#
    }
}

// =========================================================================
// 4. wasm-bindgen 0.2.120 新特性
// =========================================================================

/// # wasm-bindgen 0.2.120 更新
///
// wasm-bindgen 0.2.120（配合 Rust 1.95）的重要改进：
// - **更小的 JS shim** — 减少生成的胶水代码
// - **更好的 TypeScript 类型** — 生成更精确的 .d.ts
// - **WebIDL 更新** — 支持更多浏览器 API
// - **`link_to!` 改进** — 更灵活的模块链接
///
// # 与 Rust 1.95 协同
// - `cfg_select!` 可用于 wasm 条件编译
// - `bool::TryFrom<integer>` 简化 JS 互操作
// - `if let` guards 改进错误处理模式
pub struct WasmBindgen120;

impl WasmBindgen120 {
    /// 改进的 JS 互操作模式
    pub fn improved_js_interop() -> &'static str {
        r#"
// wasm-bindgen 0.2.120 改进的互操作

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct State {
    value: i32,
}

#[wasm_bindgen]
impl State {
    #[wasm_bindgen(constructor)]
    pub fn new(initial: i32) -> Self {
        Self { value: initial }
    }

    // 自动生成 TypeScript: get value(): number
    #[wasm_bindgen(getter)]
    pub fn value(&self) -> i32 {
        self.value
    }

    // 自动生成 TypeScript: increment(amount?: number): void
    // 使用 Option<i32> 生成可选参数
    #[wasm_bindgen]
    pub fn increment(&mut self, amount: Option<i32>) {
        self.value += amount.unwrap_or(1);
    }
}

// 使用 if let guards 处理 JS 返回值
#[wasm_bindgen]
pub fn process_result(result: JsValue) -> Result<String, JsValue> {
    if let Ok(text) = result.dyn_into::<js_sys::JsString>() {
        Ok(text.as_string().unwrap_or_default())
    } else if result.is_null() || result.is_undefined() {
        Err(JsValue::from_str("null or undefined"))
    } else {
        Err(JsValue::from_str("unexpected type"))
    }
}
"#
    }

    /// 使用 cfg_select 进行平台抽象
    pub fn cfg_select_example() -> &'static str {
        r#"
// 使用 Rust 1.95 cfg_select! 进行 WASM 条件编译

use std::cfg_select;

cfg_select! {
    wasm => {
        use wasm_bindgen::prelude::*;
        use web_sys::console;

        pub fn platform_log(msg: &str) {
            console::log_1(&msg.into());
        }
    }
    not_wasm => {
        pub fn platform_log(msg: &str) {
            println!("{}", msg);
        }
    }
}
"#
    }
}

// =========================================================================
// 5. 实践建议
// =========================================================================

/// # WASI/WASM 项目配置建议 (Rust 1.95)
pub struct WasmProjectRecommendations;

impl WasmProjectRecommendations {
    pub fn recommendations() -> Vec<(&'static str, &'static str)> {
        vec![
            (
                "目标选择",
                "新项目使用 wasm32-wasip1；实验性项目尝试 wasm32-wasip2；\
                 区块链/游戏插件使用 wasm32v1-none",
            ),
            (
                "工具链",
                "wasmtime (运行时) + wasm-tools (组件转换) + wit-bindgen (绑定生成)",
            ),
            (
                "调试",
                "wasmtime --wasm-features all --wasi-modules experimental \
                 run module.wasm",
            ),
            (
                "性能",
                "使用 wasm-opt (Binaryen) 优化；LTO = fat；codegen-units = 1",
            ),
            (
                "测试",
                "cargo test --target wasm32-wasip1 + wasmtime 运行；\
                 wasm-bindgen-test 用于浏览器测试",
            ),
            (
                "CI/CD",
                "安装 wasmtime + wasm-tools；构建后验证 WAT 输出",
            ),
        ]
    }

    /// Cargo.toml 完整配置模板
    pub fn cargo_toml_template() -> &'static str {
        r#"
# Cargo.toml — WASM/WASI 项目模板

[package]
name = "my-wasm-app"
version = "0.1.0"
edition = "2024"

[dependencies]
# 浏览器目标
[target.'cfg(target_arch = "wasm32")'.dependencies]
wasm-bindgen = "0.2.120"
js-sys = "0.3.67"
web-sys = { version = "0.3.67", features = ["console"] }

# WASI 目标
[target.'cfg(any(target_env = "wasip1", target_env = "wasip2"))'.dependencies]
# wasi = "0.14" # 需要时显式依赖

[lib]
crate-type = ["cdylib", "rlib"]

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
strip = true
panic = "abort"

[package.metadata.component]
# WASI Preview 2 组件配置
package = "my:app"

[[package.metadata.component.dependencies]]
# 依赖的其他组件
"#
    }
}

// =========================================================================
// 测试
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasi_migration_docs() {
        let docs = WasiTargetMigration::cargo_config_update();
        assert!(docs.contains("wasm32-wasip1"));
        assert!(!docs.contains("wasm32-wasi\"")); // 旧目标不应作为推荐
    }

    #[test]
    fn test_component_model_concept() {
        let concept = WasmComponentModel::rust_bindings_example();
        assert!(concept.contains("trait Operations"));
    }

    #[test]
    fn test_wasm32v1_none() {
        let desc = Wasm32v1None::target_description();
        assert!(desc.contains("no_std"));
    }

    #[test]
    fn test_wasm_bindgen_120() {
        let code = WasmBindgen120::improved_js_interop();
        assert!(code.contains("wasm_bindgen"));
    }

    #[test]
    fn test_recommendations() {
        let recs = WasmProjectRecommendations::recommendations();
        assert_eq!(recs.len(), 6);
        assert_eq!(recs[0].0, "目标选择");
    }
}
