#![forbid(unsafe_code)]
#![allow(unexpected_cfgs)]

//! - 组件（Component）、世界（World）、接口（Interface）
//! - WIT (Wasm Interface Types) 接口定义语言
//! - wit-bindgen 绑定生成
//! - wit-bindgen 绑定Generate
//! - 组件组合与链接
//! - combination and
//! - from WASI Preview 1 to Preview 2 迁移路径
//! - 工具链: wasm-tools, wasmtime, jco

use wasm_bindgen::prelude::*;

// =========================================================================
// 1. ComponentModelOverview — 组件模型核心概念
// =========================================================================

/// # 组件模型概述
/// #
/// 实现了真正的语言无关、类型安全的跨组件互操作。
/// 、type 。
#[derive(Default)]
pub struct ComponentModelOverview;

impl ComponentModelOverview {
    /// 创建新的概述实例
    pub fn new() -> Self {
        Self
    }

    pub fn what_is_component_model() -> &'static str {
        r#"WebAssembly Component Model (WASI Preview 2)

== 核心定位 ==
- WASI Preview 1 (wasm32-wasip1): 模块级系统调用接口
- WASI Preview 2 (wasm32-wasip2): 组件级类型化接口

== 关键差异 ==

| 维度 | Preview 1 | Preview 2 (Component Model) |
|------|-----------|----------------------------|
| 基本单元 | Core Module (.wasm) | Component (.wasm) |
| 接口定义 | 隐式导出/导入表 | 显式 WIT 接口定义 |
| 类型系统 | i32/i64/f32/f64/v128 | + string, list, option, result, record, variant |
| 字符串传递 | i32 指针 + i32 长度 | 原生 string 类型 |
| 错误处理 | 整数返回码 | result<T, E> |
| 组合能力 | 需运行时链接 | 静态组件组合 (wasm-tools compose) |
| 语言互操作 | 需手动 FFI | 通过 wit-bindgen 自动生成绑定 |

== 组件模型的优势 ==
1. 类型安全: 跨组件调用在编译期验证，运行时无类型错配
2. 沙箱细化: 能力基于接口粒度，而非整个模块
3. 可组合性: 组件可像乐高积木一样静态组合
4. 语言无关: WIT 作为通用 IDL，任何语言均可生成绑定
"#
    }

    /// 世界（Worlds）、接口（Interfaces）和组件（Components）
    /// 组件模型的三大核心概念及其关系。
    /// core concept and its 。
    pub fn worlds_interfaces_components() -> &'static str {
        r#"组件模型三大核心概念

== Interface（接口）==
- 命名空间化的函数和类型集合
- 类似编程语言中的 trait / interface
- 示例: wasi:filesystem/types, wasi:sockets/tcp

WIT 示例:
  package example:calculator@0.1.0;

  interface ops {
      record point { x: f64, y: f64 }
      enum op { add, sub, mul, div }
      eval: func(a: f64, b: f64, op: op) -> result<f64, string>;
  }

== World（世界）==
- 一个组件的完整接口集合
- 定义组件导入哪些接口、导出哪些接口
- 相当于组件的"类型签名"

WIT 示例:
  world calculator-world {
      import wasi:cli/stdout@0.2.0;
      export ops;
      export run: func() -> result<(), string>;
  }

== Component（组件）==
- 实现了某个 World 的 WASM 二进制单元
- 包含一个或多个 Core Module
- 通过"适配器"将 Core Module 包装为 Component

关系: World 是蓝图，Interface 是模块，Component 是实例
"#
    }

    /// wit-bindgen 用于从 WIT 文件生成绑定
    /// wit-bindgen from WIT
    /// 转换为各目标语言的类型和桩代码。
    /// conversion as goal type and 。
    pub fn wit_bindgen_usage() -> &'static str {
        r#"wit-bindgen: WIT 到目标语言的绑定生成器

== 支持的语言 ==
- Rust (wit-bindgen-rust)
- C/C++ (wit-bindgen-c)
- JavaScript/TypeScript (via jco)
- Java, Go, Python (社区实现)

== Rust 使用流程 ==

1. 编写 WIT 文件 (wit/calculator.wit):
   package example:calculator@0.1.0;
   world calculator {
       export add: func(a: s32, b: s32) -> s32;
   }

2. 在 Rust 中使用 wit-bindgen 宏:
   wit_bindgen::generate!({
       world: "calculator",
       path: "wit",
   });

   struct Calculator;

   impl Guest for Calculator {
       fn add(a: i32, b: i32) -> i32 {
           a + b
       }
   }

   export!(Calculator);

3. 编译为组件:
   cargo component build --target wasm32-wasip2

== 生成的绑定内容 ==
- WIT 中定义的 record / variant / enum 的 Rust 类型
- Guest trait（需由宿主实现）
- Export 宏（将实现注册为组件导出）
- 自动的 WASM 线性内存与高级类型之间的升降序列化
"#
    }

    /// 组件组合与链接
    /// combination and
    /// 组件模型最强大的特性之一：静态组合多个组件为一个。
    /// feature 's ：combination as 。
    pub fn composition_and_linking() -> &'static str {
        r#"组件组合与链接 (Component Composition)

== 核心思想 ==
将组件 A 的导出接口与组件 B 的导入接口静态链接，
生成一个新的独立组件 C，无需运行时链接器。

== 组合场景 ==

1. 库组件 + 应用组件:
   库组件导出加密接口，应用组件导入加密接口。
   组合后生成一个独立应用组件。

2. 虚拟化/垫片 (Shim):
   为旧版 WASI P1 模块生成 P2 适配层组件，
   将其包装为 P2 组件。

3. 平台抽象:
   应用依赖 wasi:filesystem 接口，
   组合时链接到宿主实现或模拟实现。

== 工具命令 (wasm-tools) ==

# 将两个组件组合
wasm-tools compose component-a.wasm -d component-b.wasm -o combined.wasm

# 验证组合结果
wasm-tools validate combined.wasm --features component-model

== 与动态链接的对比 ==

| 特性 | 组件组合 (静态) | 运行时动态链接 |
|------|----------------|--------------|
| 验证时机 | 构建时 | 运行时 |
| 类型安全 | 完全保证 | 依赖运行时检查 |
| 部署方式 | 单文件 | 多文件 + 注册表 |
| 性能 | 无间接开销 | 有查找开销 |
| 灵活性 | 固定拓扑 | 可动态替换 |
"#
    }
}

// =========================================================================
// 2. WasiPreview2Migration — 迁移指南
// =========================================================================

/// # WASI Preview 1 到 Preview 2 迁移指南
/// # WASI Preview 1 to Preview 2 迁移指南
/// WASI Preview 1 到 Preview 2 迁移指南
/// WASI Preview 1 to Preview 2 迁移指南
#[derive(Default)]
pub struct WasiPreview2Migration;

impl WasiPreview2Migration {
    /// 创建新的迁移指南实例
    pub fn new() -> Self {
        Self
    }

    /// from WASI Preview 1 to Preview 2 迁移路径
    pub fn migration_path() -> &'static str {
        r#"WASI Preview 1 → Preview 2 迁移路径

== 阶段一: 评估与准备 ==
1. 确认当前目标: wasm32-wasip1
2. 梳理应用使用的 WASI 接口:
   - 文件系统访问 (std::fs)
   - 网络 (std::net, wasi::http)
   - 时钟/随机数 (std::time, getrandom)
   - 环境变量/命令行参数
3. 检查依赖 crate 的 wasip2 兼容性

== 阶段二: 工具链升级 ==
1. 安装 wasm32-wasip2 目标:
   rustup target add wasm32-wasip2

2. 安装 cargo-component:
   cargo install cargo-component

3. 初始化组件项目结构:
   cargo component new --reactor my-app
   # 或将现有项目改为组件项目

== 阶段三: 接口迁移 ==
1. 定义 WIT world（明确导入/导出）
2. 将 std::fs 调用迁移到 wasi:filesystem 接口（如果使用低层 API）
3. 对于高层 Rust 代码，标准库通常保持不变
4. 将自定义宿主函数改为 WIT 接口导入

== 阶段四: 构建与验证 ==
1. 生成绑定: cargo component bindings
2. 构建组件: cargo component build --target wasm32-wasip2
3. 转换为组件（如果使用 core wasm 编译）:
   wasm-tools component new app.wasm -o app.component.wasm
4. 验证: wasm-tools validate app.component.wasm

== 阶段五: 运行时迁移 ==
1. wasmtime 运行组件:
   wasmtime run app.component.wasm
2. 更新 CI/CD 构建脚本
3. 更新部署文档
"#
    }

    /// 关键 API 变更（文件系统、套接字、时钟）
    /// key API （file system 、socket 、）
    /// key API 变更（file system、socket、时钟）
    pub fn key_api_changes() -> &'static str {
        r#"WASI P1 → P2 关键 API 变更

== 文件系统 ==

Preview 1 (基于文件描述符):
  fd_open(path_ptr, path_len, oflags, fd_out) -> errno
  fd_read(fd, iovs, iovs_len, nread) -> errno
  fd_write(fd, iovs, iovs_len, nwritten) -> errno

Preview 2 (基于资源句柄 + 路径类型):
  wasi:filesystem/types@0.2.0 接口
  - descriptor.open-at(path-flags, path, open-flags, flags) -> result<descriptor, error-code>
  - descriptor.read(offset, length) -> result<list<u8>, error-code>
  - descriptor.write(buffer, offset) -> result<void, error-code>

关键变化:
- 资源类型化: descriptor 是 handle 类型，非裸整数
- 路径基于目录描述符 + 相对路径（更安全的 capability 模型）
- 错误使用 result<T, error-code>，非整数 errno

== 套接字 ==

Preview 1: 无标准套接字 API（各宿主自行扩展）

Preview 2: wasi:sockets/tcp@0.2.0
  - tcp-socket.bind(network, local-address) -> result<void, error-code>
  - tcp-socket.connect(network, remote-address) -> result<void, error-code>
  - tcp-socket.listen() -> result<void, error-code>
  - tcp-socket.accept() -> result<tuple<tcp-socket, input-stream, output-stream>, error-code>

关键变化:
- 正式标准化的网络接口
- network 资源显式创建和授权
- 流式 IO 使用 input-stream / output-stream 资源

== 时钟 ==

Preview 1:
  clock_time_get(id: clockid, precision: timestamp, time: *timestamp) -> errno

Preview 2: wasi:clocks/wall-clock@0.2.0 + wasi:clocks/monotonic-clock@0.2.0
  - wall-clock.now() -> datetime
  - monotonic-clock.now() -> instant
  - monotonic-clock.resolution() -> duration
  - monotonic-clock.subscribe-instant(when) -> pollable

关键变化:
- 分离挂钟和单调时钟
- 返回结构化类型而非裸整数
- 支持基于 pollable 的异步等待
"#
    }

    /// WIT 接口定义概念
    /// WIT definition concept
    /// WIT 接口definitionconcept
    pub fn wit_interface_definitions() -> &'static str {
        r#"WIT (Wasm Interface Types) 接口定义概念

== WIT 设计哲学 ==
- 语言无关的接口定义语言 (IDL)
- 专注于组件间边界，非组件内部实现
- 显式能力声明：每个导入都是宿主必须提供的能力

== 核心语法元素 ==

1. Package（包）:
   package wasi:http@0.2.0;
   # 命名空间:名称@版本

2. Interface（接口）:
   interface types {
       resource request {
           constructor(method: string, path: string, headers: headers);
           method: func() -> string;
           set-method: func(method: string);
       }
       type headers = list<tuple<string, string>>;
       send: func(req: request) -> result<response, error>;
   }

3. World（世界）:
   world http-proxy {
       import wasi:filesystem/types@0.2.0;
       import wasi:sockets/tcp@0.2.0;
       export wasi:http/incoming-handler@0.2.0;
   }

4. 类型系统:
   - 基础: bool, s8/u8, s16/u16, s32/u32, s64/u64, f32, f64, char, string
   - 复合: list<T>, option<T>, result<T, E>, tuple<T, U>
   - 记录: record point { x: f64, y: f64 }
   - 枚举: enum color { red, green, blue }
   - 变体: variant filter { all, by-name(string), by-id(u64) }
   - 资源: resource file { ... }

== 版本管理 ==
- WIT 包支持语义化版本
- 组件可声明对特定版本接口的依赖
- 运行时通过版本协商确保兼容性
"#
    }
}

// =========================================================================
// 3. WasmComponentTooling — 工具链
// =========================================================================

/// # 组件模型工具链
/// # toolchain
/// # 组件模型toolchain
/// 组件模型工具链
/// toolchain
#[derive(Default)]
pub struct WasmComponentTooling;

impl WasmComponentTooling {
    /// 创建新的工具链指南实例
    /// toolchain
    pub fn new() -> Self {
        Self
    }

    pub fn wasm_tools_usage() -> &'static str {
        r#"wasm-tools: WebAssembly 组件模型工具链

== 安装 ==
cargo install wasm-tools

== 核心子命令 ==

1. component new — 将 Core WASM 模块封装为组件
   wasm-tools component new module.wasm \
       --adapt wasi_snapshot_preview1=reactor.wasm \
       -o component.wasm

   常用适配器:
   - wasi_snapshot_preview1.command.wasm (命令行应用)
   - wasi_snapshot_preview1.reactor.wasm (库/反应器)

2. compose — 静态组合多个组件
   wasm-tools compose app.wasm -d lib.wasm -o combined.wasm
   # 将 app 的导入与 lib 的导出链接

3. validate — 验证 WASM/组件格式
   wasm-tools validate component.wasm --features component-model
   # 检查二进制格式合法性和类型一致性

4. print — 反汇编为 WAT (WebAssembly Text)
   wasm-tools print component.wasm > component.wat

5. metadata show — 查看组件元数据
   wasm-tools metadata show component.wasm
   # 显示组件名、生产者信息、目标特性等

6. component wit — 提取组件的 WIT 接口
   wasm-tools component wit component.wasm
   # 从组件二进制反推其 WIT 定义
"#
    }

    /// wasmtime as组件runtime
    pub fn wasmtime_runtime() -> &'static str {
        r#"wasmtime: 组件模型运行时

== 安装 ==
cargo install wasmtime-cli

== 运行组件 ==

# 直接运行组件（自动检测模块或组件）
wasmtime run app.component.wasm

# 带目录权限运行
wasmtime run --dir=. app.component.wasm

# 带网络权限运行
wasmtime run --tcplisten 127.0.0.1:8080 server.component.wasm

# 运行时性能分析
wasmtime run --profile=guest-profile.json app.component.wasm

== wasmtime 作为库使用 (Rust) ==

use wasmtime::{Engine, Component, Linker, Store};

let engine = Engine::default();
let component = Component::from_file(&engine, "app.component.wasm")?;
let mut linker = Linker::new(&engine);
let mut store = Store::new(&engine, ());

// 链接 WASI 宿主接口
wasmtime_wasi::add_to_linker_sync(&mut linker)?;

// 实例化组件
let instance = linker.instantiate(&mut store, &component)?;

== 关键特性 ==
- 支持 wasip1 和 wasip2 目标
- 组件模型完整实现（参考实现）
- 增量编译与代码缓存
- 运行时性能分析 (guest profiling)
- WASI HTTP 实验性支持
"#
    }

    pub fn jco_javascript_generation() -> &'static str {
        r#"jco: JavaScript 的 Component Model 工具链

== 定位 ==
jco 是 Bytecode Alliance 官方维护的 JavaScript 端组件工具链，
功能与 wasmtime 对应，但专注于 JS/Node.js/Deno/Browser 环境。

== 安装 ==
npm install -g @bytecodealliance/jco

== 核心功能 ==

1. transpile — 将组件转译为 JS + WASM 文件
   jco transpile component.wasm -o pkg/
   # 生成:
   #   pkg/component.js      — JS 绑定和类型
   #   pkg/component.core.wasm — 核心 WASM 模块
   #   pkg/component.d.ts    — TypeScript 类型定义

   生成的 JS 代码可直接在 Node.js 或浏览器中 import。

2. run — 在 Node.js 中运行组件
   jco run component.wasm --args ...

3. serve — 将组件作为 HTTP 服务运行
   jco serve http-handler.component.wasm

4. types — 仅生成 TypeScript 类型
   jco types wit/ -o types/

== 在浏览器中使用转译后的组件 ==

import { Calculator } from "./pkg/component.js";

const calc = new Calculator();
const result = calc.add(2, 3);
console.log(result); // 5

== jco vs wasm-bindgen ==

| 特性 | wasm-bindgen | jco |
|------|--------------|-----|
| 目标格式 | Core Module | Component |
| 接口定义 | Rust 属性宏 | WIT 文件 |
| JS 绑定生成 | 编译期 (proc-macro) | 转译期 (jco transpile) |
| 类型系统 | 手动映射 | WIT 类型自动生成 |
| 多语言消费 | 仅限 Rust 生成的模块 | 任何 WIT 定义的组件 |
| 浏览器支持 | 原生支持 | 需转译步骤 |

== 推荐场景 ==
- 用 Rust 写库组件，通过 jco 给 Node.js/浏览器消费
- 多语言组件生态（Rust 组件被 JS 应用调用）
- 需要 WIT 作为单一事实来源的团队协作
"#
    }
}

// =========================================================================
// 4. 平台特定示例 / 非 WASM 存根
// =========================================================================

/// 检测当前目标是否支持组件模型运行时
/// when before goal runtime
/// 在 wasm32-wasip2 目标下返回 true，其他目标返回 false。
/// in wasm32-wasip2 goal under true，its goal false。
pub fn is_component_model_target() -> bool {
    cfg_select! {
        target_env = "wasip2" => true,
        _ => false,
    }
}

/// 获取当前平台的组件模型支持描述
/// when before platform describe
pub fn component_model_support_description() -> &'static str {
    cfg_select! {
        target_env = "wasip2" => "当前目标 wasm32-wasip2 原生支持组件模型",
        target_arch = "wasm32" => "浏览器 WASM 目标：需通过 wasm-tools + jco 使用组件模型",
        _ => "原生目标：可通过 wasmtime 嵌入组件运行时",
    }
}

/// 模拟组件模型环境下的接口调用
/// environment under
/// 其他目标下返回存根实现。
/// its goal under 。
pub fn simulate_component_call(interface: &str, function: &str) -> String {
    cfg_select! {
        target_env = "wasip2" => {
            format!(
                "[WASI P2] 调用接口 {}::{} — 通过组件模型 handle 资源",
                interface, function
            )
        }
        target_arch = "wasm32" => {
            format!(
                "[Browser WASM] 模拟组件调用 {}::{} — 需 jco 转译",
                interface, function
            )
        }
        _ => {
            format!(
                "[Native Stub] 模拟组件调用 {}::{} — 仅用于 host 编译测试",
                interface, function
            )
        }
    }
}

// =========================================================================
// 5. JS 互操作示例（wasm_bindgen）
// =========================================================================

#[wasm_bindgen]
#[derive(Default)]
pub struct ComponentModelJsBridge;

#[wasm_bindgen]
impl ComponentModelJsBridge {
    /// 创建 JS 桥接实例
    /// JS bridge
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self
    }

    /// 返回当前目标是否支持组件模型
    /// when before goal
    #[wasm_bindgen(js_name = isComponentModelTarget)]
    pub fn is_component_model_target_js() -> bool {
        is_component_model_target()
    }

    /// 返回平台支持描述（供 JS 显示）
    /// platform describe （ JS display ）
    #[wasm_bindgen(js_name = supportDescription)]
    pub fn support_description_js() -> String {
        component_model_support_description().to_string()
    }

    /// 模拟一次组件接口调用并返回结果字符串
    /// and result
    #[wasm_bindgen(js_name = simulateCall)]
    pub fn simulate_call_js(interface: &str, function: &str) -> String {
        simulate_component_call(interface, function)
    }

    /// 返回学习路径（供 JS 前端展示）
    /// learn （ JS frontend ）
    #[wasm_bindgen(js_name = learningPath)]
    pub fn learning_path_js() -> String {
        learning_path().to_string()
    }
}

/// 将 WIT 包名字符串解析为结构化对象。
/// will WIT as structure to 。
#[wasm_bindgen(js_name = parseWitPackageName)]
pub fn parse_wit_package_name_js(name: &str) -> Option<String> {
    parse_wit_package_name(name).map(|(ns, pkg, ver)| {
        format!(
            "{{\"namespace\":\"{}\",\"package\":\"{}\",\"version\":\"{}\"}}",
            ns, pkg, ver
        )
    })
}

// =========================================================================
// 6. 实用函数
// =========================================================================

/// 解析 WIT 风格的包名
/// WIT
/// 输入: "wasi:http@0.2.0"
/// 返回: (命名空间, 包名, 版本)
/// : (space,, this )
/// Return: (命名space, 包名, 版this)
pub fn parse_wit_package_name(name: &str) -> Option<(&str, &str, &str)> {
    let (namespace_rest, version) = name.split_once('@')?;
    let (namespace, package) = namespace_rest.split_once(':')?;
    Some((namespace, package, version))
}

/// 获取推荐的组件模型学习路径
/// learn
pub fn learning_path() -> &'static str {
    r#"WebAssembly Component Model 学习路径

1. 基础概念
   - 理解 Core WASM Module vs Component 的区别
   - 阅读: https://component-model.bytecodealliance.org/

2. 编写第一个 WIT 文件
   - 定义简单的接口和 world
   - 使用 wit-bindgen 生成 Rust 绑定

3. 构建组件
   - cargo component build
   - 或使用 wasm-tools component new

4. 组合组件
   - 编写两个互补的组件（一个导出，一个导入）
   - 使用 wasm-tools compose 链接它们

5. 多语言互操作
   - Rust 组件通过 jco 给 JS 消费
   - 或用 wasmtime 在服务端运行组件

6. 深入 WASI 接口
   - wasi:filesystem, wasi:sockets, wasi:http
   - 理解 capability-based security 在组件模型中的实现
"#
}

// =========================================================================
// 测试
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- ComponentModelOverview 测试 ---

    #[test]
    fn test_component_model_overview_creation() {
        let overview = ComponentModelOverview::new();
        let _ = overview;
    }

    #[test]
    fn test_what_is_component_model() {
        let doc = ComponentModelOverview::what_is_component_model();
        assert!(doc.contains("Component Model"));
        assert!(doc.contains("Preview 1"));
        assert!(doc.contains("Preview 2"));
    }

    #[test]
    fn test_worlds_interfaces_components() {
        let doc = ComponentModelOverview::worlds_interfaces_components();
        assert!(doc.contains("Interface"));
        assert!(doc.contains("World"));
        assert!(doc.contains("Component"));
    }

    #[test]
    fn test_wit_bindgen_usage() {
        let doc = ComponentModelOverview::wit_bindgen_usage();
        assert!(doc.contains("wit-bindgen"));
        assert!(doc.contains("WIT"));
    }

    #[test]
    fn test_composition_and_linking() {
        let doc = ComponentModelOverview::composition_and_linking();
        assert!(doc.contains("compose"));
        assert!(doc.contains("wasm-tools"));
    }

    // --- WasiPreview2Migration 测试 ---

    #[test]
    fn test_migration_creation() {
        let migration = WasiPreview2Migration::new();
        let _ = migration;
    }

    #[test]
    fn test_migration_path() {
        let doc = WasiPreview2Migration::migration_path();
        assert!(doc.contains("阶段一"));
        assert!(doc.contains("wasm32-wasip2"));
    }

    #[test]
    fn test_key_api_changes() {
        let doc = WasiPreview2Migration::key_api_changes();
        assert!(doc.contains("文件系统"));
        assert!(doc.contains("套接字"));
        assert!(doc.contains("时钟"));
    }

    #[test]
    fn test_wit_interface_definitions() {
        let doc = WasiPreview2Migration::wit_interface_definitions();
        assert!(doc.contains("WIT"));
        assert!(doc.contains("package"));
        assert!(doc.contains("world"));
    }

    // --- WasmComponentTooling 测试 ---

    #[test]
    fn test_tooling_creation() {
        let tooling = WasmComponentTooling::new();
        let _ = tooling;
    }

    #[test]
    fn test_wasm_tools_usage() {
        let doc = WasmComponentTooling::wasm_tools_usage();
        assert!(doc.contains("wasm-tools"));
        assert!(doc.contains("component new"));
        assert!(doc.contains("compose"));
        assert!(doc.contains("validate"));
    }

    #[test]
    fn test_wasmtime_runtime() {
        let doc = WasmComponentTooling::wasmtime_runtime();
        assert!(doc.contains("wasmtime"));
        assert!(doc.contains("Component"));
    }

    #[test]
    fn test_jco_javascript_generation() {
        let doc = WasmComponentTooling::jco_javascript_generation();
        assert!(doc.contains("jco"));
        assert!(doc.contains("transpile"));
    }

    // --- 平台与实用函数测试 ---

    #[test]
    fn test_is_component_model_target_native() {
        // 在原生编译目标下应为 false
        assert!(!is_component_model_target());
    }

    #[test]
    fn test_component_model_support_description() {
        let desc = component_model_support_description();
        assert!(!desc.is_empty());
    }

    #[test]
    fn test_simulate_component_call() {
        let result = simulate_component_call("wasi:filesystem/types", "open-at");
        assert!(result.contains("wasi:filesystem/types"));
        assert!(result.contains("open-at"));
    }

    #[test]
    fn test_parse_wit_package_name_valid() {
        assert_eq!(
            parse_wit_package_name("wasi:http@0.2.0"),
            Some(("wasi", "http", "0.2.0"))
        );
        assert_eq!(
            parse_wit_package_name("example:calculator@1.0.0"),
            Some(("example", "calculator", "1.0.0"))
        );
    }

    #[test]
    fn test_parse_wit_package_name_invalid() {
        assert_eq!(parse_wit_package_name("invalid"), None);
        assert_eq!(parse_wit_package_name("no-version"), None);
        assert_eq!(parse_wit_package_name(""), None);
    }

    #[test]
    fn test_learning_path() {
        let path = learning_path();
        assert!(path.contains("Component Model"));
        assert!(path.contains("WIT"));
        assert!(path.contains("cargo component"));
    }

    // --- JS 互操作桥接测试 ---

    #[test]
    fn test_component_model_js_bridge_creation() {
        let bridge = ComponentModelJsBridge::new();
        let _ = bridge;
    }

    #[test]
    fn test_is_component_model_target_js() {
        // 原生目标下应为 false
        assert!(!ComponentModelJsBridge::is_component_model_target_js());
    }

    #[test]
    fn test_support_description_js() {
        let desc = ComponentModelJsBridge::support_description_js();
        assert!(!desc.is_empty());
    }

    #[test]
    fn test_simulate_call_js() {
        let result = ComponentModelJsBridge::simulate_call_js("wasi:http/types", "send");
        assert!(result.contains("wasi:http/types"));
        assert!(result.contains("send"));
    }

    #[test]
    fn test_learning_path_js() {
        let path = ComponentModelJsBridge::learning_path_js();
        assert!(path.contains("Component Model"));
    }

    #[test]
    fn test_parse_wit_package_name_js_valid() {
        let result = parse_wit_package_name_js("wasi:http@0.2.0");
        assert!(result.is_some());
        let json = result.unwrap();
        assert!(json.contains("wasi"));
        assert!(json.contains("http"));
        assert!(json.contains("0.2.0"));
    }

    #[test]
    fn test_parse_wit_package_name_js_invalid() {
        assert_eq!(parse_wit_package_name_js("invalid"), None);
    }
}
