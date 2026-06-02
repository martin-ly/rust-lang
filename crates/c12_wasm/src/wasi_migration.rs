//! WASI 目标迁移指南 —— 从 wasm32-wasi 到 wasm32-wasip1/p2
//! # ⚠️ 重要通知
//! # ⚠️ important notify
//! # ⚠️ important
//! `wasm32-wasi` 目标已于 **Rust 1.84.0（2025年1月）** 从 Rust 中移除。
//! `wasm32-wasi` goal **Rust 1.84.0（20251）** from Rust in 。
//! 本项目已升级至 `wasm32-wasip1`（WASI Preview 1）和 `wasm32-wasip2`（WASI Preview 2）。
//! # WASI 演化时间线
//! # WASI time line
//! # WASI 演化timeline
//! 2019: wasm32-wasi (Preview 0) — 基本系统调用
//! 2023: wasm32-wasip1 (Preview 1) — 稳定版，模块级接口
//! 2023: wasm32-wasip1 (Preview 1) — ，module
//! 2024: wasm32-wasip2 (Preview 2) — 组件模型 (Component Model)
//! 2025+: WASI 0.3 — 原生异步支持 (WASIp3)
//! 2025+: WASI 0.3 — async (WASI p3)
//! # 目标三元组对照
//! # goal to
//! | 旧目标 | 新目标 | 状态 | 说明 |
//! | goal | goal | state | explain |
//! | 旧goal | 新goal | state | explain |
//! | `wasm32-wasi` | ❌ 已移除 | N/A | 2025年1月后不可用 |
//! | `wasm32-wasi` | ❌ | N/A | 20251after |
//! | `wasm32-wasip2` | ⚠️ Tier 3 | 实验性 | 支持组件模型 |
//! | `wasm32-wasip2` | ⚠️ Tier 3 | | |
//! # 参考
//! # reference
//! - [Component Model](https://component-model.bytecodealliance.org/)
//! - [wasmtime WASI 文档](https://docs.wasmtime.dev/stability-wasi-proposal-support.html)

// =========================================================================
// 1. WASI Preview 1 (wasip1) — 当前推荐目标
// =========================================================================

/// # WASI Preview 1 基础
/// - 文件系统操作 (`path_open`, `fd_read`, `fd_write`)
/// - 时钟 (`clock_time_get`)
/// - 随机数 (`random_get`)
/// - 环境变量/命令行参数
/// - environment variable /command parameter
/// ## 编译命令
/// ## command
/// ## 编译command
/// ```text
/// cargo build --target wasm32-wasip1
/// ```
///
/// ## 运行
/// ## Run
/// wasmtime target/wasm32-wasip1/debug/my_app.wasm
/// ```
pub struct Wasip1Basics;

impl Wasip1Basics {
    pub fn file_io_example() -> &'static str {
        r#"
// 编译: cargo build --target wasm32-wasip1
// 运行: wasmtime --dir=. target/wasm32-wasip1/debug/app.wasm

use std::fs;

fn main() {
    // 读取文件（需要 wasmtime --dir=. 授予目录权限）
    let content = fs::read_to_string("input.txt").unwrap();
    println!("内容: {}", content);

    // 写入文件
    fs::write("output.txt", "Hello WASI").unwrap();
}
"#
    }

    /// Capabilities 安全模型
    /// WASI 基于 capability-based security：
    /// - 程序默认**无任何权限**
    /// - program ****
    /// - 必须通过预打开目录（preopened directories）显式授权
    /// - must （preopened directories）
    /// - 文件路径基于目录文件描述符（dirfd + path）
    /// - file descriptor （dirfd + path）
    /// - 文件路径Based on目录file descriptor（dirfd + path）
    pub fn capability_security() -> &'static str {
        r#"
WASI Capability-Based Security:

1. 目录预打开:
   wasmtime --dir=/data::/mnt --dir=. my_app.wasm
   # /data 主机目录映射到 guest 的 /mnt
   # . 当前目录映射到 guest 的 /

2. 程序内访问:
   let file = std::fs::File::open("/mnt/input.txt")?;
   # 只能访问预打开的目录及其子树

3. 无网络访问（默认）:
   # 需要 wasmtime --tcplisten 127.0.0.1:8080 显式授权
"#
    }

    /// 主要变化是目标名称和工具链更新。
    /// main goal and toolchain 。
    pub fn migration_from_old_wasi() -> &'static str {
        r#"
迁移步骤 (wasm32-wasi → wasm32-wasip1):

1. 安装新目标:
   rustup target remove wasm32-wasi  # 已移除，可选
   rustup target add wasm32-wasip1

2. 更新 Cargo 配置:
   # .cargo/config.toml
   [build]
   target = "wasm32-wasip1"

3. 更新构建脚本:
   # 旧
   cargo build --target wasm32-wasi
   # 新
   cargo build --target wasm32-wasip1

4. 更新运行时:
   # 旧
   wasmtime my_app.wasm
   # 新
   wasmtime my_app.wasm  # wasmtime 自动识别
"#
    }
}

// =========================================================================
// 2. WASI Preview 2 (wasip2) — 组件模型
// =========================================================================

/// 并通过 **WIT (Wasm Interface Types)** 定义接口。
/// ## 核心概念
/// ## core concept
/// | 概念 | 说明 |
/// | concept | explain |
/// | **Component** | 高阶 WASM 单元，可导入/导出接口 |
/// | **Component** | high WASM ，/ |
/// | **Component** | WASM ，/ |
/// | **WIT** | 接口定义语言（类似 IDL） |
/// | **WIT** | definition （similar to IDL） |
/// ## 编译命令
/// ## command
/// ## 编译command
/// cargo build --target wasm32-wasip2
/// ```
pub struct Wasip2ComponentModel;

impl Wasip2ComponentModel {
    /// WIT 接口示例
    /// WIT example
    /// WIT 接口Example of
    pub fn wit_example() -> &'static str {
        r#"
// example.wit
package example:calculator@0.1.0;

interface ops {
    add: func(a: s32, b: s32) -> s32;
    sub: func(a: s32, b: s32) -> s32;
}

world calculator-world {
    export ops;
}
"#
    }

    /// 组件组合概念
    /// combination concept
    /// 组件combinationconcept
    pub fn component_composition() -> &'static str {
        r#"
组件组合 (Component Composition):

1. 模块 A 导出接口 I
2. 模块 B 导入接口 I
3. 运行时通过组件链接器（component linker）将 A 和 B 组合

优势:
- 语言无关的接口定义
- 静态链接验证（类型安全）
- 延迟实例化
- 跨组件虚拟调用优化
"#
    }

    pub fn differences_from_wasip1() -> &'static str {
        r#"
wasip1 vs wasip2:

| 特性 | wasip1 | wasip2 |
|------|--------|--------|
| 抽象层级 | 模块 (Module) | 组件 (Component) |
| 接口定义 | 隐式/导出表 | 显式 WIT |
| 类型系统 | Core WASM 类型 | 高级类型（string, list, option, result） |
| 字符串 | i32 指针+长度 | 原生 string 类型 |
| 错误处理 | 整数返回码 | result<T, E> |
| 工具链 | wasmtime 直接运行 | 需要 wit-bindgen + wasm-tools |
"#
    }
}

// =========================================================================
// 3. 工具链与生态
// =========================================================================

/// # WASI 工具链指南
/// # WASI toolchain
/// ## 必需工具
/// ## tool
/// ## 必需tool
/// ## tool
/// - `wasmtime` — WASM/WASI 运行时（推荐）
/// - `wasmtime` — WASM/WASI runtime（推荐）
/// - `wasm-tools` — 组件模型工具链
/// - `wasm-tools` — toolchain
/// - `wasm-tools` — 组件模型toolchain
/// - `wit-bindgen` — WIT 绑定生成器
/// - `wit-bindgen` — WIT 绑定generator
/// - `cargo-component` — 组件模型 Cargo 插件
/// ## 安装
/// ##
/// cargo install wasm-tools
/// cargo install cargo-component
/// ```
pub struct WasiToolchain;

impl WasiToolchain {
    /// wasmtime 常用命令
    /// wasmtime command
    /// wasmtime 常用command
    pub fn wasmtime_commands() -> &'static str {
        r#"
wasmtime 常用命令:

# 运行 wasip1 模块
wasmtime --dir=. my_app.wasm

# 运行 wasip2 组件
wasmtime run --wasm component-model my_component.wasm

# 带网络权限
wasmtime --tcplisten 127.0.0.1:8080 my_server.wasm

# 性能分析
wasmtime run --profile=guest-profile.json my_app.wasm
"#
    }

    /// cargo-component 工作流
    /// cargo-component 工作stream
    pub fn cargo_component_workflow() -> &'static str {
        r#"
cargo-component 工作流:

1. 创建组件项目:
   cargo component new --reactor my-component

2. 定义 WIT 接口:
   # wit/world.wit
   package example:my-component;
   world my-world { ... }

3. 生成绑定:
   cargo component bindings

4. 实现接口:
   #[cargo_component::component]
   impl Guest for Component {
       fn my_function() { ... }
   }

5. 构建组件:
   cargo component build
"#
    }
}

// =========================================================================
// 4. 迁移检查清单
// =========================================================================

/// 逐项确认迁移完成度。
/// complete 。
/// 。
pub struct MigrationChecklist;

impl MigrationChecklist {
    pub fn checklist() -> Vec<(&'static str, bool)> {
        vec![
            ("[ ] 移除 .cargo/config.toml 中的 wasm32-wasi", false),
            (
                "[ ] 添加 wasm32-wasip1 目标: rustup target add wasm32-wasip1",
                false,
            ),
            ("[ ] 更新 CI/CD 构建脚本中的目标名称", false),
            ("[ ] 更新 Dockerfile 中的基础镜像", false),
            ("[ ] 验证 wasmtime 版本 >= 15.0（支持 wasip1）", false),
            ("[ ] 测试文件系统访问（--dir 权限）", false),
            ("[ ] 测试标准库功能（std::fs, std::net 等）", false),
            (
                "[ ] 如需组件模型：安装 cargo-component 和 wasm-tools",
                false,
            ),
            ("[ ] 如需组件模型：定义 WIT 接口并生成绑定", false),
            ("[ ] 更新文档中的目标名称引用", false),
        ]
    }

    /// 兼容性矩阵
    /// matrix
    pub fn compatibility_matrix() -> &'static str {
        r#"
WASI 兼容性矩阵 (截至 2026-05):

运行时        | wasip1 | wasip2 | 组件模型 | 备注
-------------|--------|--------|----------|------
wasmtime     | ✅     | ✅     | ✅       | 参考实现，推荐
wasmer       | ✅     | ⚠️     | ⚠️       | 部分支持
wasm-edge    | ✅     | ⚠️     | ⚠️       | 云原生优化
browser      | ❌     | ❌     | ⚠️       | 需 polyfill
"#
    }
}

// =========================================================================
// 5. 实战示例
// =========================================================================

/// 完整 WASI 应用示例（概念性，需在 wasip1 目标下编译）
/// complete WASI application example （concept ，in wasip1 goal under ）
pub mod examples {
    /// HTTP 客户端（使用 wasi-http 提案）
    /// HTTP （ wasi-http ）
    /// HTTP 客户端（Use wasi-http 提案）
    pub fn wasi_http_client_concept() -> &'static str {
        r#"
// wasi-http 提案允许 WASM 模块发起 HTTP 请求
// 状态：wasmtime 实验性支持

// 未来代码概念:
use wasi::http::outgoing_handler;

fn fetch_url(url: &str) -> Result<Vec<u8>, Error> {
    let req = wasi::http::types::OutgoingRequest::new(...);
    let res = outgoing_handler::handle(req, None)?;
    // ... 读取响应
}
"#
    }

    /// CLI 工具（文件批处理）
    /// CLI tool （）
    /// CLI tool（文件批Handle）
    pub fn cli_batch_processor_concept() -> &'static str {
        r#"
// 编译为 wasip1，通过 wasmtime 运行
// 优势：跨平台（Windows/Linux/macOS 同一二进制）
//       沙箱安全（仅访问授权目录）

use std::fs;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    let pattern = &args[1];
    let input_dir = &args[2];
    let output_dir = &args[3];

    for entry in fs::read_dir(input_dir).unwrap() {
        let path = entry.unwrap().path();
        if path.to_string_lossy().contains(pattern) {
            let content = fs::read_to_string(&path).unwrap();
            let processed = content.to_uppercase();
            let out_path = format!("{}/{}", output_dir, path.file_name().unwrap().to_string_lossy());
            fs::write(out_path, processed).unwrap();
        }
    }
}
"#
    }
}
