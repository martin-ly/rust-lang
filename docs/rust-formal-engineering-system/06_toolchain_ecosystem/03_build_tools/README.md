# 构建工具理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **概念说明**: 构建工具负责将源代码转换为可执行程序，包括编译、链接、打包等步骤。Rust 通过 build.rs 构建脚本支持自定义构建逻辑，用于代码生成、外部库链接和条件编译配置。
> 内容已整合至： [toolchain/](../../../06_toolchain/)

[返回主索引](../../00_master_index.md) | [返回工具链索引](../README.md)

---

## 构建脚本（build.rs）

```rust
// build.rs - 自定义构建脚本
use std::env;
use std::path::Path;

fn main() {
    // 告诉 Cargo 当这些文件变化时重新运行构建
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/some_file.rs");

    // 设置编译时环境变量
    let version = env::var("CARGO_PKG_VERSION").unwrap();
    println!("cargo:rustc-env=MY_APP_VERSION={}", version);

    // 条件编译标志
    let target = env::var("TARGET").unwrap();
    if target.contains("windows") {
        println!("cargo:rustc-cfg=windows");
    }

    // 链接外部库
    println!("cargo:rustc-link-lib=static=mylib");
    println!("cargo:rustc-link-search=native=/usr/local/lib");
}
```

### 平台特定构建

```rust
// build.rs
use std::env;

fn main() {
    let target = env::var("TARGET").unwrap();

    match target.as_str() {
        "x86_64-unknown-linux-gnu" => {
            println!("cargo:rustc-link-lib=dylib=dl");
        }
        "x86_64-pc-windows-msvc" => {
            println!("cargo:rustc-link-lib=user32");
        }
        "x86_64-apple-darwin" => {
            println!("cargo:rustc-link-lib=framework=CoreFoundation");
        }
        _ => {}
    }
}
```

### 代码生成构建脚本

```rust
// build.rs - 代码生成示例
use std::env;
use std::fs;
use std::path::Path;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("generated.rs");

    // 生成代码
    let generated_code = r#"
pub const BUILD_TIMESTAMP: &str = env!("CARGO_PKG_VERSION");
pub const FEATURES: &[&str] = &["std", "alloc"];
"#;

    fs::write(&dest_path, generated_code).unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}

// 在 src/lib.rs 中使用
// include!(concat!(env!("OUT_DIR"), "/generated.rs"));
```

### 常用构建工具

```bash
# cargo-make：任务运行器
cargo install cargo-make
cargo make build
cargo make test

# just：命令运行器
cargo install just
just build
just test

# cross：交叉编译
cargo install cross
cross build --target aarch64-unknown-linux-gnu

# cargo-chef：Docker 构建优化
cargo install cargo-chef
cargo chef prepare
cargo chef cook --release

# wasm-pack：WASM 构建
cargo install wasm-pack
wasm-pack build --target web
```

### Makefile.toml (cargo-make)

```toml
# Makefile.toml
[config]
default_to_workspace = false

[tasks.format]
command = "cargo"
args = ["fmt", "--", "--check"]

[tasks.lint]
command = "cargo"
args = ["clippy", "--", "-D", "warnings"]
dependencies = ["format"]

[tasks.test]
command = "cargo"
args = ["test"]
dependencies = ["lint"]

[tasks.build]
command = "cargo"
args = ["build", "--release"]
dependencies = ["test"]

[tasks.ci-flow]
dependencies = ["format", "lint", "test", "build"]
```

### Justfile 示例

```makefile
# Justfile

# 默认配方
default:
    @just --list

# 格式化代码
fmt:
    cargo fmt

# 运行 linter
lint:
    cargo clippy -- -D warnings

# 运行测试
test:
    cargo test

# 构建发布版本
build:
    cargo build --release

# 运行所有检查
check: fmt lint test

# 清理构建产物
clean:
    cargo clean
    rm -rf target/

# 发布（带确认）
release: check
    @echo "Ready for release!"
```

### 交叉编译配置

```toml
# .cargo/config.toml
[target.aarch64-unknown-linux-gnu]
linker = "aarch64-linux-gnu-gcc"

[target.x86_64-pc-windows-gnu]
linker = "x86_64-w64-mingw32-gcc"

[target.wasm32-unknown-unknown]
runner = "wasm-bindgen-test-runner"

[build]
target = "x86_64-unknown-linux-musl"  # 静态链接
```

### 条件编译完整示例

```rust
// 根据构建配置启用不同代码
#[cfg(debug_assertions)]
fn log_level() -> &'static str {
    "debug"
}

#[cfg(not(debug_assertions))]
fn log_level() -> &'static str {
    "info"
}

// 根据特性启用功能
#[cfg(feature = "async")]
mod async_impl {
    pub async fn fetch() -> String {
        // 异步实现
        "async".to_string()
    }
}

#[cfg(not(feature = "async"))]
mod sync_impl {
    pub fn fetch() -> String {
        // 同步实现
        "sync".to_string()
    }
}
```

---

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../../../../research_notes/formal_methods/README.md](../../../../research_notes/formal_methods/README.md) |
| 类型系统形式化 | 类型理论数学定义 | [../../../../research_notes/formal_methods/type_system_formalization.md](../../../../research_notes/formal_methods/type_system_formalization.md) |
| 借用检查器证明 | 借用检查器形式化 | [../../../../research_notes/formal_methods/borrow_checker_proof.md](../../../../research_notes/formal_methods/borrow_checker_proof.md) |
| 证明索引 | 形式化证明集合 | [../../../../research_notes/PROOF_INDEX.md](../../../../research_notes/PROOF_INDEX.md) |

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 工具链文档 | 完整工具链指南 | [../../../06_toolchain/](../../../06_toolchain/) |
| Cargo 工作空间 | 工作空间配置 | [../../../06_toolchain/02_cargo_workspace_guide.md](../../../06_toolchain/02_cargo_workspace_guide.md) |
| 编译器特性 | 编译器优化指南 | [../../../06_toolchain/01_compiler_features.md](../../../06_toolchain/01_compiler_features.md) |
| 研究方法论 | 研究方法指南 | [../../../../research_notes/research_methodology.md](../../../../research_notes/research_methodology.md) |
| 工具指南 | 验证工具使用 | [../../../../research_notes/TOOLS_GUIDE.md](../../../../research_notes/TOOLS_GUIDE.md) |
| 最佳实践 | 工程最佳实践 | [../../../../research_notes/BEST_PRACTICES.md](../../../../research_notes/BEST_PRACTICES.md) |

---

[返回主索引](../../00_master_index.md) | [返回工具链索引](../README.md) | [编译器理论](../01_compiler/README.md) | [包管理器理论](../02_package_manager/README.md)
