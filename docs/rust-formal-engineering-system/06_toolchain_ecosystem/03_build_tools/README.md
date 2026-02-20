# 构建工具理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [toolchain/](../../../06_toolchain/)

[返回主索引](../../00_master_index.md)

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
```

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../../../../research_notes/formal_methods/README.md](../../../../research_notes/formal_methods/README.md) |
| 借用检查器证明 | 借用检查器形式化 | [../../../../research_notes/formal_methods/borrow_checker_proof.md](../../../../research_notes/formal_methods/borrow_checker_proof.md) |

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 工具链文档 | 完整工具链指南 | [../../../06_toolchain/](../../../06_toolchain/) |
| Cargo 工作空间 | 工作空间配置 | [../../../06_toolchain/02_cargo_workspace_guide.md](../../../06_toolchain/02_cargo_workspace_guide.md) |
| 研究方法论 | 研究方法指南 | [../../../../research_notes/research_methodology.md](../../../../research_notes/research_methodology.md) |
| 工具指南 | 验证工具使用 | [../../../../research_notes/TOOLS_GUIDE.md](../../../../research_notes/TOOLS_GUIDE.md) |
