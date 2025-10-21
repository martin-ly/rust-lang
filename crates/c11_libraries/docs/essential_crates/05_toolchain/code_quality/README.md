# 代码质量工具 (Code Quality Tools)

**类别**: 第5层 - 工具链  
**重要程度**: ⭐⭐⭐⭐⭐ (必备)  
**更新日期**: 2025-10-20

---

## 📋 目录

- [代码质量工具 (Code Quality Tools)](#代码质量工具-code-quality-tools)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. Clippy (必备 ⭐⭐⭐⭐⭐)](#1-clippy-必备-)
      - [基础用法](#基础用法)
      - [Clippy 规则级别](#clippy-规则级别)
      - [常见规则分类](#常见规则分类)
      - [clippy.toml 配置](#clippytoml-配置)
    - [2. rustfmt (必备 ⭐⭐⭐⭐⭐)](#2-rustfmt-必备-)
      - [基础用法2](#基础用法2)
      - [rustfmt.toml 配置](#rustfmttoml-配置)
      - [常见格式化示例](#常见格式化示例)
    - [3. rust-analyzer (必备 ⭐⭐⭐⭐⭐)](#3-rust-analyzer-必备-)
      - [核心功能](#核心功能)
      - [VSCode settings.json 配置](#vscode-settingsjson-配置)
    - [4. cargo-dylint (高级 🔧)](#4-cargo-dylint-高级-)
      - [创建自定义 lint](#创建自定义-lint)
  - [💡 最佳实践](#-最佳实践)
    - [1. CI/CD 集成](#1-cicd-集成)
    - [2. Pre-commit Hook](#2-pre-commit-hook)
    - [3. Makefile/justfile](#3-makefilejustfile)
  - [📊 工具对比](#-工具对比)
    - [Linter 对比](#linter-对比)
  - [🎯 实战技巧](#-实战技巧)
    - [渐进式严格化](#渐进式严格化)
    - [常用 Clippy 命令](#常用-clippy-命令)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

代码质量工具帮助开发者编写符合 Rust 最佳实践的代码，自动发现潜在问题，统一代码风格。

---

## 🔧 核心工具

### 1. Clippy (必备 ⭐⭐⭐⭐⭐)

**安装**: `rustup component add clippy`  
**用途**: Rust 官方 linter，提供700+ 代码检查规则

#### 基础用法

```bash
# 基本检查
cargo clippy

# 严格模式（将警告视为错误）
cargo clippy -- -D warnings

# 检查所有 targets
cargo clippy --all-targets

# 应用自动修复建议
cargo clippy --fix
```

#### Clippy 规则级别

```rust
// 允许特定警告
#![allow(clippy::needless_return)]

// 警告
#![warn(clippy::all)]

// 禁止（错误级别）
#![deny(clippy::correctness)]

// 在函数级别
#[allow(clippy::too_many_arguments)]
fn complex_function(a: i32, b: i32, c: i32, d: i32, e: i32, f: i32, g: i32, h: i32) {
    // ...
}
```

#### 常见规则分类

**正确性 (Correctness)** - 可能导致 bug 的代码

```rust
// ❌ 错误：无效的引用
let x = &vec![1, 2, 3][0];

// ✅ 正确
let v = vec![1, 2, 3];
let x = &v[0];

// ❌ 错误：过度借用
fn takes_ref(x: &i32) {}
let x = 5;
takes_ref(&&x);

// ✅ 正确
takes_ref(&x);
```

**性能 (Performance)** - 可优化的代码

```rust
// ❌ 性能问题：不必要的克隆
let s = "hello".to_string();
let len = s.clone().len();

// ✅ 优化
let len = s.len();

// ❌ 性能问题：低效的字符串拼接
let mut s = String::new();
for i in 0..100 {
    s = s + &i.to_string();  // 每次都重新分配
}

// ✅ 优化
let mut s = String::new();
for i in 0..100 {
    s.push_str(&i.to_string());
}
```

**风格 (Style)** - 代码风格建议

```rust
// ❌ 不推荐：冗余的返回
fn add(a: i32, b: i32) -> i32 {
    return a + b;
}

// ✅ 推荐：隐式返回
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// ❌ 不推荐：不必要的 Ok(())
fn process() -> Result<(), Error> {
    // do something
    return Ok(());
}

// ✅ 推荐
fn process() -> Result<(), Error> {
    // do something
    Ok(())
}
```

**复杂度 (Complexity)** - 过于复杂的代码

```rust
// ❌ 复杂：嵌套的 if-let
if let Some(x) = option1 {
    if let Some(y) = option2 {
        do_something(x, y);
    }
}

// ✅ 简化：使用 match 或 let-else
let (Some(x), Some(y)) = (option1, option2) else {
    return;
};
do_something(x, y);
```

#### clippy.toml 配置

```toml
# clippy.toml
# 认知复杂度阈值
cognitive-complexity-threshold = 30

# 类型复杂度阈值
type-complexity-threshold = 500

# 禁止的方法
disallowed-methods = [
    { path = "std::env::set_var", reason = "Not thread-safe" },
    { path = "std::process::exit", reason = "Use Result instead" },
]

# 禁止的类型
disallowed-types = [
    { path = "std::collections::HashMap", reason = "Use ahash::HashMap" },
]

# 函数参数数量限制
too-many-arguments-threshold = 7

# 单个字母变量允许列表
single-char-binding-names-threshold = 4
```

---

### 2. rustfmt (必备 ⭐⭐⭐⭐⭐)

**安装**: `rustup component add rustfmt`  
**用途**: 自动代码格式化工具

#### 基础用法2

```bash
# 格式化所有文件
cargo fmt

# 检查而不修改
cargo fmt -- --check

# 格式化特定文件
rustfmt src/main.rs
```

#### rustfmt.toml 配置

```toml
# rustfmt.toml
# 基础设置
edition = "2021"
max_width = 100
hard_tabs = false
tab_spaces = 4

# 导入设置
imports_granularity = "Crate"  # 合并导入
group_imports = "StdExternalCrate"  # 分组导入

# 格式化设置
newline_style = "Unix"
use_small_heuristics = "Default"
fn_single_line = false
where_single_line = false

# 注释设置
comment_width = 80
wrap_comments = true
normalize_comments = true

# 字符串设置
format_strings = true

# 宏设置
format_macro_matchers = true
format_macro_bodies = true

# 链式调用
chain_width = 60
```

#### 常见格式化示例

**导入排序**:

```rust
// 自动排序和分组
use std::collections::HashMap;
use std::io::{self, Read};

use serde::{Deserialize, Serialize};
use tokio::net::TcpListener;

use crate::config::Config;
use crate::error::Error;
```

**链式调用**:

```rust
// 自动换行
let result = some_iterator
    .filter(|x| x > &0)
    .map(|x| x * 2)
    .collect::<Vec<_>>();

// 保持简短的链式调用在一行
let result = vec![1, 2, 3].iter().sum();
```

---

### 3. rust-analyzer (必备 ⭐⭐⭐⭐⭐)

**安装**: `rustup component add rust-analyzer`  
**用途**: 语言服务器，提供 IDE 功能

#### 核心功能

- ✅ 实时代码分析
- ✅ 智能代码补全
- ✅ 类型提示
- ✅ 跳转到定义
- ✅ 查找引用
- ✅ 代码重构
- ✅ 内联提示
- ✅ 运行测试

#### VSCode settings.json 配置

```json
{
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.checkOnSave.extraArgs": ["--all-targets"],
  "rust-analyzer.cargo.features": "all",
  "rust-analyzer.inlayHints.enable": true,
  "rust-analyzer.inlayHints.chainingHints": true,
  "rust-analyzer.inlayHints.parameterHints": true,
  "rust-analyzer.assist.importGranularity": "crate",
  "rust-analyzer.completion.autoimport.enable": true,
  "editor.formatOnSave": true,
  "[rust]": {
    "editor.defaultFormatter": "rust-lang.rust-analyzer"
  }
}
```

---

### 4. cargo-dylint (高级 🔧)

**安装**: `cargo install cargo-dylint dylint-link`  
**用途**: 自定义 lint 规则

#### 创建自定义 lint

```rust
// my_lint/src/lib.rs
use clippy_utils::diagnostics::span_lint;
use rustc_hir::{Expr, ExprKind};
use rustc_lint::{LateContext, LateLintPass};

dylint_linting::declare_late_lint! {
    pub NO_TODO,
    Warn,
    "use of TODO in production code"
}

impl<'tcx> LateLintPass<'tcx> for NoTodo {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'_>) {
        if let ExprKind::Call(func, _) = expr.kind {
            if let ExprKind::Path(ref qpath) = func.kind {
                if let Some(def_id) = cx.qpath_res(qpath, func.hir_id).opt_def_id() {
                    if cx.tcx.item_name(def_id).as_str() == "todo" {
                        span_lint(
                            cx,
                            NO_TODO,
                            expr.span,
                            "TODO found in production code",
                        );
                    }
                }
            }
        }
    }
}
```

---

## 💡 最佳实践

### 1. CI/CD 集成

```yaml
# .github/workflows/ci.yml
name: Code Quality

on: [push, pull_request]

jobs:
  quality:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy
      
      - name: Check formatting
        run: cargo fmt -- --check
      
      - name: Clippy
        run: cargo clippy --all-targets -- -D warnings
```

### 2. Pre-commit Hook

```bash
#!/bin/sh
# .git/hooks/pre-commit

set -e

echo "Running rustfmt..."
cargo fmt -- --check

echo "Running clippy..."
cargo clippy --all-targets -- -D warnings

echo "Running tests..."
cargo test --quiet

echo "✅ All checks passed!"
```

### 3. Makefile/justfile

```makefile
# Makefile
.PHONY: check fmt clippy test all

check:
 cargo check --all-targets

fmt:
 cargo fmt

clippy:
 cargo clippy --all-targets -- -D warnings

test:
 cargo nextest run

all: fmt clippy test
```

---

## 📊 工具对比

### Linter 对比

| 工具 | 规则数 | 自动修复 | 可扩展 | 推荐度 |
|------|--------|---------|--------|--------|
| **clippy** | 700+ | ✅ | ✅ | ⭐⭐⭐⭐⭐ |
| **rustc lint** | 100+ | ❌ | ❌ | 内置 |
| **dylint** | 自定义 | ✅ | ✅✅ | 高级 |

---

## 🎯 实战技巧

### 渐进式严格化

```rust
// 1. 项目初期：允许所有
#![allow(clippy::all)]

// 2. 逐步启用警告
#![warn(clippy::correctness)]
#![warn(clippy::suspicious)]

// 3. 严格模式
#![deny(clippy::correctness)]
#![warn(clippy::perf)]
#![warn(clippy::style)]

// 4. 极端严格（生产级）
#![forbid(unsafe_code)]
#![deny(clippy::all)]
#![deny(warnings)]
```

### 常用 Clippy 命令

```bash
# 列出所有可用 lint
cargo clippy -- -W help

# 列出特定分类的 lint
cargo clippy -- -W clippy::correctness -W help

# 解释特定 lint
cargo clippy -- -W clippy::explicit_counter_loop -W help

# 仅检查特定 lint
cargo clippy -- -W clippy::explicit_counter_loop

# 性能分析
cargo clippy -- -W clippy::perf --verbose
```

---

## 🔗 相关资源

- [Clippy Lints List](https://rust-lang.github.io/rust-clippy/master/)
- [rustfmt Guide](https://rust-lang.github.io/rustfmt/)
- [rust-analyzer Manual](https://rust-analyzer.github.io/manual.html)

---

**导航**: [返回工具链层](../README.md) | [下一类别：测试工具](../testing/README.md)
