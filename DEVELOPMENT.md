# 开发环境设置

> **最后更新**: 2026-04-10

---

## 系统要求

### 必需工具

| 工具 | 版本 | 用途 |
|------|------|------|
| Rust | 1.96.0+ | 编译器 |
| Cargo | 1.96.0+ | 构建工具 |
| Git | 2.30+ | 版本控制 |

### 可选工具

| 工具 | 用途 | 安装命令 |
|------|------|----------|
| rustfmt | 代码格式化 | rustup component add rustfmt |
| clippy | 代码检查 | rustup component add clippy |
| miri | 内存检测 | rustup component add miri |
| cargo-audit | 安全审计 | cargo install cargo-audit |
| cargo-tarpaulin | 覆盖率 | cargo install cargo-tarpaulin |

---

## 快速开始

### 1. 克隆项目

```bash
git clone <repository-url>
cd rust-lang
```

### 2. 安装工具链

```bash
rustup show
```

### 3. 验证安装

```bash
rustc --version
cargo --version
cargo build --workspace
```

---

## 开发工作流

### 日常开发

```bash
# 拉取最新代码
git pull origin main

# 创建功能分支
git checkout -b feature/my-feature

# 修改代码...

# 运行测试
cargo test --workspace

# 代码格式化
cargo fmt

# 运行检查
cargo clippy --workspace --all-targets

# 提交更改
git add .
git commit -m "添加新功能"
```

### 构建命令

```bash
# 调试构建
cargo build

# 发布构建
cargo build --release

# 构建特定 crate
cargo build -p c01_ownership_borrow_scope

# 清理构建产物
cargo clean
```

---

## IDE 配置

### VS Code

推荐扩展:

- rust-analyzer
- CodeLLDB
- crates
- Better TOML

配置 settings.json:

```json
{
    "rust-analyzer.checkOnSave.command": "clippy",
    "rust-analyzer.cargo.features": "all"
}
```

### RustRover

- 安装 Rust 插件
- 导入项目时选择 Cargo.toml
- 启用自动导入

---

## 调试配置

### 使用 VS Code

创建 .vscode/launch.json:

```json
{
    "version": "0.2.0",
    "configurations": [
        {
            "type": "lldb",
            "request": "launch",
            "name": "Debug",
            "cargo": {
                "args": ["build"]
            }
        }
    ]
}
```

---

## 性能分析

### 基准测试

```bash
# 运行所有基准测试
cargo bench --workspace

# 运行特定 crate 的基准测试
cargo bench -p c08_algorithms
```

### 性能分析工具

```bash
# 使用 flamegraph
cargo install flamegraph
cargo flamegraph
```

---

## 内存安全检测

### Miri

```bash
# 安装 miri
rustup component add miri

# 运行 miri 检查
cargo miri test
```

---

## 常见问题

### 编译错误

清理并重建:

```bash
cargo clean
cargo build
```

### 依赖问题

更新依赖:

```bash
cargo update
```

---

## 参考文档

- Rust Book
- Cargo 文档
- rust-analyzer 手册
