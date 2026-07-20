# 🦀 Rust开发环境配置指南

**创建时间**: 2025年9月25日
**版本**: 1.0.0
**适用对象**: 所有Rust开发者

---

## 📋 目录

- [🦀 Rust开发环境配置指南](#-rust开发环境配置指南)
  - [📋 目录](#-目录)
  - [🚀 快速开始](#-快速开始)
  - [🔧 核心工具安装](#-核心工具安装)
  - [💻 IDE配置](#-ide配置)
  - [🛠️ 开发工具](#️-开发工具)
  - [📦 项目管理](#-项目管理)
  - [🧪 测试环境](#-测试环境)
  - [📊 性能分析](#-性能分析)
  - [🚀 部署配置](#-部署配置)
  - [🔒 安全配置](#-安全配置)
  - [📝 最佳实践](#-最佳实践)
  - [❓ 常见问题](#-常见问题)

---

## 🚀 快速开始

### 一键安装脚本

```bash
# Linux/macOS
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Windows
# 下载并运行 rustup-init.exe
```

### 验证安装

```bash
# 检查Rust版本
rustc --version

# 检查Cargo版本
cargo --version

# 检查rustup版本
rustup --version
```

---

## 🔧 核心工具安装

### Rust工具链

```bash
# 安装稳定版
rustup install stable

# 设置默认版本
rustup default stable

# 安装夜间版（用于实验性功能）
rustup install nightly

# 安装特定版本
rustup install 1.70.0
```

### 必要组件

```bash
# 安装格式化工具
rustup component add rustfmt

# 安装代码质量检查工具
rustup component add clippy

# 安装源码（用于IDE支持）
rustup component add rust-src

# 安装标准库文档
rustup component add rust-docs

# 安装分析工具
rustup component add rustc-dev
```

### 目标平台

```bash
# 安装WebAssembly目标
rustup target add wasm32-unknown-unknown

# 安装交叉编译目标
rustup target add x86_64-pc-windows-gnu  # Windows
rustup target add x86_64-unknown-linux-gnu  # Linux
rustup target add x86_64-apple-darwin  # macOS

# 安装移动平台目标
rustup target add aarch64-linux-android  # Android
rustup target add x86_64-apple-ios  # iOS
```

---

## 💻 IDE配置

### VS Code配置

#### 安装扩展

```bash
# 推荐扩展
code --install-extension rust-lang.rust-analyzer
code --install-extension vadimcn.vscode-lldb
code --install-extension tamasfe.even-better-toml
code --install-extension serayuzgur.crates
code --install-extension bungcip.better-toml
code --install-extension ms-vscode.vscode-json
```

#### 配置文件

```json
// .vscode/settings.json
{
    "rust-analyzer.server.path": "rust-analyzer",
    "rust-analyzer.checkOnSave.command": "clippy",
    "rust-analyzer.checkOnSave.extraArgs": ["--", "-D", "warnings"],
    "rust-analyzer.cargo.features": "all",
    "rust-analyzer.procMacro.enable": true,
    "rust-analyzer.completion.autoimport.enable": true,
    "rust-analyzer.lens.enable": true,
    "rust-analyzer.hover.actions.enable": true,
    "editor.formatOnSave": true,
    "editor.formatOnPaste": true,
    "editor.formatOnType": true,
    "[rust]": {
        "editor.defaultFormatter": "rust-lang.rust-analyzer",
        "editor.tabSize": 4,
        "editor.insertSpaces": true
    },
    "files.associations": {
        "*.toml": "toml",
        "Cargo.toml": "toml",
        "Cargo.lock": "toml"
    }
}
```

#### 任务配置

```json
// .vscode/tasks.json
{
    "version": "2.0.0",
    "tasks": [
        {
            "label": "cargo: build",
            "type": "cargo",
            "command": "build",
            "problemMatcher": ["$rustc"],
            "group": "build"
        },
        {
            "label": "cargo: test",
            "type": "cargo",
            "command": "test",
            "problemMatcher": ["$rustc"],
            "group": "test"
        },
        {
            "label": "cargo: clippy",
            "type": "cargo",
            "command": "clippy",
            "args": ["--", "-D", "warnings"],
            "problemMatcher": ["$rustc"]
        },
        {
            "label": "cargo: fmt",
            "type": "cargo",
            "command": "fmt",
            "problemMatcher": ["$rustc"]
        }
    ]
}
```

#### 调试配置

```json
// .vscode/launch.json
{
    "version": "0.2.0",
    "configurations": [
        {
            "type": "lldb",
            "request": "launch",
            "name": "Debug executable",
            "cargo": {
                "args": ["build", "--bin=${workspaceFolderBasename}", "--package=${workspaceFolderBasename}"],
                "filter": {
                    "name": "${workspaceFolderBasename}",
                    "kind": "bin"
                }
            },
            "args": [],
            "cwd": "${workspaceFolder}"
        },
        {
            "type": "lldb",
            "request": "launch",
            "name": "Debug unit tests in executable",
            "cargo": {
                "args": ["test", "--no-run", "--bin=${workspaceFolderBasename}", "--package=${workspaceFolderBasename}"],
                "filter": {
                    "name": "${workspaceFolderBasename}",
                    "kind": "bin"
                }
            },
            "args": [],
            "cwd": "${workspaceFolder}"
        }
    ]
}
```

### IntelliJ IDEA配置

#### 安装插件

1. 打开 **File** → **Settings** → **Plugins**
2. 搜索并安装以下插件：
   - **Rust**
   - **Toml**
   - **Cargo**

#### 配置Rust工具链

1. 打开 **File** → **Settings** → **Languages & Frameworks** → **Rust**
2. 设置Rust工具链路径
3. 配置Cargo路径
4. 启用实验性功能

#### 代码样式配置

1. 打开 **File** → **Settings** → **Editor** → **Code Style** → **Rust**
2. 配置代码格式化选项
3. 设置导入排序规则
4. 配置命名约定

### Vim/Neovim配置

#### 安装插件管理器

```bash
# 安装vim-plug
curl -fLo ~/.vim/autoload/plug.vim --create-dirs \
    https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim

# 安装packer.nvim (Neovim)
git clone --depth 1 https://github.com/wbthomason/packer.nvim \
    ~/.local/share/nvim/site/pack/packer/start/packer.nvim
```

#### 配置文件1

```vim
" ~/.vimrc 或 ~/.config/nvim/init.vim
" 基本设置
set nocompatible
set number
set relativenumber
set cursorline
set showcmd
set wildmenu
set redrawdelay=1
set showmatch
set incsearch
set hlsearch
set ignorecase
set smartcase
set autoindent
set smartindent
set expandtab
set tabstop=4
set shiftwidth=4
set softtabstop=4
set wrap
set wrap textwidth=100
set colorcolumn=100

" Rust特定设置
autocmd FileType rust setlocal expandtab tabstop=4 shiftwidth=4 softtabstop=4 textwidth=100 colorcolumn=100 formatoptions-=t

" 插件管理
call plug#begin('~/.vim/plugged')

" Rust开发插件
Plug 'rust-lang/rust.vim'
Plug 'racer-rust/vim-racer'
Plug 'rust-lang/rust.vim'
Plug 'vim-cargo/vim-cargo'
Plug 'cespare/vim-toml'

" 通用开发插件
Plug 'vim-airline/vim-airline'
Plug 'scrooloose/nerdtree'
Plug 'kien/ctrlp.vim'
Plug 'tpope/vim-fugitive'
Plug 'airblade/vim-gitgutter'
Plug 'majutsushi/tagbar'
Plug 'scrooloose/nerdcommenter'
Plug 'tpope/vim-surround'
Plug 'tpope/vim-repeat'
Plug 'junegunn/fzf'
Plug 'neoclide/coc.nvim', {'branch': 'release'}

call plug#end()

" 快捷键映射
let mapleader = " "

" Rust特定快捷键
nnoremap <leader>c :Cargo<space>
nnoremap <leader>cb :Cargo build<cr>
nnoremap <leader>ct :Cargo test<cr>
nnoremap <leader>cr :Cargo run<cr>
nnoremap <leader>cc :Cargo check<cr>
nnoremap <leader>cf :Cargo fmt<cr>
nnoremap <leader>cl :Cargo clippy<cr>

" 通用快捷键
nnoremap <leader>n :NERDTreeToggle<cr>
nnoremap <leader>f :CtrlP<cr>
nnoremap <leader>b :TagbarToggle<cr>
nnoremap <leader>g :Git<cr>

" 颜色方案
colorscheme desert

" 状态栏
set laststatus=2
let g:airline_powerline_fonts = 1

" NERDTree配置
let g:NERDTreeWinSize = 30

" CtrlP配置
let g:ctrlp_working_path_mode = 'ra'

" Git Gutter配置
let g:gitgutter_enabled = 1

" Tagbar配置
let g:tagbar_type_rust = {
    \ 'ctagstype' : 'rust',
    \ 'kinds' : [
        \ 'n:modules',
        \ 's:structs',
        \ 'i:interfaces',
        \ 'c:implementations',
        \ 'f:functions',
        \ 'g:enumerations',
        \ 't:type aliases',
        \ 'v:constants',
        \ 'M:macros',
        \ 'T:traits',
        \ 'C:classes',
    \ ]
\ }

" CoC配置
let g:coc_global_extensions = ['coc-rust-analyzer']
```

### Emacs配置

#### 安装包管理器

```elisp
;; 安装use-package
(require 'package)
(add-to-list 'package-archives
             '("melpa" . "https://melpa.org/packages/"))
(package-initialize)

;; 安装use-package
(unless (package-installed-p 'use-package)
  (package-refresh-contents)
  (package-install 'use-package))
```

#### 配置文件2

```elisp
;; ~/.emacs.d/init.el
(require 'use-package)

;; 基本设置
(setq-default indent-tabs-mode nil)
(setq-default tab-width 4)
(setq-default c-basic-offset 4)
(setq-default c-default-style "linux")

;; Rust配置
(use-package rust-mode
  :ensure t
  :config
  (setq rust-format-on-save t)
  (setq rust-rustfmt-bin "rustfmt")
  (setq rust-format-goto-problem t)
  (setq rust-format-show-buffer t)
  (setq rust-format-show-progress t))

(use-package cargo
  :ensure t
  :hook (rust-mode . cargo-minor-mode)
  :config
  (setq cargo-process--command-test "test")
  (setq cargo-process--command-run "run")
  (setq cargo-process--command-build "build")
  (setq cargo-process--command-clean "clean")
  (setq cargo-process--command-check "check")
  (setq cargo-process--command-clippy "clippy")
  (setq cargo-process--command-fmt "fmt"))

(use-package racer
  :ensure t
  :hook (rust-mode . racer-mode)
  :config
  (setq racer-cmd "racer")
  (setq racer-rust-src-path (concat (getenv "HOME") "/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/src"))
  (setq racer-eldoc-hook t))

(use-package company
  :ensure t
  :config
  (add-hook 'after-init-hook 'global-company-mode)
  (setq company-idle-delay 0.1)
  (setq company-minimum-prefix-length 1))

(use-package flycheck
  :ensure t
  :config
  (add-hook 'after-init-hook 'global-flycheck-mode)
  (setq flycheck-rust-cargo-executable "cargo")
  (setq flycheck-rust-clippy-executable "clippy-driver"))

(use-package toml-mode
  :ensure t
  :mode ("\\.toml\\'" . toml-mode))

;; 快捷键
(define-key rust-mode-map (kbd "C-c C-c") 'cargo-process-build)
(define-key rust-mode-map (kbd "C-c C-r") 'cargo-process-run)
(define-key rust-mode-map (kbd "C-c C-t") 'cargo-process-test)
(define-key rust-mode-map (kbd "C-c C-k") 'cargo-process-clean)
(define-key rust-mode-map (kbd "C-c C-c") 'cargo-process-check)
(define-key rust-mode-map (kbd "C-c C-l") 'cargo-process-clippy)
(define-key rust-mode-map (kbd "C-c C-f") 'cargo-process-fmt)
```

---

## 🛠️ 开发工具

### 代码质量工具

```bash
# 安装cargo-tarpaulin (代码覆盖率)
cargo install cargo-tarpaulin

# 安装cargo-audit (安全审计)
cargo install cargo-audit

# 安装cargo-outdated (依赖更新检查)
cargo install cargo-outdated

# 安装cargo-edit (依赖管理)
cargo install cargo-edit

# 安装cargo-expand (宏展开)
cargo install cargo-expand

# 安装cargo-tree (依赖树)
cargo install cargo-tree

# 安装cargo-watch (文件监控)
cargo install cargo-watch

# 安装cargo-make (构建工具)
cargo install cargo-make

# 安装cargo-release (发布工具)
cargo install cargo-release

# 安装cargo-bench (基准测试)
cargo install cargo-bench

# 安装cargo-profdata (性能分析)
cargo install cargo-profdata
```

### 调试工具

```bash
# 安装gdb调试器
# Ubuntu/Debian
sudo apt-get install gdb

# macOS
brew install gdb

# Windows
# 安装Visual Studio或MinGW

# 安装lldb调试器
# Ubuntu/Debian
sudo apt-get install lldb

# macOS
# 已包含在Xcode中

# 安装valgrind (内存检查)
# Ubuntu/Debian
sudo apt-get install valgrind

# macOS
brew install valgrind
```

### 性能分析工具

```bash
# 安装perf (Linux性能分析)
# Ubuntu/Debian
sudo apt-get install linux-tools-generic

# 安装flamegraph
cargo install flamegraph

# 安装cargo-flamegraph
cargo install cargo-flamegraph

# 安装cargo-profdata
cargo install cargo-profdata

# 安装cargo-bench
cargo install cargo-bench
```

---

## 📦 项目管理

### Cargo配置

```toml
# .cargo/config.toml
[build]
# 构建配置
rustflags = ["-C", "target-cpu=native"]
target = "x86_64-unknown-linux-gnu"

[target.'cfg(target_os = "linux")']
# Linux特定配置
rustflags = ["-C", "target-cpu=native"]

[target.'cfg(target_os = "windows")']
# Windows特定配置
rustflags = ["-C", "target-cpu=native"]

[target.'cfg(target_os = "macos")']
# macOS特定配置
rustflags = ["-C", "target-cpu=native"]

[net]
# 网络配置
retry = 2
git-fetch-with-cli = true

[registries.crates-io]
# 注册表配置
protocol = "sparse"

[alias]
# 别名配置
b = "build"
t = "test"
r = "run"
c = "check"
f = "fmt"
l = "clippy"
u = "update"
clean-all = "clean && cargo clean --doc && cargo clean --release"
test-all = "test --all --all-features"
check-all = "check --all --all-features"
fmt-check = "fmt -- --check"
clippy-all = "clippy --all --all-features -- -D warnings"
audit-all = "audit --all"
outdated-all = "outdated --all"
coverage = "tarpaulin --out Html"
bench-all = "bench --all --all-features"
release-check = "release --dry-run"
release-publish = "release --execute"

[env]
# 环境变量
RUST_LOG = "debug"
RUST_BACKTRACE = "1"
RUSTFLAGS = "-C target-cpu=native"

[profile.dev]
# 开发配置
debug = true
opt-level = 0
overflow-checks = true
debug-assertions = true
panic = "unwind"
incremental = true
codegen-units = 256
rpath = false
lto = false
debuginfo = 2
split-debuginfo = "unpacked"

[profile.release]
# 发布配置
debug = false
opt-level = 3
overflow-checks = false
debug-assertions = false
panic = "abort"
incremental = false
codegen-units = 1
rpath = false
lto = true
debuginfo = 0
split-debuginfo = "off"

[profile.test]
# 测试配置
debug = true
opt-level = 0
overflow-checks = true
debug-assertions = true
panic = "unwind"
incremental = true
codegen-units = 256
rpath = false
lto = false
debuginfo = 2
split-debuginfo = "unpacked"

[profile.bench]
# 基准测试配置
debug = false
opt-level = 3
overflow-checks = false
debug-assertions = false
panic = "abort"
incremental = false
codegen-units = 1
rpath = false
lto = true
debuginfo = 0
split-debuginfo = "off"
```

### 工作区配置

```toml
# Cargo.toml
[workspace]
members = [
    "crates/*",
    "examples/*",
    "tests/*",
]
exclude = [
    "target",
    "*.md",
    "scripts",
    "docs",
]
default-members = ["crates/*"]
resolver = "2"

[workspace.metadata]
name = "rust-learning-project"
description = "A comprehensive Rust learning project"
version = "0.1.0"
authors = ["Rust Developer"]
license = "MIT"
repository = "https://github.com/user/rust-learning-project"
documentation = "https://docs.rs/rust-learning-project"
homepage = "https://github.com/user/rust-learning-project"
keywords = ["rust", "learning", "education", "tutorial"]
categories = ["development-tools", "education"]

[workspace.dependencies]
# 核心依赖
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
thiserror = "1.0"
log = "0.4"
env_logger = "0.10"

# 异步运行时
tokio = { version = "1.0", features = ["full"] }
futures = "0.3"

# 测试框架
tokio-test = "0.4"
tempfile = "3.0"
criterion = "0.5"
proptest = "1.0"
mockall = "0.12"
rstest = "0.18"

# 代码质量
cargo-tarpaulin = "0.26"
cargo-audit = "0.18"
cargo-outdated = "0.12"

[workspace.metadata.features]
default = ["std"]
std = []
async = ["tokio", "futures"]
test = ["tokio-test", "tempfile", "criterion", "proptest", "mockall", "rstest"]
bench = ["criterion"]
dev = ["cargo-tarpaulin", "cargo-audit", "cargo-outdated"]

[workspace.metadata.config]
min-rust-version = "1.70.0"
target-rust-version = "1.70.0"
workspace-type = "mixed"
language = "rust"
platform = "cross-platform"
```

---

## 🧪 测试环境

### 测试配置

```toml
# Cargo.toml
[dev-dependencies]
tokio-test = "0.4"
tempfile = "3.0"
criterion = "0.5"
proptest = "1.0"
mockall = "0.12"
rstest = "0.18"
testcontainers = "0.15"

[features]
default = ["std"]
std = []
test = ["tokio-test", "tempfile", "criterion", "proptest", "mockall", "rstest"]
bench = ["criterion"]

[[bench]]
name = "my_benchmark"
harness = false
```

### 测试脚本

```bash
#!/bin/bash
# scripts/run-tests.sh

set -e

echo "Running all tests..."

# 运行单元测试
echo "Running unit tests..."
cargo test --lib

# 运行集成测试
echo "Running integration tests..."
cargo test --test '*'

# 运行文档测试
echo "Running documentation tests..."
cargo test --doc

# 运行基准测试
echo "Running benchmark tests..."
cargo bench

# 运行代码覆盖率测试
echo "Running coverage tests..."
cargo tarpaulin --out Html

# 运行安全审计
echo "Running security audit..."
cargo audit

# 运行依赖更新检查
echo "Checking for outdated dependencies..."
cargo outdated

echo "All tests completed successfully!"
```

---

## 📊 性能分析

### 基准测试配置

```rust
// benches/my_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::time::Duration;

fn benchmark_function(c: &mut Criterion) {
    let mut group = c.benchmark_group("my_function");

    group.measurement_time(Duration::from_secs(10));
    group.sample_size(100);
    group.confidence_level(0.95);
    group.significance_level(0.05);

    group.bench_function("basic", |b| {
        b.iter(|| my_function(black_box(42)))
    });

    group.bench_function("optimized", |b| {
        b.iter(|| my_optimized_function(black_box(42)))
    });

    group.finish();
}

criterion_group!(benches, benchmark_function);
criterion_main!(benches);
```

### 性能分析脚本

```bash
#!/bin/bash
# scripts/performance-analysis.sh

set -e

echo "Starting performance analysis..."

# 构建发布版本
echo "Building release version..."
cargo build --release

# 运行基准测试
echo "Running benchmark tests..."
cargo bench

# 生成火焰图
echo "Generating flamegraph..."
cargo flamegraph --bin my_app

# 运行性能分析
echo "Running performance analysis..."
perf record -g ./target/release/my_app
perf report

# 运行内存分析
echo "Running memory analysis..."
valgrind --tool=memcheck --leak-check=full ./target/release/my_app

echo "Performance analysis completed!"
```

---

## 🚀 部署配置

### Docker配置

```dockerfile
# Dockerfile
FROM rust:1.70-slim as builder

WORKDIR /app

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 复制Cargo文件
COPY Cargo.toml Cargo.lock ./

# 构建依赖
RUN cargo build --release

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release

# 运行时镜像
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/my_app /usr/local/bin/my_app

EXPOSE 8080

CMD ["my_app"]
```

### Docker Compose配置

```yaml
# docker-compose.yml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
      - DATABASE_URL=postgresql://user:password@db:5432/myapp
    depends_on:
      - db
    volumes:
      - ./logs:/app/logs

  db:
    image: postgres:15
    environment:
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
      - POSTGRES_DB=myapp
    volumes:
      - postgres_data:/var/lib/postgresql/data
    ports:
      - "5432:5432"

volumes:
  postgres_data:
```

### Kubernetes配置

```yaml
# k8s/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
    spec:
      containers:
      - name: rust-app
        image: my-registry/rust-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: RUST_LOG
          value: "info"
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: db-secret
              key: url
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "200m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5

---
apiVersion: v1
kind: Service
metadata:
  name: rust-app-service
spec:
  selector:
    app: rust-app
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8080
  type: LoadBalancer
```

---

## 🔒 安全配置

### 安全审计配置

```toml
# .cargo/audit.toml
[database]
url = "https://github.com/RustSec/advisory-db.git"
path = "~/.cargo/advisory-db"

[audit]
ignore = [
    "RUSTSEC-2023-0001",  # 特定漏洞ID
]

[advisories]
ignore = [
    "RUSTSEC-2023-0001",  # 特定漏洞ID
]

[package]
ignore = [
    "package-name",  # 特定包名
]
```

### 依赖安全检查

```bash
#!/bin/bash
# scripts/security-check.sh

set -e

echo "Running security checks..."

# 运行安全审计
echo "Running cargo audit..."
cargo audit

# 检查依赖漏洞
echo "Checking for vulnerabilities..."
cargo audit --deny warnings

# 检查过时的依赖
echo "Checking for outdated dependencies..."
cargo outdated

# 检查许可证
echo "Checking licenses..."
cargo license

echo "Security checks completed!"
```

---

## 📝 最佳实践

### 开发流程

1. **代码质量检查**

   ```bash
   # 格式化代码
   cargo fmt

   # 运行clippy
   cargo clippy -- -D warnings

   # 运行测试
   cargo test

   # 构建项目
   cargo build --release
   ```

2. **提交前检查**

   ```bash
   # 运行所有检查
   cargo check --all
   cargo test --all
   cargo clippy --all -- -D warnings
   cargo fmt -- --check
   ```

3. **发布前检查**

   ```bash
   # 运行完整检查
   cargo test --all --all-features
   cargo clippy --all --all-features -- -D warnings
   cargo audit
   cargo outdated
   ```

### 性能优化

1. **编译优化**

   ```toml
   # Cargo.toml
   [profile.release]
   opt-level = 3
   lto = true
   codegen-units = 1
   panic = "abort"
   ```

2. **运行时优化**

   ```bash
   # 设置环境变量
   export RUST_LOG=info
   export RUST_BACKTRACE=1
   export RUSTFLAGS="-C target-cpu=native"
   ```

### 调试技巧

1. **日志配置**

   ```rust
   use log::{info, warn, error, debug, trace};

   fn main() {
       env_logger::init();

       info!("Application started");
       debug!("Debug information");
       warn!("Warning message");
       error!("Error message");
   }
   ```

2. **调试符号**

   ```toml
   # Cargo.toml
   [profile.dev]
   debug = true
   debuginfo = 2

   [profile.release]
   debug = false
   debuginfo = 1
   ```

---

## ❓ 常见问题

### 安装问题

**Q: rustup安装失败**:

```bash
# 解决方案
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain stable
```

**Q: 组件安装失败**:

```bash
# 解决方案
rustup component add rustfmt clippy rust-src
```

**Q: 目标平台安装失败**:

```bash
# 解决方案
rustup target add wasm32-unknown-unknown
```

### 编译问题

**Q: 编译错误**:

```bash
# 解决方案
cargo clean
cargo update
cargo build
```

**Q: 链接错误**:

```bash
# 解决方案
# 安装系统依赖
sudo apt-get install build-essential pkg-config libssl-dev
```

**Q: 内存不足**:

```bash
# 解决方案
# 增加交换空间
sudo fallocate -l 2G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile
```

### 性能问题

**Q: 编译速度慢**:

```bash
# 解决方案
# 启用增量编译
export CARGO_INCREMENTAL=1
```

**Q: 运行时性能差**:

```bash
# 解决方案
# 使用发布版本
cargo build --release
```

**Q: 内存使用高**:

```bash
# 解决方案
# 使用内存分析工具
valgrind --tool=memcheck ./target/release/my_app
```

---

-**遵循这些配置指南，您将能够建立一个高效、安全、可靠的Rust开发环境！🦀**-
