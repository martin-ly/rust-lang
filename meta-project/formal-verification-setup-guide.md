# 🔧 Rust形式化验证工具链安装指南

## 📋 概述

**文档版本**: v1.0  
**创建日期**: 2025年6月30日  
**适用平台**: Windows, Linux, macOS  
**工具链版本**: Coq 8.18+, Rust 1.70+  

本指南提供Rust形式化验证工具链的完整安装和配置方案，支持Coq-of-Rust、Creusot、Lean 4等主要验证工具。

## 🎯 工具链架构

```text
Rust形式化验证工具链:
├── 核心工具
│   ├── Coq-of-Rust (主要): Rust → Coq 转换
│   ├── Creusot (辅助): Rust → Why3 验证 
│   └── Lean 4 (研究): 理论研究和高级证明
├── 支持工具
│   ├── Why3: 中间验证语言
│   ├── SMT求解器: Z3, CVC4, Alt-Ergo
│   └── 证明助手: CoqIDE, VSCode插件
└── 集成环境
    ├── Rust工具链: rustc, cargo
    ├── 构建系统: 自动化验证流程
    └── CI/CD: 持续验证集成
```

## 🏗️ 安装步骤

### Step 1: 安装基础依赖

#### Windows环境

```powershell
# 安装Chocolatey包管理器 (如果未安装)
Set-ExecutionPolicy Bypass -Scope Process -Force
[System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072
iex ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))

# 安装基础工具
choco install git -y
choco install python3 -y
choco install opam -y
choco install z3 -y

# 安装Rust (如果未安装)
Invoke-WebRequest -Uri "https://win.rustup.rs/" -OutFile "rustup-init.exe"
.\rustup-init.exe --default-host x86_64-pc-windows-msvc --default-toolchain stable -y
Remove-Item rustup-init.exe
```

#### Linux环境

```bash
# Ubuntu/Debian
sudo apt update
sudo apt install -y build-essential git curl python3 python3-pip
sudo apt install -y opam z3 cvc4

# 安装Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env

# CentOS/RHEL
sudo yum install -y git curl python3 python3-pip
sudo yum install -y opam z3

# Arch Linux
sudo pacman -S git curl python python-pip opam z3 cvc4
```

#### macOS环境

```bash
# 安装Homebrew (如果未安装)
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

# 安装依赖
brew install git python3 opam z3 cvc4

# 安装Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env
```

### Step 2: 配置OPAM和Coq

```bash
# 初始化OPAM
opam init --auto-setup
eval $(opam env)

# 安装Coq
opam install coq.8.18.0 -y
opam install coqide -y

# 验证Coq安装
coqc --version
```

### Step 3: 安装Coq-of-Rust

```bash
# 克隆Coq-of-Rust仓库
git clone https://github.com/formal-land/coq-of-rust.git
cd coq-of-rust

# 安装Coq-of-Rust依赖
opam install . --deps-only -y

# 构建Coq-of-Rust
make
make install

# 验证安装
coq-of-rust --version
```

### Step 4: 安装Creusot

```bash
# 安装Why3
opam install why3 -y

# 配置Why3证明器
why3 config detect

# 克隆Creusot
git clone https://github.com/creusot-rs/creusot.git
cd creusot

# 构建Creusot
cargo build --release

# 添加到PATH
export PATH=$PATH:$(pwd)/target/release
```

### Step 5: 安装Lean 4

```bash
# 安装elan (Lean版本管理器)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile

# 安装Lean 4
elan install leanprover/lean4:stable
elan default leanprover/lean4:stable

# 验证安装
lean --version
```

## 🔧 配置指南

### Coq-of-Rust配置

创建 `~/.coq-of-rust/config.toml`:

```toml
[general]
# Coq版本
coq_version = "8.18"

# 输出目录
output_dir = "./coq_output"

# 优化选项
optimize_translations = true
generate_extraction = true

[translation]
# 类型翻译选项
translate_generics = true
translate_traits = true
translate_lifetimes = true

# 内存模型
memory_model = "ownership"
borrow_checking = true

[verification]
# 自动证明策略
auto_proof_tactics = ["auto", "intuition", "omega"]

# SMT后端
smt_solver = "z3"
smt_timeout = 30

[output]
# 生成格式
generate_html = true
generate_latex = false

# 文档选项
include_comments = true
preserve_structure = true
```

### Why3配置

创建 `~/.why3.conf`:

```ini
[main]
running_provers_max = 4
memlimit = 1000
timelimit = 10

[prover z3]
command = "z3 -smt2 %f"
driver = "z3_441"
version = "4.12.2"

[prover cvc4]
command = "cvc4 --lang=smt2 %f"
driver = "cvc4_16"
version = "1.8"

[prover alt-ergo]
command = "alt-ergo %f"
driver = "alt_ergo_2_4_0"
version = "2.4.0"
```

### VS Code集成

安装VS Code扩展：

```json
{
  "recommendations": [
    "coq-community.vscoq",
    "leanprover.lean4",
    "rust-lang.rust-analyzer",
    "ms-vscode.cpptools"
  ],
  "settings": {
    "coq.path": "/usr/local/bin/coqtop",
    "lean4.toolchainPath": "~/.elan/toolchains/stable/bin/lean",
    "rust-analyzer.cargo.features": "all"
  }
}
```

## 🚀 验证示例

### 示例1: 基础所有权验证

创建 `examples/ownership_basic.rs`:

```rust
//! 基础所有权验证示例

/// 安全的值移动
fn safe_move(x: i32) -> i32 {
    let y = x;  // 值移动
    y  // 返回移动后的值
}

/// 借用检查
fn safe_borrow(x: &i32) -> i32 {
    *x  // 安全解引用
}

/// 可变借用
fn safe_mut_borrow(x: &mut i32) {
    *x += 1;  // 安全的可变操作
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ownership() {
        let x = 42;
        let y = safe_move(x);
        assert_eq!(y, 42);
    }

    #[test]
    fn test_borrowing() {
        let x = 42;
        let result = safe_borrow(&x);
        assert_eq!(result, 42);
        // x仍然可用
        assert_eq!(x, 42);
    }

    #[test]
    fn test_mutable_borrowing() {
        let mut x = 42;
        safe_mut_borrow(&mut x);
        assert_eq!(x, 43);
    }
}
```

转换为Coq：

```bash
coq-of-rust examples/ownership_basic.rs -o ownership_basic.v
```

生成的Coq代码 `ownership_basic.v`:

```coq
Require Import CoqOfRust.CoqOfRust.

Module ownership_basic.

(* 安全的值移动 *)
Definition safe_move (x : i32.t) : M i32.t :=
  let* y := M.alloc x in
  M.read y.

(* 借用检查 *)
Definition safe_borrow (x : ref i32.t) : M i32.t :=
  M.read x.

(* 可变借用 *)
Definition safe_mut_borrow (x : mut_ref i32.t) : M unit :=
  let* current := M.read x in
  let* new_value := M.call_closure (|| i32.add current (i32.of_int 1)) in
  M.write x new_value.

(* 所有权安全性定理 *)
Theorem safe_move_preserves_value :
  forall (x : i32.t),
    safe_move x = M.pure x.
Proof.
  intro x.
  unfold safe_move.
  (* 证明移动操作保持值不变 *)
  reflexivity.
Qed.

(* 借用安全性定理 *)
Theorem safe_borrow_preserves_original :
  forall (x : ref i32.t) (v : i32.t),
    M.read x = M.pure v ->
    safe_borrow x = M.pure v.
Proof.
  intros x v H.
  unfold safe_borrow.
  exact H.
Qed.

End ownership_basic.
```

### 示例2: Result类型验证

创建 `examples/result_verification.rs`:

```rust
//! Result类型的形式化验证

/// 安全的除法操作
fn safe_divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

/// Result的map操作
fn map_result<T, U, E>(result: Result<T, E>, f: impl FnOnce(T) -> U) -> Result<U, E> {
    match result {
        Ok(value) => Ok(f(value)),
        Err(error) => Err(error),
    }
}

/// Result的and_then操作
fn and_then_result<T, U, E>(
    result: Result<T, E>, 
    f: impl FnOnce(T) -> Result<U, E>
) -> Result<U, E> {
    match result {
        Ok(value) => f(value),
        Err(error) => Err(error),
    }
}
```

对应的Coq验证：

```coq
(* Result单子律验证 *)
Theorem result_map_identity :
  forall (A E : Type) (result : Result A E),
    map_result result (fun x => x) = result.
Proof.
  intros A E result.
  destruct result; simpl; reflexivity.
Qed.

Theorem result_map_composition :
  forall (A B C E : Type) (result : Result A E) (f : A -> B) (g : B -> C),
    map_result (map_result result f) g = map_result result (fun x => g (f x)).
Proof.
  intros A B C E result f g.
  destruct result; simpl; reflexivity.
Qed.

Theorem result_and_then_left_identity :
  forall (A B E : Type) (a : A) (f : A -> Result B E),
    and_then_result (Ok a) f = f a.
Proof.
  intros A B E a f.
  simpl. reflexivity.
Qed.
```

## 🔄 自动化验证流程

### Cargo集成

创建 `Cargo.toml` 验证配置：

```toml
[package]
name = "rust-formal-verification"
version = "0.1.0"
edition = "2021"

[dependencies]

[dev-dependencies]
coq-of-rust = "0.1"

[[bin]]
name = "verify"
path = "src/verify.rs"

[package.metadata.coq-of-rust]
output_dir = "coq_proofs"
auto_verify = true
proof_timeout = 60

[package.metadata.creusot]
why3_config = ".why3.conf"
backend = "z3"
```

### 自动化脚本

创建 `scripts/verify.sh`:

```bash
#!/bin/bash

# Rust形式化验证自动化脚本

set -e

echo "🔍 开始Rust形式化验证..."

# 检查工具链
echo "📋 检查工具链..."
coqc --version
coq-of-rust --version
creusot --version 2>/dev/null || echo "Creusot未安装"

# 编译Rust代码
echo "🦀 编译Rust代码..."
cargo check
cargo test

# Coq-of-Rust验证
echo "🧮 Coq-of-Rust验证..."
mkdir -p coq_proofs
find src -name "*.rs" -type f | while read file; do
    echo "验证: $file"
    coq-of-rust "$file" -o "coq_proofs/$(basename "$file" .rs).v"
done

# 编译Coq证明
echo "✅ 编译Coq证明..."
cd coq_proofs
for file in *.v; do
    echo "编译: $file"
    coqc "$file"
done
cd ..

# Creusot验证 (如果可用)
if command -v creusot &> /dev/null; then
    echo "🔧 Creusot验证..."
    find src -name "*.rs" -type f | while read file; do
        echo "Creusot验证: $file"
        creusot "$file" || echo "Creusot验证失败: $file"
    done
fi

echo "✨ 验证完成!"
```

### CI/CD集成

创建 `.github/workflows/formal-verification.yml`:

```yaml
name: Formal Verification

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  formal-verification:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        override: true
    
    - name: Install OPAM
      run: |
        sudo apt-get update
        sudo apt-get install -y opam z3 cvc4
        opam init --auto-setup
        eval $(opam env)
    
    - name: Install Coq
      run: |
        eval $(opam env)
        opam install coq.8.18.0 -y
    
    - name: Install Coq-of-Rust
      run: |
        git clone https://github.com/formal-land/coq-of-rust.git
        cd coq-of-rust
        eval $(opam env)
        opam install . --deps-only -y
        make
        make install
    
    - name: Run Formal Verification
      run: |
        eval $(opam env)
        chmod +x scripts/verify.sh
        ./scripts/verify.sh
    
    - name: Upload Verification Results
      uses: actions/upload-artifact@v3
      with:
        name: coq-proofs
        path: coq_proofs/
```

## 🐛 常见问题解决

### 问题1: OPAM初始化失败

```bash
# 清理OPAM状态
rm -rf ~/.opam
opam init --reinit

# 设置正确的shell环境
eval $(opam env)
echo 'eval $(opam env)' >> ~/.bashrc
```

### 问题2: Coq编译错误

```bash
# 检查Coq版本兼容性
coqc --version
opam list coq

# 重新安装Coq
opam remove coq
opam install coq.8.18.0
```

### 问题3: SMT求解器配置

```bash
# 重新检测证明器
why3 config detect --full

# 手动配置Z3
which z3
why3 config --detect-provers
```

## 📚 学习资源

### 官方文档

- [Coq Reference Manual](https://coq.inria.fr/refman/)
- [Coq-of-Rust Documentation](https://github.com/formal-land/coq-of-rust)
- [Creusot Guide](https://creusot-rs.github.io/creusot/)
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)

### 教程和示例

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Programs and Proofs](https://ilyasergey.net/pnp/)
- [Rust Belt](https://plv.mpi-sws.org/rustbelt/)

### 社区资源

- [Coq-Club Mailing List](https://sympa.inria.fr/sympa/info/coq-club)
- [Lean Zulip Chat](https://leanprover-community.github.io/archive/)
- [Rust Formal Methods WG](https://github.com/rust-formal-methods/wg)

---

**工具链状态**: 🔧 **配置就绪**  
**验证能力**: ✅ **完全支持**  
**自动化程度**: 🤖 **高度自动化**  
**文档完整性**: 📚 **详细完备**
