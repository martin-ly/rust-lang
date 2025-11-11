# 研究工具使用指南

> **创建日期**: 2025-01-27
> **最后更新**: 2025-01-27
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 持续更新中 📝

---

## 📊 目录

- [研究工具使用指南](#研究工具使用指南)
  - [📊 目录](#-目录)
  - [🎯 工具分类](#-工具分类)
  - [🔬 形式化验证工具](#-形式化验证工具)
    - [Coq](#coq)
    - [Lean](#lean)
    - [Prusti](#prusti)
    - [Kani](#kani)
  - [⚡ 性能分析工具](#-性能分析工具)
    - [Criterion.rs](#criterionrs)
    - [perf](#perf)
    - [flamegraph](#flamegraph)
  - [🔍 内存分析工具](#-内存分析工具)
    - [Miri](#miri)
    - [Valgrind](#valgrind)
    - [heaptrack](#heaptrack)
  - [🧪 测试工具](#-测试工具)
    - [cargo test](#cargo-test)
    - [proptest](#proptest)
    - [loom](#loom)
  - [📚 代码分析工具](#-代码分析工具)
    - [Clippy](#clippy)
    - [rust-analyzer](#rust-analyzer)
    - [cargo-expand](#cargo-expand)
  - [💡 使用建议](#-使用建议)
    - [工具选择](#工具选择)
    - [工具组合](#工具组合)
    - [最佳实践](#最佳实践)
  - [🔗 相关资源](#-相关资源)

---

## 🎯 工具分类

研究工具按用途分为以下几类：

1. **形式化验证工具** - 用于形式化证明和验证
2. **性能分析工具** - 用于性能测试和优化
3. **内存分析工具** - 用于内存使用分析
4. **测试工具** - 用于代码测试
5. **代码分析工具** - 用于代码质量分析

---

## 🔬 形式化验证工具

### Coq

**用途**: 交互式定理证明器，用于形式化证明

**安装**:

```bash
# 使用 opam 安装
opam install coq

# 或使用包管理器
# Ubuntu/Debian
sudo apt-get install coq

# macOS
brew install coq
```

**基本使用**:

```coq
(* 定义自然数 *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(* 定义加法 *)
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

(* 证明加法交换律 *)
Theorem plus_comm : forall n m, plus n m = plus m n.
Proof.
  (* 证明步骤 *)
Qed.
```

**相关资源**:

- [Coq 官网](https://coq.inria.fr/)
- [Coq 文档](https://coq.inria.fr/documentation)
- [Coq 教程](https://coq.inria.fr/tutorial)

---

### Lean

**用途**: 现代定理证明器，用于形式化数学和程序验证

**安装**:

```bash
# 使用 elan 安装
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 验证安装
lean --version
```

**基本使用**:

```lean
-- 定义自然数
inductive Nat
  | zero : Nat
  | succ : Nat → Nat

-- 定义加法
def add : Nat → Nat → Nat
  | n, Nat.zero => n
  | n, Nat.succ m => Nat.succ (add n m)

-- 证明加法交换律
theorem add_comm (n m : Nat) : add n m = add m n := by
  -- 证明步骤
  sorry
```

**相关资源**:

- [Lean 官网](https://leanprover.github.io/)
- [Lean 文档](https://leanprover.github.io/learn/)
- [Lean 教程](https://leanprover.github.io/theorem_proving_in_lean/)

---

### Prusti

**用途**: Rust 程序的形式化验证工具

**安装**:

```bash
# 安装 Prusti
cargo install prusti-launch

# 验证安装
cargo prusti --version
```

**基本使用**:

```rust
use prusti_contracts::*;

#[requires(x > 0)]
#[ensures(result > x)]
fn increment(x: i32) -> i32 {
    x + 1
}

#[pure]
#[ensures(result >= 0)]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

**运行验证**:

```bash
# 验证整个项目
cargo prusti

# 验证特定文件
cargo prusti --file src/lib.rs
```

**相关资源**:

- [Prusti 文档](https://viperproject.github.io/prusti-dev/)
- [Prusti 用户指南](https://viperproject.github.io/prusti-dev/user-guide/)
- [Prusti 教程](https://viperproject.github.io/prusti-dev/user-guide/getting-started.html)

---

### Kani

**用途**: Rust 程序的模型检查器

**安装**:

```bash
# 安装 Kani
cargo install kani-verifier

# 验证安装
cargo kani --version
```

**基本使用**:

```rust
#[kani::proof]
fn test_abs() {
    let x: i32 = kani::any();
    let result = abs(x);
    assert!(result >= 0);
}

fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

**运行验证**:

```bash
# 验证整个项目
cargo kani

# 验证特定函数
cargo kani --function test_abs
```

**相关资源**:

- [Kani 文档](https://github.com/model-checking/kani)
- [Kani 用户指南](https://model-checking.github.io/kani/)
- [Kani 教程](https://model-checking.github.io/kani/tutorial.html)

---

## ⚡ 性能分析工具

### Criterion.rs

**用途**: 统计驱动的 Rust 基准测试框架

**安装**:

```toml
# Cargo.toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

**基本使用**:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn benchmark_fibonacci(c: &mut Criterion) {
    c.bench_function("fibonacci 20", |b| {
        b.iter(|| fibonacci(black_box(20)))
    });
}

criterion_group!(benches, benchmark_fibonacci);
criterion_main!(benches);
```

**运行基准测试**:

```bash
cargo bench
```

**相关资源**:

- [Criterion.rs 文档](https://docs.rs/criterion/)
- [Criterion.rs 指南](https://github.com/bheisler/criterion.rs/blob/master/book/src/user_guide/index.md)

---

### perf

**用途**: Linux 性能分析工具

**安装**:

```bash
# Ubuntu/Debian
sudo apt-get install linux-perf

# 或使用包管理器
sudo apt-get install perf
```

**基本使用**:

```bash
# 记录性能数据
perf record ./target/release/my_program

# 查看报告
perf report

# 实时监控
perf top

# 统计信息
perf stat ./target/release/my_program
```

**相关资源**:

- [perf 文档](https://perf.wiki.kernel.org/)
- [perf 教程](https://perf.wiki.kernel.org/index.php/Tutorial)

---

### flamegraph

**用途**: 性能火焰图生成工具

**安装**:

```bash
# 安装 cargo-flamegraph
cargo install flamegraph

# 或使用系统包管理器
# Ubuntu/Debian
sudo apt-get install flamegraph
```

**基本使用**:

```bash
# 生成火焰图
cargo flamegraph --bin my_program

# 指定输出文件
cargo flamegraph -o flamegraph.svg --bin my_program
```

**相关资源**:

- [flamegraph 文档](https://github.com/flamegraph-rs/flamegraph)
- [flamegraph 使用指南](https://github.com/flamegraph-rs/flamegraph#usage)

---

## 🔍 内存分析工具

### Miri

**用途**: Rust 的中断执行器，用于检查未定义行为

**安装**:

```bash
# 安装 Miri
rustup component add miri

# 验证安装
miri --version
```

**基本使用**:

```bash
# 运行 Miri 检查
MIRIFLAGS="-Zmiri-tag-raw-pointers" cargo miri test

# 运行特定测试
cargo miri test --test my_test
```

**相关资源**:

- [Miri 文档](https://github.com/rust-lang/miri)
- [Miri 用户指南](https://github.com/rust-lang/miri#usage)

---

### Valgrind

**用途**: 内存错误检测工具

**安装**:

```bash
# Ubuntu/Debian
sudo apt-get install valgrind

# macOS (使用 Homebrew)
brew install valgrind
```

**基本使用**:

```bash
# 内存泄漏检测
valgrind --leak-check=full ./target/release/my_program

# 详细报告
valgrind --tool=memcheck --leak-check=yes ./target/release/my_program
```

**相关资源**:

- [Valgrind 文档](https://valgrind.org/docs/manual/manual.html)
- [Valgrind 用户指南](https://valgrind.org/docs/manual/quick-start.html)

---

### heaptrack

**用途**: 堆内存分析工具

**安装**:

```bash
# Ubuntu/Debian
sudo apt-get install heaptrack

# 或从源码编译
git clone https://github.com/KDE/heaptrack
cd heaptrack
mkdir build && cd build
cmake ..
make
sudo make install
```

**基本使用**:

```bash
# 跟踪程序
heaptrack ./target/release/my_program

# 查看报告
heaptrack_gui heaptrack.my_program.12345.gz
```

**相关资源**:

- [heaptrack 文档](https://github.com/KDE/heaptrack)
- [heaptrack 使用指南](https://github.com/KDE/heaptrack#usage)

---

## 🧪 测试工具

### cargo test

**用途**: Rust 标准测试工具

**基本使用**:

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_name

# 显示输出
cargo test -- --nocapture

# 多线程测试
cargo test -- --test-threads=1
```

---

### proptest

**用途**: 属性测试框架

**安装**:

```toml
# Cargo.toml
[dev-dependencies]
proptest = "1.0"
```

**基本使用**:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_addition_commutative(a in 0..1000i32, b in 0..1000i32) {
        assert_eq!(a + b, b + a);
    }
}
```

**相关资源**:

- [proptest 文档](https://docs.rs/proptest/)
- [proptest 教程](https://altsysrq.github.io/proptest-book/intro.html)

---

### loom

**用途**: 并发模型验证工具

**安装**:

```toml
# Cargo.toml
[dev-dependencies]
loom = "0.5"
```

**基本使用**:

```rust
#[cfg(test)]
mod tests {
    use loom::thread;

    #[test]
    fn test_concurrent() {
        loom::model(|| {
            let mut data = 0;
            thread::spawn(|| {
                data += 1;
            });
            data += 1;
        });
    }
}
```

**相关资源**:

- [loom 文档](https://docs.rs/loom/)
- [loom 使用指南](https://github.com/tokio-rs/loom#usage)

---

## 📚 代码分析工具

### Clippy

**用途**: Rust 代码检查工具

**安装**:

```bash
# 安装 Clippy
rustup component add clippy
```

**基本使用**:

```bash
# 检查代码
cargo clippy

# 自动修复
cargo clippy --fix

# 显示所有警告
cargo clippy -- -W clippy::all
```

**相关资源**:

- [Clippy 文档](https://github.com/rust-lang/rust-clippy)
- [Clippy 规则](https://rust-lang.github.io/rust-clippy/master/index.html)

---

### rust-analyzer

**用途**: Rust 语言服务器

**安装**:

```bash
# 使用 rustup
rustup component add rust-analyzer

# 或从源码编译
git clone https://github.com/rust-lang/rust-analyzer.git
cd rust-analyzer
cargo xtask install --server
```

**基本使用**:
rust-analyzer 通常在 IDE 中自动使用，提供：

- 代码补全
- 类型检查
- 重构支持
- 跳转定义

**相关资源**:

- [rust-analyzer 文档](https://rust-analyzer.github.io/)
- [rust-analyzer 用户指南](https://rust-analyzer.github.io/manual.html)

---

### cargo-expand

**用途**: 宏展开工具

**安装**:

```bash
# 安装 cargo-expand
cargo install cargo-expand
```

**基本使用**:

```bash
# 展开宏
cargo expand

# 展开特定项
cargo expand my_macro

# 输出到文件
cargo expand > expanded.rs
```

**相关资源**:

- [cargo-expand 文档](https://github.com/dtolnay/cargo-expand)
- [cargo-expand 使用指南](https://github.com/dtolnay/cargo-expand#usage)

---

## 💡 使用建议

### 工具选择

根据研究类型选择工具：

- **形式化研究** → Coq, Lean, Prusti, Kani
- **性能研究** → Criterion.rs, perf, flamegraph
- **内存研究** → Miri, Valgrind, heaptrack
- **代码质量** → Clippy, rust-analyzer
- **测试** → cargo test, proptest, loom

### 工具组合

推荐的工具组合：

1. **形式化验证组合**: Prusti + Kani + Coq
2. **性能分析组合**: Criterion.rs + perf + flamegraph
3. **内存分析组合**: Miri + Valgrind + heaptrack
4. **代码质量组合**: Clippy + rust-analyzer + cargo-expand

### 最佳实践

1. **从简单开始**: 先使用基础工具，再使用高级工具
2. **工具组合**: 组合使用多个工具获得全面结果
3. **持续集成**: 将工具集成到 CI/CD 流程
4. **文档记录**: 记录工具使用经验和结果

---

## 🔗 相关资源

- [研究方法论](./research_methodology.md) - 研究方法概述
- [实验研究索引](./experiments/README.md) - 实验研究工具
- [形式化方法索引](./formal_methods/README.md) - 形式化工具

---

**维护团队**: Rust Research Community
**最后更新**: 2025-01-27
**状态**: 📝 **持续更新中**
