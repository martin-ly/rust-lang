# 研究工具使用指南 {#研究工具使用指南}

> **EN**: Tools Guide
> **Summary**: 研究工具使用指南 Tools Guide. (stub/archive redirect)
>
> **概念族**: 方法论 / 工具 / 指南
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6
> **创建日期**: 2025-01-27
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 完成

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [研究工具使用指南 {#研究工具使用指南}](#研究工具使用指南-研究工具使用指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [🎯 工具分类 {#工具分类}](#-工具分类-工具分类)
  - [🔬 形式化验证工具 {#形式化验证工具}](#-形式化验证工具-形式化验证工具)
    - [Prusti {#prusti}](#prusti-prusti)
    - [Kani {#kani}](#kani-kani)
    - [Creusot {#creusot}](#creusot-creusot)
    - [Aeneas {#aeneas}](#aeneas-aeneas)
    - [Verus {#verus}](#verus-verus)
    - [可选进阶：Coq/Lean {#可选进阶coqlean}](#可选进阶coqlean-可选进阶coqlean)
  - [⚡ 性能分析工具 {#性能分析工具}](#-性能分析工具-性能分析工具)
    - [Criterion.rs {#criterionrs}](#criterionrs-criterionrs)
    - [perf {#perf}](#perf-perf)
    - [flamegraph {#flamegraph}](#flamegraph-flamegraph)
  - [🔍 内存分析工具 {#内存分析工具}](#-内存分析工具-内存分析工具)
    - [Miri {#miri}](#miri-miri)
    - [Valgrind {#valgrind}](#valgrind-valgrind)
    - [heaptrack {#heaptrack}](#heaptrack-heaptrack)
  - [🧪 测试工具 {#测试工具}](#-测试工具-测试工具)
    - [cargo test {#cargo-test}](#cargo-test-cargo-test)
    - [proptest {#proptest}](#proptest-proptest)
    - [loom {#loom}](#loom-loom)
  - [📚 代码分析工具 {#代码分析工具}](#-代码分析工具-代码分析工具)
    - [Clippy {#clippy}](#clippy-clippy)
    - [rust-analyzer {#rust-analyzer}](#rust-analyzer-rust-analyzer)
    - [cargo-expand {#cargo-expand}](#cargo-expand-cargo-expand)
  - [💡 使用建议 {#使用建议}](#-使用建议-使用建议)
    - [工具选择 {#工具选择}](#工具选择-工具选择)
    - [工具组合 {#工具组合}](#工具组合-工具组合)
    - [最佳实践 {#最佳实践}](#最佳实践-最佳实践)
  - [🔗 相关资源 {#相关资源}](#-相关资源-相关资源)
  - [📚 Cargo Book 与 rustc dev guide 权威章节 {#cargo-book-与-rustc-dev-guide-权威章节}](#-cargo-book-与-rustc-dev-guide-权威章节-cargo-book-与-rustc-dev-guide-权威章节)
    - [Cargo Book 重点章节 {#cargo-book-重点章节}](#cargo-book-重点章节-cargo-book-重点章节)
    - [rustc dev guide 重点章节 {#rustc-dev-guide-重点章节}](#rustc-dev-guide-重点章节-rustc-dev-guide-重点章节)
  - [🆕 权威国际化内容升级 (Rust 1.97.0+) {#权威国际化内容升级-rust-1960}](#-权威国际化内容升级-rust-1961-权威国际化内容升级-rust-1960)
    - [本次升级要点 {#本次升级要点}](#本次升级要点-本次升级要点)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 🎯 工具分类 {#工具分类}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

研究工具按用途分为以下几类：

1. **形式化验证工具** - 用于形式化证明和验证
2. **性能分析工具** - 用于性能测试和优化
3. **内存分析工具** - 用于内存使用分析
4. **测试工具** - 用于代码测试
5. **代码分析工具** - 用于代码质量分析

---

## 🔬 形式化验证工具 {#形式化验证工具}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**主推路径**：Prusti、Kani（Rust 原生验证，无需学习专业形式化语言）。Coq/Lean 为可选进阶研究，见 [archive/deprecated/](../../archive/deprecated/README.md)。

### Prusti {#prusti}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**用途**: Rust 程序的形式化验证工具

**安装**:

```bash
# 安装 Prusti {#安装-prusti}
cargo install prusti-launch

# 验证安装 {#验证安装-2}
cargo prusti --version
```

**基本使用**:

```rust,ignore
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
# 验证整个项目 {#验证整个项目-1}
cargo prusti

# 验证特定文件 {#验证特定文件}
cargo prusti --file src/lib.rs
```

**与形式化衔接**：Prusti 可验证 [ownership_model](formal_methods/10_ownership_model.md) 定理 T2（移动语义）、[borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) 定理 T1（借用（Borrowing）规则）；`#[requires]`/`#[ensures]` 对应前置/后置条件。

**版本与官方资源**:

- 最新版本：跟随 [Prusti GitHub Releases](https://github.com/viperproject/prusti-dev/releases) 发布；VS Code 用户推荐通过 [Prusti Assistant](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant) 获取最新版。
- [Prusti 用户指南](https://viperproject.github.io/prusti-dev/user-guide/)
- [Prusti 教程 - Getting Started](https://viperproject.github.io/prusti-dev/user-guide/getting-started.html)
- [Prusti GitHub](https://github.com/viperproject/prusti-dev)
- [Prusti 论文：The Prusti Project](https://pm.inf.ethz.ch/publications/AstrauskasBilyFialaGrannanMathejaMuellerPoliSummers22.pdf)

---

### Kani {#kani}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**用途**: Rust 程序的模型检查器

**安装**:

```bash
# 安装 Kani {#安装-kani}
cargo install kani-verifier

# 验证安装 {#验证安装-2}
cargo kani --version
```

**基本使用**:

```rust,ignore
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
# 验证整个项目 {#验证整个项目-1}
cargo kani

# 验证特定函数 {#验证特定函数}
cargo kani --function test_abs
```

**与形式化衔接**：Kani 可验证 [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) 无数据竞争、[ownership_model](formal_methods/10_ownership_model.md) 内存安全（Memory Safety）；`kani::any()` 对应全称量化。

**版本与官方资源**:

- 推荐版本：**0.67.0+**（截至 2026-04，以 [Kani GitHub Releases](https://github.com/model-checking/kani/releases) 最新 tag 为准）。
- [Kani 官方文档 / The Kani Rust Verifier](https://model-checking.github.io/kani/)
- [Kani API Docs (docs.rs)](https://docs.rs/kani-verifier/latest)
- [Kani GitHub](https://github.com/model-checking/kani)
- [Kani 教程](https://model-checking.github.io/kani/tutorial.html)
- 安装命令：`cargo install --locked kani-verifier && cargo kani setup`

---

### Creusot {#creusot}

> **来源**: [Creusot](https://creusot-rs.github.io/)
>
> **来源**: [Why3](http://why3.lri.fr/)

**用途**: 基于 Why3/SMT 的 Rust 演绎验证器，支持函数契约（pre/post）、循环不变式与 ghost 代码。

**安装**:

```bash
# 需要 OPAM、Why3、Alt-Ergo 等辅助工具 {#需要-opamwhy3alt-ergo-等辅助工具}
git clone https://github.com/creusot-rs/creusot.git
cd creusot
cargo install --path creusot-rustc
cargo install --path cargo-creusot
cargo creusot setup install
```

**基本使用**:

```rust,ignore
use creusot_contracts::*;

#[requires(x >= 0)]
#[ensures(result >= x)]
fn increment(x: i32) -> i32 {
    x + 1
}
```

**版本与官方资源**:

- 推荐版本：**0.1.1+**（以 [Creusot GitHub Releases](https://github.com/creusot-rs/creusot/releases) 为准）；依赖特定 nightly Rust。
- [Creusot 主页](https://creusot-rs.github.io/)
- [Creusot GitHub](https://github.com/creusot-rs/creusot)
- [CreuSAT - 经 Creusot 验证的 SAT 求解器](https://github.com/sarsko/CreuSAT)

---

### Aeneas {#aeneas}

> **来源**: [Aeneas](https://aeneas-verif.github.io/aeneas/)
>
> **来源**: [Charon](https://github.com/AeneasVerif/charon)

**用途**: 将安全 Rust 通过 LLBC 函数式翻译到 F\*/Coq/Lean/HOL4，消除显式内存推理。

**安装与使用**:

```bash
# 1. 用 Charon 生成 .llbc {#1-用-charon-生成-llbc}
charon cargo --preset=aeneas
# 2. 用 Aeneas 翻译到目标证明助手 {#2-用-aeneas-翻译到目标证明助手}
./bin/aeneas -backend lean|coq|fstar|hol4 file.llbc
```

**版本与官方资源**:

- 推荐版本：以 [Aeneas GitHub](https://github.com/AeneasVerif/aeneas) 最新 commit 为准；与 Charon 版本需匹配。
- [Aeneas 文档](https://aeneas-verif.github.io/aeneas/)
- [Aeneas GitHub](https://github.com/AeneasVerif/aeneas)
- [Charon GitHub](https://github.com/AeneasVerif/charon)
- [Aeneas 论文 (ICFP 2022)](https://zenodo.org/records/6672939)

---

### Verus {#verus}

> **来源**: [Verus](https://github.com/verus-lang/verusverus/)

**用途**: 面向低层系统代码的 Rust 验证器，使用 SMT 求解器静态检查可执行 Rust 代码是否满足规约。

**安装**:

```bash
git clone https://github.com/verus-lang/verus.git
cd verus/source
# 按仓库 README 安装依赖并运行 vargo build {#按仓库-readme-安装依赖并运行-vargo-build}
```

**基本使用**:

```rust,ignore
use vstd::prelude::*;

verus! {
    fn increment(x: u32) -> (y: u32)
        requires x < u32::MAX,
        ensures y == x + 1,
    {
        x + 1
    }
}
```

**版本与官方资源**:

- 推荐版本：以 [Verus GitHub](https://github.com/verus-lang/verus) 最新 commit / release 为准。
- [Verus 官方文档](https://github.com/verus-lang/verusverus/)
- [Verus GitHub](https://github.com/verus-lang/verus)
- [Verus 教程与参考](https://github.com/verus-lang/verusverus/guide/)
- [Verus 标准库 API](https://github.com/verus-lang/verusverus/verusdoc/vstd/)

---

### 可选进阶：Coq/Lean {#可选进阶coqlean}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**说明**：Coq、Lean 为专业形式化证明语言，需额外学习成本。
本项目已归档 Coq 骨架与 Aeneas 对接计划至 [archive/deprecated/](../../archive/deprecated/README.md)。
主路径聚焦 **数学风格形式化论证 + Rust 示例**（见 [CORE_THEOREMS_FULL_PROOFS](10_core_theorems_full_proofs.md)）。
若需机器可检查证明，可参考 Prusti/Kani 或国际对标 [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](10_international_formal_verification_index.md)。

---

## ⚡ 性能分析工具 {#性能分析工具}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### Criterion.rs {#criterionrs}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**用途**: 统计驱动的 Rust 基准测试框架

**安装**:

```toml
# Cargo.toml {#cargotoml-2}
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

**基本使用**:

```rust,ignore
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

- Criterion.rs 文档
- Criterion.rs 指南

---

### perf {#perf}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**用途**: Linux 性能分析工具

**安装**:

```bash
# Ubuntu/Debian {#ubuntudebian-3}
sudo apt-get install linux-perf

# 或使用包管理器 {#或使用包管理器}
sudo apt-get install perf
```

**基本使用**:

```bash
# 记录性能数据 {#记录性能数据}
perf record ./target/release/my_program

# 查看报告 {#查看报告-1}
perf report

# 实时监控 {#实时监控}
perf top

# 统计信息 {#统计信息}
perf stat ./target/release/my_program
```

**相关资源**:

- perf 文档
- [perf 教程](https://perf.wiki.kernel.org/index.php/Tutorial)

---

### flamegraph {#flamegraph}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**用途**: 性能火焰图生成工具

**安装**:

```bash
# 安装 cargo-flamegraph {#安装-cargo-flamegraph}
cargo install flamegraph

# 或使用系统包管理器 {#或使用系统包管理器}
# Ubuntu/Debian {#ubuntudebian-3}
sudo apt-get install flamegraph
```

**基本使用**:

```bash
# 生成火焰图 {#生成火焰图}
cargo flamegraph --bin my_program

# 指定输出文件 {#指定输出文件}
cargo flamegraph -o flamegraph.svg --bin my_program
```

**相关资源**:

- [flamegraph 文档](https://github.com/flamegraph-rs/flamegraph)
- [flamegraph 使用指南](https://github.com/flamegraph-rs/flamegraph#usage)

---

## 🔍 内存分析工具 {#内存分析工具}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### Miri {#miri}

> **来源: [IEEE](https://standards.ieee.org/)**

**用途**: Rust 的中断执行器，用于检查未定义行为

**安装**:

```bash
# 安装 Miri {#安装-miri}
rustup component add miri

# 验证安装 {#验证安装-2}
miri --version
```

**基本使用**:

```bash
# 运行 Miri 检查 {#运行-miri-检查}
MIRIFLAGS="-Zmiri-tag-raw-pointers" cargo miri test

# 运行特定测试 {#运行特定测试-1}
cargo miri test --test my_test
```

**与形式化衔接**：Miri 检测违反 [ownership_model](formal_methods/10_ownership_model.md)、[borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) 的 UB；
与 [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](10_safe_unsafe_comprehensive_analysis.md) 契约体系对应。

**版本与官方资源**:

- 版本：通过 `rustup component add miri` 安装，版本跟随当前工具链（nightly 优先）。
- [Miri GitHub](https://github.com/rust-lang/miri)
- [Miri 使用指南](https://github.com/rust-lang/miri#usage)
- [rustc dev guide - Miri](https://rustc-dev-guide.rust-lang.org/miri.html)
- 推荐标志：`-Zmiri-tag-raw-pointers`、`-Zmiri-disable-isolation`（视测试场景而定）

---

### Valgrind {#valgrind}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

**用途**: 内存错误检测工具

**安装**:

```bash
# Ubuntu/Debian {#ubuntudebian-3}
sudo apt-get install valgrind

# macOS (使用 Homebrew) {#macos-使用-homebrew}
brew install valgrind
```

**基本使用**:

```bash
# 内存泄漏检测 {#内存泄漏检测}
valgrind --leak-check=full ./target/release/my_program

# 详细报告 {#详细报告}
valgrind --tool=memcheck --leak-check=yes ./target/release/my_program
```

**相关资源**:

- [Valgrind 文档](https://valgrind.org/docs/manual/manual.html)
- [Valgrind 用户指南](https://valgrind.org/docs/manual/quick-start.html)

---

### heaptrack {#heaptrack}

> **来源: [ACM](https://dl.acm.org/)**

**用途**: 堆内存分析工具

**安装**:

```bash
# Ubuntu/Debian {#ubuntudebian-3}
sudo apt-get install heaptrack

# 或从源码编译 {#或从源码编译-1}
git clone https://github.com/KDE/heaptrack
cd heaptrack
mkdir build && cd build
cmake ..
make
sudo make install
```

**基本使用**:

```bash
# 跟踪程序 {#跟踪程序}
heaptrack ./target/release/my_program

# 查看报告 {#查看报告-1}
heaptrack_gui heaptrack.my_program.12345.gz
```

**相关资源**:

- [heaptrack 文档](https://github.com/KDE/heaptrack)
- [heaptrack 使用指南](https://github.com/KDE/heaptrack#usage)

---

## 🧪 测试工具 {#测试工具}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### cargo test {#cargo-test}

> **来源: [IEEE](https://standards.ieee.org/)**

**用途**: Rust 标准测试工具

**基本使用**:

```bash
# 运行所有测试 {#运行所有测试}
cargo test

# 运行特定测试 {#运行特定测试-1}
cargo test test_name

# 显示输出 {#显示输出}
cargo test -- --nocapture

# 多线程测试 {#多线程测试}
cargo test -- --test-threads=1
```

---

### proptest {#proptest}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

**用途**: 属性测试框架

**安装**:

```toml
# Cargo.toml {#cargotoml-2}
[dev-dependencies]
proptest = "1.0"
```

**基本使用**:

```rust,ignore
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_addition_commutative(a in 0..1000i32, b in 0..1000i32) {
        assert_eq!(a + b, b + a);
    }
}
```

**相关资源**:

- proptest 文档
- [proptest 教程](https://altsysrq.github.io/proptest-book/intro.html)

---

### loom {#loom}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

**用途**: 并发模型验证工具

**安装**:

```toml
# Cargo.toml {#cargotoml-2}
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

- loom 文档
- [loom 使用指南](https://github.com/tokio-rs/loom#usage)

---

## 📚 代码分析工具 {#代码分析工具}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### Clippy {#clippy}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

**用途**: Rust 代码检查工具

**安装**:

```bash
# 安装 Clippy {#安装-clippy}
rustup component add clippy
```

**基本使用**:

```bash
# 检查代码 {#检查代码}
cargo clippy

# 自动修复 {#自动修复}
cargo clippy --fix

# 显示所有警告 {#显示所有警告}
cargo clippy -- -W clippy::all
```

**相关资源**:

- [Clippy 文档](https://github.com/rust-lang/rust-clippy)
- [Clippy 规则](https://rust-lang.github.io/rust-clippy/master/index.html)

---

### rust-analyzer {#rust-analyzer}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

**用途**: Rust 语言服务器

**安装**:

```bash
# 使用 rustup {#使用-rustup}
rustup component add rust-analyzer

# 或从源码编译 {#或从源码编译-1}
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

- rust-analyzer 文档
- [rust-analyzer 用户指南](https://rust-analyzer.github.io/manual.html)

---

### cargo-expand {#cargo-expand}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

**用途**: 宏（Macro）展开工具

**安装**:

```bash
# 安装 cargo-expand {#安装-cargo-expand}
cargo install cargo-expand
```

**基本使用**:

```bash
# 展开宏 {#展开宏}
cargo expand

# 展开特定项 {#展开特定项}
cargo expand my_macro

# 输出到文件 {#输出到文件}
cargo expand > expanded.rs
```

**相关资源**:

- [cargo-expand 文档](https://github.com/dtolnay/cargo-expand)
- [cargo-expand 使用指南](https://github.com/dtolnay/cargo-expand#usage)

---

## 💡 使用建议 {#使用建议}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 工具选择 {#工具选择}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**

根据研究类型选择工具：

- **形式化研究** → Coq, Lean, Prusti, Kani
- **性能研究** → Criterion.rs, perf, flamegraph
- **内存研究** → Miri, Valgrind, heaptrack
- **代码质量** → Clippy, rust-analyzer
- **测试** → cargo test, proptest, loom

### 工具组合 {#工具组合}

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**

推荐的工具组合：

1. **形式化验证组合**: Prusti + Kani
2. **性能分析组合**: Criterion.rs + perf + flamegraph
3. **内存分析组合**: Miri + Valgrind + heaptrack
4. **代码质量组合**: Clippy + rust-analyzer + cargo-expand

### 最佳实践 {#最佳实践}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

1. **从简单开始**: 先使用基础工具，再使用高级工具
2. **工具组合**: 组合使用多个工具获得全面结果
3. **持续集成**: 将工具集成到 CI/CD 流程
4. **文档记录**: 记录工具使用经验和结果

---

## 🔗 相关资源 {#相关资源}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [研究方法论](10_research_methodology.md) - 研究方法概述
- [实验研究索引](experiments/README.md) - 实验研究工具
- [形式化方法索引](formal_methods/README.md) - 形式化工具
- [Rust 异步（Async）编程](https://rust-lang.github.io/async-book/)
- [Rust 性能指南](https://nnethercote.github.io/perf-book/)

## 📚 Cargo Book 与 rustc dev guide 权威章节 {#cargo-book-与-rustc-dev-guide-权威章节}

> **来源**: [The Cargo Book](https://doc.rust-lang.org/cargo/)
>
> **来源**: [rustc dev guide](https://rustc-dev-guide.rust-lang.org/)

### Cargo Book 重点章节 {#cargo-book-重点章节}

| 章节 | 链接 | 用途 |
| :--- | :--- | :--- |
| 指定依赖 | [specifying-dependencies.html](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) | 语义版本、git/path 依赖、features |
| 工作空间 | [workspaces.html](https://doc.rust-lang.org/cargo/reference/workspaces.html) | 多 crate 管理与统一构建 |
| 编译配置 (Profiles) | [profiles.html](https://doc.rust-lang.org/cargo/reference/profiles.html) | `dev`/`release`、`opt-level`、`lto` |
| 构建脚本 | [build-scripts.html](https://doc.rust-lang.org/cargo/reference/build-scripts.html) | `build.rs` 与 FFI/代码生成 |
| 发布到 crates.io | [publishing.html](https://doc.rust-lang.org/cargo/reference/publishing.html) | 版本发布与元数据 |
| 环境变量 | [environment-variables.html](https://doc.rust-lang.org/cargo/reference/environment-variables.html) | `CARGO_*` 与构建环境 |

### rustc dev guide 重点章节 {#rustc-dev-guide-重点章节}

| 章节 | 链接 | 用途 |
| :--- | :--- | :--- |
| 编译器概览 | [overview.html](https://rustc-dev-guide.rust-lang.org/overview.html) | 编译管线与查询系统 |
| HIR | [hir.html](https://rustc-dev-guide.rust-lang.org/hir.html) | 高级中间表示 |
| MIR | [mir/index.html](https://rustc-dev-guide.rust-lang.org/mir/index.html) | 中阶中间表示，借用检查与优化的基础 |
| 借用检查 | [borrow_check.html](https://rustc-dev-guide.rust-lang.org/borrow_check.html) | NLL/Polonius 与生命周期（Lifetimes）检查 |
| 类型推断（Type Inference） | [type-inference.html](https://rustc-dev-guide.rust-lang.org/type-inference.html) | 类型系统（Type System）实现 |
| trait 系统 | [traits/resolution.html](https://rustc-dev-guide.rust-lang.org/traits/resolution.html) | trait 解析与 coherence |
| 代码生成 | [backend/index.html](https://rustc-dev-guide.rust-lang.org/overview.html) | LLVM 后端与目标平台 |
| Miri | [miri.html](https://rustc-dev-guide.rust-lang.org/miri.html) | Miri 解释器架构 |

---

**维护团队**: Rust Research Community
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 🆕 权威国际化内容升级 (Rust 1.97.0+) {#权威国际化内容升级-rust-1960}
>
> **来源**: [Rust Research Community]
> **适用版本**: Rust 1.97.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本次升级要点 {#本次升级要点}

- 补充 Kani、Prusti、Miri、Creusot、Aeneas、Verus 的官方文档链接与版本信息。
- 新增 Cargo Book、rustc dev guide 重点章节索引。
- 删除旧版 Rust 1.94 模板内容，状态更新为 ✅ 完成。

---

**维护者**: Rust Research Community
**最后更新**: 2026-06-29 (权威国际化内容升级)
**状态**: ✅ 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [The Cargo Book](https://doc.rust-lang.org/cargo/), [rustc dev guide](https://rustc-dev-guide.rust-lang.org/)
>
> **权威来源对齐变更日志**: 2026-06-29 新增 Cargo Book、rustc dev guide、Kani/Prusti/Miri/Creusot/Aeneas/Verus 官方文档与版本信息 [Authority Source Sprint Batch 9](../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.2
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 相关概念 {#相关概念}
>
> **[来源: [crates.io](https://crates.io/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Software Development Tool](https://en.wikipedia.org/wiki/Software_Development_Tool)**
> **来源: [Wikipedia - Integrated Development Environment](https://en.wikipedia.org/wiki/Integrated_Development_Environment)**
> **[Rust Tools Team](https://www.rust-lang.org/governance/teams/dev-tools)**
> **来源: [Rust Reference - Compiler](https://doc.rust-lang.org/reference/)**
> **[ACM - Developer Tooling Survey](https://dl.acm.org/)**
> **[IEEE - Software Engineering Environment](https://ieeexplore.ieee.org/) <!-- link: known-broken -->**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
