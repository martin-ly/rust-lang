# Creusot 深度解析：预言变量与Rust验证

> **权威来源**: Denis, Jourdan, Marché (2022). Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM
> **项目地址**: <https://github.com/creusot-rs/creusot>
> **更新日期**: 2025年 (兼容Rust 1.94)

## 目录

- [Creusot 深度解析：预言变量与Rust验证](#creusot-深度解析预言变量与rust验证)
  - [目录](#目录)
  - [1. Creusot 概述](#1-creusot-概述)
    - [1.1 项目背景](#11-项目背景)
    - [1.2 架构概览](#12-架构概览)
  - [2. 预言变量：核心创新](#2-预言变量核心创新)
    - [2.1 什么是预言变量？](#21-什么是预言变量)
    - [2.2 为什么需要预言变量？](#22-为什么需要预言变量)
    - [2.3 形式化定义](#23-形式化定义)
  - [3. 规格语言 Pearlite](#3-规格语言-pearlite)
    - [3.1 基本语法](#31-基本语法)
    - [3.2 示例：基本函数规范](#32-示例基本函数规范)
    - [3.3 逻辑函数与谓词](#33-逻辑函数与谓词)
  - [4. 高级特性](#4-高级特性)
    - [4.1 Trait 与规范](#41-trait-与规范)
    - [4.2 幽灵状态](#42-幽灵状态)
    - [4.3 向量与序列](#43-向量与序列)
  - [5. 验证流程实战](#5-验证流程实战)
    - [5.1 完整示例：二分查找](#51-完整示例二分查找)
    - [5.2 命令行验证](#52-命令行验证)
    - [5.3 Rust 1.94 安装指南](#53-rust-194-安装指南)
  - [6. 与其他工具对比](#6-与其他工具对比)
  - [7. 限制与未来工作](#7-限制与未来工作)
    - [7.1 当前限制](#71-当前限制)
    - [7.2 Rust 1.94 兼容性说明](#72-rust-194-兼容性说明)
    - [7.3 未来方向](#73-未来方向)
  - [参考文献](#参考文献)

## 1. Creusot 概述

### 1.1 项目背景

Creusot 是由巴黎萨克雷大学 (Université Paris-Saclay) 和 INRIA 开发的一款 Rust 演绎验证工具。

```text
核心特点:
- 利用 Rust 所有权系统简化内存建模
- 使用预言变量 (Prophecy Variables) 处理可变借用
- 基于 Why3 平台，支持多种自动证明器
- 与 Rust trait 系统集成
- 持续更新以支持新Rust版本
```

### 1.2 架构概览

```text
Creusot 架构:

Rust 源码 + 规格注释
      ↓
  Creusot 前端
  - 解析 MIR
  - 提取规范
  - 所有权分析
      ↓
MLCFG (中间表示)
  - 简化控制流
  - 预言变量编码
      ↓
Why3ML 代码
  - 标准 Why3 格式
      ↓
Why3 平台
  - VC 生成
  - 证明管理
      ↓
SMT 求解器 (Alt-Ergo, Z3, CVC5)
      ↓
  验证结果
```

## 2. 预言变量：核心创新

### 2.1 什么是预言变量？

预言变量 (Prophecy Variables) 是时序逻辑中的概念，用于预测未来值。

```text
直观理解:

可变借用 &mut T 可以看作:
- 当前值 (Current Value)
- 未来值 (Future Value) - 借用结束时的值

预言变量记录这个"未来值"。

示例:
let x = &mut v;  // x: &mut i32
*x = 5;          // 当前 *x = 5
// ... 其他操作 ...
// x 结束，v 的值为预言的 "未来值"
```

### 2.2 为什么需要预言变量？

```rust
// 传统方法的问题：难以处理可变借用
fn swap(x: &mut i32, y: &mut i32) {
    let tmp = *x;
    *x = *y;
    *y = tmp;
}

// 后置条件: *x == old(*y) && *y == old(*x)
// 问题: old() 只能捕获一个时间点的值

// 预言变量解决方案:
// - 创建预言变量 p_x 表示 x 借用的未来最终值
// - 创建预言变量 p_y 表示 y 借用的未来最终值
// - 规范: *x == p_x, *y == p_y
// - 交换后: p_x == old(*y), p_y == old(*x)
```

### 2.3 形式化定义

```text
预言变量的形式化:

语法扩展:
e ::= ... | prophesy(v)  // 创建关于v的预言

语义:
prophesy(v) 创建一个预言变量 π
当与 v 关联的借用结束时，π 等于 v 的值

在分离逻辑中的表示:
&mut^π v ≡ 借用 v，预言其最终值为 π

推理规则:
{P} create_mut_borrow(x) {∃π. x: &mut^π * P}
{Q(π)} end_mut_borrow(&mut^π x) {Q(v) * v = π}
```

## 3. 规格语言 Pearlite

### 3.1 基本语法

```rust
// Pearlite: Creusot 的规格语言

// 前置条件
#[requires(...)]

// 后置条件
#[ensures(...)]

// 循环不变量
#[invariant(...)]

// 变体 (用于终止证明)
#[variant(...)]

// 逻辑函数
#[logic]
#[predicate]
```

### 3.2 示例：基本函数规范

```rust
use creusot_contracts::*;

// 简单函数规范
#[requires(x >= 0)]
#[ensures(result >= x)]
fn increment(x: u32) -> u32 {
    x + 1
}

// 使用 old() 引用旧值
#[ensures(*x == old(*y) && *y == old(*x))]
fn swap(x: &mut u32, y: &mut u32) {
    let tmp = *x;
    *x = *y;
    *y = tmp;
}

// 模式匹配结果
#[ensures(match result {
    Some(r) => r >= *x && r >= *y,
    None => false,
})]
fn max(x: &u32, y: &u32) -> Option<u32> {
    if *x >= *y { Some(*x) } else { Some(*y) }
}
```

### 3.3 逻辑函数与谓词

```rust
// 逻辑函数：纯函数，用于规范
#[logic]
fn factorial(n: u64) -> u64 {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}

// 谓词：返回 bool 的逻辑函数
#[predicate]
fn is_sorted<T: OrdLogic>(s: Seq<T>) -> bool {
    s.len() <= 1 ||
    (s[0] <= s[1] && is_sorted(s.skip(1)))
}

// 在规范中使用
#[requires(is_sorted(arr))]
#[ensures(result ==> arr.contains(needle))]
fn binary_search(arr: &[u32], needle: u32) -> bool {
    // ...
}
```

## 4. 高级特性

### 4.1 Trait 与规范

```rust
// 为 trait 添加规范
#[trait]
pub trait MyTrait {
    #[logic]
    fn invariant(&self) -> bool;

    #[requires(self.invariant())]
    #[ensures(self.invariant())]
    fn method(&mut self);
}

// 实现时继承规范
impl MyTrait for MyStruct {
    #[predicate]
    fn invariant(&self) -> bool {
        self.value >= 0
    }

    fn method(&mut self) {
        self.value += 1;
    }
}
```

### 4.2 幽灵状态

```rust
// 幽灵状态：验证时使用，运行时消除
use creusot_contracts::ghost_ptr::*;

#[requires(in_ghost(v))]
#[ensures(result == v.len())]
fn ghost_length<T>(v: GhostVec<T>) -> usize {
    v.len()
}

// 幽灵指针
#[ensures(^p == old(*p) + 1)]
fn increment_ghost(p: GhostPtrMut<i32>) {
    *p = *p + 1;
}
```

### 4.3 向量与序列

```rust
use creusot_contracts::logic::Seq;

// Seq<T> 是逻辑层面的序列类型
#[ensures(result.len() == n)]
#[ensures(forall<i: Int> 0 <= i && i < result.len() ==> result[i] == init)]
fn create_vec<T: Clone>(n: usize, init: T) -> Vec<T> {
    vec![init; n]
}

// 序列操作
#[logic]
fn reverse<T>(s: Seq<T>) -> Seq<T> {
    s.reverse()
}

#[ensures(result == reverse(old(seq)))]
fn reverse_vec<T>(seq: &mut Vec<T>) {
    seq.reverse();
}
```

## 5. 验证流程实战

### 5.1 完整示例：二分查找

```rust
use creusot_contracts::*;

// 先序谓词
#[predicate]
fn is_sorted(s: Seq<u32>) -> bool {
    forall<i: Int, j: Int> 0 <= i && i < j && j < s.len() ==> s[i] <= s[j]
}

// 二分查找规范
#[requires(is_sorted(v))]
#[ensures(forall<i: Int> 0 <= i && i < v.len() && v[i] == elem ==> result <= i)]
#[ensures(result < v.len())]
#[ensures(v[result] <= elem)]
#[ensures(result > 0 ==> v[result - 1] < elem)]
fn lower_bound(v: &[u32], elem: u32) -> usize {
    let mut lo = 0;
    let mut hi = v.len();

    #[invariant(0 <= lo && lo <= hi && hi <= v.len())]
    #[invariant(forall<i: Int> 0 <= i && i < lo ==> v[i] < elem)]
    #[invariant(forall<i: Int> hi <= i && i < v.len() ==> elem <= v[i])]
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if v[mid] < elem {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}
```

### 5.2 命令行验证

```bash
# 安装 Creusot
cargo install cargo-creusot --locked

# 验证单个文件
cargo creusot -- --why3

# 使用 Why3 IDE
cargo creusot -- --why3ide

# 批处理验证
cargo creusot -- --proof-checker
```

### 5.3 Rust 1.94 安装指南

```bash
# 检查当前Rust版本
rustc --version
# 应显示 1.94.0 或更高

# 安装/更新 Creusot (Rust 1.94)
# 注意: Creusot 可能需要特定工具链
cargo install cargo-creusot --locked

# 如果需要nightly工具链
rustup toolchain install nightly-2025-01-01
rustup default nightly-2025-01-01
cargo install cargo-creusot --locked

# 验证安装
cargo creusot --version

# 项目配置 Cargo.toml
[dependencies]
creusot-contracts = "0.4"

# 验证项目
cargo creusot

# 使用Why3验证
why3 ide output.mlcfg
```

## 6. 与其他工具对比

| 特性 | Creusot | Prusti | RustHorn | Aeneas | Verus | Kani |
|------|---------|--------|----------|--------|-------|------|
| 内存模型 | 预言变量 | 分离逻辑 | CHC | 函数式提取 | SMT数组 | CBMC |
| 自动化 | 高 | 高 | 完全自动 | 中等 | 高 | 全自动 |
| 可变借用 | 预言变量 | 分数权限 | 预言变量 | 函数式 | 资源代数 | 符号执行 |
| Trait支持 | 优秀 | 良好 | 有限 | 良好 | 优秀 | 良好 |
| 后端 | Why3 | Viper | CHC求解器 | Lean | Z3 | CBMC |
| Rust 1.94 | ⚠️需验证 | ⚠️维护中 | ⚠️实验性 | ✅支持 | ✅推荐 | ✅官方支持 |

## 7. 限制与未来工作

### 7.1 当前限制

```text
1. Unsafe Rust 支持有限
   - 主要支持 Safe Rust
   - Unsafe 代码需要手动验证

2. 标准库覆盖
   - 常用类型有规范
   - 部分类型尚未覆盖

3. 并发验证
   - 主要关注单线程
   - 并发支持正在开发

4. Rust版本兼容性
   - 依赖MIR内部表示
   - 需要跟踪Rust编译器更新
```

### 7.2 Rust 1.94 兼容性说明

**当前状态**:

- Creusot 正在积极开发中，以支持最新的 Rust 版本
- Rust 1.94 的兼容性取决于 creusot-contracts 和 cargo-creusot 的最新版本

**推荐做法**:

```bash
# 1. 检查最新版本
 cargo search cargo-creusot

# 2. 如果Rust 1.94遇到问题，尝试使用nightly
 rustup toolchain install nightly
cargo +nightly install cargo-creusot --locked

# 3. 使用 rust-toolchain.toml 锁定版本
```

**替代方案** (如果需要立即使用):

- **Verus**: 对 Rust 1.94 支持更好，适合新项目
- **Kani**: Amazon官方维护，与稳定版同步

### 7.3 未来方向

- 更好的不安全代码支持
- 并发程序验证
- 改进的错误报告
- 标准库规范完善
- 更好的 Rust 1.94+ 兼容性

---

## 参考文献

1. Denis, X., Jourdan, J.-H., & Marché, C. (2022). Creusot: A Foundry for the Deductive Verification of Rust Programs. *ICFEM*.
2. Abadi, M., & Lamport, L. (1991). The Existence of Refinement Mappings. *Theoretical Computer Science*.
3. Filliâtre, J.-C., & Paskevich, A. (2013). Why3 — Where Programs Meet Provers. *ESOP*.
4. Rust Formal Methods Interest Group. (2025). Rust Verification Tools Status. <https://rust-formal-methods.github.io/>
5. Creusot GitHub Repository. <https://github.com/creusot-rs/creusot>
