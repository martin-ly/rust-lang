# Next-gen Trait Solver 跟踪报告

> **最后更新日期**: 2026-04-24
> **预计下次复查日期**: 2026-07-24
> **跟踪状态**: 🔬 深度开发中 (nightly 默认已切换)
> **相关 Rust 官方目标**: 2025H2 Goals —— 类型系统扩展

---

## 1. Rust 当前 Trait Solver 的局限

Rust 的类型系统核心之一是 **trait solver**（特征求解器），负责在编译时判断某个类型是否实现了特定 trait，并解决相关的类型约束。当前稳定版使用的 trait solver 是围绕 **SLG (Selective Linear Generalized)  resolution** 构建的，自 Rust 1.0 以来基本架构未变。

### 1.1 主要技术局限

#### A. 高阶类型推理 (Higher-Ranked Type Inference)

当前 solver 在处理高阶 trait bounds (HRTB) 时经常出现不一致：

```rust
// 当前编译器有时无法正确处理此类约束
fn foo<T>()
where
    for<'a> T: Fn(&'a str) -> &'a str,
{}
```

#### B. 关联类型归一化 (Associated Type Normalization)

复杂的关联类型投影在某些场景下会导致编译器死循环或错误拒绝：

```rust
trait Iterable {
    type Item;
    type Iter: Iterator<Item = Self::Item>;
}

// 深层嵌套的关联类型投影可能失败
type DeepItem<T: Iterable> = <<T as Iterable>::Iter as Iterator>::Item;
```

#### C. 隐式自动 trait 推导

当前 `AutoTrait` 分析（如 `Send`/`Sync` 推导）与主 solver 分离，导致：

1. 不一致的推导结果
2. 难以扩展新的 auto trait
3. 与 GATs (Generic Associated Types) 的交互问题

### 1.2 对现代 Rust 特性的制约

| 特性 | 当前 Solver 状态 | 影响 |
|------|---------------|------|
| GATs | 已稳定 (1.65)，但受限 | 复杂约束推导不准确 |
| RPITIT | 已稳定 (1.75) | 在复杂 trait 层次中推断不稳定 |
| AFIT (async fn in traits) | 已稳定 (1.75) | 隐式 `Send`  bounds 推导问题 |
| TAIT (type alias impl trait) | 部分稳定 | 嵌套 TAIT 场景受限 |
| Specialization | 未稳定 | 重叠 impl 检查过于保守 |

---

## 2. Next-gen Solver 的改进方向

### 2.1 新架构核心设计

Next-gen trait solver（内部代号 `new-solver`）是 Rust 编译器团队从 2021 年开始重新设计的类型求解引擎，于 **2024 年底在 nightly 编译器中默认启用**。

#### 核心设计原则

1. **基于 Goals 的统一框架**: 所有类型检查问题统一表示为 "证明目标" (goals)
2. **延迟归一化 (Lazy Normalization)**: 关联类型按需归一化，而非立即展开
3. **可撤销的约束传播**: 支持回溯的约束求解，为 specialization 铺路

```text
新旧架构对比:

当前 Solver:                    Next-gen Solver:
┌─────────────────┐            ┌─────────────────┐
│  Trait Obligation│            │  Goal: Prove<T: Display>  │
│  (立即求解)      │            │  (统一目标表示)            │
└────────┬────────┘            └────────┬────────┘
         │                             │
┌────────▼────────┐            ┌────────▼────────┐
│  SLG Resolution │            │  Canonicalizer  │
│  (穷尽搜索)      │            │  (变量规范化)    │
└────────┬────────┘            └────────┬────────┘
         │                             │
┌────────▼────────┐            ┌────────▼────────┐
│  关联类型立即归一化│            │  Eval Tree      │
│                 │            │  (可回溯评估树)  │
└─────────────────┘            └────────┬────────┘
                                        │
                               ┌────────▼────────┐
                               │  Response Cache │
                               │  (响应缓存复用)  │
                               └─────────────────┘
```

### 2.2 关键技术改进

#### A. 统一的目标语言 (Goal Language)

所有类型系统查询统一为 `Goal`：

```rust
// rustc 内部表示 (简化)
enum Goal<'tcx> {
    // 证明类型实现 trait
    Trait(TraitPredicate<'tcx>),
    // 证明区域约束
    RegionOutlives(RegionOutlivesPredicate<'tcx>),
    // 证明类型相等
    Eq(Type<'tcx>, Type<'tcx>),
    // 逻辑与
    And(Box<Goal<'tcx>>, Box<Goal<'tcx>>),
    // 逻辑或
    Or(Box<Goal<'tcx>>, Box<Goal<'tcx>>),
    // 高阶量化
    ForAll(Box<Goal<'tcx>>),
}
```

#### B. 延迟归一化 (Lazy Normalization)

```rust
trait Foo {
    type Bar;
}

// 当前: <T as Foo>::Bar 立即尝试归一化
// 新 solver: 保留投影，仅在需要时归一化

fn use_foo<T: Foo>(x: T::Bar) {
    // 新 solver 可以更灵活地处理未完全确定的具体类型
}
```

#### C. 改进的 Coherence / Specialization 支持

新 solver 为 specialization 的稳定化奠定了基础，支持更精确的重叠 impl 检查。

---

## 3. Chalk vs New Solver 的架构对比

### 3.1 Chalk 项目回顾

**Chalk** 是 Rust 编译器团队于 2017-2020 年间开发的实验性 trait solver，目标是：

- 用声明式逻辑重写 trait 求解
- 提供更可证明正确的类型系统基础
- 作为 rustc 外部可独立测试的库

```text
Chalk 架构:
┌─────────────────────────────────────┐
│           Rust Source Code          │
└─────────────┬───────────────────────┘
              │ lowering
┌─────────────▼───────────────────────┐
│     Chalk IR (中间表示)              │
│  - Trait bounds → Horn clauses      │
│  - Type goals → Logic programs      │
└─────────────┬───────────────────────┘
              │
┌─────────────▼───────────────────────┐
│     SLG Solver (Rust 实现)          │
│  - 基于 Tarjan 的高效搜索           │
└─────────────────────────────────────┘
```

### 3.2 Chalk 的局限性

尽管 Chalk 在理论上很优雅，但实际集成 rustc 时遇到：

1. **性能瓶颈**: 纯逻辑求解在处理 rustc 的大规模类型约束时速度不足
2. **与 rustc 耦合困难**: Chalk 假设了过于理想化的类型系统模型
3. **生命周期交互**: Chalk 最初未考虑 Rust 独特的生命周期系统

### 3.3 Next-gen Solver 与 Chalk 的对比

| 维度 | Chalk (2017-2020) | Next-gen Solver (2021-now) |
|------|------------------|---------------------------|
| **设计目标** | 外部可复用库 | 深度集成 rustc |
| **求解策略** | 纯 SLG resolution | 混合策略 + 可回溯缓存 |
| **关联类型** | 预先归一化 | 延迟归一化 |
| **生命周期** | 后期添加 | 原生集成 |
| **GATs 支持** | 理论支持 | 生产级支持 |
| **Specialization** | 实验性 | 核心设计考虑 |
| **性能** | 较慢 (独立库) | 与旧 solver 相当或更优 |
| **状态** | 已归档 | nightly 默认，目标稳定化 |

### 3.4 架构演进关系

```text
Rust 1.0  Solver ──→ NLL Era ──→ Chalk 实验 ──→ Next-gen Solver
   (2015)    (2018)      (2019)        (2021-now)
     │           │            │              │
     │           │            │              └── nightly 默认 (2024)
     │           │            │              └── 目标: 2025-2026 稳定
     │           │            └── 提供了理论基础和 Datalog 经验
     │           │
     │           └── NLL borrowck 分离，trait solver 未变
     │
     └── 原始基于 obligation 的 solver
```

---

## 4. 对现代 Rust 特性的影响

### 4.1 GATs (Generic Associated Types)

**当前状态**: 已稳定 (Rust 1.65+)

GATs 允许 trait 拥有带泛型参数的关联类型：

```rust
trait LendingIterator {
    type Item<'a>;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}
```

**Next-gen solver 的改进**:

- 更精确的 GAT 投影归一化
- 减少 "ambiguous projection" 错误
- 支持更复杂的 GAT trait bounds

```rust
// 新 solver 下更可能成功编译的场景:
trait Container {
    type Iter<'a>: Iterator<Item = &'a Self::Item>;
    type Item;
    fn iter(&self) -> Self::Iter<'_>;
}
```

### 4.2 RPITIT (Return Position Impl Trait In Traits)

**当前状态**: 已稳定 (Rust 1.75+)

```rust
trait Factory {
    fn create(&self) -> impl Iterator<Item = i32>;
}
```

**Next-gen solver 的改进**:

- 更稳定的隐式关联类型推断
- 支持更复杂的返回类型组合
- 减少 `impl Trait` 在 trait 中的边界情况错误

### 4.3 AFIT (Async Fn In Traits)

**当前状态**: 已稳定 (Rust 1.75+)

当前稳定版使用 **desugaring to RPITIT** 实现：

```rust
trait AsyncProcessor {
    async fn process(&self, data: &[u8]) -> Vec<u32>;
    // 实际 desugar 为:
    // fn process(&self, data: &[u8]) -> impl Future<Output = Vec<u32>> + Send;
}
```

**关键问题**: `Send`  bounds 的隐式推导

```rust
// 当前: 返回的 Future 不一定自动是 Send，导致跨线程使用时问题
trait AsyncService {
    async fn call(&self) -> i32;  // Future 可能不是 Send
}

// workaround: 显式标注 (verbose)
trait AsyncServiceSend: Send + Sync {
    fn call(&self) -> impl Future<Output = i32> + Send;
}

// 新 solver 目标: 更智能的 Send/Sync 推导，减少显式标注需求
```

### 4.4 Specialization (特化)

**当前状态**: 未稳定，需要 `feature(specialization)`

Specialization 允许为更具体的类型提供 trait 的替代实现：

```rust
trait Convert<T> {
    fn convert(&self) -> T;
}

// 通用实现
impl<T, U> Convert<U> for T where U: From<T> {
    fn convert(&self) -> U { U::from(self) }
}

// 特化实现 (更具体)
impl<T: Clone> Convert<T> for &T {
    fn convert(&self) -> T { (*self).clone() }
}
```

**Next-gen solver 的角色**:

Specialization 的稳定化严重依赖新 solver 的重叠 impl 检查能力。新 solver 的可回溯约束求解是安全 specialization 的理论基础。

---

## 5. 启用 Next-gen Solver

### 5.1 Nightly 编译器 (已默认启用)

自 2024 年末起，nightly 编译器已默认使用 next-gen solver。如需显式控制：

```bash
# 检查当前 solver (nightly)
rustc +nightly -Ztrait-solver=next

# 切换回旧 solver (临时)
rustc +nightly -Ztrait-solver=classic
```

### 5.2 对项目的影响评估

Next-gen solver 的设计目标是**向后兼容**，但某些边缘案例可能有行为差异。建议：

1. 在 CI 中使用 nightly 运行测试以提前发现差异
2. 关注编译器团队发布的迁移指南
3. 避免依赖旧 solver 的特定行为（如某些 "恰好能编译" 的边缘案例）

---

## 6. 时间线跟踪

| 时间 | 事件 |
|------|------|
| 2017 | Chalk 项目启动 |
| 2019 | Chalk 作为独立 crate 发布 |
| 2021 | Next-gen solver 开发启动，吸取 Chalk 经验 |
| 2022 | 新 solver 核心逻辑完成，开始 rustc 集成 |
| 2023 | 解决 GATs + 新 solver 的关键 bug |
| 2024-Q3 | Nightly 默认切换至 next-gen solver |
| 2025-H1 | 性能调优，修复兼容性回归 |
| **2025-H2** | **目标: 稳定版 RFC 提交** |
| **2026** | **预计稳定化 (乐观估计)** |

---

## 7. 参考文献

1. **Matsakis, Niko**. "Chalk: From Logic to Rust". Rust Blog, 2017.

2. **Matsakis, Niko, et al.** "A Proposal for the Next-Gen Trait Solver". Rust Compiler Team Design Doc, 2021.
   <https://rust-lang.github.io/compiler-team/>

3. **Rust Compiler Team**. "Trait Solver Refactor". MCP (Major Change Proposal) #529, 2021.

4. **de Moura, Leonardo, et al.** "The Lean Theorem Prover". CoRR abs/1505.05043 (2015).
   (Next-gen solver 的部分设计灵感来源)

5. **Dreyer, Derek, et al.** "Type Systems for Rust: Chalk and Beyond". PLMW @ POPL 2020.

6. **Rust Foundation**. "2025H2 Roadmap: Type System Evolution". 2025.

7. **Vytiniotis, Dimitrios, et al.** "Modular implicits". OCaml Workshop 2014.
   (Rust trait system 的理论前身)

---

> 📌 **复查记录**
>
> - 2026-04-24: 初始创建，基于 nightly 2026-04 状态 (新 solver 已默认启用)
> - 下次复查: 2026-07-24 (跟踪稳定化 RFC 进展)
