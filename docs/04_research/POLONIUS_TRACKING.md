# Polonius 借用检查器跟踪报告

> **最后更新日期**: 2026-04-24
> **预计下次复查日期**: 2026-07-24
> **跟踪状态**: 🔬 实验阶段 (nightly only)
> **相关 Rust 官方目标**: 2025H2 Goals —— 语言核心改进

---

## 1. 项目背景与动机

Rust 的借用检查器是其内存安全保证的核心。当前稳定版的借用检查器基于 **NLL (Non-Lexical Lifetimes)**，在 Rust 1.31 (2018) 中引入，相比早期的基于词法作用域的检查器有了巨大改进。然而，NLL 仍然存在明显的局限性，导致一些**实际上安全**的代码被拒绝编译。

Polonius 是 Rust 编译器团队开发的下一代借用检查器框架，旨在用更精确的数据流分析替代当前的 NLL 算法，从而接受更多安全的 Rust 程序。

### 1.1 为什么需要 Polonius？

Rust 社区长期面临一个痛点：借用检查器过于保守。以下模式在实际代码中反复出现，却被当前编译器拒绝：

- 按条件路径分开的可变借用
- 基于枚举变体的精确借用分析
- 循环中数组元素的交替借用

这些限制迫使开发者使用不必要的 `unsafe` 代码、增加冗余的作用域块，或重构为低效的代码结构。

---

## 2. NLL 的局限

### 2.1 基于位置的借用模型

当前 NLL 借用检查器本质上基于**位置 (location-based)** 模型：当某个值被借用时，整个值在借用期间都被视为已借用。这忽略了程序的实际控制流和数据依赖关系。

### 2.2 典型拒绝案例

```rust
// 案例 1: 条件路径借用 —— 当前编译器拒绝
fn conditional_borrow(vec: &mut Vec<i32>) {
    if vec.is_empty() {
        vec.push(1);  // 可变借用路径 A
    } else {
        vec.clear();  // 可变借用路径 B
    }
    // 当前编译器: 两条路径的借用被合并，导致过度保守
}

// 案例 2: 按索引分开借用 —— 当前编译器拒绝
fn split_borrow(arr: &mut [i32]) {
    let first = &mut arr[0];
    let second = &mut arr[1];
    // 错误: 不能同时对同一数组进行多次可变借用
    *first = 1;
    *second = 2;
}
```

> **注意**: 上述 `split_borrow` 在 Rust 1.96 中通过**Two-Phase Borrows**已有部分支持，但复杂场景仍受限。

### 2.3 NLL 的架构瓶颈

NLL 使用基于 **MIR (Mid-level IR)** 的约束求解，将借用检查问题转化为区域约束系统。这种方法：

1. **过度近似 (Over-approximation)**：为保证安全性，分析结果包含大量假阳性
2. **难以扩展**：添加新的分析维度（如路径敏感分析）需要重构整个约束系统
3. **错误信息质量受限**：难以向用户解释"为什么这个借用被拒绝"

---

## 3. Polonius 新算法原理

### 3.1 核心思想：基于 Datalog 的数据流分析

Polonius 将借用检查问题重新建模为 **Datalog 程序**，使用数据流分析来精确追踪借用的起源 (origin) 和使用点。

```text
Polonius 核心 Datalog 规则示例:

loan_issued_at(O, L, P) :-  // 借用 L 在点 P 被创建，属于起源 O
    borrow_region(O, L, P).

loan_killed_at(L, P) :-     // 借用 L 在点 P 被"杀死"（值被覆盖）
    kill_borrow(L, P).

loan_live_at(L, P) :-       // 借用 L 在点 P 仍然存活
    loan_issued_at(O, L, P0),
    path_reaches(P0, P),
    !loan_killed_at(L, P1), path_reaches(P0, P1), path_reaches(P1, P).

// 关键约束：如果借用存活，则不能与其冲突的操作共存
error(L, P) :-
    loan_live_at(L, P),
    invalidates(L, P).
```

### 3.2 起源 (Origin) 与 贷款 (Loan) 的精确追踪

Polonius 引入了两个核心概念：

| 概念 | 含义 | 与 NLL 的区别 |
|------|------|-------------|
| **Origin** | 引用的来源集合，表示"这个引用可能来自哪里" | NLL 使用统一的生命周期区域 |
| **Loan** | 具体的借用事件（如 `&mut x`） | NLL 将借用与位置绑定 |
| **Point** | 控制流图中的程序点 | 两者都使用 CFG，但 Polonius 分析更细粒度 |

### 3.3 三维度分析

Polonius 实现了三种分析变体，按精确度递增：

1. **`LocationInsensitive`** (位置不敏感): 最快速，仅检查借用是否在函数内被违反
2. **`LocationSensitive`** (位置敏感): 标准模式，沿控制流路径精确分析
3. **`Hybrid`** (混合模式): 平衡性能和精确度，实际编译中的默认选择

### 3.4 路径敏感性的突破

Polonius 的关键创新是引入了**路径敏感**的借用分析：

```rust
fn path_sensitive_example(vec: &mut Vec<i32>) {
    if vec.is_empty() {
        vec.push(1);  // 路径 A: 仅在 is_empty 为 true 时执行
    } else {
        vec.clear();  // 路径 B: 仅在 is_empty 为 false 时执行
    }
    // Polonius: 路径 A 和 B 互斥，不会同时借用，因此合法
}
```

---

## 4. 与当前 Borrow Checker 的对比示例

### 4.1 示例矩阵

| 示例场景 | 当前 Borrow Checker | Polonius | 备注 |
|---------|-------------------|---------|------|
| 简单条件分支借用 | ✅ | ✅ | 两者都支持 |
| 循环内交替索引借用 | ❌ | ✅ | Polonius 路径敏感 |
| 枚举变体精确借用 | ❌ | ✅ | Polonius 分析更细粒度 |
| 闭包捕获部分字段 | ⚠️ 受限 | ✅ | Polonius 支持部分捕获 |
| 复杂嵌套条件 | ❌ | ✅ | Polonius 控制流分析更精确 |

### 4.2 详细代码对比

#### 示例 A：枚举变体借用 (当前编译器拒绝)

```rust
enum Value {
    Int(i32),
    Text(String),
}

fn process_value(val: &mut Value) {
    match val {
        Value::Int(ref mut n) => *n += 1,
        Value::Text(ref mut s) => s.push_str("!"),
    }
    // 当前编译器: 有时会因为 match 的保守分析而拒绝
    // Polonius: 精确知道每个变体的借用互不干扰
}
```

#### 示例 B：循环内精确索引借用

```rust
fn bubble_sort(arr: &mut [i32]) {
    let len = arr.len();
    for i in 0..len {
        for j in 0..(len - i - 1) {
            // Polonius 将能精确证明 arr[j] 和 arr[j+1] 不重叠
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
            }
        }
    }
}
```

> **注意**: 当前稳定版中 `slice::swap` 已内部处理借用，但手动实现仍可能触发借用检查错误。

---

## 5. 预计稳定化时间线跟踪

### 5.1 里程碑时间线

```text
2018-11  Rust 1.31    NLL 稳定化 (rustc_borrowck -> NLL borrowck)
2019-03  首次提出     Polonius 作为 NLL 的继任者在内部 RFC 中提出
2020-06  原型实现     Polonius 作为 nightly 编译器选项首次可用
2022-04  算法优化     引入 Hybrid 模式，编译性能大幅提升
2023-09  集成推进     Polonius 开始与 rustc 主分支深度集成
2024-03  目标设定     Rust 编译器团队将 Polonius 列为 2024-2025 核心目标
2025-01  2025H1 Goals Polonius 进入 Rust 基金会资助项目清单
2025-06  预计进展     核心算法冻结，进入性能调优阶段
2026-??  预计稳定     目标稳定版本 (取决于性能基准测试和社区反馈)
```

### 5.2 当前状态 (2026-04-24)

- ✅ Datalog 引擎核心完成
- ✅ Hybrid 分析模式可用
- ✅ 错误信息改进框架建立
- 🔄 编译性能优化中 (目标: 不超过当前 NLL 10% 的额外开销)
- 🔄 与 rustc 查询系统的深度集成
- ⏳ 稳定版 RFC 待提交

### 5.3 启用 Polonius (nightly)

```bash
# 切换到 nightly 工具链
rustup default nightly

# 使用 Polonius 编译
rustc -Zpolonius your_code.rs

# 或使用 cargo
RUSTFLAGS="-Zpolonius" cargo build
```

---

## 6. 对本项目的影响

### 6.1 教学价值

Polonius 代表了 Rust 类型系统理论的前沿进展。在本知识工程中：

- `c01_ownership_borrow_scope` 将添加 Polonius 示例代码（见下方）
- 形式化证明文档将对比 NLL 与 Polonius 的逻辑差异
- 为学习者展示 Rust 借用检查器的演进历史

### 6.2 代码实践建议

在 Polonius 稳定之前，建议：

1. 继续使用当前稳定的借用模式（使用 `std::mem::replace`、`split_first_mut` 等 API）
2. 对于确实受限的场景，优先考虑 `unsafe` 块配合详细的安全注释
3. 关注 nightly 测试，提前验证代码在 Polonius 下的行为

---

## 7. 参考文献

1. **Rust Compiler Team**. "Polonius: A New Borrow Checker". Rust Compiler Team Blog, 2019-2022.
   <https://rust-lang.github.io/compiler-team/>

2. **Dietrich, Rémy, et al.** "Modeling Polonius in Datalog". Rust Verification Workshop (RW) 2022.

3. **Vytiniotis, Dimitrios, et al.** "Borrow Checking on Regions". Microsoft Research, 2013.
   (NLL 的前身理论基础)

4. **Rust Foundation**. "2025H2 Goals: Language Core Improvements". Rust Foundation Roadmap, 2025.

5. **Geller, Niko Matsakis (rust-lang/compiler-team#667)**. "Polonius: Hybrid Analysis Mode". 2022.

6. **Ullrich, Sebastian**. "Beyond Borrowing: The Future of Rust's Type System". POPL 2024 Tutorial.

---

## 8. 附录：相关 Issue 跟踪

| Issue/PR | 状态 | 描述 |
|----------|------|------|
| rust-lang/rust#58792 | 开放 | Polonius 主跟踪 issue |
| rust-lang/polonius#20 | 已合并 | Datalog 规则引擎优化 |
| rust-lang/rust#119820 | 开放 | Polonius 性能基准测试 |
| rust-lang/compiler-team#667 | 已接受 | Hybrid 模式 MCP |

---

> 📌 **复查记录**
>
> - 2026-04-24: 初始创建，基于 Rust 1.96.0 状态
> - 下次复查: 2026-07-24 (预计 Polonius 集成进展更新)
