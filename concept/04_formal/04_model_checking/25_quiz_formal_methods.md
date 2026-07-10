> **内容分级**: [专家级]

# 测验：形式化方法概念（L4 试点扩展）
>
> **EN**: Formal Methods
> **Summary**: Quiz Formal Methods. Core Rust concept.
> ``` P * Q ``` <details> <summary>💡 点击展开答案与解析</summary> **答案**：`P * Q` 表示memory堆可以**分割**为两个不相交的部分，一部分满足 `P`，另一部分满足 `Q`。
> **formal methods定义（教学类比）**： ``` h ⊨ P * Q   ⟺   ∃h₁, h₂.  h = h₁ ⊎ h₂  ∧  h₁ ⊨ P  ∧  h₂ ⊨ Q ``` - `h` 是整个memory堆（heap） - `h₁ ⊎ h₂` 表示 `h₁` 和 `h₂` 的**不相交并集**（disjoint union） - `h₁` 和 `h₂` 没有重叠的memory地址 **
> **受众**: [研究者]
> **内容分级**: [专家级]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` 权威页。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
>
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [RustBelt](https://plv.mpi-sws.org/rustbelt/) · [验证工具链](05_verification_toolchain.md) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **后置概念**: N/A
---

> **来源**:
> [RustBelt Paper](https://plv.mpi-sws.org/rustbelt/popl18/) ·
> [Iris Project](https://iris-project.org/) ·
> [Kani Documentation](https://model-checking.github.io/kani/) ·
> [Creusot](https://github.com/creusot-rs/creusot) ·
> [Verus](https://github.com/verus-lang/verus)
>
> **前置概念**: [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md)
> [Linear Logic](../01_ownership_logic/01_linear_logic.md) ·
> [RustBelt](../02_separation_logic/04_rustbelt.md) ·
> [Separation Logic](../02_separation_logic/11_separation_logic.md) ·
> [Verification Toolchain](05_verification_toolchain.md)

---

> **⚠️ 声明**: 本测验使用形式化符号辅助直觉理解，所呈现的"定理/引理/推论"为**教学类比**，非经机器验证的严格数学证明。
> 如需严格形式化验证，请参考 Verus、Kani、Coq。
>
> **Bloom 层级**: 分析 → 评价
> **定位**: L4 嵌入式互动测验——验证形式化方法核心概念（分离逻辑、RustBelt、类型安全、验证工具链）的概念掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

---

## 认知路径

> **认知路径**: 本节从 "测验" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 测验 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 测验 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与测验的适用边界。
5. **迁移应用**: 将 测验 与前置/后置概念链接，形成跨层知识网络。

---

> **过渡**: 从 测验 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 测验 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 测验 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: 测验 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 测验 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 测验 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

---

## 反命题决策树

> **反命题 1**: "测验 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 测验 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 测验 规则被违反的直接信号。

> **反命题 3**: "其他语言对 测验 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 测验 具有语言特有的形态。

## 一、分离逻辑与所有权

### Q1. 分离逻辑（Separation Logic）中，`*`（分离合取）运算符的含义是什么？

```text
P * Q
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：`P * Q` 表示内存堆可以**分割**为两个不相交的部分，一部分满足 `P`，另一部分满足 `Q`。

**形式化定义（教学类比）**：

```text
h ⊨ P * Q   ⟺   ∃h₁, h₂.  h = h₁ ⊎ h₂  ∧  h₁ ⊨ P  ∧  h₂ ⊨ Q
```

- `h` 是整个内存堆（heap）
- `h₁ ⊎ h₂` 表示 `h₁` 和 `h₂` 的**不相交并集**（disjoint union）
- `h₁` 和 `h₂` 没有重叠的内存地址

**与 Rust 所有权（Ownership）的对应**：

| 分离逻辑 | Rust |
|:---|:---|
| `x ↦ v`（单点堆） | `let x = v;`（所有权） |
| `P * Q` | 两个不相交的所有权资源 |
| 框架规则（Frame Rule） | 借用（Borrowing）检查器：验证局部操作时不影响无关资源 |

**示例**：

```text
(x ↦ 5) * (y ↦ 10)   // x 和 y 指向不相交的内存
```

这对应 Rust 中的：

```rust
let x = 5;
let y = 10; // x 和 y 是独立的资源
```

**知识点**：分离逻辑的 `*` 是 Rust 所有权系统"资源独占"特性的数学根基。框架规则是局部推理（local reasoning）的基础。[→ 分离逻辑详解](../02_separation_logic/11_separation_logic.md)

</details>

---

### Q2. RustBelt 的核心贡献是什么？它如何证明 Rust 的类型安全？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：RustBelt（POPL 2018）是首个对 Rust 核心语言进行**机器验证**的类型安全证明。

**核心贡献**：

| 贡献 | 说明 |
|:---|:---|
| **λRust** | 定义了 Rust 核心语言的简化形式化模型 |
| **Iris 分离逻辑** | 使用高阶分离逻辑（higher-order separation logic）表达所有权和生命周期（Lifetimes） |
| **类型安全定理** | 证明：well-typed 的 λRust 程序不会出现数据竞争、use-after-free、悬垂指针 |
| **验证标准库** | 为 `Vec`、`Box`、`Rc`、`Arc` 等核心类型的 `unsafe` 实现提供形式化规约 |

**证明策略**：

```
Rust 源代码
    ↓ （提取）
λRust 形式化模型
    ↓ （Iris 编码）
分离逻辑断言
    ↓ （Coq 证明）
类型安全定理 ✓
```

**关键洞察**：Rust 的 `unsafe` 块不是"关闭检查器"，而是将**证明责任**从编译器转移到程序员。RustBelt 为 `unsafe` 代码提供了形式化的"安全契约"模板。

**知识点**：RustBelt 证明了 Rust 的安全保证有坚实的数学基础——不是工程经验，而是可验证的定理。[→ RustBelt 详解](../02_separation_logic/04_rustbelt.md)

</details>

---

## 二、类型安全与定理

### Q3. 以下"定理"（教学类比）描述的是什么性质？

```
定理（Progress）：若 ⊢ e : T，则 e 是值，或存在 e' 使得 e ⟶ e'。

定理（Preservation）：若 ⊢ e : T 且 e ⟶ e'，则 ⊢ e' : T。
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：这是**类型安全性（Type Safety）**的两个经典子性质。

**解释**：

| 定理 | 通俗表述 | Rust 对应 |
|:---|:---|:---|
| **Progress**（进展性） | 类型正确的程序不会"卡住"（stuck） |  well-typed 的 Rust 代码不会触发未定义行为（UB） |
| **Preservation**（保持性） | 求值保持类型 | 表达式求值后类型不变 |

**结合含义**：

类型安全 = Progress + Preservation

即：类型正确的程序可以一直执行下去（不会 stuck），且执行过程中始终保持类型正确。

**Rust 的增强**：Rust 的类型系统（Type System）还保证：

- **内存安全（Memory Safety）**：没有 use-after-free、double-free、悬垂指针
- **数据竞争自由**：`Send`/`Sync` 在编译期阻止数据竞争
- **初始化安全**：不能使用未初始化变量

**对比其他语言**：

| 语言 | 类型安全保证 |
|:---|:---|
| C/C++ | 无（类型系统（Type System）不保证内存安全（Memory Safety）） |
| Java | 类型安全 + 内存安全（GC） |
| Rust | 类型安全 + 内存安全（Memory Safety） + 数据竞争自由（无 GC） |

**知识点**：Progress & Preservation 是类型理论的"圣杯"。Rust 通过所有权系统将这些经典定理扩展到了内存安全（Memory Safety）和并发安全（Concurrency Safety）领域。[→ 类型语义详解](../00_type_theory/21_type_semantics.md)

</details>

---

### Q4. 线性逻辑（Linear Logic）中，`⊗`（张量积）和 `⅋`（par）与 Rust 类型系统的对应关系是什么？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 线性逻辑 | Rust 概念 | 说明 |
|:---|:---|:---|
| `A ⊗ B` | `(A, B)` — 元组 | 同时拥有 A 和 B，两者都必须被使用 |
| `A ⅋ B` | 无直接对应 | 经典逻辑的"或"的线性版本 |
| `A ⊸ B` | `fn(A) -> B` | 线性函数：消费 A，产生 B |
| `!A` | `Copy` / `Clone` | 指数模态：A 可以被复制/丢弃 |
| `1` | `()` — unit 类型 | 空资源，什么都不做 |
| `0` | `!` — never type | 不可能构造的类型 |

**线性逻辑的核心原则**：

> 每个假设必须**恰好使用一次**（不能复制，不能丢弃）。

**与 Rust 的对应**：

```rust
let x = String::from("hello"); // 获得线性资源 x
let y = x;                      // x 被移动到 y（x 不能再使用）
println!("{}", y);              // y 被使用（消耗）
// y 在这里被 drop
```

这对应线性逻辑中的：

```
let x: String in
let y = x in
print(y)
```

**Affine Logic（仿射逻辑）**：Rust 实际上是**仿射**而非严格线性的——允许丢弃（drop）而不使用。

**知识点**：线性逻辑为 Rust 所有权系统提供了精确的数学模型。理解 `⊗` 和 `⊸` 有助于深入理解为什么 Rust 的所有权规则是这样的。[→ 线性逻辑详解](../01_ownership_logic/01_linear_logic.md)

</details>

---

## 三、验证工具链

### Q5. Kani、Miri 和 BorrowSanitizer 的检测能力有何不同？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 工具 | 技术 | 检测范围 | 使用阶段 |
|:---|:---|:---|:---|
| **Kani** | 模型检测（Model Checking） | 所有可能的执行路径中的 UB、panic、断言失败 | CI / 发布前验证 |
| **Miri** | 解释执行 + 内存模型检查 | 单条执行路径上的 UB（Stacked Borrows / Tree Borrows） | 开发期调试 |
| **BorrowSanitizer** | 运行时（Runtime）检测 | 别名违规、use-after-free | 测试期（类似 ASan） |
| **Sanitizers (LLVM)** | 编译期插桩 | AddressSanitizer、MemorySanitizer、ThreadSanitizer | 测试期 |

**Kani 的独特优势**：

```rust
#[kani::proof]
fn check_abs() {
    let x: i32 = kani::any(); // 符号化值：代表所有可能的 i32
    let result = x.abs();
    assert!(result >= 0); // Kani 验证：对所有 x，此断言成立
}
```

Kani 使用 **CBMC**（C Bounded Model Checker）后端，通过 SAT/SMT 求解器验证所有输入。

**Miri 的独特优势**：

- 检测 Tree Borrows / Stacked Borrows 违规
- 检测未对齐访问、未初始化内存读取
- 检测数据竞争（`-Zmiri-disable-isolation` 模式）

**选择建议**：

| 场景 | 推荐工具 |
|:---|:---|
| 日常开发 | `cargo check` + `cargo clippy` |
| 调试 unsafe | `cargo miri test` |
| 验证关键算法 | `cargo kani` |
| 性能测试期 | Sanitizers (`-Zsanitizer=address`) |

**知识点**：没有单一工具能检测所有问题。Kani 覆盖所有路径但受状态空间限制，Miri 精确但只覆盖单路径，Sanitizers 有运行时（Runtime）开销。→ 验证工具链详解

</details>

---

### Q6. Hoare 三元组 `{P} C {Q}` 的含义是什么？如何用分离逻辑表达 Rust 的 `Box::new`？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

**Hoare 三元组**：若前置条件 `P` 成立，执行命令 `C` 后，后置条件 `Q` 成立。

```
{P} C {Q}
```

**分离逻辑扩展**：使用 `P * R` 表达内存资源的分离：

**Rust 的 `Box::new` 规约**：

```
{ emp }                    // 前置：空堆（不需要任何资源）
    Box::new(v)
{ l ↦ v }                  // 后置：获得一个新位置 l，存储值 v
```

**Rust 的 `drop(box)` 规约**：

```
{ l ↦ v }                  // 前置：拥有 l 指向 v 的资源
    drop(box)
{ emp }                    // 后置：资源释放，堆为空
```

**更复杂的例子——`Vec::push`**：

```
{ vec ↦ [a₁, ..., aₙ] * v ↦ val }
    vec.push(val)
{ vec ↦ [a₁, ..., aₙ, val] }
```

**知识点**：Hoare 逻辑是程序验证的基石。分离逻辑通过 `*` 运算符扩展了 Hoare 逻辑，使其能够表达堆内存的局部操作——这正是 Rust 所有权系统需要的数学语言。[→ Hoare 逻辑详解](../03_operational_semantics/15_hoare_logic.md)

</details>

---

## 四、形式化与工程实践

### Q7. "Soundness Bug"（健全性漏洞）在 Rust 编译器中意味着什么？为什么它比普通 bug 更严重？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

**Soundness Bug**：编译器错误地接受了本应拒绝的不安全代码，导致 well-typed 程序在运行时（Runtime）出现未定义行为。

**严重性对比**：

| 类型 | 示例 | 影响 |
|:---|:---|:---|
| 普通 bug | `rustc` panic | 编译失败，代码不受影响 |
| Soundness bug | 借用（Borrowing）检查器遗漏了悬垂引用（Reference） | 编译通过，运行期 UB、安全保证崩溃 |

**历史 Soundness Bug 示例**：

| Bug | 描述 | 状态 |
|:---|:---|:---:|
| `self` 参数生命周期（Lifetimes） | `fn foo(self: &Self)` 在某些情况下绕过生命周期检查 | 已修复 |
| `match` 绑定模式 | 某些模式绑定创建了无效引用（Reference） | 已修复 |
| `Pin` 投影 | 不安全的 `Pin` 字段投影被错误接受 | 已修复 |
| Generic associated types | GAT 实现中的隐含约束错误 | 已修复 |

**发现渠道**：

- [rust-lang/rust issues labeled `I-unsound 💥`](https://github.com/rust-lang/rust/labels/I-unsound%20%F0%9F%92%A5)
- Miri 检测
- 社区 fuzzing（如 `cargo-fuzz`）

**知识点**：Soundness 是 Rust 的核心承诺。每个 soundness bug 都是对这个承诺的破坏，因此 Rust 团队将其列为最高优先级。[→ RustBelt 详解](../02_separation_logic/04_rustbelt.md)

</details>

---

### Q8. 以下"定理"（教学类比）描述的是什么？为什么它对 Rust 的 `unsafe` 代码至关重要？

```
定理（Frame Rule）：
若 {P} C {Q}，则 {P * R} C {Q * R}
（其中 R 中不包含 C 修改的变量）
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：**框架规则（Frame Rule）**是分离逻辑的核心定理，允许在验证局部操作时**忽略无关资源**。

**直观理解**：

如果你证明了 `C` 在资源 `P` 上的行为（前置 `P`，后置 `Q`），那么 `C` 在 `P` 加上任意不相关的资源 `R` 上的行为是相同的——`R` 保持不变。

**Rust 对应**：

```rust
fn push(vec: &mut Vec<i32>, val: i32) {
    vec.push(val); // 只修改 vec，不影响其他变量
}

fn main() {
    let mut v = vec![1, 2];
    let s = String::from("hello"); // s 是"框架"资源
    push(&mut v, 3);
    // s 仍然有效，push 没有影响它
    println!("{}", s);
}
```

**为什么对 `unsafe` 至关重要**：

`unsafe` 代码的正确性依赖于"局部性"——一个 `unsafe` 块只操作它显式声明的资源，不会偷偷修改其他内存。框架规则为这种局部性提供了形式化基础。

**反例**（违反框架规则）：

```rust,ignore
unsafe {
    // 假设这个函数不仅修改 ptr 指向的内存，
    // 还偷偷修改了全局变量 GLOBAL_STATE
    bad_function(ptr);
}
```

这种全局副作用使得局部推理不可能，是 `unsafe` 代码审查的重点关注对象。

**知识点**：框架规则是"组合性验证"的数学基础——复杂系统的验证可以分解为组件的局部验证。[→ 分离逻辑详解](../02_separation_logic/11_separation_logic.md)

</details>

---

## 五、综合应用

### Q9. Verus、Creusot 和 Prusti 在 Rust 验证生态中的定位有何不同？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 工具 | 验证方法 | 前置条件标注 | 后端 | 成熟度 | 适用场景 |
|:---|:---|:---|:---|:---:|:---|
| **Verus** | SMT + 所有权类型 | `#[verifier::proof]` | Z3 | 🟢 活跃 | 系统软件（OS、分布式系统） |
| **Creusot** | 幽灵状态 + 为什么3（Why3） | `#[predicate]` | Why3 + SMT | 🟢 活跃 | 算法正确性、数据结构 |
| **Prusti** | 契约 + Viper | `#[requires(...)]` | Viper | 🟡 维护模式 | 教学方法、简单程序 |
| **Kani** | 模型检测 | `#[kani::proof]` | CBMC | 🟢 活跃 | 无状态/有限状态验证 |

**设计哲学对比**：

**Verus**（Microsoft Research）：

```rust,ignore
fn binary_search(v: &Vec<u64>, x: u64) -> (r: Option<usize>)
    requires forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
    ensures match r {
        Some(idx) => v[idx] == x,
        None => forall|i: int| 0 <= i < v.len() ==> v[i] != x,
    }
{
    // 实现 + 证明同时完成
}
```

**Creusot**（Inria）：

```rust,ignore
#[predicate]
def sorted(s: Seq<T>) -> bool {
    pearlite! { forall<i: Int, j: Int> 0 <= i && i < j && j < s.len() ==> s[i] <= s[j] }
}
```

**选择建议**：

- 验证算法/数据结构 → Creusot（Why3 生态成熟）
- 验证并发/系统代码 → Verus（支持幽灵状态、原子操作（Atomic Operations））
- 验证无 unsafe 的安全属性 → Kani（无需标注，全自动）
- 教学/入门 → Prusti（简洁的 JavaDoc 风格契约）

**知识点**：Rust 的形式化验证生态正在快速发展。选择工具时需考虑验证目标、标注负担和自动化程度之间的权衡。[→ 验证工具链详解](05_verification_toolchain.md)

</details>

---

### Q10. 以下代码在 Miri 下会报告什么？解释 Tree Borrows 与 Stacked Borrows 的区别

```rust,compile_fail
fn main() {
    let mut x = 0u8;
    let y = &mut x;
    let z = &mut x;
    *y = 1;
    *z = 2;
    println!("{x}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 编译失败（在 safe Rust 中就已经失败）。

**修正为编译通过但 Miri 报错**：

```rust
fn main() {
    let mut x = 0u8;
    let y = &mut x as *mut u8;
    let z = &mut x as *mut u8;
    unsafe {
        *y = 1;
        *z = 2;
    }
    println!("{x}");
}
```

**Miri 报告**（Stacked Borrows）：UB — 使用已失效的指针。

**Tree Borrows vs Stacked Borrows**：

| 特性 | Stacked Borrows | Tree Borrows |
|:---|:---|:---|
| 模型 | 栈结构：新引用（Reference）压栈，旧引用失效 | 树结构：引用形成父子关系 |
| `&mut → *mut` | 严格：创建 `*mut` 后 `&mut` 立即失效 | 宽松：允许某些只读重用 |
| 与 LLVM 兼容 | 是 | 更兼容（允许更多优化） |
| Miri 默认 | 曾经是 | 2023+ 默认 |
| 状态 | 概念参考 | 活跃开发，可能成为标准 |

**关键区别示例**：

```rust
let mut x = 0;
let ptr = &mut x as *mut i32;
let _ref = &mut x;     // Stacked Borrows: ptr 失效
                        // Tree Borrows: ptr 仍可读（如果 _ref 未写）
```

**为什么重要**：Borrow 模型决定了哪些 `unsafe` 代码是合法的。模型越精确，编译器优化越激进，同时保持安全保证。

**知识点**：Tree Borrows 是 Rust 内存模型的最新研究方向，旨在平衡优化能力和代码兼容性。Miri 的 `-Zmiri-tree-borrows` 标志启用该模型。[→ RustBelt 详解](../02_separation_logic/04_rustbelt.md)

</details>

---

## 六、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 形式化方法已内化 | 尝试用 Verus/Creusot 验证本工作区 crates/ 中的算法 |
| 7–9/10 | ✅ 核心概念掌握 | 阅读 RustBelt 论文（POPL 2018）和 Iris 教程 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [RustBelt](../02_separation_logic/04_rustbelt.md) · [Separation Logic](../02_separation_logic/11_separation_logic.md) |
| 0–3/10 | 📚 建议重新开始 | 从 [Linear Logic](../01_ownership_logic/01_linear_logic.md) 基础概念开始 |

---

> **对应练习**: 建议安装 Kani (`cargo install kani-verifier`) 并用 `cargo kani` 验证简单函数
>
## 嵌入式测验（Embedded Quiz）

### 测验 1：本文件是 测验：形式化方法概念（L4 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：形式化方法概念（L4 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：在 测验：形式化方法概念（L4 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：形式化方法概念（L4 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先尝试独立作答，然后对照答案解析理解错误原因，最后回到对应的概念文件重新阅读相关章节，形成"测验-反馈-复习"的闭环。
</details>

---

### 测验 3：专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）

**题目**: 专项测验与概念文件末尾的嵌入式测验有什么区别？

<details>
<summary>✅ 答案与解析</summary>

专项测验题量更大、覆盖更全面，通常按难度分层；嵌入式测验更精简，直接关联刚阅读的概念内容，用于即时检验理解。
</details>
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [RustBelt](https://plv.mpi-sws.org/rustbelt/) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [RustBelt Paper](https://plv.mpi-sws.org/rustbelt/popl18/) · [Iris Project](https://iris-project.org/) · [Kani Documentation](https://model-checking.github.io/kani/)
> **权威来源对齐变更日志**: 2026-07-10 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch L4](../../00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-10
**状态**: ✅ 权威来源对齐完成 (Batch L4)
