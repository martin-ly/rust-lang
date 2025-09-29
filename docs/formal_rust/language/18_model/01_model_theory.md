# 模型理论

## 概述

模型理论是数学逻辑的一个分支，研究数学结构与其语言描述之间的关系。
在计算机科学中，模型理论为形式化验证、类型理论和程序语义提供了理论基础。

## 基本概念

### 模型定义

**定义 1.1** (模型)
设 $\mathcal{L}$ 是一个一阶语言，$\mathcal{M} = (M, I)$ 是 $\mathcal{L}$ 的一个模型，其中：

- $M$ 是一个非空集合，称为论域
- $I$ 是解释函数，将 $\mathcal{L}$ 中的符号映射到 $M$ 上的对象

### 结构体

**定义 1.2** (结构体)
一个 $\mathcal{L}$-结构体 $\mathcal{A}$ 由以下部分组成：

- 论域 $A$ (非空集合)
- 对每个常数符号 $c$，有 $c^{\mathcal{A}} \in A$
- 对每个 $n$ 元函数符号 $f$，有 $f^{\mathcal{A}}: A^n \to A$
- 对每个 $n$ 元关系符号 $R$，有 $R^{\mathcal{A}} \subseteq A^n$

### 满足关系

**定义 1.3** (满足关系)
设 $\mathcal{A}$ 是一个 $\mathcal{L}$-结构体，$\phi$ 是一个 $\mathcal{L}$-公式，$s$ 是一个赋值函数。我们定义 $\mathcal{A} \models \phi[s]$ (读作"$\mathcal{A}$ 在赋值 $s$ 下满足 $\phi$")：

1. 如果 $\phi$ 是原子公式 $R(t_1, \ldots, t_n)$，则
   $$\mathcal{A} \models R[t_1, \ldots, t_n](s) \iff (t_1^{\mathcal{A}}[s], \ldots, t_n^{\mathcal{A}}[s]) \in R^{\mathcal{A}}$$

2. 如果 $\phi$ 是 $\neg \psi$，则
   $$\mathcal{A} \models \neg \psi[s] \iff \mathcal{A} \not\models \psi[s]$$

3. 如果 $\phi$ 是 $\psi_1 \land \psi_2$，则
   $$\mathcal{A} \models \psi_1 \land \psi_2[s] \iff \mathcal{A} \models \psi_1[s] \text{ 且 } \mathcal{A} \models \psi_2[s]$$

4. 如果 $\phi$ 是 $\exists x \psi$，则
   $$\mathcal{A} \models \exists x \psi[s] \iff \text{存在 } a \in A \text{ 使得 } \mathcal{A} \models \psi[s(x/a)]$$

## 模型论基本定理

### 紧致性定理

**定理 1.1** (紧致性定理)
设 $\Gamma$ 是一个一阶理论。如果 $\Gamma$ 的每个有限子集都有模型，则 $\Gamma$ 本身也有模型。

**证明思路**：
使用超积构造。设 $\Gamma = \{\phi_i : i \in I\}$，对每个有限子集 $F \subseteq I$，设 $\mathcal{A}_F$ 是 $\{\phi_i : i \in F\}$ 的模型。构造超积 $\prod_F \mathcal{A}_F / \mathcal{U}$，其中 $\mathcal{U}$ 是适当的超滤子。

### Löwenheim-Skolem 定理

**定理 1.2** (Löwenheim-Skolem 向下定理)
设 $\mathcal{A}$ 是一个无限 $\mathcal{L}$-结构体，$\kappa$ 是一个无限基数，且 $|\mathcal{L}| \leq \kappa \leq |A|$。则存在 $\mathcal{A}$ 的初等子结构体 $\mathcal{B}$ 使得 $|B| = \kappa$。

**定理 1.3** (Löwenheim-Skolem 向上定理)
设 $\mathcal{A}$ 是一个 $\mathcal{L}$-结构体，$\kappa$ 是一个无限基数，且 $|A| \leq \kappa$。则存在 $\mathcal{A}$ 的初等扩张 $\mathcal{B}$ 使得 $|B| = \kappa$。

## 模型论在计算机科学中的应用

### 类型理论

在类型理论中，模型论为类型系统的语义提供了基础：

**定义 1.4** (类型模型)
设 $\mathcal{T}$ 是一个类型系统，$\mathcal{M}$ 是 $\mathcal{T}$ 的模型，如果：

- 对每个类型 $T$，有对应的集合 $[T]^{\mathcal{M}}$
- 对每个项 $t : T$，有对应的元素 $[t]^{\mathcal{M}} \in [T]^{\mathcal{M}}$
- 类型规则在模型中成立

### 程序验证

模型论为程序验证提供了理论基础：

**定义 1.5** (程序模型)
设 $P$ 是一个程序，$\mathcal{M}$ 是 $P$ 的模型，如果：

- 程序状态对应模型中的元素
- 程序执行对应模型中的转换
- 程序规范对应模型中的公式

### 形式化验证

在形式化验证中，模型论提供了验证的理论基础：

**定义 1.6** (验证模型)
设 $\phi$ 是一个规范，$M$ 是一个模型，如果 $M \models \phi$，则称 $M$ 满足规范 $\phi$。

## 模型构造技术

### 超积构造

**定义 1.7** (超积)
设 $\{\mathcal{A}_i : i \in I\}$ 是一族 $\mathcal{L}$-结构体，$\mathcal{U}$ 是 $I$ 上的超滤子。超积 $\prod_{i \in I} \mathcal{A}_i / \mathcal{U}$ 定义如下：

- 论域：$\prod_{i \in I} A_i / \mathcal{U}$
- 对常数符号 $c$：$c^{\prod \mathcal{A}_i / \mathcal{U}} = [c^{\mathcal{A}_i}]_{\mathcal{U}}$
- 对函数符号 $f$：$f^{\prod \mathcal{A}_i / \mathcal{U}}([a_1]_{\mathcal{U}}, \ldots, [a_n]_{\mathcal{U}}) = [f^{\mathcal{A}_i}(a_1(i), \ldots, a_n(i))]_{\mathcal{U}}$
- 对关系符号 $R$：$([a_1]_{\mathcal{U}}, \ldots, [a_n]_{\mathcal{U}}) \in R^{\prod \mathcal{A}_i / \mathcal{U}} \iff \{i \in I : (a_1(i), \ldots, a_n(i)) \in R^{\mathcal{A}_i}\} \in \mathcal{U}$

### 初等嵌入

**定义 1.8** (初等嵌入)
设 $\mathcal{A}$ 和 $\mathcal{B}$ 是 $\mathcal{L}$-结构体，$f: A \to B$ 是一个函数。如果对每个 $\mathcal{L}$-公式 $\phi(x_1, \ldots, x_n)$ 和每个 $a_1, \ldots, a_n \in A$，有：
$$\mathcal{A} \models \phi[a_1, \ldots, a_n] \iff \mathcal{B} \models \phi[f(a_1), \ldots, f(a_n)]$$

则称 $f$ 是 $\mathcal{A}$ 到 $\mathcal{B}$ 的初等嵌入。

## 模型论与计算复杂性

### 有限模型论

**定义 1.9** (有限模型)
一个模型 $\mathcal{A}$ 是有限的，如果其论域 $A$ 是有限集合。

**定理 1.4** (有限模型论基本结果)

- 一阶逻辑在有限模型上不是紧致的
- 存在在有限模型上不可公理化的类
- 有限模型上的可满足性问题是可判定的

### 模型检查

**定义 1.10** (模型检查问题)
给定一个模型 $\mathcal{M}$ 和一个公式 $\phi$，判断是否 $\mathcal{M} \models \phi$。

**定理 1.5** (模型检查复杂性)

- 一阶逻辑的模型检查问题是 PSPACE-完全的
- 模态逻辑的模型检查问题是 P-完全的
- 时序逻辑的模型检查问题是 PSPACE-完全的

## 应用实例

### 数据库理论

在数据库理论中，模型论为查询语言提供了语义基础：

**例 1.1** (关系数据库模型)
设 $\mathcal{R}$ 是一个关系数据库模式，$\mathcal{D}$ 是一个数据库实例。则 $\mathcal{D}$ 可以看作 $\mathcal{R}$ 的一个模型，其中：

- 每个关系 $R$ 对应模型中的关系符号
- 每个元组对应模型中的一个元素
- 查询对应模型中的公式

### 软件工程

在软件工程中，模型论为软件规范提供了理论基础：

**例 1.2** (软件规范模型)
设 $S$ 是一个软件系统，$\phi$ 是一个规范。则 $S$ 满足 $\phi$ 当且仅当存在 $S$ 的模型 $\mathcal{M}$ 使得 $\mathcal{M} \models \phi$。

## 高级模型论理论

### 范畴论模型

**定义 1.11** (范畴论模型)
设 $\mathcal{C}$ 是一个范畴，$\mathcal{M}$ 是 $\mathcal{C}$ 的模型，如果：

- 对每个对象 $A \in \mathcal{C}$，有对应的集合 $[A]^{\mathcal{M}}$
- 对每个态射 $f: A \to B$，有对应的函数 $[f]^{\mathcal{M}}: [A]^{\mathcal{M}} \to [B]^{\mathcal{M}}$
- 复合和恒等态射在模型中保持

**定理 1.6** (范畴论模型存在性)
设 $\mathcal{C}$ 是一个小范畴，则存在 $\mathcal{C}$ 的模型。

**证明**：
使用 Yoneda 引理构造模型。对每个对象 $A$，定义 $[A]^{\mathcal{M}} = \text{Hom}(A, -)$。

### 同伦类型论模型

**定义 1.12** (同伦类型论模型)
设 $\mathcal{H}$ 是一个同伦类型论，$\mathcal{M}$ 是 $\mathcal{H}$ 的模型，如果：

- 对每个类型 $A$，有对应的空间 $[A]^{\mathcal{M}}$
- 对每个项 $t: A$，有对应的点 $[t]^{\mathcal{M}} \in [A]^{\mathcal{M}}$
- 类型等价对应同伦等价

**定理 1.7** (同伦类型论模型构造)
设 $\mathcal{H}$ 是一个同伦类型论，则存在 $\mathcal{H}$ 的模型。

**证明**：
使用拓扑空间构造模型。每个类型对应一个拓扑空间，每个项对应空间中的点。

### 依赖类型模型

**定义 1.13** (依赖类型模型)
设 $\mathcal{D}$ 是一个依赖类型系统，$\mathcal{M}$ 是 $\mathcal{D}$ 的模型，如果：

- 对每个类型 $A$，有对应的集合 $[A]^{\mathcal{M}}$
- 对每个依赖类型 $\Pi_{x:A} B(x)$，有对应的函数空间 $[A]^{\mathcal{M}} \to [B]^{\mathcal{M}}$
- 对每个依赖类型 $\Sigma_{x:A} B(x)$，有对应的和类型 $[A]^{\mathcal{M}} \times [B]^{\mathcal{M}}$

**定理 1.8** (依赖类型模型正确性)
如果模型 $\mathcal{M}$ 满足依赖类型系统的所有规则，则 $\mathcal{M}$ 是正确的。

**证明**：
通过归纳证明每个类型规则在模型中成立。

## 模型论在 Rust 中的应用

### 所有权模型

**定义 1.14** (所有权模型)
设 $\mathcal{O}$ 是一个所有权系统，$\mathcal{M}$ 是 $\mathcal{O}$ 的模型，如果：

- 对每个值 $v$，有对应的所有权状态 $[v]^{\mathcal{M}} \in \{\text{owned}, \text{borrowed}, \text{shared}\}$
- 所有权转移对应模型中的状态转换
- 借用检查对应模型中的约束验证

**定理 1.9** (所有权模型安全性)
如果所有权模型 $\mathcal{M}$ 满足借用检查规则，则 $\mathcal{M}$ 保证内存安全。

**证明**：
通过归纳证明每个借用规则在模型中保持内存安全。

### 生命周期模型

**定义 1.15** (生命周期模型)
设 $\mathcal{L}$ 是一个生命周期系统，$\mathcal{M}$ 是 $\mathcal{L}$ 的模型，如果：

- 对每个生命周期参数 $\alpha$，有对应的区间 $[\alpha]^{\mathcal{M}} \subseteq \mathbb{N}$
- 生命周期约束对应区间包含关系
- 生命周期推断对应区间计算

**定理 1.10** (生命周期模型正确性)
如果生命周期模型 $\mathcal{M}$ 满足生命周期规则，则 $\mathcal{M}$ 保证引用安全。

**证明**：
通过归纳证明每个生命周期规则在模型中保持引用安全。

### 类型系统模型

**定义 1.16** (Rust 类型系统模型)
设 $\mathcal{T}$ 是 Rust 类型系统，$\mathcal{M}$ 是 $\mathcal{T}$ 的模型，如果：

- 对每个类型 $T$，有对应的集合 $[T]^{\mathcal{M}}$
- 对每个 trait $Tr$，有对应的谓词 $[Tr]^{\mathcal{M}}$
- 类型推导对应模型中的计算

**定理 1.11** (Rust 类型系统模型完整性)
Rust 类型系统模型 $\mathcal{M}$ 是完整的，即所有类型安全的程序在模型中都有对应的语义。

**证明**：
通过归纳证明每个类型规则在模型中都有对应的语义。

## 模型论与程序验证

### Hoare 逻辑模型

**定义 1.17** (Hoare 逻辑模型)
设 $\mathcal{H}$ 是 Hoare 逻辑，$\mathcal{M}$ 是 $\mathcal{H}$ 的模型，如果：

- 对每个程序状态 $s$，有对应的模型状态 $[s]^{\mathcal{M}}$
- 对每个前置条件 $P$，有对应的谓词 $[P]^{\mathcal{M}}$
- 对每个后置条件 $Q$，有对应的谓词 $[Q]^{\mathcal{M}}$

**定理 1.12** (Hoare 逻辑模型正确性)
如果 Hoare 逻辑模型 $\mathcal{M}$ 满足所有推理规则，则 $\mathcal{M}$ 是正确的。

**证明**：
通过归纳证明每个推理规则在模型中成立。

### 分离逻辑模型

**定义 1.18** (分离逻辑模型)
设 $\mathcal{S}$ 是分离逻辑，$\mathcal{M}$ 是 $\mathcal{S}$ 的模型，如果：

- 对每个堆 $h$，有对应的模型堆 $[h]^{\mathcal{M}}$
- 分离合取对应堆的分离
- 分离蕴含对应堆的包含

**定理 1.13** (分离逻辑模型安全性)
如果分离逻辑模型 $\mathcal{M}$ 满足所有规则，则 $\mathcal{M}$ 保证内存安全。

**证明**：
通过归纳证明每个规则在模型中保持内存安全。

## 总结

模型论为计算机科学中的形式化方法提供了坚实的数学基础。通过模型论，我们可以：

1. **形式化语义**：为编程语言、类型系统和规范语言提供精确的语义
2. **验证理论**：为程序验证和模型检查提供理论基础
3. **构造技术**：提供构造模型和证明存在性的技术
4. **复杂性分析**：分析各种逻辑问题的计算复杂性
5. **Rust 应用**：为 Rust 的所有权、生命周期和类型系统提供理论基础
6. **程序验证**：为 Hoare 逻辑和分离逻辑提供模型论基础

模型论的发展将继续推动计算机科学中形式化方法的发展，为构建更可靠、更安全的软件系统提供理论支撑。

## 记号与术语

为保证全文一致，采用如下记号约定：

- **语言与结构**：$\mathcal{L}$ 表示一阶语言；$\mathcal{A}, \mathcal{B}, \mathcal{M}$ 表示 $\mathcal{L}$-结构；$A, B, M$ 表示其论域。
- **解释与赋值**：$I$ 为解释，$s$ 为变量赋值，$t^{\mathcal{A}}[s]$ 为项 $t$ 在 $\mathcal{A}$、赋值 $s$ 下的解释值。
- **公式与满足**：$\phi, \psi$ 为公式；$\mathcal{A} \models \phi[s]$ 表示满足关系；$\models$ 无下标时按上下文省略赋值。
- **同构与初等关系**：$\cong$ 表示结构同构；$\preccurlyeq$ 表示初等子结构；$\preccurlyeq_e$ 表示初等嵌入。
- **超积与超滤**：$\prod_{i\in I} \mathcal{A}_i / \mathcal{U}$ 表示关于超滤子 $\mathcal{U}$ 的超积。

术语对照（计算机科学语境）：

- **模型/结构 (model/structure)**：运行语义或数据语义的数学载体
- **规范 (specification)**：以逻辑公式描述的性质或约束
- **语义保持 (semantics-preserving)**：从模型到实现或优化过程不改变性质真值
- **模型检查 (model checking)**：在给定结构上判定 $\phi$ 是否为真

## 与 Rust 的语义映射

为了将模型论用于 Rust 生态中的类型系统与程序语义，给出从一阶结构到语言构件的映射草案：

- **论域 $A$ ↔ 值集合/状态空间**：如某类型的所有可构造值，或系统状态集合。
- **常数符号 ↔ 常量/零元构造器**：`const` 值或无参构造的单位值。
- **函数符号 $f: A^n\to A$ ↔ 纯函数/关联函数**：如 `fn f(a1,..,an)->A`，要求在语义上总定义且确定。
- **关系符号 $R\subseteq A^n$ ↔ 断言/谓词**：在 Rust 中可由返回 `bool` 的谓词函数或 `where` 约束表达。
- **公式 $\phi$ ↔ 规格化断言**：可由 `#[cfg(test)]` 断言、属性测试、或形式化工具（如 Prusti、Kani）表达与验证。
- **初等嵌入 ↔ 语义保真的抽象/细化映射**：如从抽象状态到实现状态的注入，其保持一阶可表达性质。

示意性规则（非强制）：

1. 若类型 `T` 的可构造值集对应论域 $A$，则函数 `fn f(t1,..,tn)->T` 可视为 $f^{\mathcal{A}}$。
2. 对性质 `P: T\to bool`，若在 $\mathcal{A}$ 中为关系 $R\subseteq A$，则 $t\in A$ 有 $P(t)=true \iff t\in R$。
3. 若优化变换 `O: Code\to Code` 保持一阶性质，则视为在语义层面对 $\mathcal{A}$ 的初等等价保持。

实际落地工具链（示例）：

- 静态层：类型系统、`where` 约束、`const` 评估、`unsafe` 不变量文档化
- 动态层：属性测试（`proptest`）、模型检查器（Kani）、符号执行（`haybale` 等）
- 规范层：Hoare 风格注解、设计不变式、协议断言

## 工程落地与验证工作流

### 最小可行验证闭环（MCVL）

1. 规格撰写：以一阶断言/时序性质表述接口契约（`requires`/`ensures`/不变式）。
2. 语义映射：将规格中的谓词、函数、关系映射到类型/函数签名与模块边界。
3. 自动验证：
   - 轻量：`proptest` 属性测试覆盖有限模型；`kani` 做按位精确模型检查。
   - 形式化：`creusot`/`Prusti` 对关键核心做证明义务生成与消解。
4. 结果回灌：将已验证性质固化为断言/类型约束/编译期检查，纳入 CI 门禁。

### 参考目录布局

```text
crate/
  src/                  # 实现
  specs/                # 规格与不变式（人类可读 + 工具注解）
  proofs/               # 形式化工件（Creusot/Prusti 文件）
  tests/                # 单元/属性/模型检查测试
  ci/                   # Kani/Creusot/Clippy/cargo-deny 流水线
```

### 常见性质模板

- 安全性：内存/借用/别名/生命周期不变量保持。
- 正确性：代数规律（幺半群/函子/同态）与协议顺序保持。
- 资源性：RAII、互斥、容量上界、超时/重试预算。

### 性能与可扩展性约束（可模型化）

- 上界复杂度：以递归度量函数形成良基下降证明（避免无界增长）。
- 背压不变量：队列长度与生产/消费速率约束的线性关系不变式。
- 并行安全：无共享可变别名；临界区最小化与无死锁次序图。

## 示例与反例

### 示例：列表长度不变性

设语言包含一元函数符号 `len: A\to N` 与二元函数 `push: A\times X\to A`，性质：对任意 $a\in A, x\in X$，有
$$ len(push(a,x)) = len(a)+1. $$

在 Rust 中可表达为（示意）：

```rust
fn push_len_invariant(xs: &Vec<i32>, x: i32) -> bool {
    let mut ys = xs.clone();
    let old_len = ys.len();
    ys.push(x);
    ys.len() == old_len + 1
}
```

该断言在有限模型（具体向量）上可通过测试/模型检查验证，从而作为 $\mathcal{A} \models \phi$ 的经验性证据。

### 反例：有限结构上的非紧致性现象

在仅限有限结构的情形下，一阶逻辑不满足紧致性。若将规范设计为仅在“所有有限长度的容器”上成立，则无法直接由紧致性推出存在模型，需使用专门的有限模型论技术与工具。

## 互操作与工具链集成

| 目标 | 工具 | 集成方式 | CI 建议 |
|---|---|---|---|
| 属性测试 | proptest | `#[test]` + 生成器 | 每次 PR 运行，最少 100 次试验 |
| 模型检查 | Kani | `cargo kani` 配置入口函数 | 夜间构建 + 关键路径必跑 |
| 证明义务 | Creusot | `requires/ensures/invariant` 注解 | 关键 crate 必跑，变更差异触发 |
| 静态质量 | clippy/rustfmt | lints/格式门禁 | 必跑，`-D warnings` |
| 供应链 | cargo-deny/audit | 漏洞/许可证扫描 | 每日计划任务 + PR 门禁 |

落地建议：为每个性质绑定“来源—验证—回归测试”三元组，以便在重构与优化时自动回归。

## 练习

1. 给出一个简单的 $\mathcal{L}$，包含常数 `nil`、二元函数 `cons` 与一元关系 `is_empty`，形式化刻画“`is_empty(nil)` 且 `¬is_empty(cons(x,s))`”。将其映射到 Rust 的类型与函数。
2. 证明：若 $f$ 是初等嵌入且 $\mathcal{A} \models \phi[a]$，则 $\mathcal{B} \models \phi[f(a)]$。并给出一个对应的 Rust 语义保持示例（如抽象状态注入到实现状态）。
3. 设性质 $\phi$ 关于不可变借用成立。讨论在 Rust 中将 $\phi$ 推广到可变借用时需要的前置条件（别名控制、不变量恢复）。
4. 构造一个有限模型，展示一阶模型检查的复杂度边界，并用小规模 Rust 原型验证之。

## 交叉引用与落地资源

- 理论延展：`01_formal_model_theory.md`、`01_formal_model_system.md`
- 实现视角：`02_model_implementation.md`
- 设计模式：参见 `../../09_design_pattern` 模块
- 验证与优化：参见 `../../c06_async` 与 `../../c20_distributed` 中的验证与复杂性实例

## 参考文献

1. Chang, C. C., & Keisler, H. J. (2012). Model theory. Elsevier.
2. Hodges, W. (1993). Model theory. Cambridge University Press.
3. Marker, D. (2002). Model theory: an introduction. Springer Science & Business Media.
4. Tent, K., & Ziegler, M. (2012). A course in model theory. Cambridge University Press.

---

## 工程落地检查清单（Practitioner Checklist）

- 规格与模型
  - 为核心不变量与性质给出一阶/时序公式表示（安全性/活性）。
  - 区分抽象模型与实现模型，并明确精化关系（抽象 ≤ 实现）。
  - 为关键接口定义可观察语义（输入/输出/错误）。

- 类型与不变式编码
  - 不变量通过构造函数/智能构造器强制成立。
  - 封装内部可变性，限制可变别名（避免将 `&mut` 外泄）。
  - 错误建模为 `Result`/判定谓词，拒绝隐式 `unwrap`。

- 状态与转移
  - 用枚举编码状态，非法转移在类型层拒绝。
  - 为每个转移给出前置/后置条件并用属性测试覆盖。
  - 为异步/并发交互定义顺序性质（有序性、幂等、可交换）。

- 验证分层
  - 单元/集成/属性/模型检查分层配置，关键路径强制门禁。
  - 并发热点用 Loom/Kani 探索并归档最小反例。
  - 规格与测试建立可追溯映射（用例 ↔ 性质 ↔ 实现）。

- 演化与兼容
  - 规格版本与实现版本绑定并提供迁移不变量。
  - 数据演化具备回放验证与向后兼容策略。
  - 破坏性变更给出形式化影响分析与缓解方案。

## 常见误区与对策（Anti-Patterns）

- 仅有测试而无形式化性质：引入“性质优先”的最小断言集；用属性测试覆盖边界。
- 规格与实现漂移：建立“规格-实现-测试”的三向链接与 CI 失配预警。
- 类型掩盖不变量：将隐含约束上移到类型层（新类型、细分枚举、封装可变性）。
- 并发顺序性质缺失：为消息/事件定义偏序与等价类，验证幂等与可交换性。
- 演化无证：为每次演化提供保持性质的证明要点与回放脚本。

## 进一步阅读与练习

- 进阶：有限模型论与数据库理论；Hoare/分离逻辑在系统编程中的应用。
- 工具：Kani/Prusti/Creusot 最小工程模板；Loom 并发探索样例集。
- 练习：
  1) 为一个简化的支付状态机给出规格、实现与模型检查对照。
  2) 为事件溯源模型设计幂等等价类并用属性测试验证。
  3) 为一次 API 破坏性演化撰写兼容性不变量与迁移验证脚本。
