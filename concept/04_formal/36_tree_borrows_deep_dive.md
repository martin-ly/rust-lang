> **内容分级**: [专家级]
> **代码状态**: 📋 综述/研究
> **定理链**: N/A — 操作语义研究
>
# Tree Borrows 深度解析
>
> **EN**: Tree Borrows Deep Dive
> **Summary**: 深入解析 Rust 别名模型的演进：从 Stacked Borrows 到 Tree Borrows，理解其设计动机、核心规则、与 Miri 的关系及生产实践影响。
> **受众**: [进阶] Unsafe Rust、形式化方法、运行时（Runtime）工具开发者
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Str
> **前置依赖**: [Unsafe Rust](../03_advanced/03_unsafe.md) · [所有权（Ownership）形式化](03_ownership_formal.md) · [Miri](31_miri.md)
> **后置延伸**: [BorrowSanitizer](34_borrow_sanitizer_in_formal.md)
>
> **来源**: [Tree Borrows 论文 (PLDI 2023)](https://pldi23.sigplan.org/) · [Miri 文档 — Tree Borrows](https://github.com/rust-lang/miri/blob/master/src/borrow_tracker/mod.rs) · [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) · [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **内容重叠提示**: 本文与 [`archive/docs/content/academic/10_tree_borrows_guide.md`](../../archive/docs/content/academic/10_tree_borrows_guide.md) 内容高度重叠。`docs/` 版本提供专项深入；`concept/` 版本为项目权威主轨。
> **内容重叠提示**: 本文与 [`knowledge/04_expert/miri/01_tree_borrows.md`](../../knowledge/04_expert/miri/01_tree_borrows.md) 内容高度重叠。`knowledge/` 版本提供专项深入；`concept/` 版本为项目权威主轨。
> **前置概念**: N/A
> **后置概念**: N/A
---

## 一、权威定义

> Tree Borrows is a new aliasing model for Rust that generalizes Stacked Borrows to support more flexible borrowing patterns.
> —— Tree Borrows 论文核心思想

**Stacked Borrows** 是 Rust 第一个广泛使用的别名模型，将每次借用（Borrowing）视为栈中的 tag。它精确但严格，某些合法模式被误判为 UB。

**Tree Borrows** 将借用（Borrowing）组织为**树结构**，允许同一内存位置存在多个并行的借用分支，从而接受更多实际代码中常见但 Stacked Borrows 禁止的模式。

---

## 二、Stacked Borrows 的核心限制

Stacked Borrows 要求借用按严格的 LIFO 顺序失效。这导致以下问题：

```rust,ignore
// Stacked Borrows 下可能报 UB，但 Tree Borrows 允许
let mut x = 0;
let r1 = &mut x;
let r2 = &mut x; // 重新借用
*r1 = 1; // Stacked Borrows 可能认为 r1 已失效
```

虽然安全 Rust 不会出现这种模式，但在 unsafe 代码、自引用（Reference）结构、某些 FFI 场景中，开发者需要更灵活的别名规则。

---

## 三、Tree Borrows 核心规则

### 3.1 树结构

- 每次借用创建一个节点。
- 子节点代表从父节点派生出的新借用。
- 节点可以独立失效，不一定要遵循 LIFO。

### 3.2 权限状态

每个 tag 可以处于以下状态之一：

| 状态 | 含义 |
|:---|:---|
| **Active** | 可读可写 |
| **Frozen** | 只读 |
| **Disabled** | 不可访问 |

### 3.3 转换规则

- 写访问会禁用所有不兼容的兄弟 tag（而非整个栈）。
- 读访问会将相关 tag 转为 Frozen。
- 子节点的访问不会随意使父节点失效。

---

## 四、Tree Borrows vs Stacked Borrows

| 维度 | Stacked Borrows | Tree Borrows |
|:---|:---|:---|
| 结构 | 栈 | 树 |
| 严格程度 | 更严格 | 更灵活 |
| Miri 默认 | 曾是默认 | 自某版本起成为默认 |
| 误报 | 较多 | 较少 |
| 漏报 | 较少 | 理论上可能略多（但仍在安全边界内） |
| 教学难度 | 较直观 | 需要理解树与权限状态 |

---

## 五、Miri 中使用 Tree Borrows

```bash
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test
```

自 Miri 某版本起，Tree Borrows 已成为默认模型。Stacked Borrows 仍可通过 `-Zmiri-stacked-borrows` 启用。

---

## 六、对 BorrowSanitizer 的影响

BorrowSanitizer 的目标是运行时（Runtime）检测 Tree Borrows 违规。与 Miri 相比：

- **速度**：原生执行，显著快于 Miri 的解释执行。
- **覆盖**：目前主要针对单线程别名违规，多线程和原子内存仍在完善。
- **精度**：需要与 Miri 的 Tree Borrows 实现持续对齐。

---

## 七、反命题与边界

- **不是许可证**：Tree Borrows 是操作语义模型，用于检测 UB，不是编写 unsafe 代码的许可。
- **仍在演进**：Rust 的正式别名模型尚未最终确定，Stacked/Tree Borrows 都是候选解释。
- **不能替代测试**：动态工具只能检测执行路径，不能证明所有路径安全。

---

## 八、嵌入式测验

**测验 1**: Tree Borrows 相比 Stacked Borrows 的主要优势是什么？

- A. 更快的编译速度
- B. 允许更多合法的别名模式
- C. 自动修复 unsafe 代码
- D. 替代借用检查器

<details>
<summary>答案</summary>
B
</details>

**测验 2**: 在 Miri 中如何显式启用 Tree Borrows？

<details>
<summary>答案</summary>
<code>MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test</code>（现代 Miri 已默认启用）
</details>

---

## 相关概念

- [BorrowSanitizer](34_borrow_sanitizer_in_formal.md)
- [Unsafe Rust](../03_advanced/03_unsafe.md)
- [形式化验证工具生态](../06_ecosystem/74_formal_verification_tools.md)
- [Rust 1.98+ 预览](../07_future/rust_1_98_preview.md)
