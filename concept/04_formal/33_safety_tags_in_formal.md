> **内容分级**: [专家级]
> **代码状态**: 📋 预览/提案 — RFC #3842 阶段
> **定理链**: N/A — 语言设计/静态分析提案
>
# Safety Tags（安全标签）
>
> **EN**: Safety Tags for Unsafe Code
> **Summary**: RFC #3842 提案，用结构化属性标记 `unsafe` 函数的安全契约，使安全前提可被工具检查、文档生成和形式化推理。
> **受众**: [进阶] 形式化方法、Unsafe Rust、系统级开发者
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **A+S** — Application + Structure
> **双维定位**: C×Eva
> **前置依赖**: [Unsafe Rust](../03_advanced/03_unsafe.md) · [形式化验证](05_verification_toolchain.md) · [Miri](../06_ecosystem/74_formal_verification_tools.md)
> **后置延伸**: [BorrowSanitizer](34_borrow_sanitizer_in_formal.md) · [AutoVerus](24_autoverus.md) · [Rust for Linux 案例](../07_future/43_rust_for_linux.md)
>
> **来源**: [RFC #3842 Safety Tags](https://github.com/rust-lang/rfcs/pull/3842) · [Safety Tags 研究仓库](https://github.com/safer-rust/safety-tags) · [safety-tool slides](https://os-checker.github.io/slides/safety-tags) · [Rust for Linux Safety Standard](https://rust-for-linux.com/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [LLVM — Alias Analysis](https://llvm.org/docs/AliasAnalysis.html) · [Rust Reference — Unsafe Blocks](https://doc.rust-lang.org/reference/unsafe-blocks.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **前置概念**: N/A
> **后置概念**: N/A
---


---

## 认知路径

> **认知路径**: 本节从 "Safety Tags（安全标签）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Safety Tags（安全标签） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Safety Tags（安全标签） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Safety Tags（安全标签）的适用边界。
5. **迁移应用**: 将 Safety Tags（安全标签） 与前置/后置概念链接，形成跨层知识网络。


## 一、权威定义

> Safety tags are a lightweight, machine-readable convention for annotating the safety requirements of `unsafe` functions and discharging them at call sites.
> —— RFC #3842 核心思想

当前 Unsafe Rust 的安全前提主要依赖人工撰写的 `# Safety` 文档注释。Safety Tags 尝试将这些契约提升为**结构化属性（structured attributes）**，让 Clippy、rust-analyzer、Miri 以及未来的形式化工具能够：

1. **统一词汇表**：用 `valid_ptr`、`aligned`、`initialized` 等标准标签表达常见前提。Safety Tags 研究原型已梳理出 21 个基础标签，可覆盖 std 中约 96% 的公开 `unsafe` API。
2. **调用点检查**：在 `unsafe` 调用处通过 `#[safety::checked(...)]` 显式声明已满足哪些标签。
3. **文档与 IDE 支持**：自动生成安全检查清单，提供补全与诊断。
4. **通向形式化**：将标签转换为验证工具的前置条件（preconditions）。

---

## 二、核心机制

### 2.1 声明安全标签：`#[safety::requires(...)]`

```rust,ignore
#![feature(safety_tags)] // 假设性 nightly feature，以实际 RFC 为准

#[safety::requires(
    valid_ptr = "src must be a valid pointer to T",
    aligned = "src must be properly aligned for T",
    initialized = "src must point to an initialized value of type T",
)]
pub unsafe fn read<T>(src: *const T) -> T {
    // ...
}
```

每个标签由**键**（标准标签名）和**人类可读说明**组成。键的集合由 Rust Project 标准化，形成共享词汇表。

### 2.2 调用点消除标签：`#[safety::checked(...)]`

```rust,ignore
let x = 42;
let r = &x as *const i32;

let v = unsafe {
    #[safety::checked(valid_ptr, aligned, initialized)]
    read(r)
};
```

调用者必须在 `#[safety::checked(...)]` 中勾选被调用函数要求的所有标签。工具可据此检查：

- 是否遗漏标签；
- 是否勾选了不存在的标签；
- 标签说明是否与调用上下文匹配。

### 2.3 与现有 `# Safety` 注释的关系

| 方式 | 可读性 | 机器可检查 | 形式化潜力 |
|:---|:---|:---|:---|
| 自由文本 `# Safety` | 高 | ❌ | 低 |
| Safety Tags | 高 | ✅ | 高 |
| Safety Tags + 文本说明 | 最高 | ✅ | 高 |

Safety Tags **不替代**人工说明，而是为其提供结构化骨架。

---

## 三、为什么需要 Safety Tags？

### 3.1 降低 unsafe 代码审计成本

大型项目（如 Rust for Linux、Asterinas、操作系统内核）包含大量 `unsafe` 函数。统一标签后，审计者可以快速扫描哪些调用缺少标签勾选，而不必逐行阅读注释。

### 3.2 支持 Rust for Linux 等安全关键场景

Rust for Linux 的 [Safety Standard](https://rust-for-linux.com/) 工作倡导用一致术语描述安全要求。Safety Tags 与该目标一致，可作为从“自然语言标准”到“机器可读契约”的桥梁。

### 3.3 与形式化验证的衔接

Safety Tags 的键值对可映射为：

- **Verus**: `requires` / `ensures` 子句；
- **Kani**: harness 中的假设（assumptions）；
- **Miri / BorrowSanitizer**: 动态检查的标签集合。

---

## 四、当前状态与时间表

| 时间 | 里程碑 |
|:---|:---|
| 2025 下半年 | RFC #3842 提交社区讨论 |
| 2025-12 | Rust OSDev Meetup 分享 safety-tool 原型与在 Rust for Linux / 星绽代码库上的标注实践 |
| 2026 | 继续推进 RFC，探索与 Clippy、rust-analyzer 的集成 |
| 未来 | 可能成为语言特性或编译器内置 lint 框架 |

**状态**: 📋 RFC 提案阶段，语法和标签词汇表均未最终确定。

---

## 五、反命题与边界

- **不能自动证明标签已满足**：`#[safety::checked(...)]` 仍依赖程序员判断，工具目前只能做语法级检查。
- **标签词汇表难以完备**：复杂的安全前提（如“链表不变量”）可能无法仅用标准标签表达。
- **与现有 unsafe 代码的兼容性**：大规模迁移需要自动化工具和社区共识。

---

## 六、嵌入式测验

**测验 1**: Safety Tags 的主要目标是什么？

- A. 完全消除 `unsafe` 关键字
- B. 将 `unsafe` 函数的安全前提结构化，使工具可检查
- C. 替代 Rust 借用（Borrowing）检查器
- D. 自动生成 FFI 绑定

<details>
<summary>答案</summary>
B
</details>

**测验 2**: 调用 `#[safety::requires(valid_ptr, aligned)]` 的函数时，调用者应使用什么属性？

<details>
<summary>答案</summary>
<code>#[safety::checked(valid_ptr, aligned)]</code>
</details>

---

## 相关概念

- [Unsafe Rust](../03_advanced/03_unsafe.md)
- [形式化验证工具生态](../06_ecosystem/74_formal_verification_tools.md)
- [BorrowSanitizer](34_borrow_sanitizer_in_formal.md)
- [AutoVerus](24_autoverus.md)
- [Rust 1.98+ 预览](../07_future/rust_1_98_preview.md)
