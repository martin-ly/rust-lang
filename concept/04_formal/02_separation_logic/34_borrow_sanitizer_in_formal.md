> **内容分级**: [专家级]
> **代码状态**: 📋 预览/研究 — Rust Project Goal 2026
> **定理链**: N/A — 工具链/运行时（Runtime）研究
>
# BorrowSanitizer 运行时别名模型检测
>
> **EN**: BorrowSanitizer: Runtime Tree Borrows Violation Detection
> **Summary**: 基于 LLVM 插桩的动态分析工具，用于检测 Rust 别名模型（Stacked Borrows / Tree Borrows）违规，特别面向多语言（Rust/C/C++）互操作场景。
> **受众**: [进阶] Unsafe Rust、系统级开发者、形式化方法研究者
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **A+S+P** — Application + Structure + Procedure
> **双维定位**: C×Eva
> **前置依赖**: [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) · [Miri](../04_model_checking/31_miri.md) · [所有权（Ownership）形式化](../01_ownership_logic/03_ownership_formal.md) · Tree Borrows
> **后置延伸**: [Safety Tags](33_safety_tags_in_formal.md) · [AutoVerus](../04_model_checking/24_autoverus.md)
>
> **来源**: [BorrowSanitizer 项目主页](https://borrowsanitizer.com/) · [Rust Project Goal #624](https://github.com/rust-lang/rust-project-goals/issues/624) · [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/borrowsanitizer.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [LLVM — Alias Analysis](https://llvm.org/docs/AliasAnalysis.html) · [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **前置概念**: N/A
> **后置概念**: N/A
---

---

## 认知路径

> **认知路径**: 本节从 "BorrowSanitizer 运行时（Runtime）别名模型检测" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 BorrowSanitizer 运行时（Runtime）别名模型检测 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 BorrowSanitizer 运行时别名模型检测 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与BorrowSanitizer 运行时（Runtime）别名模型检测的适用边界。
5. **迁移应用**: 将 BorrowSanitizer 运行时（Runtime）别名模型检测 与前置/后置概念链接，形成跨层知识网络。

## 一、权威定义

> We are building BorrowSanitizer: an LLVM-based instrumentation tool for finding violations of Rust's aliasing model.
> —— Rust Project Goal #624

BorrowSanitizer（常缩写为 BSAN）是 Rust 2026 Project Goal 之一，目标是将研究原型转化为可在实践中使用的工具。它通过在 LLVM IR 层插桩 **retag intrinsic** 来追踪引用（Reference）的创建、传递与失效，从而检测违反 Rust 别名规则的代码。

---

## 二、核心机制

### 2.1 别名模型基础

Rust 的内存安全（Memory Safety）建立在严格的别名规则之上，主要有两种操作语义解释：

| 模型 | 特点 | 代表工具 |
|:---|:---|:---|
| **Stacked Borrows** | 将每次借用（Borrowing）视为栈中的 tag，严格按 LIFO 失效 | Miri（默认） |
| **Tree Borrows** | 将借用（Borrowing）组织为树，允许更多合法的别名模式 | Miri（可选） |

BorrowSanitizer 的目标是在**运行时（Runtime）**检测这些模型的违规，而不需要像 Miri 那样解释执行整个程序。

### 2.2 LLVM 插桩与 Retag Intrinsics

BorrowSanitizer 在编译时向 LLVM IR 插入两类 intrinsic：

- `__rust_retag_mem`：对存储在内存中的指针进行 retag。
- `__rust_retag_reg`：对寄存器/SSA 值中的指针进行 retag。

```llvm
; 示例：对引用进行 retag
%x = call ptr @__rust_retag_reg(ptr %y, ...)
```

运行时（Runtime），BorrowSanitizer 维护一个 **shadow stack** 和 **shadow memory**，记录每个指针 tag 的状态（如 Active、Frozen、Disabled）。当发生非法读/写时，报告类似 Miri 的错误信息。

### 2.3 错误报告示例

```text
error: Undefined Behavior: read through <TAG>(unprotected) at ALLOC[0x0] is forbidden
help: the accessed tag <TAG>(unprotected) has state Disabled which forbids this read
help: the accessed tag <TAG>(unprotected) was created here, in the initial state Frozen
help: the accessed tag <TAG>(unprotected) later transitioned due to a foreign write
```

---

## 三、BorrowSanitizer vs Miri vs AddressSanitizer

| 维度 | Miri | BorrowSanitizer | AddressSanitizer |
|:---|:---|:---|:---|
| 执行方式 | 解释执行 Rust MIR | LLVM 插桩后原生执行 | LLVM 插桩 |
| 性能 | 慢（数量级开销） | 较快（仍显著开销） | 中等 |
| 别名规则 | 完整 Stacked/Tree Borrows | 近似模型 | 不检查别名 |
| 多语言支持 | 仅限 Rust | **Rust/C/C++ 互操作** | 任意语言 |
| 典型用途 | 单测、CI 冒烟 | 多语言库审计、集成测试 | 内存越界/Use-after-free |

BorrowSanitizer 填补了 Miri 无法覆盖的**多语言场景**：当 Rust 代码通过 FFI 与 C/C++ 共享指针时，C 端可能破坏 Rust 的别名假设。

---

## 四、2026 目标与进展

### 4.1 目标

- 从研究原型过渡到可用工具；
- 完成垃圾回收、错误报告、原子内存访问支持；
- 与 LLVM 上游集成，理想情况下通过 `-Zsanitizer=borrow` 启用；
- 在真实世界库上测试并与 Miri 结果对齐。

### 4.2 时间线

| 时间 | 进展 |
|:---|:---|
| 2026-01 | 发布首月状态更新；确定 2026 Project Goal |
| 2026-02 | 实现详细错误信息；提出 retag intrinsic MCP |
| 2026-03 | 引入 shadow stack 运行时（Runtime）；扩展 Miri 测试套件覆盖，约 80% 通过 |
| 2026-04 | 准备 LLVM 组件 PR；计划在春季启动 LLVM 侧 RFC |
| 2026 下半年 | 继续在 LLVM 上游推进，目标实现 `-Zsanitizer=borrow` |

---

## 五、使用方式（预期）

```bash
# 未来目标用法（尚未稳定）
rustc -Zsanitizer=borrow main.rs
# 或
cargo bsan test
```

目前需要通过 `cargo-bsan` 插件和定制编译器使用。2026 年项目目标包括：完成 shadow-stack 运行时（Runtime）、提出 `__rust_retag` intrinsics MCP、向 LLVM 上游提交组件 PR，最终使 `-Zsanitizer=borrow` 可直接在 nightly 使用。

---

## 六、反命题与边界

- **不是类型系统（Type System）替代**：BorrowSanitizer 是动态工具，只能发现执行到的路径上的违规。
- **性能开销**：运行时追踪每个引用（Reference）状态仍有显著开销，不适合生产环境。
- **模型差异**：BorrowSanitizer 实现的别名规则可能与 Miri 的 Stacked/Tree Borrows 存在细微差异，需要持续对齐。

---

## 七、嵌入式测验

**测验 1**: BorrowSanitizer 主要检测哪类错误？

- A. 整数溢出
- B. 违反 Rust 别名模型的内存访问
- C. 死锁
- D. 未使用的导入

<details>
<summary>答案</summary>
B
</details>

**测验 2**: BorrowSanitizer 相比 Miri 的主要优势场景是什么？

<details>
<summary>答案</summary>
Rust 与 C/C++ 的多语言互操作场景，可在原生执行速度下检测别名违规。
</details>

---

## 相关概念

- [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md)
- [形式化验证工具生态](../../06_ecosystem/08_formal_verification/74_formal_verification_tools.md)
- [Safety Tags](33_safety_tags_in_formal.md)
- [AutoVerus](../04_model_checking/24_autoverus.md)
- [Tree Borrows 深度](../01_ownership_logic/36_tree_borrows_deep_dive.md)
- [Rust 1.98+ 预览](../../07_future/00_version_tracking/rust_1_98_preview.md)
