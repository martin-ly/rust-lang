# C-to-Rust Translation Ecosystem（C 到 Rust 翻译生态）

> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **P** — Procedure
> **双维定位**: E×Eva — 评估 C→Rust 自动化翻译工具的适用性与局限
> **前置概念**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md) · [Unsafe Rust](../03_advanced/03_unsafe.md) · [FFI](../03_advanced/09_ffi_advanced.md)
> **后置概念**: [Formal Verification Tools](./47_formal_verification_tools.md) · [Compiler Internals](./45_compiler_internals.md)
> **Bloom 层级**: 分析 → 评价
>
> **主要来源**: [DARPA TRACTOR] · [C2Rust] · [Scylla (OOPSLA 2026)] · [&inator (PLDI 2026)] · [His2Trans]

---

**变更日志**:

- v1.0 (2026-05-26): 初始创建。覆盖 DARPA TRACTOR、Scylla、&inator、His2Trans、C2Rust 生态等最新权威来源 [来源: Web Authority Alignment Sprint]

---

## 📑 目录

- [C-to-Rust Translation Ecosystem](#c-to-rust-translation-ecosystem)
  - [零、TL;DR —— 30 秒选型](#零tldr--30-秒选型)
  - [一、翻译生态全景矩阵](#一翻译生态全景矩阵)
  - [二、工业级项目：DARPA TRACTOR](#二工业级项目darpa-tractor)
  - [三、学术研究前沿](#三学术研究前沿)
    - [3.1 Scylla（OOPSLA 2026）](#31-scyllaoopsla-2026)
    - [3.2 &inator（PLDI 2026）](#32-inatorpldi-2026)
    - [3.3 His2Trans（2026）](#33-his2trans2026)
  - [四、现有工具链](#四现有工具链)
    - [4.1 C2Rust 与后处理生态](#41-c2rust-与后处理生态)
  - [五、挑战与未来方向](#五挑战与未来方向)

---

## 零、TL;DR —— 30 秒选型

| 你的场景 | 首选工具 | 期望输出 |
|:---|:---|:---|
| 需要 safe Rust，C 代码无复杂别名 | **Scylla** | 纯 safe Rust（有限子集） |
| 需要精确 API 接口翻译 | **&inator** | safe 签名 + 内部实现保留 |
| 大规模工业代码库迁移 | **His2Trans / DARPA TRACTOR** | 可编译骨架 + 渐进式重构 |
| 快速原型、接受 unsafe | **C2Rust** | 机械翻译的 unsafe Rust |
| C2Rust 输出后处理 | **Crown / Laertes** | 减少 unsafe 使用比例 |

> **关键洞察**: C→Rust 翻译的本质不是"语法转换"，而是**所有权推断**。C 的裸指针在 Rust 中可能对应 `&T`、`&mut T`、`Box<T>`、`Vec<T>` 或保留为 `*const T`——选择哪个取决于别名分析、生命周期推断和数组大小推断的精度。当前没有任何工具能在所有场景下做出完美选择，这是该领域的核心开放问题。[来源: [PLDI 2026 — &inator](https://arxiv.org/abs/2604.17261)]

---

## 一、翻译生态全景矩阵

| 维度 | C2Rust | Crown | Scylla | &inator | His2Trans | DARPA TRACTOR |
|:---|:---|:---|:---|:---|:---|:---|
| **翻译范式** | 规则-based AST 转换 | C2Rust + SMT 优化 | 应用式子集 → safe Rust | 全局类型推断 + 接口翻译 | Skeleton-first + LLM 精修 | AI + 形式化验证 |
| **输出安全性** |  mostly unsafe | 减少 unsafe | ✅ safe Rust（有限子集） | ✅ safe 签名 | 渐进式 safe 化 | 目标：verified safe |
| **别名处理** | 保留裸指针 | SMT 约束推断 | 不支持复杂别名 | 全局别名分析 | 构建追踪恢复 | 待公开 |
| **数组推断** | 无 | 有限 | 有限 | ✅ 精确 | 静态分析 + 历史模式 | 待公开 |
| **工业规模** | ✅ 生产可用 | 研究 | 研究 | 研究 | 研究 | 资助阶段 |
| **形式化保证** | ❌ | 部分（SMT） | 类型安全 | 接口正确性 | 无 | 目标：完整验证 |

> **[来源: [OOPSLA 2026 — Scylla](https://arxiv.org/abs/2412.15042)]** · **[来源: [PLDI 2026 — &inator](https://arxiv.org/abs/2604.17261)]** · **[来源: [arXiv 2026 — His2Trans](https://arxiv.org/abs/2603.02617)]** · **[来源: [DARPA TRACTOR](https://www.darpa.mil/research/programs/translating-all-c-to-rust)]**

---

## 二、工业级项目：DARPA TRACTOR

**DARPA TRACTOR**（Translating All C to Rust）是美国国防部高级研究计划局于 2024 年启动的 $5M+ 资助项目，目标是创建能**安全且可验证地**将遗留 C 代码库转换为内存安全 Rust 的自动化工具。

**ForCLift**（Formally-Verified Compositional Lifting of C to Rust）是 TRACTOR 下的核心研究团队，由威斯康星大学麦迪逊分校（UW-Madison）、加州大学伯克利分校（UC Berkeley）、伊利诺伊大学厄巴纳-香槟分校（UIUC）和爱丁堡大学联合组成。

**技术路线**：

```text
Verified Lifting = 形式化方法 + 程序分析 + 大语言模型（LLM）
```

| 组件 | 功能 | 创新点 |
|:---|:---|:---|
| **组合式提升** | 将 C 函数逐函数翻译为 Rust | 模块化验证，避免全局分析爆炸 |
| **LLM 辅助合成** | 生成 idiomatic Rust 代码 | 利用 LLM 的模式识别能力处理 C 惯用法 |
| **形式化验证** | 证明翻译前后语义等价 | SMT + 程序逻辑验证输出正确性 |

> **关键洞察**: TRACTOR 的独特之处在于**"验证翻译本身"**——不仅生成 Rust 代码，还要证明生成的代码与原始 C 代码语义等价。这比"仅生成代码"难一个数量级，但也是唯一能让高保证系统（如国防、航空）接受自动翻译的路径。[来源: [DARPA TRACTOR Program](https://www.darpa.mil/research/programs/translating-all-c-to-rust)] · [来源: [UIUC News 2025](https://csl.illinois.edu/news-and-media/translating-legacy-code-for-a-safer-future)]

---

## 三、学术研究前沿

### 3.1 Scylla（OOPSLA 2026）

**Scylla** 是由 Microsoft Research 的 Fromherz & Protzenko 开发的 C→safe Rust 翻译器，发表于 OOPSLA 2026。

**核心创新**：

- **目标约束**: 仅处理 C 的"应用式子集"（applicative subset）——无复杂别名、无动态借用
- **类型推断**: 全局反向分析，从期望类型反推 C 变量应翻译为 `&T`、`&mut T` 还是 `Box<T>`
- **安全保证**: 输出代码保证通过 Rust 借用检查器，即**零 unsafe**

**局限**：

```text
Scylla 不支持的 C 模式:
  ❌ 指针算术（除数组索引外）
  ❌ 动态借用（运行时决定的 &mut / &）
  ❌ 复杂别名（如链表、图结构）
  ❌ union 和位域
```

> **关键洞察**: Scylla 证明了"在受限子集上，C→safe Rust 是可行的"。它的价值不在于处理所有 C 代码，而在于定义了**"可安全翻译的 C 子集"**的边界——这是 TRACTOR 等工业项目的重要参考。[来源: [OOPSLA 2026 — Fromherz & Protzenko, "Scylla: Translating an Applicative Subset of C to Safe Rust"](https://arxiv.org/abs/2412.15042)]

### 3.2 &inator（PLDI 2026）

**&inator** 是由普渡大学（Purdue）Chen、Coughlin 和 Bond 开发的 C→Rust **接口翻译**工具，发表于 PLDI 2026。

**核心创新**：

- **接口翻译而非代码翻译**: &inator 不翻译函数体，而是翻译**函数签名**——将 C 的 `int* foo(int* x)` 翻译为 Rust 的 `fn foo(x: &mut i32) -> &mut i32`
- **全局类型推断**: 使用 SMT 求解器（Z3）在**整个程序**范围内推断每个指针的最精确 Rust 类型
- **别名感知**: 通过全局分析处理跨函数边界的别名关系

**技术架构**：

```text
C AST → 指针关系图 → SMT 约束（Z3）→ 最优 Rust 类型分配 → 接口重写
```

> **关键洞察**: &inator 的核心贡献是证明了"接口翻译"比"全程序翻译"更容易验证——因为接口的行为由类型签名决定，而类型签名可以被形式化地比较（C 的函数类型 vs Rust 的函数类型）。这为"渐进式迁移"提供了理论基础：先翻译接口（安全边界），再逐步重写实现。[来源: [PLDI 2026 — Chen et al., "Correct, Precise C-to-Rust Interface Translation"](https://arxiv.org/abs/2604.17261)]

### 3.3 His2Trans（2026）

**His2Trans** 是 2026 年提出的**骨架优先 + 历史知识重用**框架，针对工业级 C 代码库的渐进式迁移。

**核心创新**：

- **Skeleton-first**: 先建立可编译的项目级骨架（声明、模块结构、跨模块引用），再生成函数体
- **Build Trace Recovery**: 从构建系统的实际依赖追踪中恢复项目上下文，而非依赖推测性静态分析
- **Historical Knowledge Reuse**: 重用已编译通过的翻译对（Rust API、本地模式），形成自我进化的 RAG（Retrieval-Augmented Generation）

> **关键洞察**: His2Trans 认识到现有工具的核心失败模式——"初始选择错误导致后续级联失败"。通过先建立类型一致的骨架，His2Trans 将全局构建失败转化为局部修复任务，这是从"研究原型"到"工业工具"的关键跃迁。[来源: [arXiv 2026 — "His2Trans: A Skeleton-First Framework for Self-Evolving C-to-Rust Translation"](https://arxiv.org/abs/2603.02617)]

---

## 四、现有工具链

### 4.1 C2Rust 与后处理生态

**C2Rust**（Galois / Immunant）是目前最成熟的 C→Rust 翻译工具，但输出以 **unsafe Rust** 为主。

**后处理工具链**：

| 工具 | 技术 | 效果 |
|:---|:---|:---|
| **Crown** (Zhang et al., 2023) | 所有权 + 可变性分析，SMT 约束 | 减少 raw pointer 使用，但不修改函数签名 |
| **Laertes** (Emre et al., 2021) | 重量级指针分析 + 借用检查器劫持 | 97% 成功率处理纯指针函数（libxml2 中 210/3029 函数） |
| **CRustS** (Ling et al., 2022) | 模板封装 | 封装 unsafe 代码，但不消除 |

> **关键洞察**: C2Rust 生态的核心教训——"翻译容易，安全化难"。从 unsafe Rust 到 safe Rust 的转换需要**全局所有权推断**，而这不是局部重写能解决的。&inator 和 Scylla 的成功在于绕过这个问题：&inator 只翻译接口（类型系统层面），Scylla 限制输入子集（语言层面）。[来源: [C2Rust](https://c2rust.com/)] · [来源: [Crown Paper](https://arxiv.org/abs/2305.02287)]

---

## 五、挑战与未来方向

| 挑战 | 当前状态 | 未来方向 |
|:---|:---|:---|
| **指针算术 → 切片/索引** | 部分解决（&inator, Scylla） | 需要更精确的数组大小推断 |
| **动态别名 → 借用** | 未解决 | 可能需要运行时检查（如 RefCell） |
| **union/位域 → Rust 枚举** | 手动处理 | 自动化语义映射 |
| **宏/条件编译** | C2Rust 部分支持 | 预处理标准化 |
| **验证翻译正确性** | TRACTOR / ForCLift 目标 | 组合式验证 + LLM 辅助 |

> **权威来源**: [DARPA TRACTOR](https://www.darpa.mil/research/programs/translating-all-c-to-rust) · [Scylla (OOPSLA 2026)](https://arxiv.org/abs/2412.15042) · [&inator (PLDI 2026)](https://arxiv.org/abs/2604.17261) · [His2Trans (arXiv 2026)](https://arxiv.org/abs/2603.02617) · [C2Rust](https://c2rust.com/) · [Crown](https://arxiv.org/abs/2305.02287) · [Laertes](https://arxiv.org/abs/2103.15450)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [Rust RFCs](https://rust-lang.github.io/rfcs/)
> **权威来源对齐变更日志**: 2026-05-26 创建 C-to-Rust 翻译生态专题文件，对齐 DARPA TRACTOR、PLDI 2026、OOPSLA 2026 等最新权威来源 [来源: Web Authority Alignment Sprint]

**文档版本**: 1.0
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-26
**状态**: ✅ 初始创建
