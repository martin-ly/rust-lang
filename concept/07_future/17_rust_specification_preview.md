# Rust 语言规范预研：从参考文档到形式化规范

> **Bloom 层级**: 分析 → 评价
> **定位**: 探讨 Rust 语言从**参考文档**（Rust Reference）向**形式化规范**演进的必要性与路径，分析 Ferrocene、编译器开发和形式化验证社区对规范的不同需求。
> **前置概念**: [Formal Methods](./02_formal_methods.md) · [RustBelt](../04_formal/04_rustbelt.md) · [Ferrocene](./14_ferrocene_preview.md)
> **后置概念**: [Version Tracking](./05_rust_version_tracking.md)

---

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [Ferrocene Specification](https://spec.ferrocene.dev/) · [Rust Language Specification RFC](https://github.com/rust-lang/rfcs/pull/3355) · [Rust Compiler Team — Specification](https://github.com/rust-lang/compiler-team/issues/)

## 📑 目录
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

- [Rust 语言规范预研：从参考文档到形式化规范](#rust-语言规范预研从参考文档到形式化规范)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 问题：参考文档的局限性](#11-问题参考文档的局限性)
    - [1.2 规范的多层次需求](#12-规范的多层次需求)
    - [1.3 Ferrocene 规范的先行探索](#13-ferrocene-规范的先行探索)
  - [二、技术细节](#二技术细节)
    - [2.1 规范的内容层次](#21-规范的内容层次)
    - [2.2 与形式化验证的衔接](#22-与形式化验证的衔接)
    - [2.3 维护挑战](#23-维护挑战)
  - [三、社区视角](#三社区视角)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、演进路线](#五演进路线)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)

---

## 一、核心概念
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 1.1 问题：参考文档的局限性

当前 Rust 的权威定义分散在多个文档中：

```text
当前 Rust 定义来源:
├── The Rust Reference（语言参考）
│   └── 问题: 不完整，许多行为未文档化
├── The Rustonomicon（unsafe 指南）
│   └── 问题: 非规范性质，存在"未定义行为"的灰色地带
├── rustc 源码（实际行为）
│   └── 问题: 实现即规范，但实现复杂且变化频繁
├── RFCs（设计决策记录）
│   └── 问题: 分散、历史遗留、与实现不完全一致
└── 测试套件（行为实例）
    └── 问题: 覆盖有限，无法替代规范

核心矛盾:
  "rustc 的实际行为" vs "文档描述的行为" vs "设计者意图的行为"
  三者之间经常不一致，导致:
  ├── 编译器开发者的维护困难
  ├── 第三方工具（Clippy, rust-analyzer）的语义偏差
  ├── 形式化验证工具的建模挑战
  └── 安全关键认证（Ferrocene）的证据缺口
```

> **核心痛点**: Rust 缺乏一个**单一、完整、精确**的语言规范。这在一般开发中不是问题（rustc 实现足够可靠），但在安全关键认证、形式化验证和编译器替代实现（如 gccrs）中成为根本障碍。
> [来源: [Rust RFC 3355](https://github.com/rust-lang/rfcs/pull/3355)]

---

### 1.2 规范的多层次需求

```mermaid
graph TD
    subgraph 用户层["不同用户的需求层次"]
        A["应用开发者"] -->|"需要"| B["直观的行为描述"]
        C["库作者"] -->|"需要"| D["精确的 API 契约"]
        E["编译器开发者"] -->|"需要"| F["完整的语法/语义规则"]
        G["形式化验证者"] -->|"需要"| H["可机器解析的逻辑规约"]
        I["认证机构"] -->|"需要"| J["可审计的确定性证据"]
    end

    subgraph 规范层["规范的分层结构"]
        K["用户指南"] --> L["参考文档"]
        L --> M["技术规范"]
        M --> N["形式化规约"]
    end

    用户层 --> 规范层
```

> **认知功能**: 此图展示 Rust 规范需要服务的**多层次用户群体**，以及对应的规范分层结构。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]
> **使用建议**: 不同场景查阅不同层次的规范——开发看参考文档，认证看技术规范，形式化验证看逻辑规约。
> **关键洞察**: 单一文档无法同时满足所有需求。Rust 规范的正确形态是**分层文档体系**，而非一本"圣经"。
> [来源: [Rust Specification Discussion](https://rust-lang.github.io/rust-project-goals/)]

---

### 1.3 Ferrocene 规范的先行探索

Ferrocene 项目在实践中探索了 Rust 技术规范的形态：

```text
Ferrocene Specification 的结构:
├── 语言定义
│   ├── 词法: tokens, whitespace, comments
│   ├── 语法: 上下文无关文法（基于 rustc 的 grammar）
│   ├── 语义: 类型规则、求值规则
│   └── 约束: 编译时错误条件
├── 标准库契约
│   ├── 前置条件 / 后置条件（以自然语言描述）
│   ├── 复杂度保证
│   └── 安全 invariant
├── 未定义行为清单
│   ├── 明确列出所有 UB 类别
│   └── 与 Reference 的 UB 章节对齐并扩展
└── 实现定义行为
    ├── 平台相关行为（整数大小、对齐等）
    └── 编译器选项的影响

Ferrocene 规范的局限:
├── 只覆盖 Ferrocene 认证的范围（core + 部分 alloc）
├── 自然语言描述，非形式化逻辑
├── 与 rustc 版本绑定，不跟踪 nightly
└── 独立维护，非 rust-lang 官方项目
```

> **先行价值**: Ferrocene 规范是 Rust **技术规范可行性的概念验证**。它证明了：即使不完美，一个比 Reference 更精确的规范对认证和工具开发有巨大价值。
> [来源: [Ferrocene Specification](https://spec.ferrocene.dev/)]

---

## 二、技术细节
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 2.1 规范的内容层次

```text
理想的 Rust 规范分层:

  L1: 用户参考（User Reference）
      ├── 目标读者: Rust 开发者
      ├── 内容: 行为描述、示例、最佳实践
      └── 形式: 类似当前 Rust Reference，但更完整

  L2: 技术规范（Technical Specification）
      ├── 目标读者: 工具作者、认证机构
      ├── 内容: 精确的语法/语义规则、UB 清单、实现定义行为
      └── 形式: 结构化文档，带唯一标识符的条款

  L3: 形式化规约（Formal Specification）
      ├── 目标读者: 形式化验证研究者
      ├── 内容: 操作语义、类型系统规则、逻辑断言
      └── 形式: 机器可解析的规约语言（如 K Framework, Coq）

  L4: 可执行规约（Executable Specification）
      ├── 目标读者: 编译器开发者、测试作者
      ├── 内容: 参考解释器、一致性测试套件
      └── 形式: 可运行的代码 + 测试用例
```

> **技术要点**: 各层次之间需要**可追溯性**——L1 的每个论断应能在 L2 中找到对应条款，L2 的每个规则应能在 L3 中找到形式化表达。
> [来源: [Rust Project Goals — Specification](https://rust-lang.github.io/rust-project-goals/)]

---

### 2.2 与形式化验证的衔接

```mermaid
graph LR
    subgraph 规范["语言规范"]
        A["L2 技术规范"] -->|"形式化翻译"| B["L3 形式化规约"]
    end

    subgraph 验证["形式化验证工具"]
        C["Kani"] -->|"基于"| B
        D["Verus"] -->|"基于"| B
        E["Creusot"] -->|"基于"| B
        F["RustBelt/Iris"] -->|"基于"| B
    end

    subgraph 证据["认证证据"]
        G["Ferrocene"] -->|"引用"| A
        H["DO-178C"] -->|"要求"| A
        I["ISO 26262"] -->|"要求"| A
    end

    规范 --> 验证
    规范 --> 证据
```

> **认知功能**: 此图展示语言规范作为**形式化验证和工业认证的共同基础**——一个精确的规范使验证工具和认证证据能够建立在同一语义基础上。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]
> **关键洞察**: 当前形式化验证工具各自维护对 Rust 语义的**独立理解**，导致结果不可比较。统一规范将解决这一碎片化问题。
> [来源: [Formal Methods Preview](./02_formal_methods.md)]

---

### 2.3 维护挑战

```text
Rust 规范维护的核心挑战:

  1. 语言演进速度
     ├── Rust 每 6 周一个 stable release
     ├── 每年一个 Edition（可能引入 breaking changes）
     └── 规范必须同步更新，否则迅速过时

  2. 实现与规范的差距
     ├── rustc 是"活"的实现，不断修复 bug 和优化
     ├── 规范描述的"理想行为"与 rustc 的"实际行为"可能不一致
     └── 当不一致时，以谁为准？（实现优先 vs 规范优先）

  3. 资源约束
     ├── 编写高质量规范需要全职专家团队
     ├── 当前 Rust 项目资源集中在编译器开发和生态建设
     └── 规范工作长期依赖志愿者贡献，进度缓慢

  4. 社区共识
     ├── 规范的"权威性"需要社区广泛认可
     ├── 不同子社区（embedded, web, safety-critical）有不同需求
     └── 达成共识的过程可能比编写规范本身更耗时
```

> **挑战本质**: Rust 规范的困难不是技术性的，而是**社会-技术性的**——它涉及资源分配、优先级排序和社区治理。
> [来源: [Rust Internals — Specification Discussion](https://internals.rust-lang.org/)]

---

## 三、社区视角
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

| 利益相关方 | 对规范的需求 | 当前痛点 | 优先级 |
|:---|:---|:---|:---:|
| **gccrs 团队** | 完整的语言定义，不依赖 rustc 源码 | Reference 不完整，需反向工程 rustc | **高** |
| **Ferrocene** | 可审计的技术规范，覆盖认证范围 | 独立维护，与上游不同步 | **高** |
| **形式化验证研究者** | 可机器解析的操作语义 | 各自维护独立语义模型 | **高** |
| **rust-analyzer** | 精确的语法和类型规则 | 需从 rustc 源码推断行为 | 中 |
| **嵌入式开发者** | 明确的 no_std 行为边界 | 许多行为在文档中未定义 | 中 |
| **普通开发者** | 比 Reference 更完整的行为描述 | 遇到未文档化行为时困惑 | 低 |

> **社区洞察**: 对规范需求最迫切的不是普通开发者，而是**编译器替代实现者**（gccrs）、**认证项目**（Ferrocene）和**形式化验证研究者**。这三方共同构成了推动规范工作的核心力量。
> [来源: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)]

---

## 四、反命题与边界分析
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 4.1 反命题树

```mermaid
graph TD
    ROOT["命题: Rust 应立即投入资源编写完整形式化规范"]
    ROOT --> Q1{"语言是否稳定?"}
    Q1 -->|否| FALSE1["❌ 过早 — 语言仍在快速演进"]
    Q1 -->|部分稳定| Q2{"资源是否充足?"}

    Q2 -->|否| FALSE2["❌ 资源应优先用于编译器和生态"]
    Q2 -->|是| Q3{"需求是否紧迫?"}

    Q3 -->|是| TRUE["✅ 投入 — 从 L2 技术规范开始"]
    Q3 -->|否| ALT["⚠️ 渐进 — 先完善 Reference，再逐步精确化"]

    style TRUE fill:#c8e6c9
    style FALSE1 fill:#ffebee
    style FALSE2 fill:#ffebee
    style ALT fill:#fff3e0
```

> **认知功能**: 此决策树评估编写完整形式化规范的**时机和方式**。核心判断标准是语言稳定性、资源可用性和需求紧迫性。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]
> **使用建议**: 当前阶段（2026）应采取**渐进策略**——先完善 L1/L2（Reference + 技术规范），在语言更稳定后再推进 L3/L4（形式化/可执行规约）。
> **关键洞察**: Ferrocene 的先行探索证明了"渐进可行"——从认证需要的子集开始，逐步扩展，而非等待"一次性完整规范"。
> [来源: 💡 原创分析]

---

### 4.2 边界极限

```text
边界 1: 规范的完备性不可能
├── 图灵完备语言的完全形式化规范是不可判定的
├── 规范只能覆盖"典型用法"和"已知的 corner cases"
└── 与数学公理系统类似：公理是完备的，但所有定理不可穷尽

边界 2: 规范与实现的两难
├── "规范优先": 编译器 bug 应以规范为准修复
│   └── 风险: 可能破坏现有代码的依赖行为
├── "实现优先": 规范应描述编译器实际行为
│   └── 风险: 实现中的 bug 被"规范化为正确"
└── Rust 社区的倾向: 实现优先，但逐步向规范收敛

边界 3: unsafe Rust 的规范困境
├── safe Rust 的规范相对清晰（类型系统 + 借用检查）
├── unsafe Rust 的行为高度依赖 LLVM 和平台 ABI
└── 完全规范化 unsafe Rust 可能需要先规范化 LLVM

边界 4: 跨 Edition 的规范复杂性
├── 每个 Edition 可能有不同的语义规则
├── 规范需要说明"在哪个 Edition 下有效"
└── 长期维护多 Edition 规范的成本不可忽视
```

> **边界要点**: Rust 规范工作面临的根本张力是**"精确性"与"可维护性"**的权衡。过于追求完美形式化会导致规范无法跟上语言演进；过于务实则失去规范的价值。
> [来源: [Rust Compiler Team — Specification Challenges](https://github.com/rust-lang/compiler-team/)]

---

## 五、演进路线
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

| 里程碑 | 状态 | 预计时间 | 说明 |
|:---|:---:|:---|:---|
| Rust Reference 完善 | 🟡 进行中 | 持续 | 社区驱动，逐步补充缺失内容 |
| 官方技术规范启动 | ⬜ | 2026-2027 | 可能由 Rust Foundation 资助 |
| Ferrocene 规范开源贡献 | 🟡 | 2025-2026 | Ferrocene 向社区反馈规范内容 |
| gccrs 驱动规范需求 | 🟡 | 持续 | 替代实现的需求推动规范明确 |
| 形式化语义项目 | ⬜ | 2027+ | 学术/工业合作项目 |
| 完整规范 v1.0 | ⬜ | 2030+ | 覆盖 stable Rust 的语言规范 |

> **预测**: Rust 的完整技术规范可能在 **2030 年左右** 达到可用状态。这不是因为技术困难，而是因为**优先级和社区资源分配**。在此之前，Ferrocene 规范和 gccrs 的独立努力将填补部分空白。
> [来源: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)]

---

## 六、来源与延伸阅读
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rust Reference](https://doc.rust-lang.org/reference/) | ✅ 一级 | 当前权威参考 |
| [Rust RFC 3355](https://github.com/rust-lang/rfcs/pull/3355) | ✅ 一级 | 语言规范 RFC |
| [Ferrocene Specification](https://spec.ferrocene.dev/) | ✅ 一级 | 先行技术规范 |
| [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/) | ✅ 一级 | 官方项目目标 |
| [Rust Compiler Team](https://github.com/rust-lang/compiler-team/) | ✅ 一级 | 编译器团队讨论 |
| [gccrs Project](https://gcc.gnu.org/wiki/RustFrontEnd) | ⚠️ 二级 | 替代实现需求 |

---

```rust
fn main() {
    let feature = "preview";
    println!("{}", feature);
}
```

## 相关概念文件
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

- [Formal Methods](./02_formal_methods.md) — 形式化方法工业化
- [RustBelt](../04_formal/04_rustbelt.md) — Rust 所有权的形式化模型
- [Ferrocene](./14_ferrocene_preview.md) — Rust 安全关键认证工具链
- [Version Tracking](./05_rust_version_tracking.md) — Rust 版本特性演进

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-21 创建，对齐 Rust 1.95.0+ (Edition 2024)

**文档版本**: 1.0
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-21
**状态**: ✅ 概念文件创建完成
