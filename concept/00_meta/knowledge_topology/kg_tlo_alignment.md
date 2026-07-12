# Rust 知识体系顶层本体（TLO）对齐

> **EN**: Top-level Ontology Alignment for Rust Knowledge Graph
> **Summary**: Maps project knowledge-graph entities to upper ontologies (BFO / DOLCE) for semantic-web interoperability and engineering reference.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **任务**: P2-3 顶层本体对齐
> **目标**: 将项目知识图谱 v2 的六类实体与 ISO/IEC 21838 推荐的顶层本体（BFO / DOLCE）进行显式映射，建立 `TLO → 中层本体 → 领域本体` 的分层架构，并讨论边界案例。
> **受众**: 知识工程师、形式化方法研究者、本体论实践者
> **权威来源**: 本文件为 `concept/` 权威页。
> **状态**: 教学/工程对齐草案，非形式化公理化
> **主要来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [RFCs](https://github.com/rust-lang/rfcs)

---

## 1. 标准与权威来源

| 标准 / 资源 | 说明 | 链接 |
|:---|:---|:---|
| ISO/IEC 21838-1:2021 | Information technology — Top-level ontologies (TLO) — Part 1: Requirements for TLOs and core concepts | <https://www.iso.org/standard/71954.html> |
| ISO/IEC 21838-2:2022 | Top-level ontologies — Part 2: Basic Formal Ontology (BFO) | <https://www.iso.org/standard/74374.html> |
| ISO/IEC 21838-3:2023 | Top-level ontologies — Part 3: Descriptive Ontology for Linguistic and Cognitive Engineering (DOLCE) | <https://www.iso.org/standard/77625.html> |
| BFO 官方资源 | Basic Formal Ontology 2.0 / 2020 | <https://basic-formal-ontology.org/> |
| BFO Reference | Arp, Smith & Spear, *Building Ontologies with BFO* | OBO / ISO 21838-2 配套文档 |
| DOLCE 官方资源 | ISTC-CNR DOLCE 概述 | <http://www.loa.istc.cnr.it/dolce/overview.html> |
| DOLCE 论文 | Gangemi et al., *Sweetening Ontologies with DOLCE* | 知识工程经典文献 |

> **说明**：本项目不具备 ISO 认证资质，本文档中的对齐属于**教学/工程参考映射**，用于提升知识图谱与外部语义网工具链的可解释性，而非对 BFO/DOLCE 的形式化扩展。

---

## 2. BFO / DOLCE 核心类别速览

「BFO / DOLCE 核心类别速览」部分包含 BFO 顶层二分法 与  DOLCE 顶层二分法 两条主线，本节依次说明。

### 2.1 BFO 顶层二分法

BFO 将实在（reality）首先划分为两大类：

| BFO 顶层类别 | 含义 | 关键子类 |
|:---|:---|:---|
| **Continuant**（持续体） | 在时间中存在、整体在同一时刻呈现 | Independent Continuant, Dependent Continuant |
| **Occurrent**（发生体/过程体） | 在时间中展开、具有时间部分 | Process, Process Boundary |

BFO 的持续体再细分：

| 子类别 | 含义 | 示例 |
|:---|:---|:---|
| **Independent Continuant** | 不依赖其他实体而存在的实体 | 物质对象、空间区域 |
| **Dependent Continuant** | 存在依赖于其他实体的实体 | 性质（quality）、角色（role）、 disposition |
| **Generically Dependent Continuant** | 可以在多个载体间复制的信息依赖体 | 信息内容实体（ICE）、文本、软件代码 |

### 2.2 DOLCE 顶层二分法

DOLCE 采用 **particulars** 视角，核心高阶区分包括：

| DOLCE 顶层类别 | 含义 | 关键子类 |
|:---|:---|:---|
| **Physical** | 具有时空存在 | Physical Object, Physical Region |
| **Mental** | 认知主体的心灵实体 | Mental Object, Mental Process |
| **Abstract** | 非时空的、理想化的实体 | Quality、Abstract Region、Set |
| **Social** | 社会建构（DOLCE+） | Social Object, Agentive Social Object |

DOLCE 同样区分 **Endurant**（对应 BFO Continuant）与 **Perdurant**（对应 Occurrent）。

---

## 3. Rust 知识体系实体 → TLO 映射

项目知识图谱 v2 定义了六类节点：`Concept`、`Theory`、`Model`、`Property`、`Rule`、`Primitive`。下表给出 BFO 与 DOLCE 的映射。

| 项目实体 | BFO 2.0 映射 | DOLCE 映射 | 映射理由 | Rust 示例 |
|:---|:---|:---|:---|:---|
| **Concept** | `Generically Dependent Continuant` ⊏ `Information Content Entity` | `Mental Object` / `Abstract` | 概念是对 Rust 语言机制的语义抽象，以文本/符号形式存在，可被多人共享 | `ex:Ownership`、`ex:Borrowing` |
| **Theory** | `Generically Dependent Continuant` ⊏ `Information Content Entity` | `Abstract` | 理论是形式化/半形式化的命题集合，不依赖特定物理载体 | `ex:AffineLogic`、`ex:SeparationLogic` |
| **Model** | `Generically Dependent Continuant` ⊏ `Information Content Entity` | `Abstract` / `Mental Object` | 模型是对编译器或运行时行为的解释性/预测性表示 | `ex:BorrowChecker`、`ex:StackHeapModel` |
| **Property** | `Dependent Continuant`（具体为 `Quality` / `Role`） | `Quality` / `Abstract` | 类型属性（Send/Sync）是相对于类型的关系性质；在本体层常编码为 ICE 描述的约束 | `ex:Send`、`ex:Sync` |
| **Rule** | `Generically Dependent Continuant` ⊏ `Information Content Entity` | `Abstract` | 规则是规范性的语句（如 Alias-XOR-Mutation），可被表达为文本、代码或逻辑公式 | `ex:AXM`、`ex:MoveSemanticsRule` |
| **Primitive** | `Generically Dependent Continuant` ⊏ `Information Content Entity` | `Abstract` | 语法/语义原语是语言构造的最小单位，属于抽象符号实体 | `ex:Struct`、`ex:Enum`、`ex:Reference` |

### 3.1 映射一致性说明

- 六类实体在 BFO 中均可归入 **Generically Dependent Continuant**，因为它们都是可被多载体复制的信息/符号实体；但在更细粒度区分时，`Property` 强调**依赖/关系性质**，因此也可视为 `Dependent Continuant`（Quality）。
- 在 DOLCE 中，六类实体偏向 **Abstract / Mental**；`Property` 若理解为类型上的内在性质，可映射为 `Quality`。
- 本文档采用 **BFO 为主、DOLCE 为辅** 的双映射策略，以兼容 ISO 21838-2 与 ISO 21838-3 两种 TLO 路径。

---

## 4. TLO → 中层本体 → 领域本体 分层架构

```text
┌─────────────────────────────────────────────────────────────┐
│  TLO (Top-Level Ontology)                                   │
│  ISO/IEC 21838-1/2/3: BFO / DOLCE                           │
│  Continuant / Occurrent · Independent / Dependent           │
│  Physical / Mental / Abstract                               │
└─────────────────────────────────────────────────────────────┘
                              │ 映射/特化
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  Mid-Level Ontology (MLO)                                   │
│  SKOS · PROV · IAO · Dublin Core · OWL 2                    │
│  - skos:Concept（概念组织）                                  │
│  - iao:information content entity（信息内容实体）            │
│  - prov:wasDerivedFrom / prov:generatedBy（来源追踪）        │
│  - dcterms:created / dcterms:modified（元数据）              │
└─────────────────────────────────────────────────────────────┘
                              │ 复用/对齐
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  Domain Ontology（Rust 知识体系）                            │
│  ex:Concept / ex:Theory / ex:Model / ex:Property /          │
│  ex:Rule / ex:Primitive                                     │
│  ex:dependsOn / ex:entails / ex:mutexWith / ex:refines ...  │
└─────────────────────────────────────────────────────────────┘
```

### 4.1 分层原则

| 层级 | 职责 | 本项目对应 |
|:---|:---|:---|
| TLO | 提供跨领域、跨语言的最高层范畴 | BFO Continuant/Occurrent；DOLCE Physical/Mental/Abstract |
| MLO | 提供特定知识工程任务的通用词汇 | `skos:prefLabel`、`iao:ICE`、`prov:wasDerivedFrom` |
| 领域本体 | 描述 Rust 语言专属概念与关系 | `kg_ontology_v2.md`、`kg_data_v3.json` |

---

## 5. `kg_data_v3.json` 关键实体 TLO 映射示例

「`kg_data_v3.json` 关键实体 TLO 映射…」部分按 `ex:Ownership`（所有权）、`ex:Borrowing`（借用）、`ex:Lifetimes`（生命周期）、`ex:Trait`（ trait ）等5个方面的顺序逐层展开。

### 5.1 `ex:Ownership`（所有权）

| 维度 | 映射 |
|:---|:---|
| 项目类型 | `ex:Concept` |
| BFO | `Generically Dependent Continuant` ⊏ `Information Content Entity` |
| DOLCE | `Mental Object` / `Abstract` |
| 中层本体 | `skos:Concept`、`iao:information content entity` |
| 说明 | 所有权是 Rust 编译期资源管理的核心语义概念；作为“概念”它存在于文档、教材与人脑中，而非具体物理对象。 |

### 5.2 `ex:Borrowing`（借用）

| 维度 | 映射 |
|:---|:---|
| 项目类型 | `ex:Concept` |
| BFO | `Generically Dependent Continuant` ⊏ `Information Content Entity`；其动态执行可对应 `Occurrent`（Process） |
| DOLCE | `Mental Object`（静态概念）/ `Perdurant`（运行时借用过程） |
| 中层本体 | `skos:Concept`、`prov:Activity`（若强调借用检查过程） |
| 说明 | 借用作为“关系/机制”是概念；而一次具体的借用检查行为是过程/发生体，属于边界案例。 |

### 5.3 `ex:Lifetimes`（生命周期）

| 维度 | 映射 |
|:---|:---|
| 项目类型 | `ex:Concept` |
| BFO | `Occurrent` 中的 `Process Boundary` / `Temporal Region`；静态描述时也可归为 ICE |
| DOLCE | `Abstract` / `Temporal Region` |
| 中层本体 | `skos:Concept`、`owl:Thing`（时间区域） |
| 说明 | 生命周期本质上是引用有效的**时间区间**，因此更贴近 Occurrent/Temporal Region；但作为学习概念，仍编码为 `ex:Concept`。 |

### 5.4 `ex:Trait`（ trait ）

| 维度 | 映射 |
|:---|:---|
| 项目类型 | `ex:Concept` |
| BFO | `Generically Dependent Continuant` ⊏ `Information Content Entity` |
| DOLCE | `Abstract` |
| 中层本体 | `skos:Concept` |
| 说明 | Trait 是类型行为的抽象接口规范；与 `ex:Property`（如 Send/Sync）不同，trait 自身是一个语言构造概念。 |

### 5.5 `ex:Generics`（泛型）

| 维度 | 映射 |
|:---|:---|
| 项目类型 | `ex:Concept` |
| BFO | `Generically Dependent Continuant` ⊏ `Information Content Entity` |
| DOLCE | `Abstract` |
| 中层本体 | `skos:Concept` |
| 说明 | 泛型是参数化多态的抽象描述；在运行时单态化后不再存在，因此本体上属于抽象 ICE。 |

---

## 6. 边界案例与讨论

「边界案例与讨论」涉及 `Theory` 是 Abstract 还是 Information…、`Rule` 是 Information Content Entity…、`Property` 是 Dependent Continuant 还…与关系（Relation）本身的 TLO 地位，本节逐一说明其要点。

### 6.1 `Theory` 是 Abstract 还是 Information Content Entity？

- **BFO 视角**：`Theory` 是 **Generically Dependent Continuant**，具体属于 `Information Content Entity`（ICE）。它依赖载体（论文、书籍、Coq 文件） but can be copied across carriers.
- **DOLCE 视角**：`Theory` 更接近 **Abstract**，因为它不是特定主体的心灵内容，而是理想化的公理/模型集合。
- **本项目处理**：在映射表中给出双映射，并在 RDF 中保持 `ex:Theory rdfs:subClassOf skos:Concept`，在中层本体层通过 `iao:information content entity` 链接 BFO。

### 6.2 `Rule` 是 Information Content Entity 还是 Norm ？

- Rust 规则（如 Alias-XOR-Mutation）是**规范性陈述**：规定了哪些程序状态是合法的。
- 在 BFO 中，规范/规则通常被视为 ICE；若强调其社会/制度来源，可进一步归入 **Document Act** 或 `Social Construction`（BFO 2020 的 social entities）。
- 本项目当前将 `Rule` 映射为 ICE，以与 `Property` 的“性质”区分。

### 6.3 `Property` 是 Dependent Continuant 还是 Abstract ？

- `Send`、`Sync` 等属性本质上是**类型上的关系性质**：一个类型是否满足 `Send` 取决于其结构。
- 在 BFO 中，这种“依他而在”的特性最适合 **Dependent Continuant**（特别是 `Quality` 或 `Relational Quality`）。
- 但在知识图谱的工程实践中，属性通常被编码为 `owl:Class` 或 `skos:Concept`，因此也会呈现为 ICE。文档采用 **Dependent Continuant 为主、ICE 为辅** 的说明。

### 6.4 关系（Relation）本身的 TLO 地位

- 项目关系如 `ex:dependsOn`、`ex:mutexWith` 是 **OWL ObjectProperty**，在本体层属于 **Abstract**（DOLCE）或 **Generically Dependent Continuant**（BFO：作为信息内容实体中的关系描述）。
- 具体的三元组实例（如 `ex:Ownership ex:dependsOn ex:TypeSystem`）则是 **Relational Quality** 或 **Process** 的抽象描述，取决于关系的动态性。

---

## 7. 与 `kg_ontology_v2.md` 的衔接

| `kg_ontology_v2.md` 元素 | TLO 对齐补充 |
|:---|:---|
| `ex:Concept rdfs:subClassOf skos:Concept` | 进一步映射到 BFO ICE / DOLCE Mental Object |
| `ex:Theory` / `ex:Model` / `ex:Rule` / `ex:Primitive` | 统一映射到 BFO ICE；`Rule` 作为 ICE 的子案例 |
| `ex:Property` | 映射到 BFO Dependent Continuant（Quality），同时在 SKOS 层保留为 Concept |
| `ex:dependsOn` 等 OWL 属性 | 中层本体 OWL 属性；TLO 上作为 ICE/Abstract 描述的关系 |
| RDF-star 元数据 | `prov:wasDerivedFrom`、`dcterms:created` 提供来源与时间定位，与 BFO/Occurrent 互补 |

---

## 8. 结论与后续工作

1. 已完成 Rust KG v2 六类实体到 **BFO** 与 **DOLCE** 顶层本体的显式映射。
2. 建立了 **TLO → MLO（SKOS/IAO/PROV/OWL） → 领域本体** 的三层架构。
3. 对 `Ownership`、`Borrowing`、`Lifetimes`、`Trait`、`Generics` 进行了映射示例。
4. 讨论了 `Theory`、`Rule`、`Property` 等边界案例，并说明本项目映射为**教学/工程参考**，非 ISO 认证本体。

后续可在 `kg_data_v3.json` 的 `@context` 或 `classes` 段中显式加入 `bfo:` / `dolce:` 前缀与映射断言，使对齐从文档级进入**数据级**。

---

## 9. 参考链接汇总

- ISO/IEC 21838-1:2021 — <https://www.iso.org/standard/71954.html>
- ISO/IEC 21838-2:2022 (BFO) — <https://www.iso.org/standard/74374.html>
- ISO/IEC 21838-3:2023 (DOLCE) — <https://www.iso.org/standard/77625.html>
- Basic Formal Ontology — <https://basic-formal-ontology.org/>
- DOLCE — <http://www.loa.istc.cnr.it/dolce/overview.html>
- SKOS — <https://www.w3.org/TR/skos-reference/>
- IAO — <https://github.com/information-artifact-ontology/iao/>
- PROV — <https://www.w3.org/TR/prov-overview/>

---

## 国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Hogan et al.: Knowledge Graphs (ACM Comput. Surv. 2021)](https://dl.acm.org/doi/10.1145/3447772)
