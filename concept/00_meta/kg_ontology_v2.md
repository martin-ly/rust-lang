# Rust 知识体系知识图谱本体规范 v2.0（RDF 1.2 / RDF-star / SKOS 对齐版）
>
> **EN**: Knowledge Graph Ontology v2.0
> **Summary**: Upgraded KG ontology aligned with RDF 1.2, RDF-star, SKOS multilingual labels, and SHACL validation.
>
> **受众**: [研究者]
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **Bloom 层级**: 元（Meta）
> **定位**: 本文件是 `kg_ontology.md` 的 v2 升级版，在保留原有教学关系本体的基础上，显式对齐 W3C RDF 1.2、RDF-star、SKOS、JSON-LD 1.1 与 SHACL 数据形状标准，使项目知识图谱从"规范文档"进化为"可验证、可查询、可多语言消费"的 Linked Data。
> **对齐来源**: [W3C RDF 1.2 Concepts] · [W3C RDF-star] · [W3C SKOS Reference] · [W3C JSON-LD 1.1] · [W3C SHACL] · [ISO 704:2022] · [ISO/IEC 21838-1:2021]
> **定理链**: N/A — 描述性/综述性/导航性文档
>
> **来源**: [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/)
---

> **来源**: [W3C — RDF 1.2 Concepts and Abstract Syntax] · [W3C — RDF-star] · [W3C — SKOS Reference] · [W3C — JSON-LD 1.1] · [W3C — SHACL]

## 📑 目录

- [Rust 知识体系知识图谱本体规范 v2.0（RDF 1.2 / RDF-star / SKOS 对齐版）](.#rust-知识体系知识图谱本体规范-v20rdf-12--rdf-star--skos-对齐版)
  - [📑 目录](.#-目录)
  - [一、升级动机与目标](.#一升级动机与目标)
  - [二、命名空间与词汇复用](.#二命名空间与词汇复用)
  - [三、实体类型（Node Types）](.#三实体类型node-types)
  - [四、关系类型（Edge Types）](.#四关系类型edge-types)
    - [4.1 关系属性特征](.#41-关系属性特征)
    - [4.2 RDF-star 元数据注解](.#42-rdf-star-元数据注解)
  - [五、SKOS 多语言概念方案](.#五skos-多语言概念方案)
  - [六、Turtle 示例](.#六turtle-示例)
  - [七、JSON-LD 1.1 示例](.#七json-ld-11-示例)
  - [八、与 v1 的兼容性](.#八与-v1-的兼容性)
  - [九、SHACL 验证入口](.#九shacl-验证入口)

---

## 一、升级动机与目标

v1 本体（`kg_ontology.md`）已成功定义了 Rust 知识体系的显式关系类型，并生成了机器可读的 `kg_data.json`。v2 升级目标：

1. **标准对齐**：显式映射到 RDF 1.2、SKOS、JSON-LD 1.1，降低与国际工具链的集成成本。
2. **三元组元数据**：引入 RDF-star，使每条关系边可附加来源、版本、置信度、审校状态。
3. **多语言消费**：采用 SKOS `prefLabel`/`altLabel`/`hiddenLabel` + BCP47 语言标签，支撑中英双语骨架。
4. **数据质量保障**：配套 SHACL shapes，验证概念文件头、关系类型、实体类型的合法性。
5. **可计算性**：为后续接入 Sophia/Oxigraph/SPARQL 和 KG-RAG 奠定数据模型基础。

---

## 二、命名空间与词汇复用

| 前缀 | IRI | 用途 |
|:---|:---|:---|
| `ex` | `https://rust-lang-knowledge-graph.org/` | 项目自定义实体与关系 |
| `rdf` | `http://www.w3.org/1999/02/22-rdf-syntax-ns#` | RDF 核心词汇 |
| `rdfs` | `http://www.w3.org/2000/01/rdf-schema#` | RDFS 模式词汇 |
| `owl` | `http://www.w3.org/2002/07/owl#` | OWL 2 本体词汇 |
| `skos` | `http://www.w3.org/2004/02/skos/core#` | SKOS 知识组织系统 |
| `sh` | `http://www.w3.org/ns/shacl#` | SHACL 数据形状 |
| `xsd` | `http://www.w3.org/2001/XMLSchema#` | XML Schema 数据类型 |
| `dcterms` | `http://purl.org/dc/terms/` | Dublin Core 元数据 |
| `prov` | `http://www.w3.org/ns/prov#` | 来源与可信度 |

---

## 三、实体类型（Node Types）

v2 在 v1 六类实体基础上，显式声明其为 `rdfs:Class` 或 `skos:Concept`，并附加多语言标签。

| v1 类型 | v2 RDF 类型 | SKOS 角色 | 示例 |
|:---|:---|:---|:---|
| `Concept` | `ex:Concept rdfs:subClassOf skos:Concept` | `skos:Concept` | `ex:Ownership` |
| `Theory` | `ex:Theory rdfs:subClassOf skos:Concept` | `skos:Concept` | `ex:AffineLogic` |
| `Model` | `ex:Model rdfs:subClassOf skos:Concept` | `skos:Concept` | `ex:BorrowChecker` |
| `Property` | `ex:Property rdfs:subClassOf skos:Concept` | `skos:Concept` | `ex:Send` |
| `Rule` | `ex:Rule rdfs:subClassOf skos:Concept` | `skos:Concept` | `ex:AXM` |
| `Primitive` | `ex:Primitive rdfs:subClassOf skos:Concept` | `skos:Concept` | `ex:Struct` |

**设计原则**：

- 所有实体均为 `skos:Concept`，便于复用 SKOS 的标签、注释、关系词汇。
- 用 `rdf:type` 区分子类，保留 v1 的六类语义。
- 每个实体必须至少有一个 `skos:prefLabel`（zh 和 en）。

---

## 四、关系类型（Edge Types）

v2 将 v1 的八种关系映射为 `owl:ObjectProperty`，并声明其逻辑特征。

| v1 关系 | v2 属性 | 逆属性 | OWL 特征 | 适用域/范围 |
|:---|:---|:---|:---|:---|
| `dependsOn` | `ex:dependsOn` | `ex:enables` | Transitive | Concept/Theory × Concept/Theory |
| `entails` | `ex:entails` | `ex:impliedBy` | Transitive | Concept/Rule × Concept/Property |
| `mutexWith` | `ex:mutexWith` | `ex:mutexWith` | Symmetric, Irreflexive | Property/Concept × Property/Concept |
| `refines` | `ex:refines` | `ex:refinedBy` | Transitive, Reflexive | Model/Theory × Model/Theory |
| `equivalentTo` | `ex:equivalentTo` | `ex:equivalentTo` | Symmetric, Transitive, Reflexive | Concept/Model ↔ Theory |
| `counterExample` | `ex:counterExample` | `ex:refutedBy` | Asymmetric | Concept/Property × Concept/Property |
| `instanceOf` | `ex:instanceOf` | `ex:hasInstance` | Asymmetric | Property/Rule × Concept |
| `appliesTo` | `ex:appliesTo` | `ex:governedBy` | Asymmetric | Rule × Concept/Property |

### 4.1 关系属性特征

```turtle
ex:dependsOn a owl:ObjectProperty ;
    rdfs:label "depends on"@en, "依赖于"@zh ;
    rdfs:comment "A 的理解或成立依赖于 B。"@zh ;
    owl:inverseOf ex:enables ;
    rdf:type owl:TransitiveProperty .

ex:mutexWith a owl:ObjectProperty ;
    rdfs:label "mutex with"@en, "互斥于"@zh ;
    owl:inverseOf ex:mutexWith ;
    rdf:type owl:SymmetricProperty, owl:IrreflexiveProperty .

ex:equivalentTo a owl:ObjectProperty ;
    rdfs:label "equivalent to"@en, "等价于"@zh ;
    rdf:type owl:SymmetricProperty, owl:TransitiveProperty, owl:ReflexiveProperty .
```

### 4.2 RDF-star 元数据注解

在 v1 中，三元组 `ex:Ownership ex:dependsOn ex:TypeSystem` 是一条无标签边。v2 使用 RDF-star 对该边附加元数据：

```turtle
<< ex:Ownership ex:dependsOn ex:TypeSystem >>
    ex:source "TRPL Ch. 3" ;
    ex:confidence "1.0"^^xsd:float ;
    ex:version "1.96.0" ;
    ex:reviewed true ;
    dcterms:created "2026-06-27"^^xsd:date ;
    prov:wasDerivedFrom <https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html> .
```

**元数据字段规范**：

| 字段 | 类型 | 必填 | 说明 |
|:---|:---|:---:|:---|
| `ex:source` | `xsd:string` | ✅ | 权威来源标识（如 TRPL 章节、RFC 编号） |
| `ex:confidence` | `xsd:float` [0,1] | ✅ | 关系可信度，人工审校为 1.0，自动推断为 0.6-0.9 |
| `ex:version` | `xsd:string` | ✅ | 适用的 Rust 版本 |
| `ex:reviewed` | `xsd:boolean` | ✅ | 是否经过人工审校 |
| `dcterms:created` | `xsd:date` | ⬜ | 创建日期 |
| `prov:wasDerivedFrom` | `xsd:anyURI` | ⬜ | 具体 URL 来源 |

---

## 五、SKOS 多语言概念方案

每个实体必须提供以下 SKOS 标签：

| 标签 |  Cardinality | 用途 | 示例（Ownership） |
|:---|:---:|:---|:---|
| `skos:prefLabel` | 1..n | 首选标签，每语言一个 | `"Ownership"@en`, `"所有权"@zh` |
| `skos:altLabel` | 0..n | 同义词/缩写 | `"Owner"@en`, `"拥有权"@zh` |
| `skos:hiddenLabel` | 0..n | 拼写变体/检索用 | `"ownership"@en` |
| `skos:definition` | 0..n | 定义，每语言一个 | 见概念文件摘要 |
| `skos:note` | 0..n | 教学注释 | 见认知路径 |
| `skos:broader` / `skos:narrower` | 0..n | 与 `ex:refines` 对齐 | `ex:Ownership skos:broader ex:MemorySafety` |
| `skos:related` | 0..n | 与 `ex:mutexWith` / 非依赖关系对齐 | `ex:Ownership skos:related ex:Borrowing` |

**语言标签**：遵循 BCP47，项目使用 `zh`（简体中文）、`en`（英语）。未来可扩展 `zh-Hant`、`ja`、`ko`。

---

## 六、Turtle 示例

```turtle
@prefix ex: <https://rust-lang-knowledge-graph.org/> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix skos: <http://www.w3.org/2004/02/skos/core#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix dcterms: <http://purl.org/dc/terms/> .
@prefix prov: <http://www.w3.org/ns/prov#> .

# 实体类定义
ex:Concept a rdfs:Class, owl:Class ;
    rdfs:subClassOf skos:Concept ;
    skos:prefLabel "Concept"@en, "概念"@zh .

ex:Theory a rdfs:Class, owl:Class ;
    rdfs:subClassOf skos:Concept ;
    skos:prefLabel "Theory"@en, "理论"@zh .

# 关系属性定义
ex:dependsOn a owl:ObjectProperty, owl:TransitiveProperty ;
    rdfs:label "depends on"@en, "依赖于"@zh ;
    owl:inverseOf ex:enables ;
    rdfs:domain ex:Concept, ex:Theory ;
    rdfs:range ex:Concept, ex:Theory .

ex:equivalentTo a owl:ObjectProperty,
        owl:SymmetricProperty,
        owl:TransitiveProperty,
        owl:ReflexiveProperty ;
    rdfs:label "equivalent to"@en, "等价于"@zh .

# 实体实例
ex:Ownership a ex:Concept ;
    skos:prefLabel "Ownership"@en, "所有权"@zh ;
    skos:altLabel "Owner"@en, "拥有权"@zh ;
    skos:definition "Rust's compile-time resource management mechanism ensuring each value has a unique owner."@en ;
    skos:definition "Rust 编译期资源管理机制，确保每个值有唯一所有者。"@zh ;
    skos:broader ex:MemoryManagement ;
    skos:related ex:Borrowing, ex:Lifetimes .

ex:AffineLogic a ex:Theory ;
    skos:prefLabel "Affine Logic"@en, "仿射逻辑"@zh ;
    skos:definition "A substructural logic where every premise must be used at most once."@en ;
    skos:definition "一种子结构逻辑，每个前提最多使用一次。"@zh .

# RDF-star 三元组元数据
<< ex:Ownership ex:dependsOn ex:TypeSystem >>
    ex:source "TRPL Ch. 3-4" ;
    ex:confidence "1.0"^^xsd:float ;
    ex:version "1.96.0" ;
    ex:reviewed true ;
    dcterms:created "2026-06-27"^^xsd:date ;
    prov:wasDerivedFrom <https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html> .

<< ex:Ownership ex:equivalentTo ex:AffineLogic >>
    ex:source "concept/04_formal/01_linear_logic.md" ;
    ex:confidence "0.95"^^xsd:float ;
    ex:version "1.96.0" ;
    ex:reviewed true .
```

---

## 七、JSON-LD 1.1 示例

```json
{
  "@context": {
    "ex": "https://rust-lang-knowledge-graph.org/",
    "rdf": "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
    "rdfs": "http://www.w3.org/2000/01/rdf-schema#",
    "owl": "http://www.w3.org/2002/07/owl#",
    "skos": "http://www.w3.org/2004/02/skos/core#",
    "xsd": "http://www.w3.org/2001/XMLSchema#",
    "dcterms": "http://purl.org/dc/terms/",
    "prov": "http://www.w3.org/ns/prov#"
  },
  "@id": "ex:Ownership",
  "@type": "ex:Concept",
  "skos:prefLabel": [
    { "@value": "Ownership", "@language": "en" },
    { "@value": "所有权", "@language": "zh" }
  ],
  "skos:altLabel": [
    { "@value": "Owner", "@language": "en" },
    { "@value": "拥有权", "@language": "zh" }
  ],
  "skos:definition": [
    { "@value": "Rust's compile-time resource management mechanism.", "@language": "en" },
    { "@value": "Rust 编译期资源管理机制。", "@language": "zh" }
  ],
  "ex:dependsOn": {
    "@id": "ex:TypeSystem",
    "@annotation": {
      "ex:source": "TRPL Ch. 3-4",
      "ex:confidence": { "@value": "1.0", "@type": "xsd:float" },
      "ex:version": "1.96.0",
      "ex:reviewed": true,
      "dcterms:created": { "@value": "2026-06-27", "@type": "xsd:date" },
      "prov:wasDerivedFrom": "https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html"
    }
  },
  "ex:equivalentTo": {
    "@id": "ex:AffineLogic",
    "@annotation": {
      "ex:source": "concept/04_formal/01_linear_logic.md",
      "ex:confidence": { "@value": "0.95", "@type": "xsd:float" },
      "ex:version": "1.96.0",
      "ex:reviewed": true
    }
  }
}
```

> **注**：JSON-LD 1.1 对 RDF-star 的 `@annotation` 语法是社区草案，生产环境可回退为 Turtle/N-Triples-star 序列化。

---

## 八、与 v1 的兼容性

| v1 元素 | v2 处理 | 兼容性 |
|:---|:---|:---:|
| `kg_ontology.md` 八类关系 | 保留并映射为 OWL ObjectProperty | ✅ 向后兼容 |
| `kg_data.json` 字段 | 保留，新增 `skos:` 与 `@annotation` | ✅ 向后兼容 |
| 前缀 `c:` / `t:` / `m:` / `p:` / `r:` / `prim:` | 映射为 `ex:` 命名空间下的类 | ⚠️ 需脚本转换 |
| Turtle 示例 | v1 Turtle 仍有效；v2 新增 RDF-star 注解 | ✅ 向后兼容 |

**迁移脚本计划**：后续提供 `scripts/migrate_kg_v1_to_v2.py`，自动将 v1 `kg_data.json` 转换为 v2 JSON-LD，并为所有关系附加默认元数据（confidence=1.0, reviewed=false）。

---

## 九、SHACL 验证入口

v2 配套 SHACL shapes 定义在 `concept/00_meta/kg_shapes.ttl`，可验证：

1. 每个实体必须有 `skos:prefLabel`（en + zh）。
2. 每个 `ex:Concept` 必须有 `ex:layer`（L0-L7）和 `ex:bloom`。
3. 关系类型必须是 `ex:dependsOn`、`ex:entails`、`ex:mutexWith`、`ex:refines`、`ex:equivalentTo`、`ex:counterExample`、`ex:instanceOf`、`ex:appliesTo` 之一。
4. `ex:confidence` 必须在 [0,1] 范围内。
5. `ex:version` 必须匹配 Rust 版本号格式（如 `1.96.0`）。

**运行方式**（待 `crates/c13_semantic_web/` 落地后）：

```bash
cargo run --bin kg-validate -- concept/00_meta/kg_data.json concept/00_meta/kg_shapes.ttl
```

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-06-27
**状态**: 🔄 v2 规范已冻结，待数据迁移与工具链落地
