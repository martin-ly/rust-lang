# 概念-权威来源对齐图谱（Concept-Source Alignment Atlas）

> **EN**: Concept-Source Alignment Atlas
> **Summary**: 每个核心概念与国际化权威来源的对齐：Rust Reference、TRPL、RFCs、学术、课程、工业、标准。
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、权威来源覆盖统计

| 来源层级 | 来源类型 | 引用次数 | 涉及概念数 |
|:---|:---|:---:|:---:|
| Lx_other | 其他 | 5517 | 441 |
| L1_specification | Rust Reference | 1020 | 406 |
| L1_trpl | TRPL | 781 | 390 |
| L1_github | Rust GitHub | 511 | 187 |
| L2_academic | 学术论文 | 407 | 293 |
| L1_std | std docs | 398 | 155 |
| L3_course | 顶尖课程 | 393 | 289 |
| L5_standard | 国际标准 | 311 | 275 |
| L0_wikipedia | Wikipedia | 310 | 132 |
| L1_rustonomicon | Rustonomicon | 234 | 137 |
| L1_rfc | RFCs | 216 | 99 |
| L1_cargo | Cargo Book | 164 | 63 |
| L1_blog | Rust Blog | 138 | 53 |

## 二、各层级权威来源覆盖度

| 层级 | 概念数 | Rust Reference | TRPL | RFCs | 学术 | 课程 | 标准 |
|:---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| L0 元信息层 | 63 | 55 | 56 | 6 | 10 | 4 | 0 |
| L1 基础概念层 | 49 | 45 | 48 | 13 | 34 | 34 | 33 |
| L2 进阶概念层 | 35 | 34 | 32 | 12 | 26 | 28 | 28 |
| L3 高级概念层 | 62 | 47 | 40 | 23 | 35 | 32 | 28 |
| L4 形式化理论层 | 56 | 49 | 38 | 7 | 43 | 46 | 40 |
| L5 对比分析层 | 19 | 18 | 18 | 1 | 18 | 17 | 18 |
| L6 生态工程层 | 123 | 97 | 99 | 12 | 77 | 79 | 78 |
| L7 前沿趋势层 | 65 | 61 | 59 | 25 | 50 | 49 | 50 |

## 三、缺少权威来源的概念（需补全）

| 概念 | 层级 | 当前来源数 | 建议补全来源 |
|:---|:---:|:---:|:---|
| [安全关键 Rust 专题索引](../../06_ecosystem/11_domain_applications/21_safety_critical_topic_index.md) | L6 生态工程层 | 0 | RFCs + 工业/标准来源 |

---

> 本文件由 `scripts/generate_knowledge_topology_atlas.py` 从 `concept/**/*.md` 生成；请勿手工编辑，更新后重新运行生成脚本。
