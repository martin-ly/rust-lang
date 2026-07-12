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
| Lx_other | 其他 | 5377 | 434 |
| L1_specification | Rust Reference | 1028 | 417 |
| L1_trpl | TRPL | 818 | 405 |
| L1_github | Rust GitHub | 507 | 181 |
| L3_course | 顶尖课程 | 414 | 304 |
| L2_academic | 学术论文 | 414 | 299 |
| L1_std | std docs | 390 | 151 |
| L5_standard | 国际标准 | 329 | 289 |
| L0_wikipedia | Wikipedia | 308 | 131 |
| L1_rustonomicon | Rustonomicon | 237 | 140 |
| L1_rfc | RFCs | 198 | 89 |
| L1_cargo | Cargo Book | 163 | 62 |
| L1_blog | Rust Blog | 127 | 44 |

## 二、各层级权威来源覆盖度

| 层级 | 概念数 | Rust Reference | TRPL | RFCs | 学术 | 课程 | 标准 |
|:---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| L0 元信息层 | 63 | 55 | 56 | 6 | 10 | 4 | 0 |
| L1 基础概念层 | 55 | 51 | 54 | 13 | 40 | 40 | 39 |
| L2 进阶概念层 | 38 | 37 | 35 | 12 | 29 | 31 | 31 |
| L3 高级概念层 | 60 | 50 | 43 | 20 | 35 | 35 | 31 |
| L4 形式化理论层 | 53 | 50 | 39 | 6 | 42 | 46 | 41 |
| L5 对比分析层 | 19 | 19 | 19 | 1 | 19 | 18 | 19 |
| L6 生态工程层 | 115 | 97 | 100 | 11 | 77 | 80 | 79 |
| L7 前沿趋势层 | 61 | 58 | 59 | 20 | 47 | 50 | 49 |

## 三、缺少权威来源的概念（需补全）

| 概念 | 层级 | 当前来源数 | 建议补全来源 |
|:---|:---:|:---:|:---|

---

> 本文件由 `scripts/generate_knowledge_topology_atlas.py` 从 `concept/**/*.md` 生成；请勿手工编辑，更新后重新运行生成脚本。
