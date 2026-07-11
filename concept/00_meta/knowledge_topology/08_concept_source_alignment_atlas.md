# 概念-权威来源对齐图谱（Concept-Source Alignment Atlas）

> **EN**: Concept-Source Alignment Atlas
> **Summary**: 每个核心概念与国际化权威来源的对齐：Rust Reference、TRPL、RFCs、学术、课程、工业、标准。
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、权威来源覆盖统计

| 来源层级 | 来源类型 | 引用次数 | 涉及概念数 |
|:---|:---|:---:|:---:|
| Lx_other | 其他 | 5363 | 436 |
| L1_specification | Rust Reference | 1036 | 418 |
| L1_trpl | TRPL | 822 | 408 |
| L1_github | Rust GitHub | 517 | 179 |
| L3_course | 顶尖课程 | 417 | 307 |
| L2_academic | 学术论文 | 417 | 302 |
| L1_std | std docs | 393 | 151 |
| L5_standard | 国际标准 | 332 | 292 |
| L0_wikipedia | Wikipedia | 310 | 133 |
| L1_rustonomicon | Rustonomicon | 239 | 141 |
| L1_rfc | RFCs | 200 | 87 |
| L1_cargo | Cargo Book | 163 | 62 |
| L1_blog | Rust Blog | 128 | 45 |

## 二、各层级权威来源覆盖度

| 层级 | 概念数 | Rust Reference | TRPL | RFCs | 学术 | 课程 | 标准 |
|:---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| L0 元信息层 | 63 | 55 | 56 | 6 | 10 | 4 | 0 |
| L1 基础概念层 | 55 | 51 | 54 | 13 | 40 | 40 | 39 |
| L2 进阶概念层 | 40 | 37 | 36 | 12 | 28 | 30 | 30 |
| L3 高级概念层 | 59 | 49 | 44 | 19 | 36 | 36 | 32 |
| L4 形式化理论层 | 53 | 51 | 40 | 6 | 43 | 47 | 42 |
| L5 对比分析层 | 19 | 19 | 19 | 1 | 19 | 18 | 19 |
| L6 生态工程层 | 115 | 98 | 101 | 11 | 78 | 81 | 80 |
| L7 前沿趋势层 | 61 | 58 | 58 | 19 | 48 | 51 | 50 |

## 三、缺少权威来源的概念（需补全）

| 概念 | 层级 | 当前来源数 | 建议补全来源 |
|:---|:---:|:---:|:---|
| [生命周期高级主题：从 HRTB 到自引用类型](../../02_intermediate/00_traits/18_lifetimes_advanced.md) | L2 进阶概念层 | 1 | Rust Reference / TRPL |
| [Safety Tags（安全标签）预览](../../07_future/03_preview_features/31_safety_tags_preview.md) | L7 前沿趋势层 | 1 | RFCs + 工业/标准来源 |


---

