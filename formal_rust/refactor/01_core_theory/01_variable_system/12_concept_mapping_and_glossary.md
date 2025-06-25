# 12. 术语映射与统一词汇表（12_concept_mapping_and_glossary）

## 12.1 术语映射表

| 概念/术语         | Rust官方术语 | 其他语言/理论术语 | 说明/备注           |
|-------------------|--------------|------------------|---------------------|
| 所有权            | Ownership    | Linear Ownership | 资源唯一性与转移     |
| 借用              | Borrowing    | Reference        | 可变/不可变借用      |
| 生命周期          | Lifetime     | Scope/Region     | 生命周期标注与推断   |
| 泛型              | Generics     | Parametric Types | 类型参数化           |
| trait             | Trait        | Interface        | 行为抽象与约束       |
| 型变              | Variance     | Variance         | 协变/逆变/不变       |
| ...               | ...          | ...              | ...                 |

## 12.2 统一词汇表

- 所有权（Ownership）：资源的唯一归属权，决定变量的生命周期和可用性
- 借用（Borrowing）：对资源的临时访问权，包括可变借用和不可变借用
- 生命周期（Lifetime）：变量或引用在内存中的有效区间
- 泛型（Generics）：支持类型参数化的机制
- trait：定义共享行为的抽象接口
- 型变（Variance）：类型参数在子类型关系中的变化规则
- ...

## 12.3 批判性分析

- 优势：统一术语有助于消除歧义，便于跨文档、跨语言理解
- 局限：部分术语在不同语境下含义不同，需结合上下文灵活解释

## 12.4 交叉引用

- [文档模板与质量标准](11_template_and_quality_standard.md)
- [类型系统分析](../02_type_system/index.md)
- [目录](index.md)

---

> 本文档持续更新，欢迎补充术语映射与词汇表内容。
