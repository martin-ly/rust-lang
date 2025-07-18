
# 附录：标准化补全区块

## 形式化定义

- **生命周期集合**：
  $$
  \mathbb{L} = \{\alpha_1, \alpha_2, ...\}
  $$
  其中 $\alpha$ 表示生命周期参数。
- **生命周期包含关系**：
  $$
  \alpha_1 \supseteq \alpha_2 \iff \text{\'a1 outlives \'a2}
  $$
- **借用生命周期约束**：
  $$
  \text{for<\'a>}\ fn(x: &\'a T) -> &\'a U
  $$

## 定理与证明

- **定理 1（生命周期推导正确性）**：
  生命周期推导算法能正确生成所有必要的生命周期约束。
- **定理 2（生命周期包含传递性）**：
  $$
  \forall \alpha_1, \alpha_2, \alpha_3.\ (\alpha_1 \supseteq \alpha_2 \land \alpha_2 \supseteq \alpha_3) \implies \alpha_1 \supseteq \alpha_3
  $$
- **定理 3（生命周期多态保持）**：
  生命周期多态函数在所有生命周期实例下均安全。
- **证明思路**：
  采用生命周期约束生成与传递性归纳，详见生命周期系统形式化理论。

## 符号表

| 符号         | 含义           | 备注 |
|--------------|----------------|------|
| $\mathbb{L}$ | 生命周期集合   | 见全局符号体系 |
| $\alpha$     | 生命周期参数   |      |
| $\supseteq$  | 包含关系       | 生命周期包含 |
| $\subseteq$  | 被包含关系     |      |
| $\cap$       | 交集           | 生命周期重叠 |
| $\emptyset$  | 空集           | 生命周期无交集 |
| $\text{for<\'a>}$ | 生命周期多态 |      |

## 术语表

- **生命周期（Lifetime）**：引用或值的有效作用域。
- **生命周期参数（Lifetime Parameter）**：用于泛型约束的生命周期标识符。
- **生命周期包含（Outlives）**：一个生命周期包含另一个生命周期的关系。
- **生命周期推导（Lifetime Inference）**：自动推断生命周期约束的过程。
- **生命周期多态（Lifetime Polymorphism）**：函数或类型对生命周期参数的泛化。
- **悬垂引用（Dangling Reference）**：生命周期已结束但仍被访问的引用。
- **借用检查器（Borrow Checker）**：静态分析生命周期安全性的编译器组件。

> 本区块为标准化模板，后续可根据实际内容补充详细证明、符号扩展与术语解释。
