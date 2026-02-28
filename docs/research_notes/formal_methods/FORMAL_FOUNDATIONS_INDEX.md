# 形式化基础索引

> **创建日期**: 2026-02-28
> **最后更新**: 2026-02-28
> **状态**: ✅ 已完成
> **用途**: 形式化方法理论体系的完整导航

---

## 形式化理论体系架构

```text
形式化基础
├── 逻辑基础
│   ├── 命题逻辑
│   ├── 一阶逻辑
│   ├── 高阶逻辑
│   └── 模态逻辑
├── 程序语义
│   ├── 操作语义
│   ├── 公理语义
│   └── 指称语义
├── 验证理论
│   ├── 霍尔逻辑
│   ├── 分离逻辑
│   ├── 最弱前置条件
│   └── 类型理论
├── 证明技术
│   ├── 归纳证明
│   ├── 共归纳证明
│   ├── 反证法
│   └── 构造性证明
└── 方法学
    ├── 形式化方法比较
    ├── 工具选择
    └── 案例研究
```

---

## 文档索引

### 逻辑基础

| 文档 | 内容 | 难度 |
| :--- | :--- | :--- |
| [LOGICAL_FOUNDATIONS.md](LOGICAL_FOUNDATIONS.md) | 命题/一阶/高阶/模态逻辑 | ⭐⭐⭐⭐ |
| [SEPARATION_LOGIC.md](SEPARATION_LOGIC.md) | 分离逻辑、Iris框架 | ⭐⭐⭐⭐⭐ |

### 程序语义

| 文档 | 内容 | 难度 |
| :--- | :--- | :--- |
| [OPERATIONAL_SEMANTICS.md](OPERATIONAL_SEMANTICS.md) | 小步/大步/环境语义 | ⭐⭐⭐⭐ |
| [AXIOMATIC_SEMANTICS.md](AXIOMATIC_SEMANTICS.md) | 霍尔逻辑、WP/SP | ⭐⭐⭐⭐⭐ |

### 证明技术

| 文档 | 内容 | 难度 |
| :--- | :--- | :--- |
| [PROOF_STRATEGIES.md](PROOF_STRATEGIES.md) | 归纳/共归纳/反证/构造 | ⭐⭐⭐⭐ |
| [PROOF_TECHNIQUES_MINDMAP.md](PROOF_TECHNIQUES_MINDMAP.md) | 证明技术思维导图 | ⭐⭐⭐ |

### 方法学

| 文档 | 内容 | 难度 |
| :--- | :--- | :--- |
| [FORMAL_METHODS_COMPARISON.md](FORMAL_METHODS_COMPARISON.md) | 方法比较、工具选择 | ⭐⭐⭐ |
| [CASE_STUDIES.md](CASE_STUDIES.md) | 实际案例分析 | ⭐⭐⭐⭐ |

---

## 学习路径

### 入门路径

```
1. 逻辑基础
   └── LOGICAL_FOUNDATIONS.md §1-2 (命题/一阶逻辑)

2. 操作语义
   └── OPERATIONAL_SEMANTICS.md §1-2 (小步/大步语义)

3. 霍尔逻辑
   └── AXIOMATIC_SEMANTICS.md §1 (霍尔逻辑基础)

4. 简单证明
   └── PROOF_STRATEGIES.md §1 (归纳证明)
```

### 进阶路径

```
1. 分离逻辑
   └── SEPARATION_LOGIC.md

2. 高级语义
   └── OPERATIONAL_SEMANTICS.md §3-4
   └── AXIOMATIC_SEMANTICS.md §2-4

3. 证明技术
   └── PROOF_STRATEGIES.md 全部

4. 方法比较
   └── FORMAL_METHODS_COMPARISON.md
```

### 专家路径

```
1. Iris框架
   └── SEPARATION_LOGIC.md §4

2. Rust特定形式化
   └── type_theory/
   └── formal_methods/ (核心文档)

3. 案例研究
   └── CASE_STUDIES.md

4. 工具实践
   └── coq_skeleton/
   └── VERIFICATION_TOOLS_MATRIX.md
```

---

## 与Rust形式化的联系

### 理论 → 实践映射

| 理论概念 | Rust应用 | 文档位置 |
| :--- | :--- | :--- |
| 分离逻辑 | 所有权/借用 | ownership_model.md, borrow_checker_proof.md |
| 霍尔逻辑 | 函数规范 | AXIOMATIC_SEMANTICS.md §4 |
| 类型理论 | Rust类型系统 | type_theory/ |
| 操作语义 | MIR求值 | OPERATIONAL_SEMANTICS.md §5 |
| 模态逻辑 | 并发安全性 | send_sync_formalization.md |
| 线性逻辑 | 所有权转移 | SEPARATION_LOGIC.md §3.1 |

---

## 工具链索引

### 证明助手

| 工具 | 适用理论 | 学习资源 |
| :--- | :--- | :--- |
| Coq | 高阶逻辑、分离逻辑 | coq_skeleton/ |
| Isabelle | 高阶逻辑 | 外部资源 |
| Lean | 依赖类型 | Aeneas项目 |

### 验证工具

| 工具 | 方法 | 适用场景 |
| :--- | :--- | :--- |
| Kani | 模型检测 | 快速属性检查 |
| Creusot | 演绎验证 | 函数正确性 |
| Prusti | Viper框架 | 契约验证 |
| MIRAI | 抽象解释 | 静态分析 |

---

## 快速参考

### 常用符号

| 符号 | 含义 | 使用场景 |
| :--- | :--- | :--- |
| ⊢ | 推导 | 逻辑推理 |
| ⊨ | 满足 | 语义关系 |
| →* | 多步归约 | 操作语义 |
| {P} C {Q} | 霍尔三元组 | 程序规范 |
| P * Q | 分离合取 | 分离逻辑 |
| wp(C,Q) | 最弱前置条件 | 验证条件 |

### 关键定理

| 定理 | 位置 | 重要性 |
| :--- | :--- | :--- |
| 类型安全 | type_system_foundations.md | ⭐⭐⭐⭐⭐ |
| 所有权唯一性 | ownership_model.md | ⭐⭐⭐⭐⭐ |
| 借用无竞争 | borrow_checker_proof.md | ⭐⭐⭐⭐⭐ |
| 进展性 | type_system_foundations.md | ⭐⭐⭐⭐⭐ |
| 保持性 | type_system_foundations.md | ⭐⭐⭐⭐⭐ |

---

## 外部资源

### 经典教材

| 书名 | 作者 | 适用范围 |
| :--- | :--- | :--- |
| Types and Programming Languages | Pierce | 类型理论 |
| Software Foundations | Pierce et al. | Coq入门 |
| Iris from the Ground Up | Jung et al. | 分离逻辑 |
| Concrete Semantics | Nipkow et al. | Isabelle |

### 在线资源

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Iris Project](https://iris-project.org/)
- [Rust Formal Methods Working Group](https://rust-lang.github.io/rust-formal-methods/)

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 形式化基础索引完成
