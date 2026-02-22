# Rust形式化方法学习路径

> **创建日期**: 2026-02-23
> **目标**: 为不同背景的学习者提供渐进式学习路径
> **级别**: L1为主，L2为辅

---

## 学习路径总览

```text
                        学习路径全景
                              │
        ┌─────────────────────┼─────────────────────┐
        │                     │                     │
   【初学者】            【进阶者】            【专家】
   (工程师)              (核心开发者)          (研究者)
        │                     │                     │
   ├─为什么Rust安全      ├─借用检查原理       ├─分离逻辑
   ├─所有权直觉          ├─类型系统形式化     ├─机器证明
   ├─生命周期理解        ├─并发模型           ├─国际对标
   └─常见模式            └─设计模式证明       └─工具开发
```

---

## 路径一：初学者（2-4周）

### 目标受众

- 有编程经验，想了解Rust安全机制
- 准备采用Rust的工程团队
- 技术决策者

### 学习目标

- 理解Rust为什么安全（直觉层面）
- 能够解释所有权、借用、生命周期
- 避免常见错误

### 学习路径

#### 第1周：所有权与借用

**Day 1-2: 所有权概念**

- 阅读: [形式化概念百科](./FORMAL_CONCEPTS_ENCYCLOPEDIA.md) §1.1
- 实践: 编写Move/Copy示例代码
- 检验: 能解释"为什么转移后原变量不能用"

**Day 3-4: 借用规则**

- 阅读: [形式化概念百科](./FORMAL_CONCEPTS_ENCYCLOPEDIA.md) §1.2
- 实践: 编写&和&mut示例
- 检验: 能解释"为什么可变和不可变借用不能共存"

**Day 5-7: 生命周期直觉**

- 阅读: [形式化概念百科](./FORMAL_CONCEPTS_ENCYCLOPEDIA.md) §1.3, §3
- 实践: 解决编译器生命周期错误
- 检验: 能读懂简单生命周期标注

#### 第2周：类型系统与安全保证

**Day 1-2: 类型安全**

- 阅读: [定理汇编](./THEOREMS_AND_PROOF_STRATEGIES.md) §3
- 理解: 什么是"良类型程序不会崩溃"

**Day 3-4: Send与Sync**

- 阅读: [形式化概念百科](./FORMAL_CONCEPTS_ENCYCLOPEDIA.md) §4.1
- 实践: 判断类型是否Send/Sync

**Day 5-7: 反例学习**

- 阅读: [反例集](#) §A
- 理解: 编译器阻止哪些错误

#### 第3-4周：实践与深化

- 阅读核心库文档
- 完成[Rustlings](https://github.com/rust-lang/rustlings)练习
- 阅读[官方Book](https://doc.rust-lang.org/book/)

### 学习成果检查

- [ ] 能向同事解释所有权系统
- [ ] 能解决80%的编译器错误
- [ ] 能判断代码是否线程安全

---

## 路径二：进阶者（4-8周）

### 目标受众

- Rust核心开发者
- 想深入理解编译器原理
- 准备贡献Rust生态

### 学习目标

- 理解借用检查的形式化原理
- 理解类型系统的形式化保证
- 能够阅读形式化定义

### 学习路径

#### 第1-2周：形式化基础

**主题**: 形式化方法入门

- 阅读: [认知论证框架](./COGNITIVE_ARGUMENTATION_FRAMEWORK.md)
- 学习: 如何阅读形式化定义
- 理解: L1/L2/L3的区别

#### 第3-4周：核心定理

**主题**: 所有权与借用的形式化

- 阅读: [定理汇编](./THEOREMS_AND_PROOF_STRATEGIES.md) §1, §2
- 深入: T-OW2 (所有权唯一性) 证明思路
- 深入: T-BR1 (数据竞争自由) 证明思路

#### 第5-6周：类型系统

**主题**: 类型安全的形式化

- 阅读: [定理汇编](./THEOREMS_AND_PROOF_STRATEGIES.md) §3
- 理解: 进展性与保持性
- 学习: 型变规则的形式化

#### 第7-8周：并发与异步

**主题**: 并发安全的形式化

- 阅读: [形式化概念百科](./FORMAL_CONCEPTS_ENCYCLOPEDIA.md) §4
- 理解: Send/Sync的形式化定义
- 学习: Future与Pin的形式化

### 学习成果检查

- [ ] 能读懂形式化定义
- [ ] 能解释核心定理的直觉
- [ ] 能分析借用检查行为

---

## 路径三：专家（8-24周）

### 目标受众

- 形式化方法研究者
- Rust编译器开发者
- 验证工具开发者

### 学习目标

- 理解L3机器证明
- 掌握分离逻辑
- 能够开发验证工具

### 学习路径

#### 第1-4周：Coq基础

**资源**: Software Foundations Vol 1-2

- 学习Coq证明助手
- 掌握归纳证明
- 完成基础练习

#### 第5-8周：核心定理L3证明

**主题**: 阅读并理解Coq骨架文件

- 阅读: OWNERSHIP_UNIQUENESS.v
- 阅读: BORROW_DATARACE_FREE.v
- 阅读: TYPE_SAFETY.v

#### 第9-12周：分离逻辑与Iris

**资源**: Iris教程，RustBelt论文

- 学习分离逻辑基础
- 理解资源代数
- 阅读RustBelt核心证明

#### 第13-16周：工具开发

**主题**: 验证工具

- 学习Aeneas使用
- 学习Kani模型检查
- 开发简单验证工具

#### 第17-24周：研究与贡献

- 阅读最新研究论文
- 贡献Coq证明
- 发表研究成果

---

## 学习资源索引

### 必读文档

| 文档 | 难度 | 路径 | 说明 |
| :--- | :---: | :--- | :--- |
| [形式化概念百科](./FORMAL_CONCEPTS_ENCYCLOPEDIA.md) | ⭐⭐ | 全部 | 核心概念定义 |
| [定理汇编](./THEOREMS_AND_PROOF_STRATEGIES.md) | ⭐⭐⭐ | 进阶+专家 | 证明思路 |
| [认知论证框架](./COGNITIVE_ARGUMENTATION_FRAMEWORK.md) | ⭐⭐ | 全部 | 方法论 |

### 思维导图

| 导图 | 难度 | 用途 |
| :--- | :---: | :--- |
| 所有权概念族谱 | ⭐⭐ | 理解所有权系统 |
| 证明技术概念族谱 | ⭐⭐⭐ | 了解证明方法 |
| 分布式概念族谱 | ⭐⭐⭐ | 分布式模式 |

### 决策树

| 决策树 | 用途 |
| :--- | :--- |
| 并发模型选型 | 技术选型 |
| 分布式架构选型 | 架构设计 |
| 工作流引擎选型 | 系统设计 |

### 外部资源

**官方**:

- [The Rust Programming Language](https://doc.rust-lang.org/book/)
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
- [The Rust Reference](https://doc.rust-lang.org/reference/)

**形式化方法**:

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Iris Project](https://iris-project.org/)
- [RustBelt](https://plv.mpi-sws.org/rustbelt/)

---

## 学习检验

### 初学者检验

**问题1**: 为什么这段代码编译失败？

```rust
let x = String::from("hello");
let y = x;
println!("{}", x);
```

**问题2**: Send和Sync有什么区别？

### 进阶者检验

**问题3**: 解释T-BR1定理的核心思想。

**问题4**: 什么是进展性定理？为什么重要？

### 专家检验

**问题5**: 如何在Iris中表示所有权？

**问题6**: 证明T-OW2的关键步骤是什么？

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-23
**用途**: 指导学习者渐进掌握Rust形式化方法
