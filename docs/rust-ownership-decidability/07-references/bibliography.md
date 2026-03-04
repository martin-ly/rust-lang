# 参考文献

## 目录

- [参考文献](#参考文献)
  - [目录](#目录)
  - [核心文献](#核心文献)
    - [线性逻辑与类型理论](#线性逻辑与类型理论)
    - [Rust形式化](#rust形式化)
    - [验证工具](#验证工具)
    - [类型推断与可判定性](#类型推断与可判定性)
    - [借用检查](#借用检查)
    - [并发与内存模型](#并发与内存模型)
  - [在线资源](#在线资源)
    - [官方文档](#官方文档)
    - [课程材料](#课程材料)
    - [研究项目](#研究项目)
  - [分类索引](#分类索引)
    - [按主题](#按主题)
    - [按复杂度](#按复杂度)

## 核心文献

### 线性逻辑与类型理论

1. **Girard, J.-Y.** (1987). Linear Logic. *Theoretical Computer Science*, 50:1-102.
   - 线性逻辑的开创性论文
   - 奠定了资源敏感逻辑的基础

2. **Girard, J.-Y., Lafont, Y., & Taylor, P.** (1989). *Proofs and Types*. Cambridge Tracts in Theoretical Computer Science.
   - Curry-Howard对应的经典教材
   - 包含线性λ演算

3. **Kopylov, A.P.** (2001). Decidability of Linear Affine Logic. *Information and Computation*, 164(1):173-198.
   - 证明了完整仿射逻辑的可判定性
   - TOWER-Complete复杂度

4. **Pierce, B.C.** (2002). *Types and Programming Languages*. MIT Press.
   - 类型系统标准教材 (TAPL)
   - 涵盖HM类型推断和子类型

5. **Pierce, B.C.** (2004). *Advanced Topics in Types and Programming Languages*. MIT Press.
   - TAPL的进阶续作
   - 包含线性类型和依赖类型

6. **Wadler, P.** (1990). Linear Types can Change the World! In *Programming Concepts and Methods*.
   - 将线性类型引入编程语言
   - 影响Rust设计

### Rust形式化

1. **Jung, R., et al.** (2018). RustBelt: Securing the Foundations of the Rust Programming Language. *POPL*.
   - Rust的第一个完整形式化模型
   - Iris分离逻辑的应用

2. **Jung, R., et al.** (2017). Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning. *POPL*.
   - 高阶并发分离逻辑框架
   - RustBelt的基础

3. **Weiss, A., Patterson, D., & Ahmed, A.** (2020). Oxide: The Essence of Rust. *arXiv:1903.00982*.
   - 接近Rust源代码的形式化
   - 简化但完整的所有权模型

4. **Matsushita, Y., Tsukada, T., & Kobayashi, N.** (2021). RustHorn: CHC-based Verification for Rust Programs. *ACM TOPLAS*.
    - 基于CHC的Rust验证
    - 利用所有权简化内存建模

### 验证工具

1. **Denis, X., Jourdan, J.-H., & Marché, C.** (2022). Creusot: A Foundry for the Deductive Verification of Rust Programs. *ICFEM*.
    - 预言变量编码可变借用
    - Why3后端

2. **Astrauskas, V., et al.** (2022). The Prusti Project: Formal Verification for Rust. *NSV*.
    - 基于Viper的Rust验证器
    - 商用级工具

3. **Lattuada, A., et al.** (2024). Aeneas: Rust Verification by Functional Translation. *ICFP*.
    - 函数式提取方法
    - Lean后端

4. **Lorch, J.R., et al.** (2024). Verus: A Practical Foundation for Systems Verification. *SOSP*.
    - 针对系统代码的验证框架
    - 资源代数支持

### 类型推断与可判定性

1. **Damas, L., & Milner, R.** (1982). Principal type-schemes for functional programs. *POPL*.
    - HM类型推断的经典论文
    - 算法W

2. **Lincoln, P., Mitchell, J., Scedrov, A., & Shankar, N.** (1992). Decision Problems for Propositional Linear Logic. *Annals of Pure and Applied Logic*, 56:239-311.
    - 线性逻辑可判定性结果
    - 各种片段的分类

### 借用检查

1. **Rust RFC 2094: Non-Lexical Lifetimes** (2017).
    - NLL的详细设计文档
    - 基于MIR的借用检查

2. **Pearee, D.J.** (2021). A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust. *TOPLAS*.
    - FR演算
    - 流敏感的类型系统

### 并发与内存模型

1. **Vafeiadis, V., & Narayan, C.** (2013). Relaxed Separation Logic: A Program Logic for C11 Concurrency. *OOPSLA*.
    - 并发程序的分离逻辑
    - 影响Rust并发验证

## 在线资源

### 官方文档

- [The Rust Programming Language](https://doc.rust-lang.org/book/)
- [Rust RFCs](https://rust-lang.github.io/rfcs/)
- [Rust Reference](https://doc.rust-lang.org/reference/)

### 课程材料

- **Stanford CS242**: Programming Languages (Will Crichton)
  - [课程网站](https://cs242.stanford.edu/)
  - 从理论到系统的教学方法

- **CMU 15-411**: Compiler Design
  - 包含Rust相关内容

### 研究项目

- [RustBelt](https://plv.mpi-sws.org/rustbelt/)
- [Iris Project](https://iris-project.org/)
- [Creusot](https://github.com/creusot-rs/creusot)
- [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html)
- [Verus](https://github.com/verus-lang/verus)

## 分类索引

### 按主题

**线性/仿射类型**:

- Girard (1987), Kopylov (2001), Wadler (1990)

**Rust形式化**:

- Jung et al. (2018), Weiss et al. (2020), Pearee (2021)

**验证工具**:

- Denis et al. (2022), Astrauskas et al. (2022), Lattuada et al. (2024), Lorch et al. (2024)

**可判定性理论**:

- Lincoln et al. (1992), Kopylov (2001)

### 按复杂度

**入门级**:

- Pierce (2002) TAPL
- Rust Book

**中级**:

- Girard et al. (1989) Proofs and Types
- Weiss et al. (2020) Oxide

**高级**:

- Jung et al. (2018) RustBelt
- Kopylov (2001) 仿射逻辑可判定性
