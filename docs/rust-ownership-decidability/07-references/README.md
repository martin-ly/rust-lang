# 参考文献总览

本目录汇集了与 Rust 所有权系统、类型理论和程序验证相关的全面学术资源。无论您是初学者还是研究人员，都能在这里找到适合的学习材料。

---

## 📚 文档结构

| 文档 | 内容描述 | 适用人群 | 资源数量 |
|------|----------|----------|----------|
| [academic-papers.md](./academic-papers.md) | 学术论文分类整理，涵盖类型系统、所有权理论、形式化验证和 Rust 语言研究 | 研究人员、博士生、高级开发者 | 40+ 篇论文 |
| [books-resources.md](./books-resources.md) | 经典教材、Rust 专著、PL 理论书籍和形式化方法教程 | 各阶段学习者 | 35+ 本书籍 |
| [tools-libraries.md](./tools-libraries.md) | 验证工具、静态分析器、IDE 插件和开发辅助工具 | 工程师、验证从业者 | 30+ 个工具 |
| [online-courses.md](./online-courses.md) | MOOC 课程、学术讲座、工作坊和在线学习路径 | 自学者、学生 | 25+ 门课程 |
| [bibliography.md](./bibliography.md) | 核心参考文献速查，按主题分类的精选文献列表 | 快速查阅者 | 20+ 篇核心文献 |

---

## 🎯 学习路径推荐

### 路径一：Rust 开发者进阶

适合已有 Rust 基础，想深入理解所有权系统的开发者：

```text
1. 阅读 The Rust Programming Language (TRPL) → books-resources.md
2. 学习 Programming Rust (Blandy & Orendorff) → books-resources.md
3. 了解 Rust for Rustaceans → books-resources.md
4. 研读 RustBelt 论文 → academic-papers.md
5. 尝试 Creusot/Prusti 工具 → tools-libraries.md
```

**预计学习时长**: 3-6 个月
**难度等级**: 中级到高级

### 路径二：类型系统研究者

适合对类型理论和形式化语义感兴趣的学术研究者：

```text
1. 精读 Types and Programming Languages (TAPL) → books-resources.md
2. 学习 Advanced Topics in Types and Programming Languages → books-resources.md
3. 阅读线性逻辑经典论文 (Girard 1987) → academic-papers.md
4. 研究 Oxide 和 RustBelt → academic-papers.md
5. 深入学习 Iris 分离逻辑 → academic-papers.md
```

**预计学习时长**: 6-12 个月
**难度等级**: 高级到研究级

### 路径三：程序验证工程师

适合从事形式化验证和静态分析的专业人员：

```text
1. 学习 Software Foundations / Concrete Semantics → books-resources.md
2. 了解 Why3 / Dafny 工具 → tools-libraries.md
3. 研究 Creusot、Prusti、Aeneas 等 Rust 验证器 → tools-libraries.md
4. 阅读 Verus 和 Kani 相关论文 → academic-papers.md
5. 参与实际验证项目 → online-courses.md
```

**预计学习时长**: 6-12 个月
**难度等级**: 高级

### 路径四：系统安全研究员

适合关注内存安全和系统级验证的研究人员：

```text
1. 学习 The Formal Semantics of Programming Languages → books-resources.md
2. 了解 CompCert 和 VST → tools-libraries.md
3. 研究 RustBelt 和 RefinedRust → academic-papers.md
4. 学习并发分离逻辑 → academic-papers.md
5. 探索 Mirai、MIRAI 等分析工具 → tools-libraries.md
```

**预计学习时长**: 9-12 个月
**难度等级**: 高级到研究级

---

## 📊 资源统计

### 按类型统计

| 资源类型 | 数量 | 占比 |
|----------|------|------|
| 学术论文 | 40+ | 25% |
| 书籍教材 | 35+ | 22% |
| 工具库 | 30+ | 19% |
| 在线课程 | 25+ | 16% |
| 核心文献 | 20+ | 13% |
| **总计** | **150+** | **100%** |

### 按难度统计

| 难度等级 | 资源数量 | 适合人群 |
|----------|----------|----------|
| 🟢 入门级 | 50+ | 初学者、学生 |
| 🟡 中级 | 60+ | 有经验的开发者 |
| 🔴 高级 | 40+ | 研究人员、专家 |

---

## 🔍 快速索引

### 核心主题索引

| 主题 | 相关文档 |
|------|----------|
| **线性/仿射类型** | academic-papers.md, books-resources.md |
| **所有权系统** | academic-papers.md, bibliography.md |
| **借用检查** | academic-papers.md, bibliography.md |
| **分离逻辑** | academic-papers.md, books-resources.md |
| **形式化验证** | tools-libraries.md, academic-papers.md |
| **并发验证** | academic-papers.md, bibliography.md |
| **Rust 编译器** | books-resources.md, tools-libraries.md |
| **类型推断** | academic-papers.md, bibliography.md |

### 年度推荐论文

| 年份 | 重要论文 | 影响 |
|------|----------|------|
| 1987 | Girard - Linear Logic | 线性逻辑奠基 |
| 1990 | Wadler - Linear Types can Change the World | 将线性类型引入编程 |
| 2002 | Pierce - TAPL | 类型系统标准教材 |
| 2018 | Jung et al. - RustBelt | Rust 首个完整形式化 |
| 2020 | Weiss et al. - Oxide | 接近源码的 Rust 语义 |
| 2022 | Denis et al. - Creusot | 实用的 Rust 验证工具 |
| 2024 | Lattuada et al. - Aeneas | 基于 Lean 的验证 |

---

## 🎓 学术会议与期刊

### 顶级会议（程序语言方向）

| 会议简称 | 全称 | 主题方向 |
|----------|------|----------|
| **POPL** | Principles of Programming Languages | 程序语言原理 |
| **PLDI** | Programming Language Design and Implementation | 语言设计与实现 |
| **ICFP** | International Conference on Functional Programming | 函数式编程 |
| **OOPSLA** | Object-Oriented Programming, Systems, Languages & Applications | 面向对象与系统 |
| **ESOP** | European Symposium on Programming | 编程欧洲研讨会 |
| **CPP** | Certified Programs and Proofs | 认证程序与证明 |

### 重要期刊

| 期刊简称 | 全称 | 影响因子 |
|----------|------|----------|
| **TOPLAS** | ACM Transactions on Programming Languages and Systems | 高 |
| **JFP** | Journal of Functional Programming | 中 |
| **LMCS** | Logical Methods in Computer Science | 中 |
| **PACMPL** | Proceedings of the ACM on Programming Languages | 高 |

---

## 🛠️ 使用指南

### 如何查找资源

1. **按主题查找**: 使用上述核心主题索引定位相关文档
2. **按难度查找**: 参考难度等级统计选择合适资源
3. **按格式查找**: 根据学习偏好选择书籍、论文、课程或工具

### 如何贡献

欢迎提交 Pull Request 补充新资源。请确保：

- 资源与 Rust 所有权、类型系统或程序验证相关
- 提供准确的元数据（作者、年份、链接）
- 标注适当的难度等级
- 遵循现有文档格式

---

## 📖 推荐阅读顺序

### 初学者（1-3 个月）

1. **The Rust Programming Language** (官方 Rust 书)
2. **Programming Rust** (第 2 版)
3. **Rustlings** 练习
4. **Rust by Example**

### 进阶者（3-6 个月）

1. **Rust for Rustaceans** (进阶 Rust)
2. **Types and Programming Languages** (TAPL)
3. **RustBelt 论文** (初步了解)
4. **Oxide 论文** (深入理解)

### 研究者（6-12 个月）

1. **Advanced Topics in Types and Programming Languages**
2. **Iris 论文系列**
3. **线性逻辑经典论文**
4. **各类验证工具论文**

---

## 🔗 外部链接

### Rust 官方资源

- [The Rust Programming Language](https://doc.rust-lang.org/book/)
- [Rust Reference](https://doc.rust-lang.org/reference/)
- [Rust RFCs](https://rust-lang.github.io/rfcs/)
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
- [The Rust Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)

### 研究项目

- [RustBelt](https://plv.mpi-sws.org/rustbelt/)
- [Iris Project](https://iris-project.org/)
- [Aeneas](https://github.com/AeneasVerif/aeneas)
- [Creusot](https://github.com/creusot-rs/creusot)
- [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html)
- [Verus](https://github.com/verus-lang/verus)
- [Kani](https://github.com/model-checking/kani)

### 学习社区

- [Rust 中文社区](https://rustcc.cn/)
- [Rust 官方论坛](https://users.rust-lang.org/)
- [Reddit r/rust](https://www.reddit.com/r/rust/)
- [Stack Overflow - Rust](https://stackoverflow.com/questions/tagged/rust)

---

## 📅 更新日志

| 日期 | 更新内容 | 版本 |
|------|----------|------|
| 2026-03-04 | 创建完整参考文献体系 | v1.0 |
| 2026-03-04 | 添加学术论文分类整理 | v1.0 |
| 2026-03-04 | 添加书籍和资源索引 | v1.0 |
| 2026-03-04 | 添加工具和库索引 | v1.0 |
| 2026-03-04 | 添加在线课程和学习路径 | v1.0 |

---

## 📝 许可说明

本目录中的资源列表仅供学习和研究使用。各资源的版权归属原作者和出版机构。引用时请遵循学术规范。

---

**维护者**: Rust 所有权可判定性研究项目
**最后更新**: 2026-03-04
