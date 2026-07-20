# 递归迭代补充：借用检查器参考文献的形式化论证与证明


## 📊 目录

- [1. 核心论文与书籍](#1-核心论文与书籍)
- [2. 工具文档与设计文档](#2-工具文档与设计文档)
- [3. 学术会议与社区资源](#3-学术会议与社区资源)
- [4. 注释与推荐阅读](#4-注释与推荐阅读)


## 1. 核心论文与书籍

- **Jung, R., et al. (2018). RustBelt: Securing the Foundations of the Rust Programming Language. POPL.**
  - 用分离逻辑形式化证明Rust类型系统与借用检查器的健全性。
- **Weiss, A., et al. (2019). Oxide: The Essence of Rust. arXiv.**
  - 提出简化的Rust核心语言，形式化所有权、借用、生命周期等机制。
- **Polonius: Next-Generation Borrow Checking.**
  - Datalog规则形式化借用与生命周期推理，支持自动化验证与反例生成。
- **Pierce, B. C. (2002). Types and Programming Languages. MIT Press.**
  - 类型系统与形式化验证的经典教材。

## 2. 工具文档与设计文档

- **Rust官方文档**：所有权、借用、生命周期、借用检查器原理与实现。
- **Polonius项目文档**：Datalog规则、自动化验证、反例生成。
- **MIR borrow checker设计文档**：MIR控制流分析、生命周期插桩。
- **Clippy、rust-analyzer等工具文档**：静态分析、自动化测试、IDE集成。

## 3. 学术会议与社区资源

- **POPL、PLDI、OOPSLA等会议论文集**：编程语言理论与安全前沿。
- **Rust官方博客、编译器团队设计文档、社区最佳实践**。
- **GitHub、Zulip等社区讨论与开源实现。**

## 4. 注释与推荐阅读

- 每条文献附简要注释，便于快速定位理论与工程重点。
- 推荐结合论文、工具文档与社区资源，系统理解借用检查器的形式化论证与工程实现。

---

> **递归补充说明**：本节内容将持续迭代完善，欢迎补充最新论文、工具文档、工程案例，推动Rust借用检查器参考文献的形式化论证与证明体系不断进化。
