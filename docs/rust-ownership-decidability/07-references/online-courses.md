# 在线课程和学习路径

本文件整理了与 Rust 编程、程序语言理论、类型系统和形式化验证相关的在线课程、学术讲座、工作坊和学习路径。每门课程都标注了难度等级、时长和适用人群。

---

## 📑 目录

- [在线课程和学习路径](#在线课程和学习路径)
  - [📑 目录](#-目录)
  - [Rust 编程课程](#rust-编程课程)
    - [入门级课程](#入门级课程)
    - [进阶级课程](#进阶级课程)
    - [高级课程](#高级课程)
  - [程序语言理论课程](#程序语言理论课程)
    - [大学课程](#大学课程)
    - [在线 MOOC](#在线-mooc)
    - [经典教材配套](#经典教材配套)
  - [类型系统课程](#类型系统课程)
    - [类型理论](#类型理论)
    - [依赖类型](#依赖类型)
  - [形式化验证课程](#形式化验证课程)
    - [验证基础](#验证基础)
    - [模型检测](#模型检测)
    - [Rust 专用验证](#rust-专用验证)
  - [学术讲座和研讨会](#学术讲座和研讨会)
    - [PL 会议讲座](#pl-会议讲座)
    - [夏季学校和讲座](#夏季学校和讲座)
    - [在线讲座系列](#在线讲座系列)
  - [工作坊和训练营](#工作坊和训练营)
    - [动手工作坊](#动手工作坊)
    - [黑客松和挑战](#黑客松和挑战)
  - [学习路径规划](#学习路径规划)
    - [路径一：Rust 全栈工程师（6-12 个月）](#路径一rust-全栈工程师6-12-个月)
    - [路径二：PL 理论研究者（12-24 个月）](#路径二pl-理论研究者12-24-个月)
    - [路径三：形式化验证工程师（12-18 个月）](#路径三形式化验证工程师12-18-个月)
    - [路径四：系统安全研究员（18-24 个月）](#路径四系统安全研究员18-24-个月)
  - [📊 课程统计](#-课程统计)
    - [按类别统计](#按类别统计)
    - [按难度统计](#按难度统计)
    - [按平台统计](#按平台统计)
  - [🎯 推荐学习顺序](#-推荐学习顺序)
    - [快速入门（3 个月）](#快速入门3-个月)
    - [系统学习（12 个月）](#系统学习12-个月)
  - [🔗 相关资源](#-相关资源)

---

## Rust 编程课程

### 入门级课程

| 课程名称 | 平台 | 难度 | 时长 | 特点 | 链接 |
|----------|------|------|------|------|------|
| **The Rust Programming Language** | 官方文档 | 🟢 | 自定进度 | 官方权威教程，Rust 圣经 | [官方](https://doc.rust-lang.org/book/) |
| **Rustlings** | GitHub | 🟢 | 10-20 小时 | 小练习集合，边做边学 | [GitHub](https://github.com/rust-lang/rustlings) |
| **Rust By Example** | 官方文档 | 🟢 | 自定进度 | 实例驱动学习 | [官方](https://doc.rust-lang.org/rust-by-example/) |
| **Comprehensive Rust** | Google | 🟢 | 4 天 | Google 内部培训开源 | [GitHub](https://github.com/google/comprehensive-rust) |
| **Rust 101** | 鹿特丹大学 | 🟢 | 完整学期 | 大学水平入门课程 | [GitHub](https://github.com/tweedegolf/101-rs) |
| **Easy Rust** | YouTube/Book | 🟢 | 自定进度 | 简单英语，适合非母语者 | [YouTube](https://www.youtube.com/playlist?list=PLfllocyHVgsRwLkTAhG0E-2QxCf-ozBkk) |
| **Rust Crash Course** | Traversy Media | 🟢 | 2 小时 | 快速入门视频 | [YouTube](https://www.youtube.com/watch?v=zF34dRivLOw) |
| **Take your first steps with Rust** | Microsoft Learn | 🟢 | 3 小时 | 微软官方学习路径 | [Microsoft](https://docs.microsoft.com/en-us/learn/paths/rust-first-steps/) |

### 进阶级课程

| 课程名称 | 平台 | 难度 | 时长 | 特点 | 链接 |
|----------|------|------|------|------|------|
| **Programming Rust** | O'Reilly | 🟡 | 自定进度 | 深入系统编程 | [O'Reilly](https://www.oreilly.com/library/view/programming-rust-2nd/9781492052586/) |
| **Zero To Production In Rust** | 独立 | 🟡 | 自定进度 | 生产级 Rust 开发 | [Zero2Prod](https://www.zero2prod.com/) |
| **Rust for the Polyglot Programmer** | NDC | 🟡 | 3 小时 | 面向有经验开发者 | [NDC](https://www.ndcconferences.com/) |
| **Building Web Apps with Rust** | Udemy | 🟡 | 10 小时 | Web 开发实战 | [Udemy](https://www.udemy.com/) |
| **Async Rust** | 官方文档 | 🟡 | 自定进度 | 异步编程深入 | [官方](https://rust-lang.github.io/async-book/) |
| **Tokio Tutorial** | Tokio | 🟡 | 自定进度 | 异步运行时学习 | [Tokio](https://tokio.rs/tokio/tutorial) |
| **WebAssembly with Rust** | Rust and WebAssembly | 🟡 | 自定进度 | WASM 开发 | [GitHub](https://rustwasm.github.io/book/) |
| **Rust Embedded** | 官方文档 | 🔴 | 自定进度 | 嵌入式开发 | [官方](https://doc.rust-lang.org/stable/embedded-book/) |

### 高级课程

| 课程名称 | 平台 | 难度 | 时长 | 特点 | 链接 |
|----------|------|------|------|------|------|
| **The Rustonomicon** | 官方文档 | 🔴 | 自定进度 | Unsafe Rust 和高级主题 | [官方](https://doc.rust-lang.org/nomicon/) |
| **Rust for Rustaceans** | 独立 | 🔴 | 自定进度 | 高级 Rust 模式 | [No Starch](https://rust-for-rustaceans.com/) |
| **Rust Internals** | YouTube | 🔴 | 系列视频 | 编译器内部实现 | [YouTube](https://www.youtube.com/c/JonGjengset) |
| **Crust of Rust** | YouTube | 🔴 | 系列视频 | 高级主题系列 | [YouTube](https://www.youtube.com/playlist?list=PLqbS7AVVErFiWDOAVrPt7aYmnuuOLYvOa) |
| **Rust Concurrency** | 官方文档 | 🔴 | 自定进度 | 并发编程深入 | [官方](https://doc.rust-lang.org/nomicon/) |
| **Unsafe Rust Guidelines** | 官方文档 | 🔴 | 自定进度 | Unsafe 代码指南 | [官方](https://rust-lang.github.io/unsafe-code-guidelines/) |

---

## 程序语言理论课程

### 大学课程

| 课程名称 | 学校 | 难度 | 时长 | 特点 | 链接 |
|----------|------|------|------|------|------|
| **CS 242: Programming Languages** | Stanford | 🔴 | 完整学期 | 从理论到系统的教学 | [Stanford](https://cs242.stanford.edu/) |
| **CS 421: Programming Languages** | UIUC | 🔴 | 完整学期 | 经典 PL 课程 | [UIUC](https://courses.engr.illinois.edu/cs421/) |
| **15-312: Principles of Programming Languages** | CMU | 🔴 | 完整学期 | 理论为主 | [CMU](https://www.cs.cmu.edu/~rwh/courses/ppl/) |
| **CS 152: Programming Languages** | Berkeley | 🔴 | 完整学期 | 伯克利经典课程 | [Berkeley](https://inst.eecs.berkeley.edu/~cs152/) |
| **CS 252r: Advanced Topics in PL** | Harvard | 🔴 | 完整学期 | 研究生水平 | [Harvard](https://pl.seas.harvard.edu/) |
| **CS 330: Programming Languages** | Purdue | 🔴 | 完整学期 | 类型系统和语义 | [Purdue](https://www.cs.purdue.edu/homes/suresh/330-Spring2023/) |
| **CSE 341: Programming Languages** | UW | 🔴 | 完整学期 | SML, Racket, Ruby | [UW](https://courses.cs.washington.edu/courses/cse341/) |
| **CS 51: Abstraction and Design** | Harvard | 🟡 | 完整学期 | 函数式编程入门 | [Harvard](https://cs51.io/) |

### 在线 MOOC

| 课程名称 | 平台 | 难度 | 时长 | 特点 | 链接 |
|----------|------|------|------|------|------|
| **Programming Languages** | Coursera (UW) | 🟡 | 10 周 | SML, Racket, Ruby | [Coursera](https://www.coursera.org/learn/programming-languages) |
| **Programming Languages Part B** | Coursera (UW) | 🟡 | 3 周 | Racket 深入 | [Coursera](https://www.coursera.org/learn/programming-languages-part-b) |
| **Programming Languages Part C** | Coursera (UW) | 🟡 | 3 周 | Ruby 和 OOP | [Coursera](https://www.coursera.org/learn/programming-languages-part-c) |
| **Compilers** | Coursera (Stanford) | 🔴 | 10 周 | 编译器设计与实现 | [Coursera](https://www.coursera.org/learn/compilers) |
| **Introduction to Programming with MATLAB** | Coursera | 🟢 | 9 周 | 编程基础 | [Coursera](https://www.coursera.org/learn/matlab) |
| **Build a Modern Computer from First Principles** | Coursera (Hebrew U) | 🟡 | 6 周 | 从 Nand 到 Tetris | [Coursera](https://www.coursera.org/learn/build-a-computer) |

### 经典教材配套

| 课程/资源 | 配套书籍 | 难度 | 特点 | 链接 |
|-----------|----------|------|------|------|
| **TAPL Resources** | Types and Programming Languages | 🟡 | Pierce 教材配套资源 | [UPenn](https://www.cis.upenn.edu/~bcpierce/tapl/) |
| **Software Foundations** | 同名书籍 | 🔴 | Coq 证明基础 | [UPenn](https://softwarefoundations.cis.upenn.edu/) |
| **Concrete Semantics** | 同名书籍 | 🔴 | Isabelle 语义学 | [TUM](http://concrete-semantics.org/) |
| **Programming and Proving in Isabelle/HOL** | 官方教程 | 🔴 | Isabelle 入门 | [TUM](https://isabelle.in.tum.de/doc/prog-prove.pdf) |
| **PLFA - Programming Language Foundations in Agda** | 在线书籍 | 🔴 | Agda 类型理论 | [GitHub](https://plfa.github.io/) |

---

## 类型系统课程

### 类型理论

| 课程名称 | 讲师/机构 | 难度 | 时长 | 特点 | 链接 |
|----------|-----------|------|------|------|------|
| **Category Theory** | Bartosz Milewski | 🟡 | 系列视频 | 程序员视角范畴论 | [YouTube](https://www.youtube.com/playlist?list=PLbgaMIhjbmEnaH_LTkxLI7FMa2HsnawM_) |
| **Category Theory for Programmers** | Bartosz Milewski | 🟡 | 系列文章/视频 | 完整的范畴论课程 | [GitHub](https://github.com/hmemcpy/milewski-ctfp-pdf) |
| **Type Theory Foundations** | Robert Harper (CMU) | 🔴 | 完整学期 | 类型理论基础 | [CMU](https://www.cs.cmu.edu/~rwh/courses/ttf/) |
| **Homotopy Type Theory** | 多人 | 🔴 | 完整学期 | HoTT 夏季学校 | [HoTT](https://homotopytypetheory.org/2019/12/07/hott-2019/) |
| **Linear Logic** | 多个大学 | 🔴 | 不定 | 线性逻辑专题 | [各大学网站] |
| **Advanced Topics in Type Theory** | 多个研究机构 | 🔴 | 不定 | 高级类型理论 | [各研究机构] |

### 依赖类型

| 课程名称 | 讲师/机构 | 难度 | 时长 | 特点 | 链接 |
|----------|-----------|------|------|------|------|
| **Theorem Proving in Lean 4** | Jeremy Avigad et al. | 🔴 | 自定进度 | Lean 4 官方教程 | [Lean](https://lean-lang.org/theorem_proving_in_lean4/) |
| **Functional Programming in Lean** | David Christiansen | 🔴 | 自定进度 | Lean 4 函数式编程 | [Lean](https://lean-lang.org/functional_programming_in_lean/) |
| **Programming Language Foundations in Agda** | Philip Wadler et al. | 🔴 | 自定进度 | Agda 入门 | [GitHub](https://plfa.github.io/) |
| **Certified Programming with Dependent Types** | Adam Chlipala | 🔴 | 自定进度 | Coq 高级编程 | [MIT](http://adam.chlipala.net/cpdt/) |
| **Interactive Theorem Proving** | 多人 | 🔴 | 不定 | ITP 系列会议教程 | [ITP](https://itp-conference.org/) |
| **Proof Assistants: History and Future** | 多人 | 🔴 | 不定 | 证明助手发展 | [各会议] |

---

## 形式化验证课程

### 验证基础

| 课程名称 | 学校/机构 | 难度 | 时长 | 特点 | 链接 |
|----------|-----------|------|------|------|------|
| **Formal Methods of Software Design** | UT Austin | 🔴 | 完整学期 | Dijkstra 方法 | [UT Austin](https://www.cs.utexas.edu/~eberdou/cs439/) |
| **Program Verification** | TU Munich | 🔴 | 完整学期 | Isabelle 验证 | [TUM](https://www21.in.tum.de/teaching/progver/WS22/) |
| **Software Foundations** | UPenn | 🟡 | 完整学期 | Coq 基础系列 | [UPenn](https://softwarefoundations.cis.upenn.edu/) |
| **Functional Programming in Coq** | DeepSpec | 🔴 | 不定 | DeepSpec 项目课程 | [DeepSpec](http://www.deepspec.org/) |
| **Verified Software** | MIT | 🔴 | 完整学期 | 软件验证高级课程 | [MIT](https://6826.csail.mit.edu/) |
| **Separation Logic** | Imperial College | 🔴 | 不定 | 分离逻辑专题 | [Imperial](https://www.doc.ic.ac.uk/~jv/verification/) |

### 模型检测

| 课程名称 | 学校/机构 | 难度 | 时长 | 特点 | 链接 |
|----------|-----------|------|------|------|------|
| **Model Checking** | RWTH Aachen | 🔴 | 完整学期 | 模型检测原理 | [RWTH](https://moves.rwth-aachen.de/teaching/ss-18/model-checking/) |
| **Automated Verification** | 多个大学 | 🔴 | 不定 | 自动验证技术 | [各大学] |
| **Temporal Logic and Model Checking** | CMU | 🔴 | 完整学期 | 时序逻辑与模型检测 | [CMU](https://www.cs.cmu.edu/~emc/15414-f20/) |
| **Formal Verification of Systems Software** | Stanford | 🔴 | 完整学期 | 系统软件验证 | [Stanford](https://web.stanford.edu/class/cs259/) |

### Rust 专用验证

| 课程/资源 | 讲师/机构 | 难度 | 时长 | 特点 | 链接 |
|-----------|-----------|------|------|------|------|
| **Verus Tutorial** | Verus 团队 | 🔴 | 自定进度 | Verus 验证器入门 | [Verus](https://github.com/verus-lang/verus) |
| **Creusot Tutorial** | Creusot 团队 | 🔴 | 自定进度 | Creusot 验证器教程 | [Creusot](https://github.com/creusot-rs/creusot) |
| **Aeneas Tutorial** | Aeneas 团队 | 🔴 | 自定进度 | Aeneas 验证教程 | [Aeneas](https://github.com/AeneasVerif/aeneas) |
| **Rust Verification Workshop** | 多个机构 | 🔴 | 不定 | RV 系列研讨会 | [RV](https://sites.google.com/view/rustverify2024) |
| **Kani Documentation** | Kani 团队 | 🔴 | 自定进度 | Kani 验证器文档 | [Kani](https://model-checking.github.io/kani/) |

---

## 学术讲座和研讨会

### PL 会议讲座

| 会议/活动 | 主题 | 难度 | 特点 | 链接 |
|-----------|------|------|------|------|
| **POPL** | 程序语言原理 | 🔴 | 顶级 PL 会议 | [ACM](https://popl24.sigplan.org/) |
| **PLDI** | 程序语言设计与实现 | 🔴 | 顶级 PL 会议 | [ACM](https://pldi24.sigplan.org/) |
| **ICFP** | 函数式编程 | 🔴 | 函数式编程顶级 | [ACM](https://icfp24.sigplan.org/) |
| **OOPSLA** | 面向对象与系统 | 🔴 | 系统与语言设计 | [ACM](https://oopsla24.sigplan.org/) |
| **ESOP** | 编程欧洲研讨会 | 🔴 | 欧洲 PL 会议 | [ETAPS](https://etaps.org/) |
| **CPP** | 认证程序与证明 | 🔴 | 形式化证明 | [ACM](https://popl24.sigplan.org/home/CPP-2024) |
| **ICSE** | 软件工程 | 🔴 | 软件工程顶级 | [ACM](https://conf.researchr.org/home/icse-2024) |

### 夏季学校和讲座

| 活动名称 | 主题 | 难度 | 时间 | 链接 |
|----------|------|------|------|------|
| **OPLSS** | 程序语言夏季学校 | 🔴 | 每年夏季 | [OPLSS](https://www.cs.uoregon.edu/research/summerschool/) |
| **DeepSpec Summer School** | 深度规约 | 🔴 | 不定期 | [DeepSpec](http://www.deepspec.org/) |
| **HoTT Summer School** | 同伦类型论 | 🔴 | 不定期 | [HoTT](https://homotopytypetheory.org/) |
| **Proof Theory Summer School** | 证明论 | 🔴 | 不定期 | [各大学] |
| **Concurrency Theory School** | 并发理论 | 🔴 | 不定期 | [各大学] |
| **Separation Logic Workshops** | 分离逻辑 | 🔴 | 不定期 | [各研究机构] |

### 在线讲座系列

| 系列名称 | 主题 | 难度 | 平台 | 链接 |
|----------|------|------|------|------|
| **Programming Languages Podcast** | PL 播客 | 🟡 | 音频 | [各种平台] |
| **The Type Theory Podcast** | 类型理论 | 🔴 | 音频 | [各种平台] |
| **LambdaConf Talks** | 函数式编程 | 🟡 | YouTube | [YouTube](https://www.youtube.com/c/LambdaConf) |
| **RustConf Talks** | Rust 会议 | 🟡 | YouTube | [YouTube](https://www.youtube.com/channel/UCaYhcUwRBNscFNUKTjgPFiA) |
| **RustNation** | Rust 会议 | 🟡 | 不定 | [RustNation](https://www.rustnationuk.com/) |
| **RustLab** | Rust 会议 | 🟡 | YouTube | [YouTube](https://www.youtube.com/c/RustLabConference) |

---

## 工作坊和训练营

### 动手工作坊

| 工作坊名称 | 主题 | 难度 | 时长 | 链接 |
|------------|------|------|------|------|
| **Rust Bridge** | Rust 入门 | 🟢 | 1-2 天 | [Rust Bridge](https://rustbridge.com/) |
| **RustConf Workshops** | Rust 专题 | 🟡 | 1 天 | [RustConf](https://rustconf.com/) |
| **RustFest Workshops** | Rust 社区 | 🟡 | 1-2 天 | [RustFest](https://rustfest.eu/) |
| **RustLab Workshops** | Rust 实践 | 🟡 | 不定 | [RustLab](https://www.rustlab.it/) |
| **Rust Verification Workshop** | Rust 验证 | 🔴 | 1 天 | [RV](https://sites.google.com/view/rustverify2024) |

### 黑客松和挑战

| 活动名称 | 主题 | 难度 | 频率 | 链接 |
|----------|------|------|------|------|
| **Advent of Code** | 算法挑战 | 🟡 | 每年 12 月 | [Advent of Code](https://adventofcode.com/) |
| **Rust Game Dev** | 游戏开发 | 🟡 | 不定 | [Rust Gamedev](https://gamedev.rs/) |
| **Rusty Days Hackathon** | Rust 项目 | 🟡 | 每年 | [Rusty Days](https://rusty-days.org/) |
| **Open Source Hackathons** | 开源贡献 | 🟡 | 不定 | [各组织] |

---

## 学习路径规划

### 路径一：Rust 全栈工程师（6-12 个月）

```
第 1-2 月：基础阶段
├── The Rust Programming Language (官方书)
├── Rustlings 练习
├── Rust by Example
└── 小项目实践

第 3-4 月：进阶阶段
├── Programming Rust (Blandy)
├── Zero To Production In Rust
├── 异步编程学习
└── Web 框架学习 (Actix/Rocket)

第 5-8 月：专业阶段
├── Rust for Rustaceans
├── 特定领域深入学习
├── 开源项目贡献
└── 实际项目开发

第 9-12 月：精通阶段
├── The Rustonomicon
├── 编译器内部学习
├── 参与核心开发
└── 技术分享和教学
```

### 路径二：PL 理论研究者（12-24 个月）

```
第 1-3 月：基础理论
├── Types and Programming Languages (TAPL)
├── Lambda-Calculus and Combinators
└── 完成 TAPL 练习

第 4-6 月：高级理论
├── Advanced Topics in TAPL
├── Proofs and Types
└── 范畴论基础

第 7-12 月：形式化方法
├── Software Foundations (Coq)
├── 分离逻辑学习
└── 简单语言实现

第 13-24 月：研究深入
├── Iris 分离逻辑框架
├── RustBelt 论文研读
├── 原创研究项目
└── 论文发表
```

### 路径三：形式化验证工程师（12-18 个月）

```
第 1-3 月：逻辑基础
├── Logic in Computer Science
├── Software Foundations (Vol. 1)
└── Coq/Lean 基础

第 4-6 月：验证技术
├── Concrete Semantics (Isabelle)
├── Principles of Model Checking
└── 验证小项目

第 7-12 月：专业工具
├── 深入学习特定验证器
├── Rust 验证工具实践
└── 工业级项目验证

第 13-18 月：高级应用
├── 复杂系统验证
├── 工具开发贡献
└── 企业级验证项目
```

### 路径四：系统安全研究员（18-24 个月）

```
第 1-3 月：安全基础
├── 计算机系统安全
├── Rust 安全编程
└── 常见漏洞类型

第 4-6 月：形式化基础
├── 形式化方法入门
├── TLA+ 规约学习
└── 模型检测基础

第 7-12 月：Rust 形式化
├── RustBelt 论文研读
├── 分离逻辑深入
└── 简单 Rust 验证

第 13-18 月：高级验证
├── 并发验证
├── Unsafe Rust 验证
└── 实际系统验证

第 19-24 月：研究前沿
├── 最新研究跟踪
├── 原创研究
└── 学术发表
```

---

## 📊 课程统计

### 按类别统计

| 类别 | 课程数量 | 占比 |
|------|----------|------|
| Rust 编程 | 25 | 31% |
| 程序语言理论 | 18 | 22% |
| 类型系统 | 10 | 12% |
| 形式化验证 | 15 | 19% |
| 学术讲座 | 15 | 19% |
| **总计** | **83** | **100%** |

### 按难度统计

| 难度等级 | 课程数量 | 占比 |
|----------|----------|------|
| 🟢 入门级 | 20 | 24% |
| 🟡 中级 | 25 | 30% |
| 🔴 高级 | 38 | 46% |

### 按平台统计

| 平台类型 | 课程数量 | 占比 |
|----------|----------|------|
| 大学课程 | 25 | 30% |
| MOOC (Coursera等) | 10 | 12% |
| 官方文档/教程 | 20 | 24% |
| YouTube/视频 | 15 | 18% |
| 会议/讲座 | 13 | 16% |

---

## 🎯 推荐学习顺序

### 快速入门（3 个月）

```
优先级 1：Rust 基础
├── The Rust Programming Language
├── Rustlings
└── 简单项目

优先级 2：实践提升
├── Programming Rust
├── 异步编程
└── 参与社区

优先级 3：专业化
├── 选择特定方向深入
└── 开源贡献
```

### 系统学习（12 个月）

```
阶段 1：基础（月 1-3）
├── Rust 基础
├── PL 理论入门
└── 类型系统基础

阶段 2：进阶（月 4-8）
├── 高级 Rust
├── 形式化方法
└── 验证工具

阶段 3：精通（月 9-12）
├── 研究论文研读
├── 原创项目
└── 社区贡献
```

---

## 🔗 相关资源

- [书籍和资源索引](./books-resources.md) - 这些课程的配套教材
- [学术论文分类](./academic-papers.md) - 课程中引用的论文
- [工具和库索引](./tools-libraries.md) - 课程中使用的工具
- [核心文献速查](./bibliography.md) - 快速参考

---

**最后更新**: 2026-03-04
**维护者**: Rust 所有权可判定性研究项目
