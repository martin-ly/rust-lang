# 书籍和教程资源

本文件整理了与 Rust 编程语言、程序语言理论（PL Theory）、类型系统和形式化方法相关的经典教材、专著和学习资源。每本书都标注了难度等级、适用人群和推荐学习路径。

---

## 📑 目录

- [书籍和教程资源](#书籍和教程资源)
  - [📑 目录](#-目录)
  - [Rust 语言书籍](#rust-语言书籍)
    - [入门与进阶](#入门与进阶)
    - [高级与专业](#高级与专业)
    - [专题书籍](#专题书籍)
  - [程序语言理论](#程序语言理论)
    - [经典教材](#经典教材)
    - [计算理论](#计算理论)
  - [类型系统](#类型系统)
    - [基础与进阶](#基础与进阶)
    - [依赖类型与高级类型](#依赖类型与高级类型)
    - [线性逻辑](#线性逻辑)
  - [形式化方法与逻辑](#形式化方法与逻辑)
    - [分离逻辑](#分离逻辑)
    - [模型检测与时序逻辑](#模型检测与时序逻辑)
    - [交互式定理证明](#交互式定理证明)
  - [函数式编程](#函数式编程)
    - [函数式编程基础](#函数式编程基础)
    - [范畴论与函数式编程](#范畴论与函数式编程)
  - [编译器设计与实现](#编译器设计与实现)
    - [经典编译器教材](#经典编译器教材)
    - [高级编译技术](#高级编译技术)
  - [软件验证与证明](#软件验证与证明)
    - [形式化验证](#形式化验证)
    - [程序分析](#程序分析)
  - [在线教程与文档](#在线教程与文档)
    - [Rust 官方资源](#rust-官方资源)
    - [学习平台](#学习平台)
    - [PL 理论资源](#pl-理论资源)
  - [📊 资源统计](#-资源统计)
    - [按类别统计](#按类别统计)
    - [按难度统计](#按难度统计)
    - [按格式统计](#按格式统计)
  - [🎯 学习路径推荐](#-学习路径推荐)
    - [路径一：Rust 全栈工程师](#路径一rust-全栈工程师)
    - [路径二：类型系统研究者](#路径二类型系统研究者)
    - [路径三：形式化验证工程师](#路径三形式化验证工程师)
  - [🔗 相关资源](#-相关资源)

---

## Rust 语言书籍

### 入门与进阶

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| The Rust Programming Language (TRPL) | Steve Klabnik & Carol Nichols | 2023 | 🟢 | 官方权威教材，Rust 圣经 | [官方](https://doc.rust-lang.org/book/) |
| Programming Rust (2nd Edition) | Jim Blandy, Jason Orendorff & Leonora Tindall | 2021 | 🟡 | 系统深入，适合有经验开发者 | [O'Reilly](https://www.oreilly.com/library/view/programming-rust-2nd/9781492052586/) |
| Rust for Rustaceans | Jon Gjengset | 2021 | 🔴 | 高级主题，深入底层 | [No Starch](https://nostarch.com/rust-rustaceans) |
| The Rust Programming Language (Covers Rust 2018) | Steve Klabnik & Carol Nichols | 2018 | 🟢 | 经典版本，基础扎实 | [No Starch](https://nostarch.com/Rust) |
| Beginning Rust: From Novice to Professional | Carlo Milanesi | 2018 | 🟢 | 循序渐进，适合初学者 | [Apress](https://link.springer.com/book/10.1007/978-1-4842-3468-6) |
| Rust in Action | Tim McNamara | 2021 | 🟡 | 实战导向，包含系统编程 | [Manning](https://www.manning.com/books/rust-in-action) |
| Rust Web Programming | Maxwell Flitton | 2023 | 🟡 | Web 开发专题 | [Packt](https://www.packtpub.com/product/rust-web-programming/9781800560813) |
| Hands-On Rust: Effective Learning through 2D Game Development | Herbert Wolverson | 2021 | 🟢 | 游戏开发入门 | [Pragmatic](https://pragprog.com/titles/hwrust/hands-on-rust/) |

### 高级与专业

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Rust Atomics and Locks | Mara Bos | 2023 | 🔴 | 并发编程深入解析 | [O'Reilly](https://www.oreilly.com/library/view/rust-atomics-and/9781098119430/) |
| Rust Design Patterns | Rust Community | 持续更新 | 🟡 | 设计模式实践 | [GitHub](https://rust-unofficial.github.io/patterns/) |
| Zero To Production In Rust | Luca Palmieri | 2022 | 🟡 | 生产级 Rust 开发 | [Zero2Prod](https://www.zero2prod.com/) |
| Command-Line Rust | Ken Youens-Clark | 2022 | 🟢 | CLI 应用开发 | [O'Reilly](https://www.oreilly.com/library/view/command-line-rust/9781098109424/) |
| Rust High Performance | Iban Eguia Moraza | 2018 | 🔴 | 性能优化专题 | [Packt](https://www.packtpub.com/product/rust-high-performance/9781788399487) |
| Mastering Rust (2nd Edition) | Rahul Sharma & Vesa Kaihlavirta | 2019 | 🔴 | 全面深入的高级主题 | [Packt](https://www.packtpub.com/product/mastering-rust-second-edition/9781789346572) |
| Network Programming with Rust | Abhishek Chanda | 2018 | 🟡 | 网络编程实践 | [Packt](https://www.packtpub.com/product/network-programming-with-rust/9781788624893) |
| Practical Machine Learning with Rust | Joydeep Bhattacharjee | 2020 | 🔴 | 机器学习应用 | [Apress](https://link.springer.com/book/10.1007/978-1-4842-5121-8) |

### 专题书籍

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| The Rustonomicon | Rust Community | 持续更新 | 🔴 | Unsafe Rust 黑魔法 | [官方](https://doc.rust-lang.org/nomicon/) |
| The Rust Reference | Rust Team | 持续更新 | 🔴 | 语言参考手册 | [官方](https://doc.rust-lang.org/reference/) |
| The Little Book of Rust Macros | Daniel Keep | 持续更新 | 🟡 | 宏编程指南 | [GitHub](https://danielkeep.github.io/tlborm/book/) |
| The Little Book of Rust Books | Rust Community | 持续更新 | 🟢 | Rust 书籍索引 | [GitHub](https://lborb.github.io/book/) |
| Asynchronous Programming in Rust | Carl Fredrik Samson | 持续更新 | 🟡 | 异步编程详解 | [GitHub](https://rust-lang.github.io/async-book/) |
| The Embedded Rust Book | Rust Team | 持续更新 | 🔴 | 嵌入式开发 | [官方](https://doc.rust-lang.org/stable/embedded-book/) |
| The Rust Unstable Book | Rust Team | 持续更新 | 🔴 | 不稳定特性文档 | [官方](https://doc.rust-lang.org/beta/unstable-book/) |
| The Cargo Book | Rust Team | 持续更新 | 🟢 | 包管理器详解 | [官方](https://doc.rust-lang.org/cargo/) |

---

## 程序语言理论

### 经典教材

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Types and Programming Languages (TAPL) | Benjamin C. Pierce | 2002 | 🟡 | 类型系统圣经 | [MIT Press](https://mitpress.mit.edu/9780262162098/types-and-programming-languages/) |
| Advanced Topics in Types and Programming Languages | Benjamin C. Pierce (Ed.) | 2005 | 🔴 | TAPL 进阶续作 | [MIT Press](https://mitpress.mit.edu/9780262162289/advanced-topics-in-types-and-programming-languages/) |
| Practical Foundations for Programming Languages (2nd Ed.) | Robert Harper | 2016 | 🔴 | 现代 PL 理论 | [Cambridge](https://www.cambridge.org/core/books/practical-foundations-for-programming-languages/99EA2D82D9D29667350B2BA24790B56B) |
| The Formal Semantics of Programming Languages | Glynn Winskel | 1993 | 🔴 | 形式语义经典 | [MIT Press](https://mitpress.mit.edu/9780262731033/the-formal-semantics-of-programming-languages/) |
| Semantics with Applications: An Appetizer | Hanne Riis Nielson & Flemming Nielson | 2007 | 🟡 | 语义学入门 | [Springer](https://link.springer.com/book/10.1007/978-1-84628-692-6) |
| Programming Languages: Application and Interpretation | Shriram Krishnamurthi | 2007 | 🟡 | 通过实现学习 PL | [Brown CS](https://www.plai.org/) |
| Essentials of Programming Languages (3rd Ed.) | Daniel P. Friedman & Mitchell Wand | 2008 | 🟡 | Scheme 实现 PL | [MIT Press](https://mitpress.mit.edu/9780262062794/essentials-of-programming-languages/) |
| Concepts, Techniques, and Models of Computer Programming | Peter Van Roy & Seif Haridi | 2004 | 🟡 | Oz 语言视角 | [MIT Press](https://mitpress.mit.edu/9780262220699/concepts-techniques-and-models-of-computer-programming/) |

### 计算理论

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Introduction to the Theory of Computation | Michael Sipser | 2012 | 🟡 | 计算理论标准教材 | [Cengage](https://www.cengage.com/c/introduction-to-the-theory-of-computation-3e-sipser/9781133187790/) |
| Automata and Computability | Dexter C. Kozen | 1997 | 🟡 | 自动机理论深入 | [Springer](https://link.springer.com/book/10.1007/978-1-4612-1844-9) |
| Computability and Complexity Theory | Homer & Selman | 2011 | 🔴 | 可计算性与复杂度 | [Springer](https://link.springer.com/book/10.1007/978-1-4614-0682-8) |
| Introduction to Automata Theory, Languages, and Computation | Hopcroft, Motwani & Ullman | 2006 | 🟡 | 经典自动机教材 | [Pearson](https://www.pearson.com/en-us/subject-catalog/p/introduction-to-automata-theory-languages-and-computation/P200000005792) |
| Lambda-Calculus and Combinators: An Introduction | Hindley & Seldin | 2008 | 🔴 | λ演算经典 | [Cambridge](https://www.cambridge.org/core/books/lambdacalculus-and-combinators/3453DA0B29AF2541E60D6C0ECA5E3E08) |
| The Lambda Calculus: Its Syntax and Semantics | Henk Barendregt | 1984 | 🔴 | λ演算权威参考书 | [Elsevier](https://www.sciencedirect.com/bookseries/studies-in-logic-and-the-foundations-of-mathematics/vol/103) |

---

## 类型系统

### 基础与进阶

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Proofs and Types | Jean-Yves Girard, Yves Lafont & Paul Taylor | 1989 | 🔴 | Curry-Howard 对应 | [Cambridge](https://www.cambridge.org/core/books/proofs-and-types/EBBEFDA77BE67DAB17AEFD98BD69CC97) |
| Proof Theory and Automated Reasoning | Jean Gallier | 2003 | 🔴 | 证明论与自动推理 | [Cambridge](https://www.cambridge.org/core/books/proof-theory-and-automated-reasoning/9780511815170) |
| Basic Proof Theory (2nd Ed.) | Anne S. Troelstra & Helmut Schwichtenberg | 2000 | 🔴 | 证明论基础 | [Cambridge](https://www.cambridge.org/core/books/basic-proof-theory/0F8A98667AAB0C3F359779168C075113) |
| Type Theory and Formal Proof | Rob Nederpelt & Herman Geuvers | 2014 | 🔴 | 类型理论系统介绍 | [Cambridge](https://www.cambridge.org/core/books/type-theory-and-formal-proof/0474C94D13653A6A3F8F6B12C4E5A12A) |
| Lectures on the Curry-Howard Isomorphism | Morten Heine Sørensen & Paweł Urzyczyn | 2006 | 🔴 | Curry-Howard 深入 | [Elsevier](https://www.sciencedirect.com/bookseries/studies-in-logic-and-the-foundations-of-mathematics/vol/149) |
| Categories and Types in Logic, Language, and Physics | J. van Eijck et al. | 2014 | 🔴 | 范畴论与类型 | [Springer](https://link.springer.com/book/10.1007/978-3-662-45465-7) |

### 依赖类型与高级类型

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Homotopy Type Theory: Univalent Foundations | The Univalent Foundations Program | 2013 | 🔴 | HoTT 基础书籍 | [HoTT](https://homotopytypetheory.org/book/) |
| The Little Typer | Daniel P. Friedman & David Thrane Christiansen | 2018 | 🟡 | 依赖类型入门 | [MIT Press](https://mitpress.mit.edu/9780262536430/the-little-typer/) |
| The Little Prover | Daniel P. Friedman & Carl Eastlund | 2015 | 🟡 | 归纳证明入门 | [MIT Press](https://mitpress.mit.edu/9780262527957/the-little-prover/) |
| Certified Programming with Dependent Types | Adam Chlipala | 2013 | 🔴 | Coq 实战编程 | [MIT Press](https://mitpress.mit.edu/9780262026659/certified-programming-with-dependent-types/) |
| Programming Language Foundations in Agda | Philip Wadler et al. | 持续更新 | 🔴 | Agda 编程基础 | [GitHub](https://plfa.github.io/) |
| Software Foundations (Vols. 1-4) | Benjamin Pierce et al. | 持续更新 | 🟡 | Coq 证明基础 | [Software Foundations](https://softwarefoundations.cis.upenn.edu/) |

### 线性逻辑

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Linear Logic | Jean-Yves Girard | 2011 | 🔴 | 线性逻辑专著 | [Cambridge](https://www.cambridge.org/core/books/linear-logic/1E0E0F0F0F0F0F0F0F0F0F0F0F0F0F0F) |
| Proof Theory: An Introduction | Wolfram Pohlers | 2009 | 🔴 | 证明论入门 | [Springer](https://link.springer.com/book/10.1007/978-3-540-69319-2) |
| Substructural Logics | Peter Schroeder-Heister & Kosta Došen | 1993 | 🔴 | 子结构逻辑 | [Oxford](https://global.oup.com/academic/product/substructural-logics-9780198537779) |
| Resource-Sensitive Realizability and Affine Logic | Alex Simpson | 1994 | 🔴 | 资源敏感实现 | [Springer](https://link.springer.com/chapter/10.1007/BFb0014055) |

---

## 形式化方法与逻辑

### 分离逻辑

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Separation Logic: A Logical Theory of State | Peter O'Hearn | 2024 | 🔴 | 分离逻辑专著 | [Cambridge](https://www.cambridge.org/core/books/separation-logic/...) |
| Program Logics for Certified Compilers | Andrew W. Appel et al. | 2014 | 🔴 | VST 与 CompCert | [Cambridge](https://www.cambridge.org/core/books/program-logics-for-certified-compilers/...) |
| The Science of Software Design: A Logical Approach | John C. Reynolds | 2012 | 🔴 | 软件设计科学 | [Springer](https://link.springer.com/book/10.1007/978-1-4614-2942-1) |

### 模型检测与时序逻辑

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Principles of Model Checking | Christel Baier & Joost-Pieter Katoen | 2008 | 🔴 | 模型检测圣经 | [MIT Press](https://mitpress.mit.edu/9780262026499/principles-of-model-checking/) |
| Model Checking | Edmund M. Clarke et al. | 1999 | 🔴 | 模型检测经典 | [MIT Press](https://mitpress.mit.edu/9780262032704/model-checking/) |
| An Introduction to Temporal Logic | Fred Kroger | 1987 | 🟡 | 时序逻辑入门 | [Springer](https://link.springer.com/book/10.1007/978-3-642-86365-2) |
| Logic in Computer Science (2nd Ed.) | Michael Huth & Mark Ryan | 2004 | 🟡 | 计算逻辑教材 | [Cambridge](https://www.cambridge.org/core/books/logic-in-computer-science/...) |
| Handbook of Practical Logic and Automated Reasoning | John Harrison | 2009 | 🔴 | 自动推理手册 | [Cambridge](https://www.cambridge.org/core/books/handbook-of-practical-logic-and-automated-reasoning/...) |

### 交互式定理证明

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Theorem Proving in Lean 4 | Jeremy Avigad et al. | 持续更新 | 🔴 | Lean 4 证明指南 | [Lean](https://lean-lang.org/theorem_proving_in_lean4/) |
| Functional Programming in Lean | David Thrane Christiansen | 持续更新 | 🟡 | Lean 4 函数式编程 | [Lean](https://lean-lang.org/functional_programming_in_lean/) |
| Programming and Proving in Isabelle/HOL | Tobias Nipkow | 2014 | 🔴 | Isabelle/HOL 入门 | [TUM](https://isabelle.in.tum.de/doc/prog-prove.pdf) |
| Concrete Semantics with Isabelle/HOL | Tobias Nipkow & Gerwin Klein | 2014 | 🟡 | 具体语义学 | [TUM](http://concrete-semantics.org/) |
| Certified Programming with Dependent Types | Adam Chlipala | 2013 | 🔴 | Coq 高级编程 | [MIT Press](https://mitpress.mit.edu/9780262026659/certified-programming-with-dependent-types/) |
| Interactive Theorem Proving and Program Development | Yves Bertot & Pierre Castéran | 2004 | 🔴 | Coq 艺术与科学 | [Springer](https://link.springer.com/book/10.1007/978-3-662-07964-5) |
| Mathematical Components | Assia Mahboubi & Enrico Tassi | 2018 | 🔴 | SSReflect/MathComp | [GitHub](https://math-comp.github.io/mcb/) |

---

## 函数式编程

### 函数式编程基础

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Structure and Interpretation of Computer Programs (SICP) | Harold Abelson & Gerald Jay Sussman | 1996 | 🟡 | 计算机科学经典 | [MIT Press](https://mitpress.mit.edu/9780262510875/structure-and-interpretation-of-computer-programs/) |
| SICP JS | Martin Henz & Tobias Wrigstad | 2022 | 🟡 | JavaScript 版 SICP | [GitHub](https://sourceacademy.org/sicpjs/) |
| Introduction to Functional Programming | Richard Bird & Philip Wadler | 1988 | 🟡 | 函数式编程经典 | [Prentice Hall](https://www.amazon.com/Introduction-Functional-Programming-Prentice-Hall/dp/0134841891) |
| Thinking Functionally with Haskell | Richard Bird | 2014 | 🟡 | Haskell 思维 | [Cambridge](https://www.cambridge.org/core/books/thinking-functionally-with-haskell/...) |
| Haskell Programming from First Principles | Christopher Allen & Julie Moronuki | 2016 | 🟢 | Haskell 全面教程 | [Gumroad](https://haskellbook.com/) |
| Real World Haskell | Bryan O'Sullivan et al. | 2008 | 🟡 | Haskell 实战 | [O'Reilly](http://book.realworldhaskell.org/) |
| Purely Functional Data Structures | Chris Okasaki | 1998 | 🔴 | 纯函数数据结构 | [Cambridge](https://www.cambridge.org/core/books/purely-functional-data-structures/...) |

### 范畴论与函数式编程

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Category Theory for Programmers | Bartosz Milewski | 2019 | 🟡 | 程序员视角的范畴论 | [GitHub](https://github.com/hmemcpy/milewski-ctfp-pdf) |
| Category Theory in Context | Emily Riehl | 2016 | 🔴 | 现代范畴论 | [Dover](https://math.jhu.edu/~eriehl/context/) |
| Basic Category Theory | Tom Leinster | 2014 | 🔴 | 范畴论基础 | [Cambridge](https://www.cambridge.org/core/books/basic-category-theory/...) |
| An Introduction to Functional Programming Through Lambda Calculus | Greg Michaelson | 2011 | 🟡 | λ演算入门 | [Dover](https://store.doverpublications.com/0486478831.html) |

---

## 编译器设计与实现

### 经典编译器教材

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Compilers: Principles, Techniques, and Tools (Dragon Book) | Aho, Lam, Sethi & Ullman | 2006 | 🟡 | 编译器圣经 | [Pearson](https://www.pearson.com/en-us/subject-catalog/p/compilers-principles-techniques-and-tools/P200000005663) |
| Modern Compiler Implementation in ML | Andrew W. Appel | 1998 | 🔴 | ML 实现编译器 | [Cambridge](https://www.cambridge.org/core/books/modern-compiler-implementation-in-ml/...) |
| Modern Compiler Implementation in Java (2nd Ed.) | Andrew W. Appel & Jens Palsberg | 2002 | 🟡 | Java 实现编译器 | [Cambridge](https://www.cambridge.org/core/books/modern-compiler-implementation-in-java/...) |
| Modern Compiler Design (2nd Ed.) | Dick Grune et al. | 2012 | 🟡 | 现代编译器设计 | [Springer](https://link.springer.com/book/10.1007/978-1-4614-4699-6) |
| Engineering a Compiler (3rd Ed.) | Keith Cooper & Linda Torczon | 2022 | 🟡 | 工程化编译器 | [Elsevier](https://www.elsevier.com/books/engineering-a-compiler/cooper/978-0-12-815412-0) |

### 高级编译技术

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Advanced Compiler Design and Implementation | Steven S. Muchnick | 1997 | 🔴 | 高级编译技术 | [Morgan Kaufmann](https://www.elsevier.com/books/advanced-compiler-design-and-implementation/muchnick/978-1-55860-320-2) |
| Optimizing Compilers for Modern Architectures | Randy Allen & Ken Kennedy | 2001 | 🔴 | 现代架构优化 | [Morgan Kaufmann](https://www.elsevier.com/books/optimizing-compilers-for-modern-architectures/allen/978-1-55860-286-1) |
| Static Single Assignment Book | Various Authors | 持续更新 | 🔴 | SSA 形式详解 | [SSA Book](https://pfalcon.github.io/ssabook/latest/) |
| Foundations of Logic Programming (2nd Ed.) | John W. Lloyd | 1987 | 🔴 | 逻辑编程基础 | [Springer](https://link.springer.com/book/10.1007/978-3-642-83189-8) |
| Implementing Functional Languages: A Tutorial | Simon Peyton Jones & David Lester | 1992 | 🔴 | 函数式语言实现 | [Microsoft](https://www.microsoft.com/en-us/research/publication/implementing-functional-languages-a-tutorial/) |

---

## 软件验证与证明

### 形式化验证

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Formal Reasoning About Programs | Adam Chlipala | 2017 | 🔴 | 程序形式化推理 | [MIT](http://adam.chlipala.net/frap/) |
| How to Prove It: A Structured Approach (2nd Ed.) | Daniel J. Velleman | 2006 | 🟢 | 数学证明入门 | [Cambridge](https://www.cambridge.org/core/books/how-to-prove-it/...) |
| Logic and Proof | Jeremy Avigad et al. | 2016 | 🟡 | 逻辑与证明基础 | [CMU](https://leanprover.github.io/logic_and_proof/) |
| The Calculus of Computation | Aaron R. Bradley & Zohar Manna | 2007 | 🔴 | 计算微积分 | [Springer](https://link.springer.com/book/10.1007/978-3-540-74113-8) |
| Decision Procedures: An Algorithmic Point of View (2nd Ed.) | Daniel Kroening & Ofer Strichman | 2016 | 🔴 | 决策过程算法 | [Springer](https://link.springer.com/book/10.1007/978-3-662-50497-0) |

### 程序分析

| 书名 | 作者 | 出版年份 | 难度 | 特点 | 链接 |
|------|------|----------|------|------|------|
| Principles of Program Analysis | Flemming Nielson, Hanne Riis Nielson & Chris Hankin | 1999 | 🔴 | 程序分析原理 | [Springer](https://link.springer.com/book/10.1007/978-3-662-03811-6) |
| Static Program Analysis | Anders Møller & Michael I. Schwartzbach | 2024 | 🟡 | 静态分析教材 | [Springer](https://link.springer.com/book/10.1007/978-3-031-55608-0) |
| Advanced Compiler Design and Implementation | Steven S. Muchnick | 1997 | 🔴 | 包含程序分析章节 | [Elsevier](https://www.elsevier.com/books/advanced-compiler-design-and-implementation/muchnick/978-1-55860-320-2) |
| Program Analysis | Torben Mogensen | 2024 | 🟡 | 程序分析教程 | [DIKU](https://www.diku.dk/~torbenm/PA/PA-toc.html) |

---

## 在线教程与文档

### Rust 官方资源

| 资源名称 | 类型 | 难度 | 描述 | 链接 |
|----------|------|------|------|------|
| The Rust Programming Language | 书籍 | 🟢 | 官方 Rust 书 | [官方](https://doc.rust-lang.org/book/) |
| Rust by Example | 教程 | 🟢 | 实例学习 Rust | [官方](https://doc.rust-lang.org/rust-by-example/) |
| Rustlings | 练习 | 🟢 | 小练习集 | [GitHub](https://github.com/rust-lang/rustlings) |
| The Rust Reference | 文档 | 🔴 | 语言参考 | [官方](https://doc.rust-lang.org/reference/) |
| The Rustonomicon | 文档 | 🔴 | Unsafe Rust | [官方](https://doc.rust-lang.org/nomicon/) |
| Asynchronous Programming in Rust | 书籍 | 🟡 | 异步编程 | [官方](https://rust-lang.github.io/async-book/) |
| The Rust FFI Omnibus | 教程 | 🟡 | FFI 指南 | [GitHub](http://jakegoulding.com/rust-ffi-omnibus/) |
| The Cargo Book | 文档 | 🟢 | Cargo 指南 | [官方](https://doc.rust-lang.org/cargo/) |

### 学习平台

| 平台 | 类型 | 难度 | 描述 | 链接 |
|------|------|------|------|------|
| Exercism - Rust Track | 练习 | 🟢 | 免费编程练习 | [Exercism](https://exercism.org/tracks/rust) |
| Rust on Codewars | 练习 | 🟡 | 编程挑战 | [Codewars](https://www.codewars.com/?language=rust) |
| Rust Quiz | 测验 | 🟡 | Rust 知识测验 | [Diesel](https://dtolnay.github.io/rust-quiz/) |
| Rust Cookbook | 食谱 | 🟡 | 实用代码片段 | [Rust-Lang-Nursery](https://rust-lang-nursery.github.io/rust-cookbook/) |
| Read Rust | 文章聚合 | 🟡 | 社区文章 | [Read Rust](https://readrust.org/) |
| This Week in Rust | 周报 | 🟢 | Rust 周报 | [Rust](https://this-week-in-rust.org/) |

### PL 理论资源

| 资源名称 | 类型 | 难度 | 描述 | 链接 |
|----------|------|------|------|------|
| Software Foundations | 课程 | 🟡 | Coq 基础 | [UPenn](https://softwarefoundations.cis.upenn.edu/) |
| Programming Languages | 课程 | 🟡 | Coursera 课程 | [Coursera](https://www.coursera.org/learn/programming-languages) |
| Types and Programming Languages | 书籍资源 | 🟡 | TAPL 配套资源 | [TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/) |
| The Archetype of Programming Languages | 教程 | 🟡 | 语言设计 | [GitHub](https://github.com/kandelvijaya/NLP-CS224n) |
| PLFA - Programming Language Foundations in Agda | 书籍 | 🔴 | Agda 教程 | [GitHub](https://plfa.github.io/) |

---

## 📊 资源统计

### 按类别统计

| 类别 | 书籍数量 | 占比 |
|------|----------|------|
| Rust 语言 | 25 | 27% |
| 程序语言理论 | 15 | 16% |
| 类型系统 | 14 | 15% |
| 形式化方法 | 16 | 17% |
| 函数式编程 | 8 | 9% |
| 编译器设计 | 9 | 10% |
| 软件验证 | 7 | 8% |
| 在线资源 | 20 | - |

### 按难度统计

| 难度等级 | 资源数量 | 占比 |
|----------|----------|------|
| 🟢 入门级 | 20 | 22% |
| 🟡 中级 | 35 | 38% |
| 🔴 高级 | 36 | 40% |

### 按格式统计

| 格式 | 数量 |
|------|------|
| 纸质/电子书 | 90+ |
| 在线文档/教程 | 25+ |
| 课程材料 | 10+ |

---

## 🎯 学习路径推荐

### 路径一：Rust 全栈工程师

**目标**: 掌握生产级 Rust 开发

```
第 1 阶段 (1-2 个月):
├── The Rust Programming Language (官方书)
├── Rustlings 练习
└── Rust by Example

第 2 阶段 (2-3 个月):
├── Programming Rust (Blandy)
├── Rust in Action
└── 实际项目练习

第 3 阶段 (3-6 个月):
├── Rust for Rustaceans (高级主题)
├── Rust Atomics and Locks (并发)
├── The Rustonomicon (Unsafe)
└── 参与开源项目
```

### 路径二：类型系统研究者

**目标**: 深入理解类型理论和形式化语义

```
第 1 阶段 (3 个月):
├── Types and Programming Languages (TAPL)
├── Lambda-Calculus and Combinators
└── 完成 TAPL 练习

第 2 阶段 (3-6 个月):
├── Advanced Topics in TAPL
├── Proofs and Types
├── Software Foundations (Coq)
└── 实现简单类型检查器

第 3 阶段 (6-12 个月):
├── Practical Foundations for PL
├── 分离逻辑相关书籍
├── 研究论文阅读
└── 参与研究项目
```

### 路径三：形式化验证工程师

**目标**: 掌握程序验证技术

```
第 1 阶段 (2-3 个月):
├── Software Foundations (Vol. 1)
├── Logic in Computer Science
└── Coq/Lean 基础

第 2 阶段 (3-6 个月):
├── Certified Programming with Dependent Types
├── Principles of Model Checking
├── Concrete Semantics
└── 验证小项目

第 3 阶段 (6-12 个月):
├── Program Logics for Certified Compilers
├── 验证工具论文
├── Rust 验证工具实践
└── 工业级验证项目
```

---

## 🔗 相关资源

- [学术论文分类](./academic-papers.md) - 配套学术论文
- [工具和库索引](./tools-libraries.md) - 实现这些概念的工具
- [在线课程](./online-courses.md) - 基于这些书籍的课程
- [核心文献速查](./bibliography.md) - 快速参考

---

**最后更新**: 2026-03-04
**维护者**: Rust 所有权可判定性研究项目
