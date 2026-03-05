# 工具和库索引

本文件整理了与 Rust 程序验证、静态分析、形式化方法和开发辅助相关的工具、库和 IDE 插件。
每个工具都包含功能描述、使用场景、难度等级和官方链接。

---

## 📑 目录

- [工具和库索引](#工具和库索引)
  - [📑 目录](#-目录)
  - [Rust 验证工具](#rust-验证工具)
    - [高级验证器](#高级验证器)
    - [中级验证工具](#中级验证工具)
    - [安全分析工具](#安全分析工具)
  - [通用验证工具](#通用验证工具)
    - [模型检测器](#模型检测器)
    - [SMT 求解器](#smt-求解器)
    - [霍尔逻辑验证器](#霍尔逻辑验证器)
  - [静态分析工具](#静态分析工具)
    - [Rust 专用分析器](#rust-专用分析器)
    - [通用静态分析器](#通用静态分析器)
  - [形式化方法框架](#形式化方法框架)
    - [分离逻辑框架](#分离逻辑框架)
    - [程序逻辑框架](#程序逻辑框架)
    - [重写和等价性](#重写和等价性)
  - [证明助手和定理证明器](#证明助手和定理证明器)
    - [主流证明助手](#主流证明助手)
    - [自动化定理证明](#自动化定理证明)
    - [证明自动化库](#证明自动化库)
  - [IDE 和编辑器插件](#ide-和编辑器插件)
    - [Rust 专用 IDE 支持](#rust-专用-ide-支持)
    - [通用 IDE 插件](#通用-ide-插件)
    - [辅助开发工具](#辅助开发工具)
  - [测试和模糊测试工具](#测试和模糊测试工具)
    - [Rust 测试工具](#rust-测试工具)
    - [模糊测试工具](#模糊测试工具)
    - [符号执行工具](#符号执行工具)
  - [文档和代码生成工具](#文档和代码生成工具)
    - [文档工具](#文档工具)
    - [代码生成工具](#代码生成工具)
  - [📊 工具统计](#-工具统计)
    - [按类别统计](#按类别统计)
    - [按难度统计](#按难度统计)
    - [按活跃度统计](#按活跃度统计)
  - [🎯 工具选择指南](#-工具选择指南)
    - [场景一：Rust 代码验证入门](#场景一rust-代码验证入门)
    - [场景二：生产级 Rust 验证](#场景二生产级-rust-验证)
    - [场景三：学术研究和教学](#场景三学术研究和教学)
    - [场景四：安全关键系统](#场景四安全关键系统)
  - [🔗 相关资源](#-相关资源)

---

## Rust 验证工具

### 高级验证器

| 工具名称 | 后端 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **Creusot** | Why3 | 🔴 | 预言变量编码可变借用，生成证明义务 | 活跃 | [GitHub](https://github.com/creusot-rs/creusot) |
| **Prusti** | Viper | 🔴 | 基于 Viper 的 Rust 验证器，商用级 | 活跃 | [ETH Zurich](https://www.pm.inf.ethz.ch/research/prusti.html) |
| **Aeneas** | Lean | 🔴 | 函数式提取方法，Lean 后端验证 | 活跃 | [GitHub](https://github.com/AeneasVerif/aeneas) |
| **Verus** | Z3/SMT | 🔴 | 针对系统代码的验证框架，资源代数支持 | 活跃 | [GitHub](https://github.com/verus-lang/verus) |
| **Kani** | CBMC | 🔴 | 有界模型检查器，验证 unsafe 代码 | 活跃 | [GitHub](https://github.com/model-checking/kani) |
| **Flux** | Liquid Types | 🔴 | Liquid Types for Rust，细化类型 | 活跃 | [GitHub](https://github.com/liquid-rust/flux) |

### 中级验证工具

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **MIRAI** | 抽象解释 | 🔴 | Facebook 的 Rust 抽象解释器 | 维护中 | [GitHub](https://github.com/facebookexperimental/MIRAI) |
| **Crux** | SMT | 🔴 | Galois 的 Rust 符号执行工具 | 活跃 | [GitHub](https://github.com/GaloisInc/crucible) |
| **SMACK** | Boogie | 🔴 | 支持 Rust 的 LLVM 验证工具链 | 活跃 | [GitHub](https://github.com/smackers/smack) |
| **SeVero** | 类型检查 | 🔴 | Rust 细化类型验证器原型 | 研究 | [GitHub](https://github.com/secure-foundations/veri-datalog) |
| **RustHorn** | CHC | 🔴 | 基于 CHC 的 Rust 验证 | 研究 | [GitHub](https://github.com/sakste/rusthorn) |

### 安全分析工具

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **Rudra** | 静态分析 | 🔴 | 检测 Rust 中的内存安全 bug | 活跃 | [GitHub](https://github.com/sslab-gatech/Rudra) |
| **MIRChecker** | 静态分析 | 🟡 | 基于 MIR 的 Rust 静态分析器 | 活跃 | [GitHub](https://github.com/wcventure/MirChecker) |
| **Lockbud** | 死锁检测 | 🟡 | Rust 死锁检测工具 | 活跃 | [GitHub](https://github.com/BurtonQin/lockbud) |
| **PTA** | 指针分析 | 🔴 | Rust 指针分析框架 | 研究 | [GitHub](https://github.com/paulgessinger/ptanalysis) |
| **Cargo Geiger** | Unsafe 检测 | 🟢 | 检测 crate 中的 unsafe 代码 | 活跃 | [GitHub](https://github.com/rust-secure-code/cargo-geiger) |

---

## 通用验证工具

### 模型检测器

| 工具名称 | 支持语言 | 难度 | 功能特点 | 状态 | 链接 |
|----------|----------|------|----------|------|------|
| **CBMC** | C/C++/Rust | 🔴 | C 有界模型检查器，Kani 后端 | 活跃 | [GitHub](https://github.com/diffblue/cbmc) |
| **SPIN** | Promela | 🔴 | 经典的显式状态模型检测器 | 活跃 | [SPIN](http://spinroot.com/spin/whatispin.html) |
| **NuSMV** | SMV | 🔴 | 符号模型检测器 | 活跃 | [NuSMV](http://nusmv.fbk.eu/) |
| **TLA+ Toolbox** | TLA+ | 🟡 | 分布式系统形式化规约 | 活跃 | [GitHub](https://github.com/tlaplus/tlaplus) |
| **Alloy Analyzer** | Alloy | 🟡 | 关系建模分析器 | 活跃 | [MIT](https://alloytools.org/) |
| **mCRL2** | mCRL2 | 🔴 | 进程代数模型检测 | 活跃 | [mCRL2](https://www.mcrl2.org/) |
| **UPPAAL** | Timed Automata | 🔴 | 实时系统模型检测 | 活跃 | [UPPAAL](https://uppaal.org/) |

### SMT 求解器

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **Z3** | SMT | 🔴 | Microsoft 开发的工业级 SMT 求解器 | 活跃 | [GitHub](https://github.com/Z3Prover/z3) |
| **CVC5** | SMT | 🔴 | 斯坦福开发的 SMT 求解器 | 活跃 | [GitHub](https://github.com/cvc5/cvc5) |
| **Yices 2** | SMT | 🔴 | SRI 开发的 SMT 求解器 | 活跃 | [SRI](https://yices.csl.sri.com/) |
| **Boolector** | SMT | 🔴 | 专注于位向量和数组 | 活跃 | [GitHub](https://github.com/Boolector/boolector) |
| **MathSAT5** | SMT | 🔴 | 工业级 SMT 求解器 | 活跃 | [MathSAT](https://mathsat.fbk.eu/) |
| **Alt-Ergo** | SMT | 🔴 | 支持算术和数组理论 | 活跃 | [GitHub](https://github.com/OCamlPro/alt-ergo) |

### 霍尔逻辑验证器

| 工具名称 | 目标语言 | 难度 | 功能特点 | 状态 | 链接 |
|----------|----------|------|----------|------|------|
| **Why3** | ML/Ada/C | 🔴 | 泛型验证平台，多种后端 | 活跃 | [Why3](http://why3.lri.fr/) |
| **Dafny** | Dafny | 🔴 | Microsoft 的验证语言 | 活跃 | [GitHub](https://github.com/dafny-lang/dafny) |
| **Boogie** | Boogie | 🔴 | Microsoft 的中间验证语言 | 活跃 | [GitHub](https://github.com/boogie-org/boogie) |
| **Viper** | Viper | 🔴 | ETH Zurich 的验证基础设施 | 活跃 | [ETH](https://www.pm.inf.ethz.ch/research/viper.html) |
| **Frama-C** | C | 🔴 | C 代码分析平台 | 活跃 | [Frama-C](https://frama-c.com/) |
| **VeriFast** | C/Java | 🔴 | 基于分离逻辑的验证器 | 活跃 | [VeriFast](https://github.com/verifast/verifast) |

---

## 静态分析工具

### Rust 专用分析器

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **Clippy** | Lint | 🟢 | Rust 官方 Lint 工具 | 活跃 | [GitHub](https://github.com/rust-lang/rust-clippy) |
| **Rustfmt** | 格式化 | 🟢 | Rust 官方格式化工具 | 活跃 | [GitHub](https://github.com/rust-lang/rustfmt) |
| **MIRAI** | 抽象解释 | 🔴 | Rust 抽象解释器 | 维护中 | [GitHub](https://github.com/facebookexperimental/MIRAI) |
| **Cargo Audit** | 安全审计 | 🟢 | 检测依赖中的已知漏洞 | 活跃 | [GitHub](https://github.com/RustSec/rustsec) |
| **Cargo Deny** | 许可证/安全 | 🟢 | 依赖检查和限制 | 活跃 | [GitHub](https://github.com/EmbarkStudios/cargo-deny) |
| **Cargo Udeps** | 死代码 | 🟢 | 检测未使用的依赖 | 活跃 | [GitHub](https://github.com/est31/cargo-udeps) |
| **Cargo Geiger** | Unsafe 统计 | 🟢 | 统计 unsafe 代码量 | 活跃 | [GitHub](https://github.com/rust-secure-code/cargo-geiger) |
| **Cargo Fuzz** | 模糊测试 | 🟡 | libFuzzer 集成 | 活跃 | [GitHub](https://github.com/rust-fuzz/cargo-fuzz) |
| **Rudra** | 不安全检测 | 🔴 | 内存安全问题检测 | 活跃 | [GitHub](https://github.com/sslab-gatech/Rudra) |
| **Miri** | 解释器 | 🔴 | Rust 中间表示解释器 | 活跃 | [GitHub](https://github.com/rust-lang/miri) |

### 通用静态分析器

| 工具名称 | 支持语言 | 难度 | 功能特点 | 状态 | 链接 |
|----------|----------|------|----------|------|------|
| **Infer** | C/Java/ObjC | 🟡 | Facebook 的静态分析器 | 活跃 | [GitHub](https://github.com/facebook/infer) |
| **Clang Static Analyzer** | C/C++/ObjC | 🟡 | LLVM 静态分析器 | 活跃 | [LLVM](https://clang-analyzer.llvm.org/) |
| **Coverity** | 多语言 | 🔴 | 商业静态分析器 | 商业 | [Synopsys](https://www.synopsys.com/software-integrity/security-testing/static-analysis-sast.html) |
| **SonarQube** | 多语言 | 🟡 | 开源代码质量管理 | 活跃 | [SonarQube](https://www.sonarqube.org/) |
| **CodeQL** | 多语言 | 🔴 | GitHub 的语义代码分析 | 活跃 | [GitHub](https://codeql.github.com/) |
| **PMD** | Java/其他 | 🟡 | Java 静态分析器 | 活跃 | [PMD](https://pmd.github.io/) |
| **SpotBugs** | Java | 🟡 | Java bug 模式检测 | 活跃 | [SpotBugs](https://spotbugs.github.io/) |
| **Bandit** | Python | 🟢 | Python 安全分析 | 活跃 | [GitHub](https://github.com/PyCQA/bandit) |
| **Pylint** | Python | 🟢 | Python Lint 工具 | 活跃 | [GitHub](https://github.com/PyCQA/pylint) |

---

## 形式化方法框架

### 分离逻辑框架

| 工具名称 | 语言 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **Iris** | Coq | 🔴 | 高阶并发分离逻辑框架 | 活跃 | [Website](https://iris-project.org/) |
| **VST** | Coq | 🔴 | Verified Software Toolchain for C | 活跃 | [Princeton](https://vst.cs.princeton.edu/) |
| **Bedrock** | Coq | 🔴 | 底层代码验证框架 | 活跃 | [MIT](https://bedrock.systems/) |
| **CN** | C | 🔴 | 可验证的 C 子集 | 活跃 | [GitHub](https://github.com/rems-project/cerberus) |
| **Gillian** | 多语言 | 🔴 | 符号执行平台 | 活跃 | [GitHub](https://github.com/GillianPlatform/Gillian) |

### 程序逻辑框架

| 工具名称 | 语言 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **CompCert** | C | 🔴 | 验证的 C 编译器 | 活跃 | [Inria](http://compcert.inria.fr/) |
| **CertiKOS** | C/Assembly | 🔴 | 验证的 OS 内核 | 活跃 | [Yale](https://flint.cs.yale.edu/certikos/) |
| **seL4** | C | 🔴 | 验证的操作系统微内核 | 活跃 | [seL4](https://sel4.systems/) |
| **Everest** | F* | 🔴 | 验证的安全协议栈 | 活跃 | [Microsoft](https://project-everest.github.io/) |
| **Fiat-Crypto** | Coq | 🔴 | 验证的加密原语 | 活跃 | [GitHub](https://github.com/mit-plv/fiat-crypto) |

### 重写和等价性

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **Coq** | 定理证明 | 🔴 | 归纳构造演算证明助手 | 活跃 | [Coq](https://coq.inria.fr/) |
| **Lean 4** | 定理证明 | 🔴 | 依赖类型定理证明器 | 活跃 | [Lean](https://lean-lang.org/) |
| **Isabelle/HOL** | 定理证明 | 🔴 | 高阶逻辑证明助手 | 活跃 | [Isabelle](https://isabelle.in.tum.de/) |
| **Agda** | 定理证明 | 🔴 | 依赖类型编程语言 | 活跃 | [Agda](https://agda.readthedocs.io/) |
| **Twelf** | LF | 🔴 | 逻辑框架 | 活跃 | [Twelf](http://twelf.org/) |

---

## 证明助手和定理证明器

### 主流证明助手

| 工具名称 | 逻辑基础 | 难度 | 功能特点 | 状态 | 链接 |
|----------|----------|------|----------|------|------|
| **Coq** | CiC | 🔴 | 最广泛使用的证明助手 | 活跃 | [Coq](https://coq.inria.fr/) |
| **Lean 4** | CIC + 其他 | 🔴 | 现代化的定理证明器 | 活跃 | [Lean](https://lean-lang.org/) |
| **Isabelle/HOL** | HOL | 🔴 | 高阶逻辑自动化强 | 活跃 | [Isabelle](https://isabelle.in.tum.de/) |
| **Agda** | Martin-Löf TT | 🔴 | 依赖类型编程 | 活跃 | [Agda](https://agda.readthedocs.io/) |
| **Idris 2** | 依赖类型 | 🔴 | 可编程类型系统 | 活跃 | [Idris](https://www.idris-lang.org/) |
| **Matita** | CiC | 🔴 | 意大利开发的证明助手 | 维护 | [Matita](http://matita.cs.unibo.it/) |
| **NuPRL** | 构造类型论 | 🔴 | 计算类型论先驱 | 活跃 | [NuPRL](http://www.nuprl.org/) |

### 自动化定理证明

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **E Theorem Prover** | ATP | 🔴 | 等式定理证明器 | 活跃 | [E](https://eprover.org/) |
| **Vampire** | ATP | 🔴 | 一阶逻辑自动证明 | 活跃 | [Vampire](https://vprover.github.io/) |
| **Prover9** | ATP | 🔴 | 等式和一阶逻辑 | 活跃 | [Prover9](https://www.cs.unm.edu/~mccune/prover9/) |
| **Metis** | ATP | 🔴 | 一阶逻辑证明器 | 活跃 | [GitHub](https://github.com/gilith/metis) |
| **Z3** | SMT | 🔴 | 可满足性模理论 | 活跃 | [GitHub](https://github.com/Z3Prover/z3) |
| **cvc5** | SMT | 🔴 | 最新的 SMT 求解器 | 活跃 | [GitHub](https://github.com/cvc5/cvc5) |

### 证明自动化库

| 库名称 | 目标 | 难度 | 功能特点 | 状态 | 链接 |
|--------|------|------|----------|------|------|
| **MathComp** | Coq | 🔴 | 数学组件库 | 活跃 | [GitHub](https://github.com/math-comp/math-comp) |
| **stdpp** | Coq | 🔴 | 标准库扩展 | 活跃 | [GitLab](https://gitlab.mpi-sws.org/iris/stdpp) |
| **Iris** | Coq | 🔴 | 分离逻辑框架 | 活跃 | [Website](https://iris-project.org/) |
| **mathlib4** | Lean 4 | 🔴 | 数学库 | 活跃 | [GitHub](https://github.com/leanprover-community/mathlib4) |
| **HOL-Library** | Isabelle | 🔴 | HOL 标准库 | 活跃 | [Isabelle](https://isabelle.in.tum.de/) |

---

## IDE 和编辑器插件

### Rust 专用 IDE 支持

| 工具名称 | 编辑器 | 难度 | 功能特点 | 状态 | 链接 |
|----------|--------|------|----------|------|------|
| **rust-analyzer** | VS Code/多 | 🟢 | Rust 官方 LSP 实现 | 活跃 | [GitHub](https://github.com/rust-lang/rust-analyzer) |
| **IntelliJ Rust** | IntelliJ | 🟢 | JetBrains 官方插件 | 活跃 | [JetBrains](https://www.jetbrains.com/rust/) |
| **Rust for VS Code** | VS Code | 🟢 | 官方插件（已合并到 rust-analyzer） | 归档 | [VS Code](https://marketplace.visualstudio.com/items?itemName=rust-lang.rust) |
| **Rustfmt** | 多 | 🟢 | 代码格式化集成 | 活跃 | [GitHub](https://github.com/rust-lang/rustfmt) |
| **Clippy** | 多 | 🟢 | Lint 集成 | 活跃 | [GitHub](https://github.com/rust-lang/rust-clippy) |

### 通用 IDE 插件

| 工具名称 | 编辑器 | 难度 | 功能特点 | 状态 | 链接 |
|----------|--------|------|----------|------|------|
| **CoqIDE** | 独立 | 🟡 | Coq 官方 IDE | 活跃 | [Coq](https://coq.inria.fr/) |
| **Coq LSP** | VS Code/Emacs | 🟡 | Coq 语言服务器 | 活跃 | [GitHub](https://github.com/ejgallego/coq-lsp) |
| **VsCoq** | VS Code | 🟡 | VS Code Coq 插件 | 活跃 | [GitHub](https://github.com/coq-community/vscoq) |
| **Lean 4 VS Code** | VS Code | 🟡 | 官方 Lean 4 插件 | 活跃 | [VS Code](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) |
| **Isabelle/jEdit** | jEdit | 🟡 | Isabelle 官方 IDE | 活跃 | [Isabelle](https://isabelle.in.tum.de/) |
| **Isabelle VS Code** | VS Code | 🟡 | VS Code Isabelle 插件 | 活跃 | [GitHub](https://github.com/makarius/vscode-isabelle) |
| **Agda Mode** | Emacs/VS Code | 🟡 | Agda 编辑器支持 | 活跃 | [Agda](https://agda.readthedocs.io/) |

### 辅助开发工具

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **Cargo** | 构建工具 | 🟢 | Rust 包管理器 | 活跃 | [官方](https://doc.rust-lang.org/cargo/) |
| **crates.io** | 包仓库 | 🟢 | Rust 包注册中心 | 活跃 | [crates.io](https://crates.io/) |
| **docs.rs** | 文档托管 | 🟢 | 自动文档生成 | 活跃 | [docs.rs](https://docs.rs/) |
| **lib.rs** | 包搜索 | 🟢 | 替代 crates.io 界面 | 活跃 | [lib.rs](https://lib.rs/) |
| **Cargo Watch** | 开发工具 | 🟢 | 文件变化自动构建 | 活跃 | [GitHub](https://github.com/watchexec/cargo-watch) |
| **Cargo Expand** | 开发工具 | 🟢 | 宏展开查看 | 活跃 | [GitHub](https://github.com/dtolnay/cargo-expand) |

---

## 测试和模糊测试工具

### Rust 测试工具

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **built-in test** | 单元测试 | 🟢 | Rust 内置测试框架 | 内置 | [官方](https://doc.rust-lang.org/book/ch11-01-writing-tests.html) |
| **Criterion** | 基准测试 | 🟢 | 统计基准测试 | 活跃 | [GitHub](https://github.com/bheisler/criterion.rs) |
| **Proptest** | 属性测试 | 🟡 | 基于假设的测试 | 活跃 | [GitHub](https://github.com/AltSysrq/proptest) |
| **Quickcheck** | 属性测试 | 🟡 | Haskell QuickCheck 移植 | 活跃 | [GitHub](https://github.com/BurntSushi/quickcheck) |
| **Mockall** | Mock | 🟡 | 强大的 Mock 框架 | 活跃 | [GitHub](https://github.com/asomers/mockall) |
| **Fake** | 测试数据 | 🟢 | 生成假数据 | 活跃 | [GitHub](https://github.com/cksac/fake-rs) |

### 模糊测试工具

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **Cargo Fuzz** | 模糊测试 | 🟡 | libFuzzer 集成 | 活跃 | [GitHub](https://github.com/rust-fuzz/cargo-fuzz) |
| **AFL.rs** | 模糊测试 | 🟡 | AFL 模糊测试器 | 活跃 | [GitHub](https://github.com/rust-fuzz/afl.rs) |
| **Honggfuzz** | 模糊测试 | 🟡 | 覆盖率引导模糊测试 | 活跃 | [GitHub](https://github.com/rust-fuzz/honggfuzz-rs) |
| **Bolero** | 模糊测试 | 🟡 | 统一测试框架 | 活跃 | [GitHub](https://github.com/camshaft/bolero) |
| **LibAFL** | 模糊测试 | 🔴 | 可定制的模糊测试框架 | 活跃 | [GitHub](https://github.com/AFLplusplus/LibAFL) |

### 符号执行工具

| 工具名称 | 支持语言 | 难度 | 功能特点 | 状态 | 链接 |
|----------|----------|------|----------|------|------|
| **KLEE** | LLVM | 🔴 | 符号执行引擎 | 活跃 | [GitHub](https://github.com/klee/klee) |
| **Angr** | 二进制 | 🔴 | Python 二进制分析 | 活跃 | [GitHub](https://github.com/angr/angr) |
| **Triton** | 二进制 | 🔴 | 动态二进制分析 | 活跃 | [GitHub](https://github.com/JonathanSalwan/Triton) |
| **S2E** | 多语言 | 🔴 | 选择性符号执行 | 活跃 | [GitHub](https://github.com/S2E/s2e) |
| **Manticore** | EVM/WASM | 🔴 | 智能合约分析 | 活跃 | [GitHub](https://github.com/trailofbits/manticore) |

---

## 文档和代码生成工具

### 文档工具

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **rustdoc** | 文档生成 | 🟢 | Rust 官方文档工具 | 内置 | [官方](https://doc.rust-lang.org/rustdoc/) |
| **mdBook** | 文档生成 | 🟢 | Rust 文档书生成器 | 活跃 | [GitHub](https://github.com/rust-lang/mdBook) |
| **docs.rs** | 文档托管 | 🟢 | 自动文档托管 | 活跃 | [docs.rs](https://docs.rs/) |
| **Rustlings** | 学习工具 | 🟢 | 小练习集合 | 活跃 | [GitHub](https://github.com/rust-lang/rustlings) |
| **Rust by Example** | 教程 | 🟢 | 实例教程 | 活跃 | [官方](https://doc.rust-lang.org/rust-by-example/) |

### 代码生成工具

| 工具名称 | 类型 | 难度 | 功能特点 | 状态 | 链接 |
|----------|------|------|----------|------|------|
| **bindgen** | FFI | 🟡 | C/C++ 头文件绑定生成 | 活跃 | [GitHub](https://github.com/rust-lang/rust-bindgen) |
| **cbindgen** | FFI | 🟡 | Rust 到 C 头文件生成 | 活跃 | [GitHub](https://github.com/mozilla/cbindgen) |
| **prost** | 代码生成 | 🟡 | Protocol Buffers 代码生成 | 活跃 | [GitHub](https://github.com/tokio-rs/prost) |
| **tonic** | 代码生成 | 🟡 | gRPC 代码生成 | 活跃 | [GitHub](https://github.com/hyperium/tonic) |
| **serde** | 序列化 | 🟡 | 序列化框架 | 活跃 | [GitHub](https://github.com/serde-rs/serde) |
| **StructOpt** | CLI | 🟢 | 命令行参数解析 | 活跃 | [GitHub](https://github.com/TeXitoi/structopt) |
| **clap** | CLI | 🟢 | 命令行解析器 | 活跃 | [GitHub](https://github.com/clap-rs/clap) |

---

## 📊 工具统计

### 按类别统计

| 类别 | 工具数量 | 占比 |
|------|----------|------|
| Rust 验证工具 | 15 | 16% |
| 通用验证工具 | 18 | 19% |
| 静态分析工具 | 20 | 21% |
| 形式化方法框架 | 12 | 13% |
| 证明助手 | 15 | 16% |
| IDE/编辑器插件 | 12 | 13% |
| 测试/模糊测试 | 15 | 16% |
| 文档/代码生成 | 10 | 11% |

### 按难度统计

| 难度等级 | 工具数量 | 占比 |
|----------|----------|------|
| 🟢 入门级 | 25 | 27% |
| 🟡 中级 | 20 | 21% |
| 🔴 高级 | 48 | 52% |

### 按活跃度统计

| 活跃度 | 工具数量 | 占比 |
|--------|----------|------|
| 活跃维护 | 75 | 81% |
| 维护中 | 12 | 13% |
| 研究/实验 | 6 | 6% |

---

## 🎯 工具选择指南

### 场景一：Rust 代码验证入门

**推荐工具链**:

```text
1. Miri - 理解 Rust 语义和 unsafe 行为
2. Clippy - 代码质量检查
3. Cargo Fuzz - 发现边界情况
4. Kani - 有界验证简单属性
```

### 场景二：生产级 Rust 验证

**推荐工具链**:

```text
1. Creusot - 完整功能规范验证
2. Prusti - 使用 Viper 后端验证
3. Verus - 系统级代码验证
4. Miri + Sanitizers - 运行时检查
```

### 场景三：学术研究和教学

**推荐工具链**:

```text
1. Aeneas - 学习函数式验证方法
2. Iris (Coq) - 分离逻辑研究
3. Why3 - 泛型验证概念学习
4. TLA+ - 分布式系统规约
```

### 场景四：安全关键系统

**推荐工具链**:

```text
1. seL4 + CAmkES - 微内核验证
2. CompCert - 验证的编译
3. Coq/Isabelle - 形式化证明
4. Kani + MIRAI - Rust 专用验证
```

---

## 🔗 相关资源

- [学术论文分类](./academic-papers.md) - 这些工具背后的理论基础
- [书籍和资源索引](./books-resources.md) - 学习使用这些工具的教材
- [在线课程](./online-courses.md) - 教授这些工具的课程
- [核心文献速查](./bibliography.md) - 工具相关的核心论文

---

**最后更新**: 2026-03-04
**维护者**: Rust 所有权可判定性研究项目
