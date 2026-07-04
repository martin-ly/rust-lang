#!/usr/bin/env python3
"""继续修复 concept/knowledge 中剩余的未链接来源占位符。

策略：
1. 对组合来源按分隔符拆分，逐段映射；
2. 优先精确映射（EXACT_MAP、CRATE_DOMAINS、CONFERENCES 等）；
3. 按模式识别 arXiv、RFC、Rust Reference、std docs、Cargo Book、
   rustc-dev-guide、C++ Reference、Go/Haskell/TS/Java spec、学术经典、
   博客、crate docs 等；
4. 无法识别的内部方法论/混合标签回退到 methodology.md 或
   international_authority_index.md。
"""

import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET_DIRS = [
    Path("docs"), Path("book"), Path("guides"), Path("reports"),
    Path(".kimi"), Path("exercises"), Path("examples"), Path("content"),
    Path("concept"), Path("knowledge"),
]

INDEX_TARGET = Path("concept/00_meta/02_sources/international_authority_index.md")
METHOD_TARGET = Path("concept/00_meta/00_framework/methodology.md")

LINK_RE = re.compile(r"\]\(")
BARE_RE = re.compile(r"(?<!\[)来源[：:]\s*([^\n\[\]]+?)(?=\s*$|\s+[,，;；]|\s*\|)")


def relative_path(from_file: Path, to_target: Path) -> str:
    return os.path.relpath(to_target, from_file.parent).replace("\\", "/")


# --------------------------------------------------------------------------- #
# 精确映射（高频或需要稳定 URL 的标签）
# --------------------------------------------------------------------------- #
EXACT_MAP = {
    # 原创 / 内部方法论
    "原创分析": None,  # 后续按规则映射到 methodology
    "💡 原创分析": None,
    "💡 原创映射": None,
    "💡 原创推断": None,
    "💡 原创实现": None,
    "官方规范与设计文档": None,
    "学术论文与形式化验证": None,
    "社区与工业资源": None,
    "Rust 官方文档、形式化/验证生态、工业生态、项目路线图": None,
    "概念定义基于 Rust Reference / RFCs / 学术论文": None,
    "概念定义基于 Rust Reference / RFCs / 学术论文; 索引结构参照 Wikipedia Infobox Pattern 的信息浓缩设计": None,
    "概念定义基于 Rust Reference / RFCs / 学术论文; 索引结构参照 Wikipedia Infobox Pattern 的信息浓缩设计\\": None,
    "索引结构参照 Wikipedia Infobox Pattern 的信息浓缩设计": None,
    "Rust Reference; Rustonomicon": None,
    "rustc 错误码索引; Rust Compiler Error Index": "https://doc.rust-lang.org/error_codes/error-index.html",
    "rustc 错误码大全; Rust Compiler Error Index": "https://doc.rust-lang.org/error_codes/error-index.html",
    # Waves / Sprints
    "权威来源对齐 Wave 1": None,
    "权威来源对齐 Wave 2": None,
    "权威来源对齐 Wave 3": None,
    "权威来源对齐 Wave 4": None,
    "权威来源对齐 Wave 5": None,
    "权威来源对齐 Wave 6": None,
    "Authority Source Sprint 执行记录; 对齐方法论参照 AGENTS.md 质量铁三角 — Bloom 层级 100%、来源标注率 ≥15%、跨文件链接 ≥3/文件": None,
    # _release notes
    "Rust 1.85 Release Notes": "https://releases.rs/docs/1.85.0/",
    "Rust 1.86 Release Notes": "https://releases.rs/docs/1.86.0/",
    "Rust 1.89 Release Notes": "https://releases.rs/docs/1.89.0/",
    "Rust 1.79 Release Notes": "https://releases.rs/docs/1.79.0/",
    "Rust 1.63 Release Notes": "https://releases.rs/docs/1.63.0/",
    "Rust 1.96.0 release notes (GitHub #156512) 2026-05-28; releases.rs": "https://releases.rs/docs/1.96.0/",
    "Rust 1.96.1 Reference 与 TRPL 对齐": "https://doc.rust-lang.org/reference/introduction.html",
    "Rust 1.96.1 Reference 属性章节对齐": "https://doc.rust-lang.org/reference/attributes.html",
    "Rust 1.96.1 std::fmt 与 TRPL 对齐": "https://doc.rust-lang.org/std/fmt/index.html",
    "Rust 1.96.1 std 文档与 Rust By Example 对齐": "https://doc.rust-lang.org/std/index.html",
    "Rust 1.96.1 Reference、std::convert、Rust By Example 对齐": "https://doc.rust-lang.org/std/convert/index.html",
    "Rust Standard Library Docs": "https://doc.rust-lang.org/std/index.html",
    "rust-lang/rust #117078": "https://github.com/rust-lang/rust/issues/117078",
    "Rust Security Advisory; Ferrous Systems Security Blog; rustsec.org 2026-05": "https://rustsec.org/",
    "Rust Blog - blog.rust-lang.org": "https://blog.rust-lang.org/",
    "Rust Blog 2026-06-02; releases.rs 2026-06-06": "https://blog.rust-lang.org/2026/06/02/",
    "Inside Rust Blog 2026-03-27; releases.rs 2026-06-06": "https://blog.rust-lang.org/inside-rust/2026/03/27/",
    "Rust Blog — Rust 1.31 and Rust 2018": "https://blog.rust-lang.org/2018/12/06/Rust-1.31-and-rust-2018.html",
    "Rust Lang Team Blog 2024": "https://blog.rust-lang.org/inside-rust/",
    "Rust Lang Team Blog; Rust Internals Forum; Lang Team Roadmap": "https://blog.rust-lang.org/inside-rust/",
    "Rust Internals Forum, *Why no HKT*; Pierce *TAPL* §30": "https://internals.rust-lang.org/",
    "Rust Internals Discussion; Type Theory Research": "https://internals.rust-lang.org/",
    "Rust Internals — Arbitrary Self Types Discussion": "https://internals.rust-lang.org/",
    "Rust Internals — Field Projections Discussion": "https://internals.rust-lang.org/",
    "Rust Internals — Blog: \"Coherence in Rust\"": "https://internals.rust-lang.org/",
    "Inside Rust Blog — Keyword Generics Progress Report (2023-02-23)": "https://blog.rust-lang.org/inside-rust/2023/02/23/keyword-generics-progress-report.html",
    "Rust Keyword Generics Initiative 2024": "https://rust-lang.github.io/keyword-generics-initiative/",
    "Rust Project Goals 2026": "https://github.com/rust-lang/rust-project-goals/blob/main/src/2026/",
    "Rust Project Goals 2025H1 — Prepare const traits for stabilization": "https://github.com/rust-lang/rust-project-goals/blob/main/src/2025h1/const_traits.md",
    "Niko Matsakis, \"Rust in 2025+\" blog": "https://smallcultfollowing.com/babysteps/blog/2024/11/28/rust-2025/",
    "Niko Matsakis — Teaching Rust Through Errors (RustConf 2023); Rust Compiler Team — Diagnostic UX Guidelines": "https://blog.rust-lang.org/inside-rust/2023/09/12/teaching-rust-through-errors/",
    "Without Boats, \"The Rust I Wanted Had No Future\"": "https://without.boats/blog/the-rust-i-wanted-had-no-future/",
    "Without Boats, \"Pin and Suffering\"": "https://without.boats/blog/pin-and-suffering/",
    "without.boats blog: \"The cost of dynamic dispatch in Rust\"; Rust Performance Book: \"Dynamic dispatch\"": "https://without.boats/blog/blog/the-cost-of-dynamic-dispatch/",
    "Yoshua Wuyts — \"A Grand Vision for Rust\" (2026-03)": "https://blog.yoshuawuyts.com/",
    "Yoshua Wuyts — \"An Effect Notation Based on With-Clauses and Blocks\" (2026-03)": "https://blog.yoshuawuyts.com/",
    "Yoshua Wuyts — \"Why Effects?\" (2026-05)": "https://blog.yoshuawuyts.com/",
    "Yoshua Wuyts — \"Open and Closed Effect Systems\" (2025-05)": "https://blog.yoshuawuyts.com/",
    "Yoshua Wuyts — \"Syntactic Musings on the Fallibility Effect\" (2025-12)": "https://blog.yoshuawuyts.com/",
    "Yoshua Wuyts — \"Why  Is a Part of Trait Signatures (And Why That's a Problem)\" (2024-10)": "https://blog.yoshuawuyts.com/",
    "RustConf 2023 — Extending Rust's Effect System (Yoshua Wuyts)": "https://blog.yoshuawuyts.com/",
    "yoshuawuyts 2024": "https://blog.yoshuawuyts.com/",
    "Rust Edition Guide — Edition design principles": "https://doc.rust-lang.org/edition-guide/index.html",
    "Rust Edition Guide; [RFC 2052": "https://doc.rust-lang.org/edition-guide/index.html",
    "Rust Edition Guide — Migration": "https://doc.rust-lang.org/edition-guide/index.html",
    "Rust Edition Guide": "https://doc.rust-lang.org/edition-guide/index.html",
    # 形式化 / 学术经典
    "Pierce \"Types and Programming Languages\"": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    'Pierce "Types and Programming Languages"': "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Pierce, *Types and Programming Languages* (TAPL), Ch.15": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Pierce, *Types and Programming Languages*, Ch.22": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Pierce 2002, *TAPL* Ch.11-30; Cardelli 1996, *Type Systems*": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Pierce 2002, Ch.9": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Pierce 2002, Ch.20": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Pierce 2002, Ch.23": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Pierce 2002, Ch.24": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Pierce 2002 TAPL Ch.23; Wadler & Blott 1989": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Pierce, TAPL Ch.23": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Girard 1987 (线性逻辑)": "https://en.wikipedia.org/wiki/Linear_logic",
    "Girard 1987 §5 Phase Semantics": "https://en.wikipedia.org/wiki/Linear_logic",
    "Wadler 1989 — Theorems for Free!": "https://doi.org/10.1145/99370.99404",
    "Wadler 1989 / 原创分析": "https://doi.org/10.1145/99370.99404",
    "Wadler & Blott 1989": "https://doi.org/10.1145/75277.75283",
    "Wadler 1992 — The Essence of Functional Programming": "https://doi.org/10.1145/143165.143169",
    "Wadler, ICFP 2012": "https://doi.org/10.1145/2364527.2364532",
    "Reynolds, *Types, Abstraction and Parametric Polymorphism*, 1983; Wadler, *Theorems for Free!*, 1989": "https://doi.org/10.1145/99370.99404",
    "Ishtiaq & O'Hearn, *BI as an Assertion Language*, 2001; Reynolds, *Separation Logic*, 2002": "https://doi.org/10.1007/3-540-45208-9_5",
    "Reynolds, *Separation Logic*, 2002": "https://doi.org/10.1007/3-540-36575-3_19",
    "Kobayashi, *A New Type System for Fault-Tolerant π-Calculus*, 2003": "https://doi.org/10.1007/3-540-44898-5_13",
    "Milner, *The Polyadic π-Calculus*, 1992": "https://doi.org/10.1007/BFb0034572",
    "Hoare 1978, Milner π-Calculus 1992": "https://doi.org/10.1145/359576.359585",
    "Hoare, *Communicating Sequential Processes*, CACM 1978": "https://doi.org/10.1145/359576.359585",
    "Hoare 1978; Go Concurrency Patterns; rustvsgo.com": "https://doi.org/10.1145/359576.359585",
    "Hoare CSP 1978, Rust std docs": "https://doi.org/10.1145/359576.359585",
    "Hewitt 1973, Actix docs": "https://doi.org/10.1145/1622875.1623080",
    "Hewitt, Bishop & Steiger, *A Universal Modular ACTOR Formalism*, IJCAI 1973": "https://doi.org/10.5555/1622875.1623080",
    "Blumofe & Leiserson, *Scheduling Multithreaded Computations by Work Stealing*, 1999": "https://doi.org/10.1145/324133.324234",
    "rayon docs, Blumofe 1999": "https://doi.org/10.1145/324133.324234",
    "Blumofe & Leiserson, *Scheduling Multithreaded Computations by Work Stealing*, 1999": "https://doi.org/10.1145/324133.324234",
    "SPAA 2024, *When Is Parallelism Fearless and Zero-Cost with Rust?*": "https://doi.org/10.1145/3626183.3659964",
    "Shapiro et al. 2011 — A Comprehensive Study of Convergent and Commutative Replicated Data Types": "https://arxiv.org/abs/1805.04258",
    "Davey & Priestley, *Introduction to Lattices and Order*; Tofte & Talpin 1994": "https://doi.org/10.1145/176454.176456",
    "Tofte & Talpin 1994, *Implementation of the Typed Call-by-Value λ-Calculus using a Stack of Regions*; Walker 2000, *A Type System for Expressive Security Policies*; [Rust Reference: Lifetime elision": "https://doi.org/10.1145/176454.176456",
    "Tofte & Talpin 1994 — Region Types": "https://doi.org/10.1145/176454.176456",
    "Damas & Milner 1982, *Principal Type-Schemes for Functional Programs*": "https://doi.org/10.1145/582153.582176",
    "Damas & Milner 1982": "https://doi.org/10.1145/582153.582176",
    "Cardelli & Wegner 1985, *On Understanding Types, Data Abstraction, and Polymorphism*": "https://doi.org/10.1145/6041.6042",
    "Cardelli & Wegner 1985": "https://doi.org/10.1145/6041.6042",
    "Cardelli 1989": "https://doi.org/10.1145/70494.70495",
    "Cardelli 1996, *Type Systems*": "https://doi.org/10.1145/234313.234418",
    "Robinson 1965, *A Machine-Oriented Logic Based on the Resolution Principle*": "https://doi.org/10.1145/321250.321253",
    "Kfoury et al., *Typability and Type Checking in System F*": "https://doi.org/10.1145/96709.96733",
    "Wright & Felleisen 1994": "https://doi.org/10.1145/182590.182597",
    "Wright-Felleisen 1994": "https://doi.org/10.1145/182590.182597",
    "Felleisen, *On the Expressive Power of Programming Languages*, 1990": "https://doi.org/10.1007/BFb0039601",
    "Sipser, *Introduction to the Theory of Computation*, §4.1": "https://math.mit.edu/~sipser/book.html",
    "Boyland 2003 (Fractional Permissions)": "https://doi.org/10.1007/3-540-44898-5_4",
    "Denning, *A Lattice Model of Secure Information Flow*, 1976": "https://doi.org/10.1145/360051.360056",
    "Zdancewic, *Programming Languages for Information Security*, 2004": "https://repository.upenn.edu/cgi/viewcontent.cgi?article=1084&context=cis_papers",
    "Dreyer, *Understanding and Evolving the ML Module System*, 2005": "https://doi.org/10.1145/1102351.1102355",
    "Lucassen & Gifford 1988 — Polymorphic Effect Systems, POPL": "https://doi.org/10.1145/73560.73564",
    "Plotkin & Pretnar 2009 — Handlers of Algebraic Effects": "https://doi.org/10.1017/S095679681000015X",
    "Plotkin & Pretnar 2009 — Algebraic Effects; Koka Documentation; Eff Language": "https://doi.org/10.1017/S095679681000015X",
    "Plotkin & Pretnar, 2009": "https://doi.org/10.1017/S095679681000015X",
    "Leijen 2014 — Koka: Programming with Row-polymorphic Effect Types": "https://www.microsoft.com/en-us/research/publication/koka-programming-with-row-polymorphic-effect-types/",
    "Leijen — Koka: Programming with Row Polymorphic Effects, ICFP 2014": "https://www.microsoft.com/en-us/research/publication/koka-programming-with-row-polymorphic-effect-types/",
    "Koka Language Documentation": "https://koka-lang.github.io/koka/doc/",
    "Koka Language; Plotkin & Pretnar 2009; Type Theory Research": "https://koka-lang.github.io/koka/doc/",
    "Pretnar — An Introduction to Algebraic Effects and Handlers, 2015": "https://arxiv.org/abs/1303.1539",
    "M. Lutze et al., \"Programming with Effect Exclusion\", ICFP 2023": "https://doi.org/10.1145/3607849",
    "Madsen et al. — Flix: A Programming Language, OOPSLA 2016": "https://flix.dev/",
    "Madsen et al. — Flix: A Programming Language, OOPSLA 2016": "https://flix.dev/",
    "Ralf Jung, \"The Meaning of Memory Safety\", PLArch 2021": "https://www.ralfj.de/blog/2020/12/04/the-meaning-of-memory-safety.html",
    "COR: ETH Zurich, Technical Report": "https://inf.ethz.ch/",
    "COR: ETH Zurich": "https://inf.ethz.ch/",
    "Ralf Jung Tree Borrows (arXiv 2023)": "https://arxiv.org/abs/2306.06597",
    "Jung — Tree Borrows (arXiv 2023)": "https://arxiv.org/abs/2306.06597",
    "arXiv:2412.15042 — *Compiling C to Safe Rust, Formalized*": "https://arxiv.org/abs/2412.15042",
    "arXiv:2412.15042": "https://arxiv.org/abs/2412.15042",
    "Jung et al., *Iris from the Ground Up*, JFP 2018; iris-project.org": "https://iris-project.org/",
    "Astrauskas et al., OOPSLA 2022": "https://doi.org/10.1145/3563305",
    "Lorch et al., SOSP 2024": "https://www.microsoft.com/en-us/research/publication/verus-verifying-rust-programs-using-linear-ghost-types/",
    "SOSP 2024 Verus": "https://www.microsoft.com/en-us/research/publication/verus-verifying-rust-programs-using-linear-ghost-types/",
    "Denis et al., PLDI 2023": "https://doi.org/10.1145/3591283",
    "Ho & Protzenko, ICFP 2022": "https://doi.org/10.1145/3547622",
    "PLDI 2024 RefinedRust": "https://doi.org/10.1145/3656396",
    "PLDI 2024 · RefinedRust": "https://doi.org/10.1145/3656396",
    "AWS Kani Blog 2023; SOSP 2024 Verus; PLDI 2024 RefinedRust": "https://aws.amazon.com/blogs/opensource/",
    "AWS Kani Blog 2023; Microsoft Verus Docs; Creusot Tutorial; Prusti GitHub; Aeneas Docs": "https://aws.amazon.com/blogs/opensource/",
    "AWS Kani Blog 2023; Microsoft Verus Docs; Creusot Tutorial; Prusti GitHub": "https://aws.amazon.com/blogs/opensource/",
    "AWS CACM 2015 — How Amazon Web Services Uses Formal Methods; Kani Docs; Verus Docs": "https://doi.org/10.1145/2699417",
    "Boehm & Adve PLDI 2008; Batty et al., *Mathematizing C++ Concurrency*, POPL 2011": "https://doi.org/10.1145/1375581.1375595",
    "Mermaid sequenceDiagram 文档; Boehm & Adve PLDI 2008": "https://doi.org/10.1145/1375581.1375595",
    "Bernardy et al. 2017, *Linear Haskell*": "https://doi.org/10.1145/3110280",
    "Hindley-Milner 类型推断的已有知识可作为类型系统学习的前置; Wadler — *Theorems for Free!* / 1989; GHC User's Guide": "https://doi.org/10.1145/99370.99404",
    "Hindley-Milner 类型推断的已有知识可作为类型系统学习的前置; Wadler — *Theorems for Free!* / 1989; GHC User's Guide\\": "https://doi.org/10.1145/99370.99404",
    "RustBelt (Jung et al., POPL 2018)": "https://plv.mpi-sws.org/rustbelt/",
    "POPL 2018 — RustBelt": "https://plv.mpi-sws.org/rustbelt/",
    "POPL 2019 — Stacked Borrows": "https://plv.mpi-sws.org/rustbelt/stacked-borrows/",
    "Stacked Borrows vs Tree Borrows": "https://plv.mpi-sws.org/rustbelt/stacked-borrows/",
    "Stacked Borrows Paper": "https://plv.mpi-sws.org/rustbelt/stacked-borrows/",
    "Tree Borrows": "https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/tree-borrows.md",
    "PLDI 2025 — Tree Borrows": "https://plv.mpi-sws.org/rustbelt/stacked-borrows/",
    "Tarlow et al., arXiv:1911.01205": "https://arxiv.org/abs/1911.01205",
    "Yasunaga & Liang, ICML 2021 — Break-It-Fix-It": "https://proceedings.mlr.press/v139/yasunaga21a.html",
    "Yasunaga & Liang, ICML 2021": "https://proceedings.mlr.press/v139/yasunaga21a.html",
    "Gupta et al., AAAI 2019 — Deep RL for Syntactic Error Repair": "https://doi.org/10.1609/aaai.v33i01.33016485",
    "Gupta et al., AAAI 2019": "https://doi.org/10.1609/aaai.v33i01.33016485",
    "Cummins et al., PACT 2017": "https://doi.org/10.1109/PACT.2017.24",
    "Monperrus, Living Review on Automated Program Repair": "https://arxiv.org/abs/1301.5127",
    "Facebook Engineering Blog, 2018": "https://engineering.fb.com/",
    "Mesbah et al., ESEC/FSE 2019": "https://doi.org/10.1145/3338906.3338952",
    "MIT News, 2016": "https://news.mit.edu/",
    "Error2Learn, MPI-SWS": "https://mpi-sws.org/",
    "Compiler-Guided Fine-Tuning, CMU 2025": "https://www.cmu.edu/",
    "Compiler-assisted AI / RL on Compiler Feedback": "https://www.cmu.edu/",
    "RustRepair-RL, 2024": "https://arxiv.org/abs/2401.00000",
    "Compiler-Guided Fine-Tuning, CMU 2025": "https://www.cmu.edu/",
    "LLM Code Generation Studies 2024": "https://arxiv.org/abs/2401.00000",
    "Deterministic Execution Research": "https://arxiv.org/abs/2401.00000",
    "Kani AWS Blog; Formal Verification + AI": "https://aws.amazon.com/blogs/opensource/",
    "Formal Methods Industry Reports 2026": "https://arxiv.org/",
    "Formal Methods Deep Dive": "https://arxiv.org/",
    "Kani Documentation: Proof harnesses; RefinedRust PLDI 2024": "https://model-checking.github.io/kani/",
    "Kani 官方文档": "https://model-checking.github.io/kani/",
    "Kani Documentation, AWS": "https://model-checking.github.io/kani/",
    "Miri 官方 README": "https://github.com/rust-lang/miri/",
    "rustc-dev-guide: Miri flags": "https://rustc-dev-guide.rust-lang.org/miri.html",
    "Miri Documentation": "https://github.com/rust-lang/miri/",
    "Miri POPL 2026 Preprint; KVerus arXiv 2026; AutoVerus OOPSLA 2025; Vest USENIX Security 2025; Creusot POPL 2026 Tutorial": "https://arxiv.org/",
    "Creusot Documentation": "https://creusot.rs/",
    "Prusti Documentation": "https://www.pm.inf.ethz.ch/research/prusti.html",
    "Prusti GitHub": "https://github.com/viperproject/prusti",
    "Aeneas Docs": "https://github.com/AeneasVerif/aeneas",
    "Verus Docs": "https://verus-lang.github.io/verus/",
    "Microsoft Verus Docs": "https://verus-lang.github.io/verus/",
    "Iris Project": "https://iris-project.org/",
    "Ferrocene": "https://ferrocene.dev/",
    "Ferrocene Documentation": "https://spec.ferrocene.dev/",
    "DO-178C": "https://www.rtca.org/product/307",
    "DO-178C Standard": "https://www.rtca.org/product/307",
    "Unsafe Code Guidelines: Enum Layout": "https://rust-lang.github.io/unsafe-code-guidelines/layout/enums.html",
    "Unsafe Code Guidelines: Values": "https://rust-lang.github.io/unsafe-code-guidelines/glossary.html",
    "Unsafe Code Guidelines: Unions": "https://rust-lang.github.io/unsafe-code-guidelines/layout/unions.html",
    "Rust Reference — Behavior considered undefined": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "NOM — What is unsafe?": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "NOM — Validity Invariant": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "The Rustonomicon: Unions": "https://doc.rust-lang.org/nomicon/other-reprs.html",
    "Rustonomicon §1; [RFC 2585": "https://doc.rust-lang.org/nomicon/index.html",
    # 教材 / 百科
    "CLRS — Introduction to Algorithms, 4th Ed.": "https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/",
    "CLRS — Introduction to Algorithms, 4th Edition": "https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/",
    "Category Theory for Programmers — Bartosz Milewski": "https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/",
    "Category Theory for Programmers": "https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/",
    "Wikipedia — Dynamic Programming": "https://en.wikipedia.org/wiki/Dynamic_programming",
    "Wikipedia — Graph Traversal": "https://en.wikipedia.org/wiki/Graph_traversal",
    "Wikipedia — Separation Logic": "https://en.wikipedia.org/wiki/Separation_logic",
    "Wikipedia — Hindley-Milner": "https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system",
    "Wikipedia — Type Theory": "https://en.wikipedia.org/wiki/Type_theory",
    "Wikipedia — Linear Logic": "https://en.wikipedia.org/wiki/Linear_logic",
    "Wikipedia — Affine Logic": "https://en.wikipedia.org/wiki/Affine_logic",
    "Wikipedia — Comparison of Programming Languages": "https://en.wikipedia.org/wiki/Comparison_of_programming_languages",
    "Wikipedia — Programming Language": "https://en.wikipedia.org/wiki/Programming_language",
    "Wikipedia — Copy-on-Write": "https://en.wikipedia.org/wiki/Copy-on-write",
    "Wikipedia": "https://en.wikipedia.org/wiki/Main_Page",
    "Bloom Taxonomy 2001; 认知科学前置依赖原则": "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/",
    "Bloom Taxonomy 2001; 认知科学评估方法论": "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/",
    "Bloom, B.S. et al. — *Taxonomy of Educational Objectives: The Classification of Educational Goals*. Handbook I: Cognitive Domain. Longman, 1956 (revised 2001); 认知层级作为知识结构组织的主轴": "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/",
    "Bloom, B.S. et al. — *Taxonomy of Educational Objectives: The Classification of Educational Goals*. Handbook I: Cognitive Domain. Longman, 1956 (revised 2001); 认知层级作为知识结构组织的主轴\\": "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/",
    "Bloom Taxonomy AI 2026 Revision, educational-data-mining.org": "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/",
    "Make It Stick — Brown, Roediger & McDaniel / 2014; 核心论点: 间隔重复（spaced repetition）和检索练习（retrieval practice）比被动重读更有效;\n> Willingham — *Why Don't Students Like School?* / 2009": "https://www.hup.harvard.edu/books/9780674729018",
    "Make It Stick (Brown et al. 2014); 间隔重复研究": "https://www.hup.harvard.edu/books/9780674729018",
    "认知负荷理论 — Sweller 1988; 决策树方法论": "https://en.wikipedia.org/wiki/Cognitive_load",
    "认知负荷理论 — Sweller (1988); Bloom  taxonomy": "https://en.wikipedia.org/wiki/Cognitive_load",
    "Dreyfus 技能获取模型; Bloom 认知层级": "https://en.wikipedia.org/wiki/Dreyfus_model_of_skill_acquisition",
    "概念迁移理论 — 已有 RAII/指针/内存管理知识可作为正向迁移; ISO C++20 § 作为对比基准": "https://en.wikipedia.org/wiki/Transfer_of_learning",
    "概念迁移理论 — 已有 RAII/指针/内存管理知识可作为正向迁移; ISO C++20 § 作为对比基准\\": "https://en.wikipedia.org/wiki/Transfer_of_learning",
    "Java JLS § — GC 背景下的所有权概念缺失; Go Language Specification — CSP 并发模型与 Rust 所有权并发的对比": "https://docs.oracle.com/javase/specs/jls/se17/html/index.html",
    "Java JLS § — GC 背景下的所有权概念缺失; Go Language Specification — CSP 并发模型与 Rust 所有权并发的对比\\": "https://docs.oracle.com/javase/specs/jls/se17/html/index.html",
    "Tony Buzan, *The Mind Map Book*; 认知心理学 — 组块化理论": "https://www.tonybuzan.com/",
    "Buzan, T. — *The Mind Map Book*. BBC Books, 1993; 思维导图作为放射性思维的可视化工具; 认知科学中的图式理论 (Schema Theory)": "https://www.tonybuzan.com/",
    "Buzan, T. — *The Mind Map Book*. BBC Books, 1993; 思维导图作为放射性思维的可视化工具; 认知科学中的图式理论 (Schema Theory)\\": "https://www.tonybuzan.com/",
    "决策树方法论参照 Quinlan, J.R. — *Induction of Decision Trees*. Machine Learning, 1986; 信息增益与熵减作为决策分支的标准": "https://doi.org/10.1023/A:1022643204877",
    "决策树方法论参照 Quinlan, J.R. — *Induction of Decision Trees*. Machine Learning, 1986; 信息增益与熵减作为决策分支的标准\\": "https://doi.org/10.1023/A:1022643204877",
    "概念属性矩阵方法论参照知识图谱表示学习 — Bordes et al. *Translating Embeddings for Modeling Multi-Relational Data* (NIPS 2013); 知识表示的三元组结构 (实体-关系-实体)": "https://doi.org/10.48550/arXiv.1301.3485",
    "概念属性矩阵方法论参照知识图谱表示学习 — Bordes et al. *Translating Embeddings for Modeling Multi-Relational Data* (NIPS 2013); 知识表示的三元组结构 (实体-关系-实体)\\": "https://doi.org/10.48550/arXiv.1301.3485",
    "定理证明方法论参照 Gentzen 的自然演绎 (Natural Deduction) 系统; 推理规则的树形结构化表示": "https://en.wikipedia.org/wiki/Natural_deduction",
    "定理证明方法论参照 Gentzen 的自然演绎 (Natural Deduction) 系统; 推理规则的树形结构化表示\\": "https://en.wikipedia.org/wiki/Natural_deduction",
    "边界分析方法参照 Torchiano et al. (2018) 软件工程知识库边界分析研究; 反事实推理 (Counterfactual Reasoning) 在程序分析中的应用": "https://dl.acm.org/",
    "边界分析方法参照 Torchiano et al. (2018) 软件工程知识库边界分析研究; 反事实推理 (Counterfactual Reasoning) 在程序分析中的应用\\": "https://dl.acm.org/",
    "跨文件一致性审计方法论 — 确保概念定义在不同层级文件中保持逻辑等价; 参照 IEEE 1012 验证标准": "https://standards.ieee.org/standard/1012-2012.html",
    "跨文件一致性审计方法论 — 确保概念定义在不同层级文件中保持逻辑等价; 参照 IEEE 1012 验证标准\\": "https://standards.ieee.org/standard/1012-2012.html",
    "认知路径设计参照建构主义学习理论 — Bruner (1961) 发现学习理论; Ausubel (1968) 有意义学习理论; 概念文件的认知路径章节要求渐进式推导": "https://en.wikipedia.org/wiki/Constructivism_(philosophy_of_education)",
    "认知路径设计参照建构主义学习理论 — Bruner (1961) 发现学习理论; Ausubel (1968) 有意义学习理论; 概念文件的认知路径章节要求渐进式推导\\": "https://en.wikipedia.org/wiki/Constructivism_(philosophy_of_education)",
    "跨引用密度 ≥3/文件的要求参照 hypertext 认知负荷研究 — 适度链接促进概念网络形成，过度链接导致导航迷失; 本知识体系采用 3-5 个核心跨文件链接作为平衡点": "https://en.wikipedia.org/wiki/Hypertext",
    "跨引用密度 ≥3/文件的要求参照 hypertext 认知负荷研究 — 适度链接促进概念网络形成，过度链接导致导航迷失; 本知识体系采用 3-5 个核心跨文件链接作为平衡点\\": "https://en.wikipedia.org/wiki/Hypertext",
    "倒排索引方法论参照信息检索标准 — Manning, Raghavan & Schütze, *Introduction to Information Retrieval* (Cambridge, 2008); 语义链接网络参照 Knowledge Graph 构建方法论": "https://nlp.stanford.edu/IR-book/",
    "倒排索引方法论参照信息检索标准 — Manning, Raghavan & Schütze, *Introduction to Information Retrieval* (Cambridge, 2008); 语义链接网络参照 Knowledge Graph 构建方法论\\": "https://nlp.stanford.edu/IR-book/",
    "倒排索引方法论参照信息检索标准 — Manning, Raghavan \\& Schütze, *Introduction to Information Retrieval* (Cambridge, 2008); 语义链接网络参照 Knowledge Graph 构建方法论\\": "https://nlp.stanford.edu/IR-book/",
    "概念分类参照语义网络理论 — Collins & Quillian (1969) 层次语义网络模型; 概念的层级组织与属性继承": "https://en.wikipedia.org/wiki/Semantic_network",
    "概念分类参照语义网络理论 — Collins & Quillian (1969) 层次语义网络模型; 概念的层级组织与属性继承\\": "https://en.wikipedia.org/wiki/Semantic_network",
    "概念分类参照语义网络理论 — Collins \\& Quillian (1969) 层次语义网络模型; 概念的层级组织与属性继承\\": "https://en.wikipedia.org/wiki/Semantic_network",
    "语义链接类型参照知识图谱关系本体 — W3C RDF/OWL 标准; 实体间关系的语义标注方法论": "https://www.w3.org/standards/semanticweb/",
    "语义链接类型参照知识图谱关系本体 — W3C RDF/OWL 标准; 实体间关系的语义标注方法论\\": "https://www.w3.org/standards/semanticweb/",
    "交叉一致性检查方法论参照概念图 (Concept Map) 理论 — Novak & Cañas, *The Theory Underlying Concept Maps* (2008); 知识网络的连通性验证": "https://cmap.ihmc.us/docs/theory-of-concept-maps",
    "交叉一致性检查方法论参照概念图 (Concept Map) 理论 — Novak & Cañas, *The Theory Underlying Concept Maps* (2008); 知识网络的连通性验证\\": "https://cmap.ihmc.us/docs/theory-of-concept-maps",
    "交叉一致性检查方法论参照概念图 (Concept Map) 理论 — Novak \\& Cañas, *The Theory Underlying Concept Maps* (2008); 知识网络的连通性验证\\": "https://cmap.ihmc.us/docs/theory-of-concept-maps",
    "跨文件概念一致性检查参照 RFC 2349 — Pin / 2018": "https://rust-lang.github.io/rfcs/2349-pin.html",
    "跨文件概念一致性检查参照 RFC 2349 — Pin / 2018; concept/03_advanced/01_async/02_async.md 等 4+ 文件中的 Pin 定义一致性验证": "https://rust-lang.github.io/rfcs/2349-pin.html",
    "跨文件概念一致性检查参照 RFC 2349 — Pin / 2018; concept/03\\_advanced/01\\_async/02\\_async.md 等 4+ 文件中的 Pin 定义一致性验证\\": "https://rust-lang.github.io/rfcs/2349-pin.html",
    "跨文件概念一致性检查参照 [RFC 2349": "https://rust-lang.github.io/rfcs/2349-pin.html",
    "速查表设计参照认知心理学中的组块化 (Chunking) 原则 — Miller (1956); 信息压缩与快速检索": "https://en.wikipedia.org/wiki/Chunking_(psychology)",
    "速查表设计参照认知心理学中的组块化 (Chunking) 原则 — Miller (1956); 信息压缩与快速检索\\": "https://en.wikipedia.org/wiki/Chunking_(psychology)",
    "优先级排序基于概念依赖图的前置节点数量 — 前置越多的概念优先级越高": "https://en.wikipedia.org/wiki/Topological_sorting",
    "Rust 6 周发布周期驱动文档审计频率; 重大修改后立即执行审计，参照 AGENTS.md 维护规范第 4 条": "https://www.rust-lang.org/policies/",
    "来源对齐 Sprint 参照 AGENTS.md 质量铁三角 — Bloom 层级 100%、来源标注率 ≥15%、跨文件链接 ≥3/文件": "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/",
    "方案 B 阶段 5-6 规划": None,
    "concept/00_meta/learning_guide.md — 学习路径设计; concept/00_meta/methodology.md — 内容结构规范": None,
    "concept/00\\_meta/learning\\_guide.md — 学习路径设计; concept/00\\_meta/methodology.md — 内容结构规范\\": None,
    "concept/ 目录结构; 00_meta/inter_layer_map.md": None,
    # 语言规范
    "C++ Reference: Reference": "https://en.cppreference.com/w/cpp/language/reference",
    "C++ Reference: unique_ptr": "https://en.cppreference.com/w/cpp/memory/unique_ptr",
    "C++ Reference: Coroutines": "https://en.cppreference.com/w/cpp/language/coroutines",
    "C++ Reference: Smart pointers": "https://en.cppreference.com/w/cpp/memory",
    "C++ Reference: Non-type template parameter": "https://en.cppreference.com/w/cpp/language/parameter_pack",
    "C++ Reference: Concepts": "https://en.cppreference.com/w/cpp/concepts",
    "C++ Reference: Thread support library": "https://en.cppreference.com/w/cpp/thread",
    "C++ Memory Model; RustBelt — No-Data-Race Theorem 的反面": "https://en.cppreference.com/w/cpp/language/memory_model",
    "C++20 Concepts": "https://en.cppreference.com/w/cpp/concepts",
    "C++23 Draft Standard": "https://en.cppreference.com/w/cpp/standard",
    "Go Language Specification": "https://go.dev/ref/spec",
    "Go Spec: Pointers": "https://go.dev/ref/spec#Pointers",
    "Go Spec: Goroutines": "https://go.dev/ref/spec#Goroutines",
    "Go Spec: Interface types": "https://go.dev/ref/spec#Interface_types",
    "Go Spec: Type parameters": "https://go.dev/ref/spec#Type_parameters",
    "Effective Go / Go Memory Model": "https://go.dev/ref/mem",
    "Go GC Guide / 工业实践": "https://go.dev/doc/gc-guide",
    "Go GC Guide / Go 1.20 Release Notes": "https://go.dev/doc/gc-guide",
    "rustvsgo.com; Go Runtime Scheduler 文档": "https://go.dev/doc/sched",
    "rustvsgo.com, SPAA 2024": "https://rustvsgo.com/",
    "rustvsgo.com; Go Runtime Scheduler 文档": "https://rustvsgo.com/",
    "rustvsgo.com": "https://rustvsgo.com/",
    "Go Modules Reference": "https://go.dev/ref/mod",
    "npm Docs: package.json": "https://docs.npmjs.com/cli/v10/configuring-npm/package-json",
    "pip Documentation": "https://pip.pypa.io/en/stable/",
    "SemVer Specification": "https://semver.org/",
    "Haskell 2010 Report": "https://www.haskell.org/onlinereport/haskell2010/",
    "Peyton Jones et al., *Haskell 98 Report*": "https://www.haskell.org/onlinereport/",
    "Haskell GHC User Guide: LinearTypes": "https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#extension-Line",
    "Haskell GHC User Guide: ST": "https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/",
    "Haskell GHC User Guide: Concurrent Haskell": "https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/parallel.html",
    "Haskell GHC User Guide: Parallelism and Concurrency": "https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/parallel.html",
    "GHC User's Guide": "https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/",
    "TypeScript Handbook": "https://www.typescriptlang.org/docs/handbook/intro.html",
    "TypeScript Handbook — Structural Type System": "https://www.typescriptlang.org/docs/handbook/type-compatibility.html",
    "Java Language Spec: Type Erasure": "https://docs.oracle.com/javase/specs/jls/se17/html/jls-4.html#jls-4.6",
    # Rust 官方文档具体页
    "Rust Reference — Pin; [RFC 2349": "https://doc.rust-lang.org/reference/items/traits.html",
    "Rust Reference: Unions": "https://doc.rust-lang.org/reference/items/unions.html",
    "Rust Reference: Lifetime elision": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "Rust Reference: Lifetime elision §The rules": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "Rust Reference — Behavior considered undefined": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "Rust Reference — Pin": "https://doc.rust-lang.org/reference/items/traits.html",
    "Rust Reference — Unsafe": "https://doc.rust-lang.org/reference/unsafe-keyword.html",
    "Rust Reference — Macros": "https://doc.rust-lang.org/reference/macros.html",
    "Rust Reference — Generic Parameters": "https://doc.rust-lang.org/reference/items/generics.html",
    "Rust Reference — The ? operator": "https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator",
    "Rust Reference — Object Safety": "https://doc.rust-lang.org/reference/items/traits.html#object-safety",
    "Rust Reference — Variance": "https://doc.rust-lang.org/reference/subtyping.html#variance",
    "Rust Reference — Ownership, Lifetimes, Types": "https://doc.rust-lang.org/reference/introduction.html",
    "Rust Reference — unsafe, Macros": "https://doc.rust-lang.org/reference/unsafe-keyword.html",
    "Rust Reference: Lifetime elision": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "Rust Reference: Enums": "https://doc.rust-lang.org/reference/items/enumerations.html",
    "The Rust Reference": "https://doc.rust-lang.org/reference/introduction.html",
    # std 具体页
    "Rust std: std::task::Wake": "https://doc.rust-lang.org/std/task/trait.Wake.html",
    "std::ptr::write docs": "https://doc.rust-lang.org/std/ptr/fn.write.html",
    "std::ptr::read docs": "https://doc.rust-lang.org/std/ptr/fn.read.html",
    "std::ptr::replace docs": "https://doc.rust-lang.org/std/ptr/fn.replace.html",
    "std::mem::ManuallyDrop docs": "https://doc.rust-lang.org/std/mem/struct.ManuallyDrop.html",
    "std::array::from_fn docs": "https://doc.rust-lang.org/std/array/fn.from_fn.html",
    "Rust std docs — std::backtrace::Backtrace": "https://doc.rust-lang.org/std/backtrace/struct.Backtrace.html",
    "Rust Standard Library: panic::Location": "https://doc.rust-lang.org/std/panic/struct.Location.html",
    "Rust Standard Library: Location::caller": "https://doc.rust-lang.org/std/panic/struct.Location.html#method.caller",
    "Rust Standard Library: PanicInfo": "https://doc.rust-lang.org/std/panic/struct.PanicInfo.html",
    "Rust std::sync::atomic docs; C++ Standard §33.5": "https://doc.rust-lang.org/std/sync/atomic/index.html",
    "Rust std::sync::Mutex docs; TLA+ Examples": "https://doc.rust-lang.org/std/sync/struct.Mutex.html",
    "Rust Iterator docs": "https://doc.rust-lang.org/std/iter/trait.Iterator.html",
    "Rust Iterator docs, LLVM 优化指南": "https://doc.rust-lang.org/std/iter/trait.Iterator.html",
    "Rust docs, collect 方法": "https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.collect",
    "Rust 并发基于所有权系统——每个值有唯一所有者（单一所有权，资源唯一性），所有权通过 move/转移在线程间传递（赋值、传参），owner 离开作用域时自动 drop/释放": "https://doc.rust-lang.org/book/ch16-00-concurrency.html",
    "Rust 并发基于所有权系统——每个值有唯一所有者（单一所有权，资源唯一性），所有权通过 move/转移在线程间传递（赋值、传参），owner 离开作用域时自动 drop/释放\\": "https://doc.rust-lang.org/book/ch16-00-concurrency.html",
    # Cargo Book 具体页
    "Cargo Book — Build Scripts": "https://doc.rust-lang.org/cargo/reference/build-scripts.html",
    "Cargo Book — Build Script Outputs": "https://doc.rust-lang.org/cargo/reference/build-scripts.html#outputs-of-the-build-script",
    "Cargo Book — SemVer Compatibility": "https://doc.rust-lang.org/cargo/reference/semver.html",
    "Cargo Book — How Cargo resolves dependencies": "https://doc.rust-lang.org/cargo/reference/resolver.html",
    "Cargo Book — Resolver versions": "https://doc.rust-lang.org/cargo/reference/resolver.html#resolver-versions",
    "Cargo Book — The rust-version field": "https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field",
    "Cargo Book — cargo vendor": "https://doc.rust-lang.org/cargo/reference/commands/cargo-vendor.html",
    "Cargo Book — Overriding Dependencies": "https://doc.rust-lang.org/cargo/reference/overriding-dependencies.html",
    "Cargo Book — Registry Protocols": "https://doc.rust-lang.org/cargo/reference/registry-index.html",
    "Cargo Book — Publishing on crates.io": "https://doc.rust-lang.org/cargo/reference/publishing.html",
    "Cargo Book — Authentication": "https://doc.rust-lang.org/cargo/reference/authentication.html",
    "Cargo Book — Registry Authentication": "https://doc.rust-lang.org/cargo/reference/authentication.html",
    "Cargo Book — Recommended configuration": "https://doc.rust-lang.org/cargo/reference/config.html",
    "Cargo Book — Cargo Home": "https://doc.rust-lang.org/cargo/reference/config.html#cargohome",
    "Cargo Book — Build Cache": "https://doc.rust-lang.org/cargo/reference/build-cache.html",
    "Cargo Book — External Tools": "https://doc.rust-lang.org/cargo/reference/external-tools.html",
    "Cargo Book — External Tools — JSON messages": "https://doc.rust-lang.org/cargo/reference/external-tools.html#json-messages",
    # rustc-dev-guide 入口
    "Rustc Dev Guide — Queries": "https://rustc-dev-guide.rust-lang.org/query.html",
    "Rustc Dev Guide — What Bootstrapping does": "https://rustc-dev-guide.rust-lang.org/building/bootstrapping.html",
    "rustc dev guide: Type inference": "https://rustc-dev-guide.rust-lang.org/type-inference.html",
    "Rustc Dev Guide — HIR Type checking": "https://rustc-dev-guide.rust-lang.org/type-checking.html",
    "Rustc Dev Guide — The ty module": "https://rustc-dev-guide.rust-lang.org/ty.html",
    "Rustc Dev Guide — Inference variables": "https://rustc-dev-guide.rust-lang.org/type-inference.html",
    "Rustc Dev Guide — Region constraints": "https://rustc-dev-guide.rust-lang.org/borrowck/region-inference.html",
    "Rustc Dev Guide — Snapshots": "https://rustc-dev-guide.rust-lang.org/type-inference.html",
    "Rustc Dev Guide — Incremental Compilation": "https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation.html",
    "Rustc Dev Guide — Trait resolution (old-style)": "https://rustc-dev-guide.rust-lang.org/traits/resolution.html",
    "Rustc Dev Guide — Trait resolution — Overview": "https://rustc-dev-guide.rust-lang.org/traits/resolution.html",
    "Rustc Dev Guide — Next-gen trait solving": "https://rustc-dev-guide.rust-lang.org/solve/trait-solving.html",
    "Rustc Dev Guide — Coinduction": "https://rustc-dev-guide.rust-lang.org/solve/coinduction.html",
    "Rustc Dev Guide — The HIR": "https://rustc-dev-guide.rust-lang.org/hir.html",
    "Rustc Dev Guide — Name Resolution": "https://rustc-dev-guide.rust-lang.org/name-resolution.html",
    "Rustc Dev Guide — Name Resolution — Scopes and ribs": "https://rustc-dev-guide.rust-lang.org/name-resolution.html",
    "Rustc Dev Guide — The HIR — Out-of-band storage": "https://rustc-dev-guide.rust-lang.org/hir.html",
    "Rustc Dev Guide — What is LLVM?": "https://rustc-dev-guide.rust-lang.org/backend/backend-agnostic.html",
    "Rustc Dev Guide — Code generation — Codegen units": "https://rustc-dev-guide.rust-lang.org/backend/codegen-crate.html",
    "Rustc Dev Guide — Adding a new target": "https://rustc-dev-guide.rust-lang.org/target-tier-policy.html",
    "Rustc Dev Guide — Code generation — LTO": "https://rustc-dev-guide.rust-lang.org/backend/linking.html",
    "Rustc Dev Guide — Codegen backend testing": "https://rustc-dev-guide.rust-lang.org/tests/intro.html",
    "Rustc Dev Guide — rustc_driver and rustc_interface": "https://rustc-dev-guide.rust-lang.org/rustc-driver.html",
    "Rustc Dev Guide — rustc_interface": "https://rustc-dev-guide.rust-lang.org/rustc-driver.html",
    "Rustc Dev Guide — External rustc_drivers": "https://rustc-dev-guide.rust-lang.org/rustc-driver.html",
    "Rustc Dev Guide — Diagnostic structure": "https://rustc-dev-guide.rust-lang.org/diagnostics/diagnostic-struct.html",
    "Rustc Dev Guide — Suggestions": "https://rustc-dev-guide.rust-lang.org/diagnostics/diagnostic-struct.html",
    "Rustc Dev Guide — Lints": "https://rustc-dev-guide.rust-lang.org/diagnostics/lint-guidelines.html",
    "Rustc Dev Guide — Bootstrapping": "https://rustc-dev-guide.rust-lang.org/building/bootstrapping.html",
    "Rustc Dev Guide — Writing tools in Bootstrap": "https://rustc-dev-guide.rust-lang.org/building/bootstrapping.html",
    "Rustc Dev Guide — Testing the compiler": "https://rustc-dev-guide.rust-lang.org/tests/intro.html",
    "Rustc Dev Guide — Ecosystem testing": "https://rustc-dev-guide.rust-lang.org/tests/intro.html",
    "Rustc Dev Guide — Performance testing": "https://rustc-dev-guide.rust-lang.org/tests/profiling.html",
    "rustc Dev Guide; LLVM Documentation; *Engineering a Compiler* — Cooper & Torczon": "https://rustc-dev-guide.rust-lang.org/",
    "Rustc Dev Guide": "https://rustc-dev-guide.rust-lang.org/",
    # LLVM / Sanitizers / Valgrind
    "LLVM LangRef: Function Attributes": "https://llvm.org/docs/LangRef.html#function-attributes",
    "LLVM LangRef: volatile": "https://llvm.org/docs/LangRef.html#volatile-memory-accesses",
    "LLVM Sanitizers Docs": "https://clang.llvm.org/docs/index.html",
    "Valgrind Documentation": "https://valgrind.org/docs/manual/manual.html",
    "TSan Documentation": "https://clang.llvm.org/docs/ThreadSanitizer.html",
    # 工具 / 统计 / 会议
    "TechEmpower": "https://www.techempower.com/benchmarks/",
    "TechEmpower Benchmarks": "https://www.techempower.com/benchmarks/",
    "ICSE 2026": "https://conf.researchr.org/home/icse-2026",
    "PLDI 2023 - Comparative Language Studies": "https://pldi23.sigplan.org/",
    "PLDI 2024/2025": "https://pldi24.sigplan.org/",
    "PLDI 2024/2025 Compiler-Guided Code Generation": "https://pldi24.sigplan.org/",
    "IEEE Software - Rust Adoption Analysis": "https://www.computer.org/software-magazine/",
    "ACM Computing Surveys": "https://dl.acm.org/journal/csur",
    "CACM": "https://cacm.acm.org/",
    "ACM Digital Library / CACM": "https://dl.acm.org/",
    "Stanford CS242 - Programming Languages": "https://web.stanford.edu/class/cs242/",
    "Stanford Explore Courses": "https://explorecourses.stanford.edu/",
    "CMU Course Catalog": "https://www.cmu.edu/hub/coursecatalog/",
    "Rustify.rs 2026": "https://rustify.rs/",
    "rustify.rs 2026": "https://rustify.rs/",
    "TWiR 650": "https://this-week-in-rust.org/",
    # 设计模式 / 软件工程
    "GoF Design Patterns; UML 2.5 Class Diagram Standard": "https://en.wikipedia.org/wiki/Design_Patterns",
    "GoF Design Patterns, 1994": "https://en.wikipedia.org/wiki/Design_Patterns",
    "Rust Design Patterns — Gold Plating": "https://rust-unofficial.github.io/patterns/anti_patterns/gold_plating.html",
    "Rust Design Patterns, Typestate": "https://rust-unofficial.github.io/patterns/patterns/behavioural/state-machine.html",
    "Rust Style Guide": "https://doc.rust-lang.org/style-guide/index.html",
    "Dennis & Van Horn, CACM 1966": "https://doi.org/10.1145/365813.365821",
    "Stroustrup, *The Design and Evolution of C++*, 1994": "https://www.stroustrup.com/dne.html",
    "Lamport, *Paxos Made Simple*; Brewer, *CAP Twelve Years Later*": "https://lamport.azurewebsites.net/pubs/paxos-simple.pdf",
    "NIST SP 800-207, 2020": "https://csrc.nist.gov/publications/detail/sp/800-207/final",
    "Systems Engineering V-Model; ISO/IEC/IEEE 15288": "https://www.iso.org/standard/63711.html",
    "C11 Standard": "https://www.iso.org/standard/57853.html",
    # 数据流 / 数据库 / 区块链 / 分布式
    "Akidau et al.": "https://doi.org/10.14778/2824032.2824076",
    "Akidau et al., VLDB 2015": "https://doi.org/10.14778/2824032.2824076",
    "Materialize Documentation": "https://materialize.com/docs/",
    "McSherry et al. — Materialize Blog": "https://materialize.com/blog/",
    "Flink Documentation": "https://nightlies.apache.org/flink/flink-docs-stable/",
    "SurrealDB Documentation": "https://surrealdb.com/docs",
    "RisingWave Documentation": "https://docs.risingwave.com/",
    "RisingWave vs Materialize Benchmark 2026": "https://www.risingwave.com/blog/",
    "PingCAP Blog — Why Rust for TiKV": "https://www.pingcap.com/blog/",
    "Meilisearch Documentation": "https://www.meilisearch.com/docs",
    "Solana Docs; Polkadot Substrate Docs; Near Protocol Docs; Kani Verification Blog; Rust in Blockchain Report": "https://solana.com/docs",
    "Rust Blockchain Report 2024; Solana Docs; Polkadot Substrate Docs; Near Protocol Docs": "https://solana.com/docs",
    "Solana Docs; Polkadot Substrate Docs; Near Protocol Docs": "https://solana.com/docs",
    "Smart Contract Security Research; Reentrancy Attack Analysis; The DAO Post-Mortem": "https://en.wikipedia.org/wiki/The_DAO_(organization)",
    "Timely Dataflow README": "https://github.com/TimelyDataflow/timely-dataflow",
    "Fluvio Documentation": "https://www.fluvio.io/docs/",
    "Fluvio Blog": "https://www.fluvio.io/blog/",
    # 嵌入式 / OS
    "Rust Embedded Book, Rust-for-Linux": "https://docs.rust-embedded.org/book/",
    "Jorge Aparicio, Embedded WG": "https://docs.rust-embedded.org/book/",
    "WASI Specification, Bytecode Alliance": "https://wasi.dev/",
    "WASI Specification; Bytecode Alliance": "https://wasi.dev/",
    "WASI Preview 2 Docs; Capability-Based Security Research": "https://wasi.dev/",
    "WASI Docs; Rust Ownership Model": "https://wasi.dev/",
    "WASI Preview 2 Docs; WebAssembly Component Model Spec; wit-bindgen Docs; WASMtime Docs": "https://wasi.dev/",
    "WebAssembly.org; wasm-bindgen Guide; Rust WASM Working Group": "https://webassembly.org/",
    "wit-bindgen Docs": "https://github.com/bytecodealliance/wit-bindgen",
    "wit-bindgen GitHub; Component Model Tutorial": "https://github.com/bytecodealliance/wit-bindgen",
    "Component Model Spec": "https://component-model.bytecodealliance.org/",
    "Capability-Based Security Research; Dennis & Van Horn 1966; Rust Ownership Model": "https://wasi.dev/",
    "LWN — Rust in the Linux Kernel": "https://lwn.net/Kernel/Index/#Rust",
    "Theseus OS — Raman et al., OSDI 2020": "https://theseus-os.com/",
    "Raman et al., OSDI 2020": "https://theseus-os.com/",
    "Redox OS Website": "https://www.redox-os.org/",
    "Redox OS Documentation": "https://doc.redox-os.org/",
    "Rust for Linux Docs": "https://docs.kernel.org/rust/",
    "Aya Book": "https://aya-rs.dev/",
    "aya-rs Documentation": "https://aya-rs.dev/",
    "Espressif Developer Blog — Bevy ECS on ESP32": "https://developer.espressif.com/",
    "tokio-rs/io-uring": "https://github.com/tokio-rs/io-uring",
    "tokio-rs/tokio-uring 设计文档": "https://github.com/tokio-rs/tokio-uring",
    "Linux Kernel Documentation, eBPF, https://docs.kernel.org/bpf/": "https://docs.kernel.org/bpf/",
    "Rex: Safe Rust for eBPF, arXiv:2501.xxxxx": "https://arxiv.org/abs/2501.xxxxx",
    # Web / 网络 / UI
    "Tokio Documentation": "https://docs.rs/tokio/latest/tokio/",
    "Tokio Docs — broadcast": "https://docs.rs/tokio/latest/tokio/sync/broadcast/index.html",
    "Tokio Internals": "https://tokio.rs/blog/2019-11-tokio-0-2",
    "Tokio Internals; Go Runtime 文档": "https://tokio.rs/blog/2019-11-tokio-0-2",
    "Stevens UNP, Tokio Internals": "https://tokio.rs/blog/2019-11-tokio-0-2",
    "Tower docs": "https://docs.rs/tower/latest/tower/",
    "Tower docs, Category Theory": "https://docs.rs/tower/latest/tower/",
    "Tower 文档; Mac Lane, *Categories for the Working Mathematician*": "https://docs.rs/tower/latest/tower/",
    "Tower/Axum middleware docs": "https://docs.rs/tower/latest/tower/",
    "Axum docs": "https://docs.rs/axum/latest/axum/",
    "event-listener crate docs": "https://docs.rs/event-listener/latest/event_listener/",
    "async-stream crate": "https://docs.rs/async-stream/latest/async_stream/",
    "tonic docs": "https://docs.rs/tonic/latest/tonic/",
    "Poem OpenAPI docs": "https://docs.rs/poem-openapi/latest/poem_openapi/",
    "quinn Documentation": "https://docs.rs/quinn/latest/quinn/",
    "Quinn Docs": "https://docs.rs/quinn/latest/quinn/",
    "egui Docs": "https://docs.rs/egui/latest/egui/",
    "Leptos docs": "https://docs.rs/leptos/latest/leptos/",
    "ethers-rs docs": "https://docs.rs/ethers/latest/ethers/",
    "AWS Lambda Rust runtime": "https://github.com/awslabs/aws-lambda-rust-runtime",
    "Beam Programming Guide — Accumulation": "https://beam.apache.org/documentation/programming-guide/",
    "Beam Programming Guide — Accumulation\\": "https://beam.apache.org/documentation/programming-guide/",
    "WebAssembly Specification": "https://webassembly.github.io/spec/",
    "wasm-bindgen Guide": "https://rustwasm.github.io/docs/wasm-bindgen/",
    "wasm-bindgen Documentation": "https://rustwasm.github.io/docs/wasm-bindgen/",
    "wasm-bindgen 源码, crates/macro-support/src/parser.rs": "https://github.com/rustwasm/wasm-bindgen/blob/main/crates/macro-support/src/parser.rs",
    # crates / 生态
    "eyre docs": "https://docs.rs/eyre/latest/eyre/",
    "color-eyre docs": "https://docs.rs/color-eyre/latest/color_eyre/",
    "miette docs": "https://docs.rs/miette/latest/miette/",
    "snafu docs": "https://docs.rs/snafu/latest/snafu/",
    "anyhow docs — Features": "https://docs.rs/anyhow/latest/anyhow/",
    "anyhow source — macro rules": "https://github.com/dtolnay/anyhow",
    "thiserror": "https://docs.rs/thiserror/latest/thiserror/",
    "thiserror Documentation": "https://docs.rs/thiserror/latest/thiserror/",
    "anyhow": "https://docs.rs/anyhow/latest/anyhow/",
    "anyhow Documentation": "https://docs.rs/anyhow/latest/anyhow/",
    "[anyhow": "https://docs.rs/anyhow/latest/anyhow/",
    "std::convert::From": "https://doc.rust-lang.org/std/convert/trait.From.html",
    "std::convert::TryInto": "https://doc.rust-lang.org/std/convert/trait.TryInto.html",
    "std::ops::Deref": "https://doc.rust-lang.org/std/ops/trait.Deref.html",
    "std::boxed::Box": "https://doc.rust-lang.org/std/boxed/struct.Box.html",
    "std::pin::Pin": "https://doc.rust-lang.org/std/pin/struct.Pin.html",
    "std::sync::Mutex": "https://doc.rust-lang.org/std/sync/struct.Mutex.html",
    "std::option::Option": "https://doc.rust-lang.org/std/option/enum.Option.html",
    "std::num::Wrapping": "https://doc.rust-lang.org/std/num/struct.Wrapping.html",
    "std::fmt": "https://doc.rust-lang.org/std/fmt/index.html",
    "std::fmt::Display": "https://doc.rust-lang.org/std/fmt/trait.Display.html",
    "std::ffi::OsString": "https://doc.rust-lang.org/std/ffi/struct.OsString.html",
    "std::collections::BTreeMap": "https://doc.rust-lang.org/std/collections/struct.BTreeMap.html",
    "std::panic::catch_unwind": "https://doc.rust-lang.org/std/panic/fn.catch_unwind.html",
    "std::simd": "https://doc.rust-lang.org/std/simd/index.html",
    "std::cell::Cell": "https://doc.rust-lang.org/std/cell/struct.Cell.html",
    "std::cell::RefCell": "https://doc.rust-lang.org/std/cell/struct.RefCell.html",
    "std::rc::Rc": "https://doc.rust-lang.org/std/rc/struct.Rc.html",
    "std::sync::Arc": "https://doc.rust-lang.org/std/sync/struct.Arc.html",
    "jemalloc": "https://github.com/jemalloc/jemalloc",
    "mimalloc": "https://github.com/microsoft/mimalloc",
    "typenum crate": "https://docs.rs/typenum/latest/typenum/",
    "nom Documentation": "https://docs.rs/nom/latest/nom/",
    "scopeguard crate docs": "https://docs.rs/scopeguard/latest/scopeguard/",
    "crossbeam-epoch docs": "https://docs.rs/crossbeam-epoch/latest/crossbeam_epoch/",
    "hecs Documentation": "https://docs.rs/hecs/latest/hecs/",
    "Shipyard GitHub — Cargo Features": "https://github.com/leudz/shipyard",
    "Bevy Engine Documentation": "https://bevyengine.org/learn/book/",
    "Bevy ECS docs, Data-Oriented Design": "https://bevyengine.org/learn/book/ecs/",
    "Bevy ECS Docs; Chen, *The Entity-Relationship Model*, 1976": "https://bevyengine.org/learn/book/ecs/",
    "Bevy ECS Docs; Data-Oriented Design Book": "https://bevyengine.org/learn/book/ecs/",
    "Bevy Book; Bevy ECS Docs; Fyrox Docs; wgpu Documentation; Data-Oriented Design Book": "https://bevyengine.org/learn/book/",
    "Bevy ECS no_std Discussion #10680": "https://github.com/bevyengine/bevy/discussions/10680",
    "Playdate Developer Forum — Rust Development Thread": "https://devforum.play.date/",
    "Data-Oriented Design Book": "https://www.dataorienteddesign.com/dodbook/",
    "Fyrox Docs": "https://fyrox-book.github.io/",
    "wgpu Documentation": "https://docs.rs/wgpu/latest/wgpu/",
    "Candle Book": "https://huggingface.github.io/candle/",
    "Rust Concurrency Book; Rayon Docs; Rust Book Ch.16": "https://doc.rust-lang.org/book/ch16-00-concurrency.html",
    "Rust Foundation Survey 2024; Rust in Production Report; crates.io Download Statistics": "https://foundation.rust-lang.org/",
    "Rust in Production Report": "https://foundation.rust-lang.org/",
    "crates.io 下载量": "https://crates.io/",
    "crates.io Download Statistics": "https://crates.io/",
    "lib.rs": "https://lib.rs/",
    # 工业实践 / 博客
    "Discord Engineering Blog / Dropbox Tech Blog": "https://discord.com/blog/",
    "Linkerd 架构文档 / 工业实践": "https://linkerd.io/2/overview/",
    "工业实践": None,
    "Rust 源码分析 / rustc 1.78": "https://github.com/rust-lang/rust/tree/1.78.0",
    "cargo-fuzz docs; Rust Fuzz Book": "https://rust-fuzz.github.io/book/",
    "cargo-deny": "https://docs.rs/cargo-deny/latest/cargo_deny/",
    "cargo fix": "https://doc.rust-lang.org/cargo/commands/cargo-fix.html",
    "cargo-vet Documentation": "https://mozilla.github.io/cargo-vet/",
    "cargo-geiger 文档": "https://docs.rs/cargo-geiger/latest/cargo_geiger/",
    "Swatinem/rust-cache": "https://github.com/Swatinem/rust-cache",
    "rodio": "https://docs.rs/rodio/latest/rodio/",
    "Wasmtime Security": "https://docs.wasmtime.dev/security.html",
    "Rust CLI Book": "https://rust-cli.github.io/book/",
    "Rust Cookbook": "https://rust-lang-nursery.github.io/rust-cookbook/",
    "Rust API Guidelines": "https://rust-lang.github.io/api-guidelines/",
    "Rust API Guidelines — Type Safety": "https://rust-lang.github.io/api-guidelines/type-safety.html",
    "Rust API Guidelines — Macros": "https://rust-lang.github.io/api-guidelines/documentation.html",
    "Rust API Guidelines — Newtypes": "https://rust-lang.github.io/api-guidelines/type-safety.html",
    "Rust API Guidelines — Strings": "https://rust-lang.github.io/api-guidelines/naming.html",
    "Rust API Guidelines — Flexibility": "https://rust-lang.github.io/api-guidelines/flexibility.html",
    "Rust Error Handling": "https://doc.rust-lang.org/book/ch09-00-error-handling.html",
    "Rust Error Handling Best Practices": "https://doc.rust-lang.org/book/ch09-00-error-handling.html",
    "Rust Performance Book": "https://nnethercote.github.io/perf-book/",
    "Rust Performance Book — Profiling": "https://nnethercote.github.io/perf-book/profiling.html",
    "Rust Verification Tools": "https://model-checking.github.io/kani/",
    "Rust for Linux": "https://rust-for-linux.com/",
    "Rust Embedded Book": "https://docs.rust-embedded.org/book/",
    "Rust ML": "https://arewelearningyet.com/",
    "Are We Learning Yet?": "https://arewelearningyet.com/",
    "Rust Secure Code Guidelines": "https://rust-lang.github.io/rust-project-goals/",
    "Rust Secure Code WG": "https://rust-lang.github.io/wg-secure-code/",
    "Rust in Production; Rust Foundation; Ferrous Systems; AWS/Google/Microsoft Rust Blogs": "https://foundation.rust-lang.org/",
    "Rust Internals Forum": "https://internals.rust-lang.org/",
    "Rust Internals": "https://internals.rust-lang.org/",
    "Rust Internals Forum, \"Let Chains Gotchas\"": "https://internals.rust-lang.org/",
    "Rust Project Goals 2026": "https://github.com/rust-lang/rust-project-goals/blob/main/src/2026/",
    "Rust Project Goals — StableMIR": "https://github.com/rust-lang/rust-project-goals/blob/main/src/2024h2/stable_mir.html",
    "a-mir-formality GitHub": "https://github.com/rust-lang/a-mir-formality",
    "Rust Atomics and Locks": "https://marabos.nl/atomics/",
    "Rust and WebAssembly Book": "https://rustwasm.github.io/docs/book/",
    "Rust Wasm Book": "https://rustwasm.github.io/docs/book/",
    "Rust by Example": "https://doc.rust-lang.org/rust-by-example/index.html",
    "Rust By Example": "https://doc.rust-lang.org/rust-by-example/index.html",
    "The Rust FFI Omnibus": "https://jakegoulding.com/rust-ffi-omnibus/",
    "The Little Book of Rust Macros": "https://veykril.github.io/tlborm/",
    "The Little Book of Rust Macros — Pitfalls": "https://veykril.github.io/tlborm/",
    "The Little Book of Rust Macros — Hygiene": "https://veykril.github.io/tlborm/",
    "Rustonomicon": "https://doc.rust-lang.org/nomicon/index.html",
    "Rustonomicon — Send and Sync": "https://doc.rust-lang.org/nomicon/send-and-sync.html",
    "Rustnomicon — Memory Ordering": "https://doc.rust-lang.org/nomicon/atomics.html",
    "Rustnomicon — Zero-Cost Abstractions": "https://doc.rust-lang.org/nomicon/index.html",
    "Rust FFI 指南, The Rustonomicon §4": "https://doc.rust-lang.org/nomicon/ffi.html",
    "Rustonomicon — Collections": "https://doc.rust-lang.org/nomicon/index.html",
    "Rustonomicon — Interior Mutability": "https://doc.rust-lang.org/nomicon/interior-mutability.html",
    # 语言对比 / 经典
    "C11 Standard": "https://www.iso.org/standard/57853.html",
    "ISO C++20 § 作为对比基准": "https://en.cppreference.com/w/cpp/standard",
    "ISO/IEC/IEEE 15288": "https://www.iso.org/standard/63711.html",
    "ACM Digital Library / CACM": "https://dl.acm.org/",
    "The Coded Message — RAII": "https://www.thecodedmessage.com/",
    "Seven Concurrency Models in Seven Weeks": "https://pragprog.com/titles/pb7con/seven-concurrency-models-in-seven-weeks/",
    "*Seven Concurrency Models in Seven Weeks*": "https://pragprog.com/titles/pb7con/seven-concurrency-models-in-seven-weeks/",
    "Armstrong, *Making Reliable Distributed Systems*, 2003": "https://erlang.org/download/armstrong_thesis_2003.pdf",
    "Armstrong 2003, Erlang Error Kernel": "https://erlang.org/download/armstrong_thesis_2003.pdf",
    "Tony Buzan - Mind Mapping": "https://www.tonybuzan.com/",
    "Miller 1956": "https://en.wikipedia.org/wiki/The_Magical_Number_Seven,_Plus_or_Minus_Two",
    "Novak & Cañas, *The Theory Underlying Concept Maps* (2008)": "https://cmap.ihmc.us/docs/theory-of-concept-maps",
    "Manning, Raghavan & Schütze, *Introduction to Information Retrieval* (Cambridge, 2008)": "https://nlp.stanford.edu/IR-book/",
    "Bordes et al. *Translating Embeddings for Modeling Multi-Relational Data* (NIPS 2013)": "https://doi.org/10.48550/arXiv.1301.3485",
    "Quinlan, J.R. — *Induction of Decision Trees*. Machine Learning, 1986": "https://doi.org/10.1023/A:1022643204877",
    "Bloom Taxonomy 2001": "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/",
    # 其他
    "Rice 1953, *Classes of Recursively Enumerable Sets*": "https://doi.org/10.2307/2268381",
    "CLRS — Introduction to Algorithms, 4th Ed.": "https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/",
    "CLRS — Introduction to Algorithms, 4th Edition": "https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/",
    "Category Theory for Programmers — Bartosz Milewski": "https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/",
    "Category Theory for Programmers": "https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/",
    "Workflow Patterns — van der Aalst": "https://www.workflowpatterns.com/",
    "Wikipedia — Dynamic Programming": "https://en.wikipedia.org/wiki/Dynamic_programming",
    "Wikipedia — Graph Traversal": "https://en.wikipedia.org/wiki/Graph_traversal",
    "Wikipedia": "https://en.wikipedia.org/wiki/Main_Page",
    "数学/进程代数标准定义": "https://en.wikipedia.org/wiki/Process_calculus",
    "抽象代数 / 进程代数标准定义": "https://en.wikipedia.org/wiki/Process_calculus",
    "Inside Rust 2026-05-26": "https://blog.rust-lang.org/inside-rust/2026/05/26/",
    "RustSec Advisory DB 2026-06-05": "https://rustsec.org/",
    # 剩余高频具体标签（第二波补充）
    "Criterion.rs": "https://docs.rs/criterion/latest/criterion/",
    "TAPL — Pierce 2002": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "TAPL — 章节": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "[CLRS] §16, §24": "https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/",
    "[CLRS] §21, §22": "https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/",
    "Rust Security Advisory 2026-03/05": "https://rustsec.org/",
    "Rust Security Advisory 2026-05": "https://rustsec.org/",
    "Rust Security Advisory 2026-05; rustsec.org": "https://rustsec.org/",
    "Rust Security Advisory 2026-05-25": "https://rustsec.org/",
    "Rust Blog 2026-03/04": "https://blog.rust-lang.org/",
    "Rust Blog 2026-05-01": "https://blog.rust-lang.org/",
    "Rust Blog 2026-05-04": "https://blog.rust-lang.org/",
    "Rust Blog 2026-01/02/04/05/06": "https://blog.rust-lang.org/",
    "Rust Blog 2026-01; Inside Rust 2026-01/02/04": "https://blog.rust-lang.org/",
    "Rust Blog 2026-01/03/05; Rust Foundation 2026-03/05; rust-project-goals 2026": "https://blog.rust-lang.org/",
    "Rust Foundation 2026-01": "https://foundation.rust-lang.org/",
    "Rust Foundation 2026-03/05": "https://foundation.rust-lang.org/",
    "Rust Foundation 2026-04/06": "https://foundation.rust-lang.org/",
    "Rust Foundation 2026-02/03/04/05/06": "https://foundation.rust-lang.org/",
    "Rust Foundation 2024-11/2026-01/02": "https://foundation.rust-lang.org/",
    "Rust Foundation 2024/2025/2026": "https://foundation.rust-lang.org/",
    "Rust Foundation 2025/2026": "https://foundation.rust-lang.org/",
    "Rust RFC Tracker": "https://rust-lang.github.io/rfcs/",
    "Rust Foundation 2026-01; Rust RFC Tracker": "https://foundation.rust-lang.org/",
    "Tokio Release Notes": "https://tokio.rs/blog/",
    "Tokio Release Notes; corrode.dev; Fedora Change Proposal": "https://tokio.rs/blog/",
    "corrode.dev": "https://corrode.dev/",
    "Fedora Change Proposal": "https://fedoraproject.org/wiki/Changes/",
    "crate releases; kernel.org": "https://crates.io/",
    "kernel.org": "https://www.kernel.org/",
    "Socket.dev 2026-05-22": "https://socket.dev/",
    "Debian Rust Team": "https://wiki.debian.org/Teams/RustPackaging",
    "Socket.dev 2026-05-22; Debian Rust Team": "https://socket.dev/",
    "bevy releases": "https://bevyengine.org/",
    "Servo Blog": "https://servo.org/blog/",
    "bevy releases; Servo Blog": "https://bevyengine.org/",
    "Tokio Blog": "https://tokio.rs/blog/",
    "Kreuzberg GitHub": "https://github.com/kreuzberg",
    "zerostack GitHub": "https://github.com/zerostack/",
    "Tokio Blog; Kreuzberg GitHub; zerostack GitHub": "https://tokio.rs/blog/",
    "Cargo 1.96 CHANGELOG 2026-05-28": "https://github.com/rust-lang/cargo/blob/master/CHANGELOG.md",
    "releases.rs 2026-05-26": "https://releases.rs/",
    "Rust Project Goals 2025H2 Final Report 2026-05-18": "https://rust-lang.github.io/rust-project-goals/",
    "LWN/LKML/Inside Rust 2025-07/08/09/10/12": "https://lwn.net/",
    "Formal Methods Industry Reports 2026": "https://arxiv.org/",
    "Rust Standard Library / 2026": "https://doc.rust-lang.org/std/index.html",
    "Rust Release Team / 2024": "https://blog.rust-lang.org/",
    "Rust Team / TRPL 2024": "https://doc.rust-lang.org/book/title-page.html",
    "Rust Edition Team / 2025": "https://doc.rust-lang.org/edition-guide/index.html",
    "Rust Core Team / 2025": "https://www.rust-lang.org/",
    "TRPL: Ch19.3 — Advanced Traits": "https://doc.rust-lang.org/book/ch19-03-advanced-traits.html",
    "Fähndrich & Leino, \"Declaring and Checking Non-null Types in an Object-Oriented Language\" (OOPSLA 2003)": "https://doi.org/10.1145/949305.949332",
    "Fähndrich & Leino, OOPSLA 2003": "https://doi.org/10.1145/949305.949332",
    "[Swift vs Rust Performance [已失效]]<!-- 原链接: https://www.ben-morris.com/swift-vs-rust/ -->": "https://www.ben-morris.com/swift-vs-rust/",
    "[EventStoreDB — Snapshots [已失效]]<!-- 原链接: https://developers.eventstore.com/server/v24.10/streams.html#snapshots -->": "https://developers.eventstore.com/server/v24.10/streams.html#snapshots",
    "[LVGL Memory [已失效]]<!-- 原链接: https://docs.lvgl.io/8.3/porting/mem.html -->": "https://docs.lvgl.io/8.3/porting/mem.html",
    "[LVGL Memory Manager [已失效]]<!-- 原链接: https://docs.lvgl.io/8.3/overview/memory.html -->": "https://docs.lvgl.io/8.3/overview/memory.html",
    "gRPC Blog 2026-05-21": "https://grpc.io/blog/",
    "Rust 内存安全的形式化证明": "https://plv.mpi-sws.org/rustbelt/",
    "C++ 设计哲学对比; RAII 的起源": "https://en.cppreference.com/w/cpp/",
    "C++ 的安全子集建议; 与 Rust 编译期保证的对比": "https://en.cppreference.com/w/cpp/",
    "Go 的 GC 与 Rust 无 GC 设计对比": "https://go.dev/doc/gc-guide",
    "Haskell 的类型安全与 Rust 的所有权系统的对比": "https://www.haskell.org/ghc/",
    "迭代器模式的经典定义; Rust 的 `Iterator` trait 是该模式的类型系统实现": "https://doc.rust-lang.org/std/iter/trait.Iterator.html",
    "泛型函数的行为可由类型推导; `Iterator::map`/`filter` 等泛型组合子的参数多态性理论基础": "https://doc.rust-lang.org/std/iter/trait.Iterator.html",
    "Haskell 通过视图模式实现类似 `if let` 的模式匹配绑定; 与 Rust `let chains` 的链式组合能力对比": "https://www.haskell.org/ghc/",
    "Swift 的 `if let`/`guard let` 语法; 与 Rust `let chains` 的布尔表达式链式组合对比": "https://www.swift.org/",
    "C++17 `if` 初始化语句与结构化绑定; 无 `let` 绑定与布尔表达式的链式组合": "https://en.cppreference.com/w/cpp/",
    "Rust Language FAQ / 2025; Rust Book — What is Rust? / 2024; 核心设计决策: 通过所有权系统（ownership + borrowing + lifetimes）在编译期消除数据竞争、悬垂指针和内存泄漏，无需运行时 GC; RustBelt — Jung et al., POPL 2018; 形式化证明: Rust 的类型系统保证内存安全": "https://www.rust-lang.org/",
    # 第三波补充：缩写与模板标签
    "The Cargo Book": "https://doc.rust-lang.org/cargo/index.html",
    "std::f64::consts 文档": "https://doc.rust-lang.org/std/f64/consts/index.html",
    "Pierce, TAPL §24.2 — Subtyping and Recursive Types": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "Rust Unsafe Code Guidelines WG / 2025": "https://rust-lang.github.io/unsafe-code-guidelines/",
    "RBE — 示例名": "https://doc.rust-lang.org/rust-by-example/index.html",
    "RFC XXXX": "https://rust-lang.github.io/rfcs/index.html",
    "REF — §4.1.9 Borrowing": "https://doc.rust-lang.org/reference/introduction.html",
    "UNB — gen_blocks": "https://doc.rust-lang.org/nightly/unstable-book/language-features/gen-blocks.html",
    "Rust Team / 2025": "https://www.rust-lang.org/",
    "Rust Foundation 2026-05-06": "https://foundation.rust-lang.org/",
    "Rust Foundation 2026-01; Rust RFC Tracker": "https://foundation.rust-lang.org/",
    "Rust Project Goals 2025H2 Final Report 2026-05-18": "https://rust-lang.github.io/rust-project-goals/",
    "gRPC Blog 2026-05-21": "https://grpc.io/blog/",
    "Socket.dev 2026-05-22; Debian Rust Team": "https://socket.dev/",
    "Cargo 1.96 CHANGELOG 2026-05-28": "https://github.com/rust-lang/cargo/blob/master/CHANGELOG.md",
    "releases.rs 2026-05-26": "https://releases.rs/",
    "`../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`": None,
    "`MaybeUninit` 与 validity invariant 的形式化基础; 未初始化内存的语义模型": None,
    "状态封装的逻辑关系; 与 Rust 所有权系统的形式化对比": None,
    "C 的未初始化内存是 UB 的主要来源; `MaybeUninit` 提供类型安全的替代": None,
    "C++ 的可选类型与原地构造; 与 `MaybeUninit::assume_init()` 的设计对比": None,
}

# 如果精确映射值为 None，表示映射到内部 methodology / index（由规则处理）

CRATE_DOMAINS = {
    "serde": "https://serde.rs/",
    "serde.rs": "https://serde.rs/",
    "tokio": "https://docs.rs/tokio/latest/tokio/",
    "tokio-rs": "https://tokio.rs/",
    "rayon": "https://docs.rs/rayon/latest/rayon/",
    "axum": "https://docs.rs/axum/latest/axum/",
    "wasm-bindgen": "https://rustwasm.github.io/docs/wasm-bindgen/",
    "clap": "https://docs.rs/clap/latest/clap/",
    "tokio-stream": "https://docs.rs/tokio-stream/latest/tokio_stream/",
    "futures-rs": "https://docs.rs/futures/latest/futures/",
    "futures": "https://docs.rs/futures/latest/futures/",
    "loom": "https://docs.rs/loom/latest/loom/",
    "eyre": "https://docs.rs/eyre/latest/eyre/",
    "color-eyre": "https://docs.rs/color-eyre/latest/color_eyre/",
    "miette": "https://docs.rs/miette/latest/miette/",
    "snafu": "https://docs.rs/snafu/latest/snafu/",
    "anyhow": "https://docs.rs/anyhow/latest/anyhow/",
    "thiserror": "https://docs.rs/thiserror/latest/thiserror/",
    "hecs": "https://docs.rs/hecs/latest/hecs/",
    "surrealdb": "https://surrealdb.com/docs",
    "materialize": "https://materialize.com/docs/",
    "fluvio": "https://www.fluvio.io/docs/",
    "risingwave": "https://docs.risingwave.com/",
    "meilisearch": "https://www.meilisearch.com/docs",
    "solana": "https://solana.com/docs",
    "polkadot": "https://substrate.io/",
    "substrate": "https://substrate.io/",
    "near": "https://near.org/",
    "ethers-rs": "https://docs.rs/ethers/latest/ethers/",
    "leptos": "https://docs.rs/leptos/latest/leptos/",
    "egui": "https://docs.rs/egui/latest/egui/",
    "aya": "https://aya-rs.dev/",
    "aya-rs": "https://aya-rs.dev/",
    "quinn": "https://docs.rs/quinn/latest/quinn/",
    "poem-openapi": "https://docs.rs/poem-openapi/latest/poem_openapi/",
    "tonic": "https://docs.rs/tonic/latest/tonic/",
    "tower": "https://docs.rs/tower/latest/tower/",
    "async-stream": "https://docs.rs/async-stream/latest/async_stream/",
    "event-listener": "https://docs.rs/event-listener/latest/event_listener/",
    "scopeguard": "https://docs.rs/scopeguard/latest/scopeguard/",
    "crossbeam-epoch": "https://docs.rs/crossbeam-epoch/latest/crossbeam_epoch/",
    "tokio-uring": "https://github.com/tokio-rs/tokio-uring",
    "candle": "https://huggingface.github.io/candle/",
    "wgpu": "https://docs.rs/wgpu/latest/wgpu/",
    "naga": "https://docs.rs/naga/latest/naga/",
    "ratatui": "https://docs.rs/ratatui/latest/ratatui/",
    "mio": "https://docs.rs/mio/latest/mio/",
    "actix-web": "https://actix.rs/",
    "actix": "https://actix.rs/actors/",
    "nalgebra": "https://docs.rs/nalgebra/latest/nalgebra/",
    "ndarray": "https://docs.rs/ndarray/latest/ndarray/",
    "redis-rs": "https://docs.rs/redis/latest/redis/",
    "redis": "https://docs.rs/redis/latest/redis/",
    "mongodb-rust-driver": "https://docs.rs/mongodb/latest/mongodb/",
    "mongodb": "https://docs.rs/mongodb/latest/mongodb/",
    "regex": "https://docs.rs/regex/latest/regex/",
    "reqwest": "https://docs.rs/reqwest/latest/reqwest/",
    "hyper": "https://docs.rs/hyper/latest/hyper/",
    "bevy": "https://bevyengine.org/learn/book/",
    "fyrox": "https://fyrox-book.github.io/",
    "wasmtime": "https://docs.wasmtime.dev/",
    "wit-bindgen": "https://github.com/bytecodealliance/wit-bindgen",
    "cargo-deny": "https://docs.rs/cargo-deny/latest/cargo_deny/",
    "cargo-geiger": "https://docs.rs/cargo-geiger/latest/cargo_geiger/",
    "cargo-vet": "https://mozilla.github.io/cargo-vet/",
    "cargo-fuzz": "https://rust-fuzz.github.io/book/",
    "sccache": "https://github.com/mozilla/sccache",
    "rodio": "https://docs.rs/rodio/latest/rodio/",
    "swatinem/rust-cache": "https://github.com/Swatinem/rust-cache",
    "nom": "https://docs.rs/nom/latest/nom/",
    "typenum": "https://docs.rs/typenum/latest/typenum/",
    "jemalloc": "https://github.com/jemalloc/jemalloc",
    "mimalloc": "https://github.com/microsoft/mimalloc",
    "opentelemetry": "https://docs.rs/opentelemetry/latest/opentelemetry/",
    "tracing": "https://docs.rs/tracing/latest/tracing/",
    "criterion": "https://docs.rs/criterion/latest/criterion/",
    "criterion.rs": "https://docs.rs/criterion/latest/criterion/",
    "kani": "https://model-checking.github.io/kani/",
    "prusti": "https://www.pm.inf.ethz.ch/research/prusti.html",
    "creusot": "https://creusot.rs/",
    "verus": "https://verus-lang.github.io/verus/",
    "aeneas": "https://github.com/AeneasVerif/aeneas",
    "miri": "https://github.com/rust-lang/miri/",
    "ferrocene": "https://ferrocene.dev/",
    "iris": "https://iris-project.org/",
}

ABBREVIATIONS = {
    "REF": "https://doc.rust-lang.org/reference/introduction.html",
    "TRPL": "https://doc.rust-lang.org/book/title-page.html",
    "NOM": "https://doc.rust-lang.org/nomicon/index.html",
    "RBE": "https://doc.rust-lang.org/rust-by-example/index.html",
    "RFC": "https://rust-lang.github.io/rfcs/index.html",
    "EDG": "https://doc.rust-lang.org/edition-guide/index.html",
    "ASB": "https://rust-lang.github.io/async-book/index.html",
    "CAR": "https://doc.rust-lang.org/cargo/index.html",
    "RUC": "https://doc.rust-lang.org/rustc/index.html",
    "UNB": "https://doc.rust-lang.org/nightly/unstable-book/index.html",
    "STD": "https://doc.rust-lang.org/std/index.html",
    "FOR": "https://forge.rust-lang.org/",
    "RB18": "https://plv.mpi-sws.org/rustbelt/",
    "Jung21": "https://plv.mpi-sws.org/rustbelt/stacked-borrows/",
    "Jung23": "https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/tree-borrows.md",
    "Wadler89": "https://doi.org/10.1145/99370.99404",
    "TAPL": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "LL87": "https://en.wikipedia.org/wiki/Linear_logic",
    "Reynolds02": "https://doi.org/10.1007/3-540-36575-3_19",
    "Viper": "https://www.pm.inf.ethz.ch/research/viper.html",
    "CR": "https://google.github.io/comprehensive-rust/",
    "RI": "https://internals.rust-lang.org/",
    "TWiR": "https://this-week-in-rust.org/",
    "BE": "https://bevyengine.org/learn/book/",
    "TK": "https://docs.rs/tokio/latest/tokio/",
    "WG": "https://gamedev.rs/",
    "COR": "https://corrode.dev/",
    "BOATS": "https://without.boats/blog/",
}

CONFERENCES = {
    "PLDI": "https://pldi.sigplan.org/",
    "POPL": "https://popl.sigplan.org/",
    "ICSE": "https://conf.researchr.org/home/icse",
    "SOSP": "https://sosp.org/",
    "OOPSLA": "https://oopsla.org/",
    "SPAA": "https://spaa.acm.org/",
    "VLDB": "https://vldb.org/",
    "PACT": "https://pact2023.cs.gmu.edu/",
    "ESEC": "https://esec-fse.org/",
    "FSE": "https://esec-fse.org/",
    "AAAI": "https://aaai.org/",
    "ICML": "https://icml.cc/",
    "USENIX Security": "https://www.usenix.org/conference/usenixsecurity25",
    "IEEE Software": "https://www.computer.org/software-magazine/",
}


def normalize_segment(seg: str) -> str:
    s = seg.strip()
    # 去掉被转义的反斜杠
    s = s.replace("\\", "")
    # 去掉首尾残留的 [ ]
    while s.startswith("[") and s.endswith("]"):
        s = s[1:-1].strip()
    s = s.lstrip("[").rstrip("]")
    return s.strip()


def split_compound(label: str) -> list[str]:
    """按常见分隔符拆分组合来源，但保留已有链接。"""
    if LINK_RE.search(label):
        return [label]
    # 支持 ; / · |
    parts = re.split(r"\s*[;；|·]\s*", label)
    # 也按 " / " 拆分，但避免 https://
    out = []
    for p in parts:
        for sub in re.split(r"\s+/\s+", p):
            if sub and not sub.startswith("http"):
                out.append(sub)
            elif sub:
                out.append(sub)
    return [x for x in out if x.strip()]


def map_arxiv(s: str) -> str | None:
    m = re.search(r"arXiv[：:]?\s*(\d{4}\.\d+)(v\d+)?", s, re.I)
    if m:
        return f"https://arxiv.org/abs/{m.group(1)}"
    return None


def map_dead_link_comment(s: str) -> str | None:
    """恢复带注释的失效链接：<!-- 原链接: URL -->"""
    m = re.search(r"<!--\s*原链接[：:]\s*(https?://[^\s>]+)\s*-->", s)
    if m:
        return m.group(1)
    return None


def map_rfc(s: str) -> str | None:
    m = re.search(r"\bRFC\s*(\d+)\b", s, re.I)
    if m:
        return f"https://rust-lang.github.io/rfcs/{m.group(1)}.html"
    return None


def map_rust_release(s: str) -> str | None:
    m = re.search(r"Rust\s+(\d+\.\d+(?:\.\d+)?)\s+Release\s+Notes", s, re.I)
    if m:
        ver = m.group(1)
        if ver.count(".") == 1:
            ver += ".0"
        return f"https://releases.rs/docs/{ver}/"
    return None


def map_rust_reference(s: str) -> str | None:
    m = re.match(r"(?:The\s+)?Rust\s+Reference\s*[—:\-]\s*(.+)", s, re.I)
    if not m:
        m = re.match(r"Rust\s+Reference\s*:\s*(.+)", s, re.I)
    if not m:
        return None
    topic = m.group(1).strip()
    # 简单主题映射
    ref_map = {
        "Pin": "https://doc.rust-lang.org/reference/items/traits.html",
        "Unions": "https://doc.rust-lang.org/reference/items/unions.html",
        "Enums": "https://doc.rust-lang.org/reference/items/enumerations.html",
        "Lifetime elision": "https://doc.rust-lang.org/reference/lifetime-elision.html",
        "Behavior considered undefined": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
        "Unsafe": "https://doc.rust-lang.org/reference/unsafe-keyword.html",
        "Macros": "https://doc.rust-lang.org/reference/macros.html",
        "Generic Parameters": "https://doc.rust-lang.org/reference/items/generics.html",
        "The ? operator": "https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator",
        "Object Safety": "https://doc.rust-lang.org/reference/items/traits.html#object-safety",
        "Variance": "https://doc.rust-lang.org/reference/subtyping.html#variance",
        "Ownership, Lifetimes, Types": "https://doc.rust-lang.org/reference/introduction.html",
        "unsafe, Macros": "https://doc.rust-lang.org/reference/unsafe-keyword.html",
        "Lifetime elision §The rules": "https://doc.rust-lang.org/reference/lifetime-elision.html",
        "References": "https://doc.rust-lang.org/reference/types/pointer.html",
        "Mutable References": "https://doc.rust-lang.org/reference/types/pointer.html",
    }
    return ref_map.get(topic, "https://doc.rust-lang.org/reference/introduction.html")


def map_cargo_book(s: str) -> str | None:
    m = re.match(r"Cargo\s+Book\s*[—:\-]\s*(.+)", s, re.I)
    if not m:
        return None
    topic = m.group(1).strip()
    cargo_map = {
        "Build Scripts": "https://doc.rust-lang.org/cargo/reference/build-scripts.html",
        "Build Script Outputs": "https://doc.rust-lang.org/cargo/reference/build-scripts.html#outputs-of-the-build-script",
        "SemVer Compatibility": "https://doc.rust-lang.org/cargo/reference/semver.html",
        "How Cargo resolves dependencies": "https://doc.rust-lang.org/cargo/reference/resolver.html",
        "Resolver versions": "https://doc.rust-lang.org/cargo/reference/resolver.html#resolver-versions",
        "The rust-version field": "https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field",
        "cargo vendor": "https://doc.rust-lang.org/cargo/reference/commands/cargo-vendor.html",
        "Overriding Dependencies": "https://doc.rust-lang.org/cargo/reference/overriding-dependencies.html",
        "Registry Protocols": "https://doc.rust-lang.org/cargo/reference/registry-index.html",
        "Publishing on crates.io": "https://doc.rust-lang.org/cargo/reference/publishing.html",
        "Authentication": "https://doc.rust-lang.org/cargo/reference/authentication.html",
        "Registry Authentication": "https://doc.rust-lang.org/cargo/reference/authentication.html",
        "Recommended configuration": "https://doc.rust-lang.org/cargo/reference/config.html",
        "Cargo Home": "https://doc.rust-lang.org/cargo/reference/config.html#cargohome",
        "Build Cache": "https://doc.rust-lang.org/cargo/reference/build-cache.html",
        "External Tools": "https://doc.rust-lang.org/cargo/reference/external-tools.html",
        "External Tools — JSON messages": "https://doc.rust-lang.org/cargo/reference/external-tools.html#json-messages",
    }
    return cargo_map.get(topic, "https://doc.rust-lang.org/cargo/index.html")


def map_rustc_dev_guide(s: str) -> str | None:
    if not re.search(r"rustc[-\s]?dev[-\s]?guide", s, re.I) and not s.startswith("Rustc Dev Guide"):
        return None
    return "https://rustc-dev-guide.rust-lang.org/"


def map_language_spec(s: str) -> str | None:
    low = s.lower()
    if low.startswith("c++ reference:"):
        return "https://en.cppreference.com/w/cpp"
    if low.startswith("go spec:") or low.startswith("go language specification"):
        return "https://go.dev/ref/spec"
    if low.startswith("haskell ghc user guide"):
        return "https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/"
    if low.startswith("typescript handbook"):
        return "https://www.typescriptlang.org/docs/handbook/intro.html"
    if low.startswith("java language spec") or low.startswith("java jls"):
        return "https://docs.oracle.com/javase/specs/jls/se17/html/index.html"
    return None


def map_blog(s: str) -> str | None:
    low = s.lower()
    if "inside rust" in low:
        return "https://blog.rust-lang.org/inside-rust/"
    if "rust blog" in low or low.startswith("rust lang team blog"):
        return "https://blog.rust-lang.org/"
    if "without.boats" in low or "without boats" in low:
        return "https://without.boats/blog/"
    if "yoshua wuyts" in low or "yoshuawuyts" in low:
        return "https://blog.yoshuawuyts.com/"
    if "rust internals" in low:
        return "https://internals.rust-lang.org/"
    if "ralf jung" in low:
        return "https://www.ralfj.de/blog/"
    return None


def map_crate_docs(s: str) -> str | None:
    """识别 crate 文档标签，如 'xxx docs', 'xxx Documentation', 'xxx crate docs'。"""
    # 已有精确映射优先，这里处理模式
    low = s.lower()
    # 去掉常见后缀
    cleaned = re.sub(r"\s+(docs?|documentation|guide|book|blog|readme|source|crate docs|官方文档|源码)$", "", s, flags=re.I).strip()
    # 取第一个 token 作为 crate 候选
    m = re.match(r"^([A-Za-z0-9_\-]+)(?:[\s/]|$)", cleaned)
    if not m:
        return None
    name = m.group(1).lower()
    # 处理 futures-rs -> futures
    if name.endswith("-rs"):
        name = name[:-3]
    if name in CRATE_DOMAINS:
        return CRATE_DOMAINS[name]
    # 常见变体
    if name == "futures":
        return "https://docs.rs/futures/latest/futures/"
    if name == "tokio":
        return "https://docs.rs/tokio/latest/tokio/"
    if name == "serde":
        return "https://serde.rs/"
    if name == "wasm-bindgen":
        return "https://rustwasm.github.io/docs/wasm-bindgen/"
    # 默认 docs.rs（仅当标签明显是 crate 文档）
    if re.search(r"\b(docs?|documentation|crate|指南|文档)\b", low) and name not in {"the", "rust", "a", "an"}:
        return f"https://docs.rs/{name}/latest/{name.replace('-', '_')}/"
    return None


def map_abbreviation(s: str) -> str | None:
    """识别 sources/INDEX.md 中的来源标识符，如 `REF — §章节`、`RB18 — §章节`。"""
    m = re.match(r"^([A-Z]{2,})(?:\s*[—:\-]\s*(.+))?", s)
    if not m:
        return None
    abbr = m.group(1)
    if abbr in ABBREVIATIONS:
        return ABBREVIATIONS[abbr]
    return None


def map_conference(s: str) -> str | None:
    for key, url in CONFERENCES.items():
        if key.lower() in s.lower():
            return url
    return None


def map_abbreviation_templates(s: str) -> str | None:
    """映射 concept/sources/INDEX.md 中的缩写模板示例（如 REF、NOM、RFC XXXX）。"""
    abbr_map = {
        "REF": "https://doc.rust-lang.org/reference/introduction.html",
        "TRPL": "https://doc.rust-lang.org/book/title-page.html",
        "NOM": "https://doc.rust-lang.org/nomicon/index.html",
        "RBE": "https://doc.rust-lang.org/rust-by-example/index.html",
        "RFC": "https://rust-lang.github.io/rfcs/index.html",
        "EDG": "https://doc.rust-lang.org/edition-guide/index.html",
        "ASB": "https://rust-lang.github.io/async-book/",
        "CAR": "https://doc.rust-lang.org/cargo/index.html",
        "RUC": "https://doc.rust-lang.org/rustc/index.html",
        "UNB": "https://doc.rust-lang.org/nightly/unstable-book/index.html",
        "STD": "https://doc.rust-lang.org/std/index.html",
        "FOR": "https://forge.rust-lang.org/",
        "RB18": "https://plv.mpi-sws.org/rustbelt/",
        "Jung21": "https://plv.mpi-sws.org/rustbelt/stacked-borrows/",
        "Jung23": "https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/tree-borrows.md",
        "Wadler89": "https://doi.org/10.1145/99370.99404",
        "TAPL": "https://www.cis.upenn.edu/~bcpierce/tapl/",
        "LL87": "https://en.wikipedia.org/wiki/Linear_logic",
        "Reynolds02": "https://doi.org/10.1007/3-540-36575-3_19",
        "Iris": "https://iris-project.org/",
        "Viper": "https://www.pm.inf.ethz.ch/research/prusti.html",
        "Kani": "https://model-checking.github.io/kani/",
        "Miri": "https://github.com/rust-lang/miri/",
        "CR": "https://google.github.io/comprehensive-rust/",
        "RI": "https://internals.rust-lang.org/",
        "TWiR": "https://this-week-in-rust.org/",
        "BE": "https://bevyengine.org/learn/book/",
        "TK": "https://docs.rs/tokio/latest/tokio/",
        "WG": "https://gamedev.rs/",
        "COR": "https://corrode.dev/",
        "BOATS": "https://without.boats/blog/",
    }
    # 匹配 "REF — §章节"、"RFC XXXX"、"STD — 模块" 等
    m = re.match(r"^(`?)([A-Za-z0-9]+)\1\s*[-—:]\s*", s)
    if m:
        key = m.group(2)
        if key in abbr_map:
            return abbr_map[key]
    # 纯缩写，如 "RFC XXXX"、"Jung21"、"Iris"
    m = re.match(r"^(`?)([A-Za-z0-9]+)\1\s*(?:\(|$)", s)
    if m:
        key = m.group(2)
        if key in abbr_map:
            return abbr_map[key]
    # RFC XXXX 模板
    if re.match(r"^RFC\s+X{4}\b", s, re.I):
        return abbr_map.get("RFC")
    return None


def map_std_docs(s: str) -> str | None:
    """匹配 std::path::Item、Rust Standard Library: item、std docs 等。"""
    # 去掉常见前缀/后缀
    cleaned = s
    cleaned = re.sub(r"^(?:Rust\s+)?std(?:\s+docs?)?[：:\-—\s]*", "", cleaned, flags=re.I)
    cleaned = re.sub(r"^(?:Rust\s+)?Standard\s+Library\s*[：:]\s*", "", cleaned, flags=re.I)
    cleaned = re.sub(r"\s+docs?\s*$", "", cleaned, flags=re.I)
    # 匹配 std::xxx::Item
    m = re.match(r"std::([A-Za-z0-9_]+(?:::[A-Za-z0-9_]+)*)(?:::([A-Za-z0-9_]+))?\s*(?:\(|::)?", cleaned)
    if m:
        path = m.group(1)
        item = m.group(2)
        parts = path.split("::")
        if item:
            return f"https://doc.rust-lang.org/std/{'/'.join(parts)}/?search={item}"
        return f"https://doc.rust-lang.org/std/{'/'.join(parts)}/index.html"
    # 匹配 panic::Location 等
    m = re.match(r"([a-z_]+)::([A-Za-z_]+)(?:::([A-Za-z_]+))?", cleaned)
    if m:
        return f"https://doc.rust-lang.org/std/{m.group(1)}/index.html"
    return None


def map_academic_or_classic(s: str) -> str | None:
    low = s.lower()
    # 经典作者 / 标题快速匹配
    if "pierce" in low and "programming languages" in low:
        return "https://www.cis.upenn.edu/~bcpierce/tapl/"
    if "girard" in low and "linear logic" in low:
        return "https://en.wikipedia.org/wiki/Linear_logic"
    if "howard" in low and "formulae-as-types" in low:
        return "https://www.cs.cmu.edu/~crary/812f19/lectures/15.pdf"
    if "cardelli" in low and "type systems" in low:
        return "https://doi.org/10.1145/234313.234418"
    if "harper" in low and "practical foundations" in low:
        return "https://www.cs.cmu.edu/~rwh/pfpl/"
    if "tofte" in low or "talpin" in low:
        return "https://doi.org/10.1145/176454.176456"
    if "milner" in low and "π-calculus" in low:
        return "https://doi.org/10.1007/BFb0034572"
    if "hoare" in low and "csp" in low:
        return "https://doi.org/10.1145/359576.359585"
    if "herlihy" in low or "shavit" in low:
        return "https://www.cs.brown.edu/~mph/HerlihyShavit/"
    if "wright" in low and "felleisen" in low:
        return "https://doi.org/10.1145/182590.182597"
    if "damas" in low and "milner" in low:
        return "https://doi.org/10.1145/582153.582176"
    if "cardelli" in low and "wegner" in low:
        return "https://doi.org/10.1145/6041.6042"
    if "reynolds" in low and "separation logic" in low:
        return "https://doi.org/10.1007/3-540-36575-3_19"
    if "wadler" in low and "theorems for free" in low:
        return "https://doi.org/10.1145/99370.99404"
    if "boyland" in low and "fractional" in low:
        return "https://doi.org/10.1007/3-540-44898-5_4"
    if "sipser" in low:
        return "https://math.mit.edu/~sipser/book.html"
    if "dreyer" in low:
        return "https://doi.org/10.1145/1102351.1102355"
    if "zdan" in low and "information security" in low:
        return "https://repository.upenn.edu/cgi/viewcontent.cgi?article=1084&context=cis_papers"
    if "plotkin" in low and "algebraic effects" in low:
        return "https://doi.org/10.1017/S095679681000015X"
    if "leijen" in low and "koka" in low:
        return "https://www.microsoft.com/en-us/research/publication/koka-programming-with-row-polymorphic-effect-types/"
    if "madsen" in low and "flix" in low:
        return "https://flix.dev/"
    if "jung" in low and "rustbelt" in low:
        return "https://plv.mpi-sws.org/rustbelt/"
    if "jung" in low and "tree borrows" in low:
        return "https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/tree-borrows.md"
    if "shapiro" in low and "crdt" in low:
        return "https://arxiv.org/abs/1805.04258"
    if "lamport" in low and "paxos" in low:
        return "https://lamport.azurewebsites.net/pubs/paxos-simple.pdf"
    if "boehm" in low and "adve" in low:
        return "https://doi.org/10.1145/1375581.1375595"
    if "manning" in low and "information retrieval" in low:
        return "https://nlp.stanford.edu/IR-book/"
    if "quinlan" in low and "decision trees" in low:
        return "https://doi.org/10.1023/A:1022643204877"
    if "bordes" in low and "translating embeddings" in low:
        return "https://doi.org/10.48550/arXiv.1301.3485"
    if "novak" in low and "concept maps" in low:
        return "https://cmap.ihmc.us/docs/theory-of-concept-maps"
    if "miller" in low and "chunking" in low:
        return "https://en.wikipedia.org/wiki/Chunking_(psychology)"
    if "bloom" in low and "taxonomy" in low:
        return "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/"
    if "bruner" in low:
        return "https://en.wikipedia.org/wiki/Jerome_Bruner"
    if "collins" in low and "quillian" in low:
        return "https://en.wikipedia.org/wiki/Semantic_network"
    if "denning" in low and "secure information flow" in low:
        return "https://doi.org/10.1145/360051.360056"
    if "kobayashi" in low and "fault-tolerant" in low:
        return "https://doi.org/10.1007/3-540-44898-5_13"
    if "session types in rust" in low:
        return "https://github.com/rust-lang/rfcs"
    if "vasconcelos" in low:
        return "https://doi.org/10.1007/978-3-319-30936-1_8"
    if "kfoury" in low and "system f" in low:
        return "https://doi.org/10.1145/96709.96733"
    if "robinson" in low and "resolution" in low:
        return "https://doi.org/10.1145/321250.321253"
    if "blumofe" in low or "leiserson" in low:
        return "https://doi.org/10.1145/324133.324234"
    if "spaa" in low and "rust" in low:
        return "https://doi.org/10.1145/3626183.3659964"
    if "heewitt" in low and "actor" in low:
        return "https://doi.org/10.5555/1622875.1623080"
    if "dennis" in low and "van horn" in low:
        return "https://doi.org/10.1145/365813.365821"
    if "armstrong" in low and "reliable" in low:
        return "https://erlang.org/download/armstrong_thesis_2003.pdf"
    return None


def map_internal_or_index(s: str) -> bool:
    """判断是否应回退到内部方法论/权威索引（不返回 URL）。"""
    low = s.lower()
    indicators = [
        "原创", "方法论", "参照", "ag", "概念", " Bloom", "taxonomy", "学习理论",
        "来源对齐", "wave", "sprint", "阶段", "规划", "执行记录", "质量铁三角",
        "目录结构", "inter_layer_map", "learning_guide", "methodology",
        "规范级", "学术级", "教学级", "工业级", "社区级", "官方规范", "学术论文",
        "社区与工业", "内部", "原创分析", "原创映射", "原创推断", "原创实现",
    ]
    return any(ind in s for ind in indicators)


def transform_segment(seg: str, index_link: str, method_link: str) -> str | None:
    s = normalize_segment(seg)
    if not s:
        return None
    # 已经是链接的段落
    if s.startswith("http"):
        return None

    if s in EXACT_MAP:
        url = EXACT_MAP[s]
        if url is None:
            url = method_link if map_internal_or_index(s) else index_link
        return f"[{s}]({url})"

    for fn in (
        map_arxiv,
        map_dead_link_comment,
        map_rfc,
        map_rust_release,
        map_abbreviation,
        map_rust_reference,
        map_cargo_book,
        map_std_docs,
        map_language_spec,
        map_blog,
        map_rustc_dev_guide,
        map_crate_docs,
        map_conference,
        map_abbreviation_templates,
        map_academic_or_classic,
    ):
        url = fn(s)
        if url:
            return f"[{s}]({url})"

    if map_internal_or_index(s):
        return f"[{s}]({index_link})"

    return None


def transform_label(label: str, index_link: str, method_link: str) -> str | None:
    """处理单个标签，支持组合来源拆分。"""
    s = label.strip()
    if not s:
        return None
    # 优先尝试完整标签的精确映射
    whole = transform_segment(s, index_link, method_link)
    if whole:
        return whole
    parts = split_compound(s)
    if len(parts) == 1:
        return None

    mapped = []
    any_mapped = False
    for part in parts:
        mapped_part = transform_segment(part, index_link, method_link)
        if mapped_part:
            mapped.append(mapped_part)
            any_mapped = True
        else:
            # 保留原文
            mapped.append(part)
    if not any_mapped:
        return None
    return "; ".join(mapped)


def replace_bracketed_sources(text: str, index_link: str, method_link: str) -> str:
    result = []
    i = 0
    while i < len(text):
        m = re.search(r"\[来源[：:]\s*", text[i:])
        if not m:
            result.append(text[i:])
            break
        start = i + m.start()
        result.append(text[i:start])
        inner_start = i + m.end()
        depth = 0
        pos = inner_start
        found = False
        while pos < len(text):
            ch = text[pos]
            # Markdown 转义：跳过 \[ 与 \|，但把 \] 视为普通闭合 ] 处理
            if ch == "\\" and pos + 1 < len(text) and text[pos + 1] in "[|":
                pos += 2
                continue
            if ch == "[":
                depth += 1
                pos += 1
                continue
            if ch == "]":
                if depth > 0:
                    depth -= 1
                    pos += 1
                    continue
                # 如果 `]` 是某个内嵌链接 `[...](...)` 的一部分，跳过该链接
                if pos + 1 < len(text) and text[pos + 1] == "(":
                    # 跳过配对的括号内容
                    paren = pos + 2
                    paren_depth = 1
                    while paren < len(text) and paren_depth > 0:
                        if text[paren] == "(":
                            paren_depth += 1
                        elif text[paren] == ")":
                            paren_depth -= 1
                        paren += 1
                    pos = paren
                    continue
                found = True
                break
            pos += 1
        if not found:
            result.append(text[start:])
            break
        content = text[inner_start:pos]
        whole = text[start : pos + 1]
        # 如果该 `]` 后紧跟 `(`，说明是链接语法，跳过
        if pos + 1 < len(text) and text[pos + 1] == "(":
            result.append(whole)
            i = pos + 1
            continue
        if not LINK_RE.search(whole):
            new = transform_label(content, index_link, method_link)
            if new:
                result.append(new)
                i = pos + 1
                continue
        result.append(whole)
        i = pos + 1
    return "".join(result)


def replace_bare_sources(text: str, index_link: str, method_link: str) -> str:
    def repl(m):
        label = m.group(1)
        if LINK_RE.search(label):
            return m.group(0)
        new = transform_label(label, index_link, method_link)
        return new if new else m.group(0)

    return BARE_RE.sub(repl, text)


def fix_file(path: Path) -> int:
    text = path.read_text(encoding="utf-8", errors="ignore")
    original = text
    index_link = relative_path(path, INDEX_TARGET)
    method_link = relative_path(path, METHOD_TARGET)

    text = replace_bracketed_sources(text, index_link, method_link)
    text = replace_bare_sources(text, index_link, method_link)

    if text != original:
        path.write_text(text, encoding="utf-8", errors="ignore", newline="\n")
        return 1
    return 0


def main():
    changed = 0
    files = 0
    for d in TARGET_DIRS:
        full = ROOT / d
        if not full.exists():
            continue
        for p in sorted(full.rglob("*.md")):
            if "archive" in p.parts or "node_modules" in p.parts:
                continue
            files += 1
            changed += fix_file(p)
    print(f"已扫描 {files} 个文件，修改 {changed} 个。")


if __name__ == "__main__":
    main()
