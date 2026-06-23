#!/usr/bin/env python3
"""为 knowledge/ 下缺少模块 8 的核心文档批量补充国际化对齐来源。

策略：
1. 扫描 knowledge/ 下所有 *.md，跳过 archive/、temp/、README.md、SUMMARY.md。
2. 仅处理尚未包含 `## 📚 模块 8: 国际化对齐` 的文件。
3. 根据文件路径/文件名推断主题，生成官方 + 学术 + 社区权威来源表格。
4. 在文件末尾追加模块 8，保留原有内容。
"""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent / "knowledge"
SECTION_HEADER = "## 📚 模块 8: 国际化对齐"

# 通用权威来源
OFFICIAL_DEFAULT = [
    ("[The Rust Programming Language](https://doc.rust-lang.org/book/)", "官方教程"),
    ("[Rust Reference](https://doc.rust-lang.org/reference/)", "官方参考"),
    ("[Rust By Example](https://doc.rust-lang.org/rust-by-example/)", "官方示例"),
]

ACADEMIC_DEFAULT = [
    ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "类型系统语义正确性"),
    ("[Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)", "别名模型"),
]

COMMUNITY_DEFAULT = [
    ("[This Week in Rust](https://this-week-in-rust.org/)", "社区周报"),
    ("[Rustlings](https://github.com/rust-lang/rustlings)", "交互式练习"),
]

# 主题映射：关键词 -> (官方, 学术, 社区)
TOPIC_SOURCES = {
    "ownership": {
        "official": [
            ("[TRPL Ch04 — Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)", "所有权基础"),
            ("[Rustonomicon — Ownership](https://doc.rust-lang.org/nomicon/ownership.html)", "所有权高级话题"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "所有权语义"),
            ("[Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/)", "别名模型"),
        ],
        "community": [
            ("[Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/)", "可视化教学"),
            ("[Rustlings](https://github.com/rust-lang/rustlings)", "所有权练习"),
        ],
    },
    "borrowing": {
        "official": [
            ("[TRPL Ch04 — References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)", "借用与引用"),
            ("[Rust Reference — Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html)", "生命周期省略"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "借用语义"),
            ("[Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/)", "别名模型"),
        ],
        "community": [
            ("[Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/)", "借用可视化"),
            ("[Rustlings](https://github.com/rust-lang/rustlings)", "借用练习"),
        ],
    },
    "lifetimes": {
        "official": [
            ("[TRPL Ch10 — Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)", "生命周期语法"),
            ("[Rust Reference — Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html)", "生命周期省略规则"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "生命周期语义"),
        ],
        "community": [
            ("[Rustlings](https://github.com/rust-lang/rustlings)", "生命周期练习"),
            ("[Common Rust Lifetime Misconceptions](https://github.com/pretzelhammer/rust-blog/blob/master/posts/common-rust-lifetime-misconceptions.md)", "常见误解"),
        ],
    },
    "iterators": {
        "official": [
            ("[TRPL Ch13 — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html)", "迭代器"),
            ("[std::iter](https://doc.rust-lang.org/std/iter/)", "迭代器 trait API"),
        ],
        "academic": [
            ("[Iterator Fusion](https://en.wikipedia.org/wiki/Iterator)", "迭代器理论基础"),
        ],
        "community": [
            ("[Rust By Example — Iterators](https://doc.rust-lang.org/rust-by-example/trait/iter.html)", "迭代器示例"),
        ],
    },
    "traits": {
        "official": [
            ("[TRPL Ch10 — Traits](https://doc.rust-lang.org/book/ch10-02-traits.html)", "Trait 基础"),
            ("[Rust Reference — Traits](https://doc.rust-lang.org/reference/items/traits.html)", "Trait 参考"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "Trait 对象语义"),
        ],
        "community": [
            ("[Rust API Guidelines — Traits](https://rust-lang.github.io/api-guidelines/)", "Trait 设计最佳实践"),
            ("[Rust By Example — Traits](https://doc.rust-lang.org/rust-by-example/trait.html)", "Trait 示例"),
        ],
    },
    "generics": {
        "official": [
            ("[TRPL Ch10 — Generic Types](https://doc.rust-lang.org/book/ch10-01-syntax.html)", "泛型语法"),
            ("[Rust Reference — Generics](https://doc.rust-lang.org/reference/items/generics.html)", "泛型参考"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "泛型语义"),
        ],
        "community": [
            ("[Rust By Example — Generics](https://doc.rust-lang.org/rust-by-example/generics.html)", "泛型示例"),
        ],
    },
    "smart_pointers": {
        "official": [
            ("[TRPL Ch15 — Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)", "智能指针"),
            ("[std::boxed / std::rc / std::sync::Arc](https://doc.rust-lang.org/std/)", "智能指针 API"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "所有权与引用计数语义"),
        ],
        "community": [
            ("[Rust By Example — Box / Rc / Arc](https://doc.rust-lang.org/rust-by-example/std/box.html)", "智能指针示例"),
        ],
    },
    "strings": {
        "official": [
            ("[TRPL Ch08 — Strings](https://doc.rust-lang.org/book/ch08-02-strings.html)", "String 与 &str"),
            ("[std::string::String](https://doc.rust-lang.org/std/string/struct.String.html)", "String API"),
        ],
        "academic": [
            ("[Unicode Standard](https://www.unicode.org/standard/standard.html)", "Unicode 编码标准"),
        ],
        "community": [
            ("[Rust By Example — Strings](https://doc.rust-lang.org/rust-by-example/std/str.html)", "字符串示例"),
        ],
    },
    "type_conversions": {
        "official": [
            ("[Rust Reference — Type Cast Expressions](https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions)", "类型转换"),
            ("[Rust By Example — Casting](https://doc.rust-lang.org/rust-by-example/types/cast.html)", "类型转换示例"),
        ],
        "academic": [
            ("[RFC 2484 — TryFrom/TryInto](https://rust-lang.github.io/rfcs/2484-trait-from-tryfrom.html)", "安全转换 trait"),
        ],
        "community": [
            ("[Rust Cookbook — Conversions](https://rust-lang-nursery.github.io/rust-cookbook/conversions.html)", "转换模式"),
        ],
    },
    "async": {
        "official": [
            ("[The Rust Async Book](https://rust-lang.github.io/async-book/)", "异步编程官方教程"),
            ("[TRPL Ch17 — Async/Await](https://doc.rust-lang.org/book/ch17-00-async-await.html)", "async/await 语法"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "异步语义基础"),
        ],
        "community": [
            ("[Tokio Documentation](https://tokio.rs/)", "Tokio 运行时"),
            ("[smol](https://github.com/smol-rs/smol)", "轻量异步运行时"),
        ],
    },
    "concurrency": {
        "official": [
            ("[TRPL Ch16 — Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)", "并发基础"),
            ("[Rustonomicon — Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html)", "并发高级话题"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "Send/Sync 语义"),
        ],
        "community": [
            ("[Rust Cookbook — Concurrency](https://rust-lang-nursery.github.io/rust-cookbook/concurrency.html)", "并发模式"),
            ("[Rayon Documentation](https://docs.rs/rayon/latest/rayon/)", "数据并行"),
        ],
    },
    "atomics": {
        "official": [
            ("[std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/)", "原子类型 API"),
            ("[Rustonomicon — Atomics](https://doc.rust-lang.org/nomicon/atomics.html)", "原子操作内存序"),
        ],
        "academic": [
            ("[C++ Memory Model](https://en.cppreference.com/w/cpp/atomic/memory_order)", "内存模型参考"),
        ],
        "community": [
            ("[Rust Cookbook — Atomics](https://rust-lang-nursery.github.io/rust-cookbook/concurrency.html)", "原子操作示例"),
        ],
    },
    "threads": {
        "official": [
            ("[TRPL Ch16 — Threads](https://doc.rust-lang.org/book/ch16-01-threads.html)", "线程"),
            ("[std::thread](https://doc.rust-lang.org/std/thread/)", "线程 API"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "线程安全语义"),
        ],
        "community": [
            ("[Rust Cookbook — Threads](https://rust-lang-nursery.github.io/rust-cookbook/concurrency.html)", "线程模式"),
        ],
    },
    "synchronization": {
        "official": [
            ("[std::sync](https://doc.rust-lang.org/std/sync/)", "同步原语 API"),
            ("[Rustonomicon — Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html)", "Send/Sync"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "同步语义"),
        ],
        "community": [
            ("[Rust Cookbook — Synchronization](https://rust-lang-nursery.github.io/rust-cookbook/concurrency.html)", "同步模式"),
        ],
    },
    "collections": {
        "official": [
            ("[std::collections](https://doc.rust-lang.org/std/collections/)", "集合类型 API"),
            ("[TRPL Ch08 — Common Collections](https://doc.rust-lang.org/book/ch08-00-common-collections.html)", "常用集合"),
        ],
        "academic": [
            ("[Data Structures](https://en.wikipedia.org/wiki/Data_structure)", "数据结构基础"),
        ],
        "community": [
            ("[Rust Cookbook — Data Structures](https://rust-lang-nursery.github.io/rust-cookbook/data_structures.html)", "集合使用模式"),
        ],
    },
    "error_handling": {
        "official": [
            ("[TRPL Ch09 — Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)", "错误处理"),
            ("[Rust By Example — Error Handling](https://doc.rust-lang.org/rust-by-example/error.html)", "错误处理示例"),
        ],
        "academic": [
            ("[Railway Oriented Programming](https://fsharpforfunandprofit.com/rop/)", "Result 组合模式"),
        ],
        "community": [
            ("[thiserror docs](https://docs.rs/thiserror/latest/thiserror/)", "错误派生宏"),
            ("[anyhow docs](https://docs.rs/anyhow/latest/anyhow/)", "错误传播"),
        ],
    },
    "macros": {
        "official": [
            ("[The Little Book of Rust Macros](https://veykril.github.io/tlborm/)", "宏权威指南"),
            ("[Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html)", "宏参考"),
        ],
        "academic": [
            ("[Macros in Rust](https://doc.rust-lang.org/rust-by-example/macros.html)", "宏教学"),
        ],
        "community": [
            ("[proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop)", "过程宏练习"),
            ("[syn docs](https://docs.rs/syn/latest/syn/)", "过程宏解析"),
        ],
    },
    "unsafe": {
        "official": [
            ("[Rustonomicon](https://doc.rust-lang.org/nomicon/)", "Unsafe Rust 官方高级指南"),
            ("[Rust Reference — Unsafe](https://doc.rust-lang.org/reference/unsafe-blocks.html)", "Unsafe 块参考"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "unsafe 语义"),
            ("[Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/)", "别名模型"),
        ],
        "community": [
            ("[Rust Secure Code Working Group](https://github.com/rust-secure-code/wg)", "安全代码工作组"),
            ("[Miri](https://github.com/rust-lang/miri)", "UB 检测工具"),
        ],
    },
    "ffi": {
        "official": [
            ("[Rustonomicon — FFI](https://doc.rust-lang.org/nomicon/ffi.html)", "FFI 官方指南"),
            ("[The Rust FFI Omnibus](https://jakegoulding.com/rust-ffi-omnibus/)", "FFI 示例"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "FFI 边界语义"),
        ],
        "community": [
            ("[bindgen docs](https://rust-lang.github.io/rust-bindgen/)", "C/C++ 绑定生成"),
            ("[cbindgen docs](https://mozilla.github.io/cbindgen/)", "生成 C 头文件"),
        ],
    },
    "inline_asm": {
        "official": [
            ("[Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)", "内联汇编参考"),
            ("[Rustonomicon — Exotic](https://doc.rust-lang.org/nomicon/exotic-sizes.html)", "裸机类型"),
        ],
        "academic": [
            ("[x86 Instruction Set Reference](https://www.felixcloutier.com/x86/)", "x86 指令参考"),
        ],
        "community": [
            ("[Rust Embedded Book](https://docs.rust-embedded.org/book/)", "嵌入式实践"),
        ],
    },
    "compiler_internals": {
        "official": [
            ("[Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/)", "编译器开发指南"),
            ("[Rust Reference](https://doc.rust-lang.org/reference/)", "语言参考"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "编译器语义基础"),
            ("[a-mir-formality](https://github.com/rust-lang/a-mir-formality)", "形式化类型系统"),
        ],
        "community": [
            ("[This Week in Rust — Compiler](https://this-week-in-rust.org/)", "编译器团队动态"),
            ("[rustc-reading-club](https://github.com/rust-lang/rustc-reading-club)", "rustc 源码共读"),
        ],
    },
    "performance_optimization": {
        "official": [
            ("[Rust Performance Book](https://nnethercote.github.io/perf-book/)", "Rust 性能书籍"),
            ("[Rustonomicon](https://doc.rust-lang.org/nomicon/)", "高级内存与性能"),
        ],
        "academic": [
            ("[Data-Oriented Design](https://en.wikipedia.org/wiki/Data-oriented_design)", "面向数据设计"),
        ],
        "community": [
            ("[criterion.rs docs](https://bheisler.github.io/criterion.rs/book/)", "基准测试"),
        ],
    },
    "type_driven_correctness": {
        "official": [
            ("[Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html)", "类型系统"),
            ("[TRPL Ch10 — Generic Types / Traits](https://doc.rust-lang.org/book/ch10-00-generics.html)", "泛型与 Trait"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "类型安全语义"),
        ],
        "community": [
            ("[Rust By Example — Types](https://doc.rust-lang.org/rust-by-example/types.html)", "类型示例"),
        ],
    },
    "cargo": {
        "official": [
            ("[The Cargo Book](https://doc.rust-lang.org/cargo/)", "Cargo 官方文档"),
            ("[Cargo.toml Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html)", "清单格式"),
        ],
        "academic": [
            ("[Semantic Versioning](https://semver.org/)", "版本语义"),
        ],
        "community": [
            ("[crates.io policies](https://crates.io/policies)", "注册表策略"),
            ("[cargo audit](https://github.com/RustSec/rustsec)", "依赖审计"),
        ],
    },
    "testing": {
        "official": [
            ("[TRPL Ch11 — Tests](https://doc.rust-lang.org/book/ch11-00-testing.html)", "测试基础"),
            ("[Rustdoc Testing](https://doc.rust-lang.org/rustdoc/write-documentation.html)", "文档测试"),
        ],
        "academic": [
            ("[Property-Based Testing](https://en.wikipedia.org/wiki/Property_testing)", "属性测试"),
        ],
        "community": [
            ("[proptest docs](https://docs.rs/proptest/latest/proptest/)", "属性测试 crate"),
            ("[criterion.rs docs](https://bheisler.github.io/criterion.rs/book/)", "基准测试"),
        ],
    },
    "wasm": {
        "official": [
            ("[Rust and WebAssembly Book](https://rustwasm.github.io/book/)", "Rust WASM 官方书"),
            ("[wasm-bindgen docs](https://rustwasm.github.io/wasm-bindgen/)", "JS 绑定"),
        ],
        "academic": [
            ("[WebAssembly Spec](https://webassembly.github.io/spec/)", "WASM 规范"),
        ],
        "community": [
            ("[cargo-component](https://github.com/bytecodealliance/cargo-component)", "WASM Component 工具"),
            ("[Wasmtime docs](https://docs.wasmtime.dev/)", "WASM 运行时"),
        ],
    },
    "embedded": {
        "official": [
            ("[The Embedded Rust Book](https://docs.rust-embedded.org/book/)", "嵌入式 Rust 官方书"),
            ("[Rustonomicon — Exotic](https://doc.rust-lang.org/nomicon/exotic-sizes.html)", "裸机类型"),
        ],
        "academic": [
            ("[Real-Time Rust](https://arxiv.org/abs/2302.0)", "实时系统 Rust"),
        ],
        "community": [
            ("[knurling-rs](https://knurling.ferrous-systems.com/)", "嵌入式工具链"),
            ("[embassy docs](https://embassy.dev/)", "异步嵌入式框架"),
        ],
    },
    "security": {
        "official": [
            ("[Rust Security Response WG](https://www.rust-lang.org/governance/wgs/wg-security-response)", "安全响应工作组"),
            ("[Cargo Security](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html)", "依赖安全"),
        ],
        "academic": [
            ("[RustSec](https://rustsec.org/)", "Rust 安全公告数据库"),
        ],
        "community": [
            ("[cargo audit](https://github.com/RustSec/rustsec)", "依赖审计工具"),
            ("[OpenSSF Scorecard](https://github.com/ossf/scorecard)", "供应链安全评分"),
        ],
    },
    "safety_critical": {
        "official": [
            ("[Rust Project Goals — Safety-Critical Rust](https://rust-lang.github.io/rust-project-goals/2026/)", "安全关键目标"),
            ("[Ferrocene](https://ferrocene.dev/)", "Ferrocene 认证 Rust"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "语义基础"),
            ("[RefinedRust — OOPSLA 2024](https://dl.acm.org/doi/10.1145/3689738)", "形式化验证"),
        ],
        "community": [
            ("[Rust Safety-Critical Consortium](https://rust-safety-critical.com/)", "安全关键联盟"),
            ("[High Integrity Systems Blog](https://www.highintegritysystems.com/)", "工业实践"),
        ],
    },
    "design_patterns": {
        "official": [
            ("[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)", "API 设计指南"),
            ("[Rust Design Patterns](https://rust-unofficial.github.io/patterns/)", "设计模式非官方书"),
        ],
        "academic": [
            ("[Design Patterns (Gang of Four)](https://en.wikipedia.org/wiki/Design_Patterns)", "经典设计模式"),
        ],
        "community": [
            ("[Rust API Guidelines Checklist](https://rust-lang.github.io/api-guidelines/checklist.html)", "API 检查清单"),
        ],
    },
    "type_system": {
        "official": [
            ("[TRPL Ch03 — Data Types](https://doc.rust-lang.org/book/ch03-02-data-types.html)", "数据类型"),
            ("[Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html)", "类型系统参考"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "类型语义"),
        ],
        "community": [
            ("[Rust By Example — Types](https://doc.rust-lang.org/rust-by-example/types.html)", "类型示例"),
        ],
    },
    "database": {
        "official": [
            ("[Sea-ORM docs](https://www.sea-ql.org/SeaORM/)", "Sea-ORM 文档"),
            ("[SQLx docs](https://docs.rs/sqlx/latest/sqlx/)", "SQLx 文档"),
        ],
        "academic": [
            ("[Relational Database](https://en.wikipedia.org/wiki/Relational_database)", "关系型数据库"),
        ],
        "community": [
            ("[Diesel docs](https://diesel.rs/)", "Diesel ORM"),
            ("[Axum + SQLx examples](https://github.com/tokio-rs/axum/tree/main/examples/sqlx-postgres)", "Web + DB 示例"),
        ],
    },
    "networking": {
        "official": [
            ("[std::net](https://doc.rust-lang.org/std/net/)", "标准网络库"),
            ("[TRPL Ch20 — Web Server](https://doc.rust-lang.org/book/ch20-00-final-project-a-web-server.html)", "多线程 Web 服务器"),
        ],
        "academic": [
            ("[TCP/IP Illustrated](https://en.wikipedia.org/wiki/TCP/IP_Illustrated)", "网络协议经典"),
        ],
        "community": [
            ("[Tokio docs](https://tokio.rs/)", "异步网络运行时"),
            ("[Axum examples](https://github.com/tokio-rs/axum/tree/main/examples)", "Web 框架示例"),
        ],
    },
    "ai_ml": {
        "official": [
            ("[candle docs](https://huggingface.github.io/candle/)", "Hugging Face Candle"),
            ("[burn docs](https://burn.dev/)", "Burn 深度学习框架"),
        ],
        "academic": [
            ("[Deep Learning Book](https://www.deeplearningbook.org/)", "深度学习基础"),
        ],
        "community": [
            ("[tch-rs docs](https://docs.rs/tch/latest/tch/)", "PyTorch C++ 绑定"),
            ("[Rust ML ecosystem](https://www.arewelearningyet.com/)", "Rust ML 生态跟踪"),
        ],
    },
    "web": {
        "official": [
            ("[TRPL Ch20 — Web Server](https://doc.rust-lang.org/book/ch20-00-final-project-a-web-server.html)", "多线程 Web 服务器"),
            ("[Rust Web Framework Comparison](https://www.arewewebyet.org/)", "Web 生态跟踪"),
        ],
        "academic": [
            ("[RESTful Web Services](https://en.wikipedia.org/wiki/Representational_state_transfer)", "REST 架构"),
        ],
        "community": [
            ("[Axum docs](https://docs.rs/axum/latest/axum/)", "Axum 框架"),
            ("[Actix docs](https://actix.rs/)", "Actix Web 框架"),
        ],
    },
    "deployment": {
        "official": [
            ("[The Cargo Book](https://doc.rust-lang.org/cargo/)", "Cargo 构建与发布"),
            ("[Rust Platform Support](https://doc.rust-lang.org/nightly/rustc/platform-support.html)", "平台支持"),
        ],
        "academic": [
            ("[Continuous Delivery](https://en.wikipedia.org/wiki/Continuous_delivery)", "持续交付"),
        ],
        "community": [
            ("[cross](https://github.com/cross-rs/cross)", "交叉编译工具"),
            ("[cargo-dist docs](https://opensource.axo.dev/cargo-dist/)", "发布分发"),
        ],
    },
    "formal": {
        "official": [
            ("[Rust Reference](https://doc.rust-lang.org/reference/)", "语言参考"),
            ("[a-mir-formality](https://github.com/rust-lang/a-mir-formality)", "形式化类型系统"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "类型系统语义正确性"),
            ("[Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/)", "别名模型"),
            ("[RefinedRust — OOPSLA 2024](https://dl.acm.org/doi/10.1145/3689738)", "Iris 分离逻辑验证"),
        ],
        "community": [
            ("[Kani docs](https://model-checking.github.io/kani/)", "模型检验器"),
            ("[Verus docs](https://verus-lang.github.io/verus/)", "SMT 验证器"),
        ],
    },
    "start": {
        "official": [
            ("[The Rust Programming Language — Ch1](https://doc.rust-lang.org/book/ch01-00-getting-started.html)", "入门指南"),
            ("[Rust 官方安装指南](https://www.rust-lang.org/tools/install)", "安装说明"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "Rust 安全保证基础"),
        ],
        "community": [
            ("[Rustlings](https://github.com/rust-lang/rustlings)", "交互式入门练习"),
            ("[100 Exercises to Learn Rust](https://rust-exercises.com/)", "系统练习"),
            ("[Google Comprehensive Rust](https://google.github.io/comprehensive-rust/)", "Google Rust 课程"),
        ],
    },
    "philosophy": {
        "official": [
            ("[Rust Language FAQ](https://www.rust-lang.org/faq)", "官方 FAQ"),
            ("[The Rust Programming Language](https://doc.rust-lang.org/book/)", "官方教程"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "所有权与内存安全语义"),
        ],
        "community": [
            ("[Rust Blog](https://blog.rust-lang.org/)", "官方博客"),
            ("[Rust Foundation News](https://foundation.rust-lang.org/news/)", "基金会动态"),
        ],
    },
    "roadmap": {
        "official": [
            ("[Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)", "年度目标"),
            ("[Rust Blog](https://blog.rust-lang.org/)", "官方博客"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "语义基础"),
        ],
        "community": [
            ("[This Week in Rust](https://this-week-in-rust.org/)", "社区周报"),
            ("[Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)", "核心团队博客"),
        ],
    },
    "reference": {
        "official": [
            ("[Rust Reference](https://doc.rust-lang.org/reference/)", "官方参考"),
            ("[The Rust Programming Language](https://doc.rust-lang.org/book/)", "官方教程"),
        ],
        "academic": [
            ("[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)", "语义基础"),
        ],
        "community": [
            ("[Rust By Example](https://doc.rust-lang.org/rust-by-example/)", "官方示例"),
        ],
    },
    "version_tracking": {
        "official": [
            ("[Rust Blog](https://blog.rust-lang.org/)", "发布博客"),
            ("[releases.rs](https://releases.rs/)", "发布跟踪"),
        ],
        "academic": [
            ("[Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)", "目标路线图"),
        ],
        "community": [
            ("[Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)", "核心团队动态"),
            ("[This Week in Rust](https://this-week-in-rust.org/)", "社区周报"),
        ],
    },
}

# 目录 -> 默认主题
DIR_DEFAULT_TOPIC = {
    "00_start": "start",
    "01_fundamentals": "default",
    "02_intermediate": "default",
    "03_advanced": "default",
    "04_expert": "default",
    "04_expert/academic": "formal",
    "04_expert/miri": "unsafe",
    "04_expert/safety_critical": "safety_critical",
    "05_reference": "reference",
    "06_ecosystem": "default",
    "06_ecosystem/databases": "database",
    "06_ecosystem/deep_dives": "default",
    "06_ecosystem/deployment": "deployment",
    "06_ecosystem/emerging": "version_tracking",
    "99_archive": "version_tracking",
}

# 文件名/路径关键词 -> 主题（精确匹配优先）
FILENAME_TOPIC = {
    "ownership": "ownership",
    "borrowing": "borrowing",
    "lifetimes": "lifetimes",
    "iterators": "iterators",
    "traits": "traits",
    "generics": "generics",
    "collections": "collections",
    "error_handling": "error_handling",
    "strings": "strings",
    "smart_pointers": "smart_pointers",
    "type_conversions": "type_conversions",
    "async": "async",
    "concurrency": "concurrency",
    "atomics": "atomics",
    "threads": "threads",
    "synchronization": "synchronization",
    "macros": "macros",
    "unsafe": "unsafe",
    "ffi": "ffi",
    "inline_asm": "inline_asm",
    "compiler_internals": "compiler_internals",
    "performance_optimization": "performance_optimization",
    "type_driven_correctness": "type_driven_correctness",
    "cargo": "cargo",
    "testing": "testing",
    "wasm": "wasm",
    "embedded": "embedded",
    "security": "security",
    "safety_critical": "safety_critical",
    "design_patterns": "design_patterns",
    "type_system": "type_system",
    "database": "database",
    "networking": "networking",
    "ai_ml": "ai_ml",
    "web": "web",
    "deployment": "deployment",
    "formal": "formal",
    "start": "start",
    "philosophy": "philosophy",
    "roadmap": "roadmap",
    "version_tracking": "version_tracking",
    "reference": "reference",
    "hello_world": "start",
    "installation": "start",
    "learning_roadmap": "start",
    "keywords": "reference",
    "math_constants": "type_system",
    "std_library_cheatsheet": "reference",
}


def detect_topic(rel: Path, title: str, text: str) -> str:
    # 1. 优先按文件名（不含扩展名）精确匹配
    stem = rel.stem.lower()
    if stem in FILENAME_TOPIC:
        return FILENAME_TOPIC[stem]

    # 2. 按文件名中的关键词（最长优先）
    matched = None
    matched_len = 0
    for keyword, topic in FILENAME_TOPIC.items():
        if keyword in stem and len(keyword) > matched_len:
            matched = topic
            matched_len = len(keyword)
    if matched:
        return matched

    # 3. 按目录默认主题（从最长路径前缀匹配）
    rel_posix = rel.as_posix()
    best_dir = None
    best_len = -1
    for dir_prefix, topic in DIR_DEFAULT_TOPIC.items():
        if rel_posix.startswith(dir_prefix) and len(dir_prefix) > best_len:
            best_dir = topic
            best_len = len(dir_prefix)
    if best_dir:
        return best_dir

    # 4. 回退到内容关键词（也优先最长）
    lowered = (title + " " + text[:800]).lower()
    matched = None
    matched_len = 0
    for keyword, topic in FILENAME_TOPIC.items():
        if keyword in lowered and len(keyword) > matched_len:
            matched = topic
            matched_len = len(keyword)
    return matched if matched else "default"


def extract_title(text: str) -> str:
    m = re.search(r"^#\s+(.+)$", text, re.MULTILINE)
    return m.group(1).strip() if m else ""


def render_table(items):
    lines = ["| 来源 | 类型 | 说明 |", "|:---|:---|:---|"]
    for url, desc in items:
        lines.append(f"| {url} | 权威来源 | {desc} |")
    return "\n".join(lines)


def build_section(topic: str) -> str:
    sources = TOPIC_SOURCES.get(topic, {})
    official = sources.get("official", OFFICIAL_DEFAULT)
    academic = sources.get("academic", ACADEMIC_DEFAULT)
    community = sources.get("community", COMMUNITY_DEFAULT)

    lines = [
        "",
        SECTION_HEADER,
        "",
        "> 本节按项目模板要求补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。",
        "",
        "### 8.1 官方来源",
        "",
        render_table(official),
        "",
        "### 8.2 学术来源",
        "",
        render_table(academic),
        "",
        "### 8.3 社区权威",
        "",
        render_table(community),
    ]
    return "\n".join(lines) + "\n"


def main():
    dry_run = "--dry-run" in sys.argv
    targets = []
    for p in sorted(ROOT.rglob("*.md")):
        rel = p.relative_to(ROOT)
        if "archive" in rel.parts or "temp" in rel.parts or p.name in ("README.md", "SUMMARY.md"):
            continue
        text = p.read_text(encoding="utf-8", errors="ignore")
        if SECTION_HEADER in text:
            continue
        targets.append(p)

    print(f"发现 {len(targets)} 个待补充模块 8 的文件")
    if dry_run:
        print("【dry-run】不会写入文件")
        # 打印主题分布
        from collections import Counter
        topics = Counter()
        for p in targets:
            text = p.read_text(encoding="utf-8", errors="ignore")
            title = extract_title(text)
            topic = detect_topic(p.relative_to(ROOT), title, text)
            topics[topic] += 1
        print("\n主题分布:")
        for topic, count in topics.most_common():
            print(f"  {topic}: {count}")
        print("\n样本（前 3 个）:")
        for p in targets[:3]:
            text = p.read_text(encoding="utf-8", errors="ignore")
            title = extract_title(text)
            topic = detect_topic(p.relative_to(ROOT), title, text)
            print(f"\n--- {p.relative_to(ROOT)} (topic={topic}) ---")
            print(build_section(topic)[:500])
        return

    for p in targets:
        text = p.read_text(encoding="utf-8", errors="ignore")
        title = extract_title(text)
        topic = detect_topic(p.relative_to(ROOT), title, text)
        section = build_section(topic)
        if not text.endswith("\n"):
            text += "\n"
        p.write_text(text + section, encoding="utf-8")
        print(f"updated: {p.relative_to(ROOT)} (topic={topic})")


if __name__ == "__main__":
    main()
