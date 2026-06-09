import os

quizzes = {
    "concept/07_future/15_rpitit_preview.md": [
        ("RPITIT（Return Position Impl Trait In Traits）是什么？",
         "允许在 trait 定义中使用 `impl Trait` 作为返回类型。之前 `impl Trait` 只能在自由函数和 inherent impl 中使用，不能在 trait 方法中。"),
        ("RPITIT 与关联类型（Associated Type）有什么关系？",
         "RPITIT 是关联类型的语法糖。编译器将 `fn method() -> impl Trait` 自动转换为带有隐式关联类型的形式，简化了 trait 定义。"),
        ("这个特性对 `async fn` 在 trait 中的支持有什么帮助？",
         "`async fn` 在 trait 中的本质就是 RPITIT（返回 `impl Future`）。RPITIT 的稳定化是 `async fn` in trait 的基础。"),
        ("RPITIT 在 Rust 1.75 中已稳定，但在 1.96 中有什么后续改进？",
         "后续改进包括生命周期捕获规则的精确控制（`use<'a>` 语法），解决了返回类型隐式捕获过多生命周期的问题。"),
        ("RPITIT 对 API 设计有什么影响？",
         "简化了 trait 定义，减少了显式关联类型的样板代码。使 trait 方法可以像自由函数一样使用 `impl Trait`，提高了表达能力。"),
    ],
    "concept/07_future/16_type_alias_impl_trait_preview.md": [
        ("Type Alias Impl Trait（TAIT）是什么？",
         "允许在类型别名中使用 `impl Trait`，如 `type MyIter = impl Iterator<Item = i32>`。隐藏具体类型同时提供命名抽象。"),
        ("TAIT 与 `impl Trait` 在函数返回位置有什么区别？",
         "`impl Trait` 在函数返回位置是匿名的、局部的。TAIT 提供了命名，可在多个函数间共享同一隐藏类型，实现模块化抽象。"),
        ("TAIT 对递归类型和状态机有什么帮助？",
         "允许命名递归类型（如 `type TreeNode = impl Node`），简化自引用结构体和复杂状态机的类型签名。"),
        ("TAIT 目前的限制是什么？",
         "只能在模块级或关联类型中使用，不能用于局部变量。编译器需要确保所有使用位置的底层类型一致。"),
        ("这个特性预计何时完全稳定？",
         "部分功能已在 stable 中可用（关联类型位置）。完整的 TAIT 预计在 2026-2027 年间逐步稳定化。"),
    ],
    "concept/07_future/17_const_trait_preview.md": [
        ("`const trait` 与 `const fn` 有什么区别？",
         "`const fn` 是单个函数可在编译期执行。`const trait` 允许 trait 的方法在常量上下文中使用，使泛型常量代码成为可能。"),
        ("为什么 `Vec::new()`  historically 不是 `const fn`？",
         "因为 `Vec` 的分配需要堆内存，而常量上下文 historically 不支持分配。`const_mut_refs` 和 `const_heap` 功能逐步放宽限制。"),
        ("`~const Trait` 语法是什么意思？",
         "表示\"这个泛型参数可以是 const 或非 const 的 trait 实现\"。允许函数同时服务于 const 和运行时上下文。"),
        ("`const trait` 对嵌入式开发有什么意义？",
         "允许在编译期构造复杂数据结构（如查找表、配置结构），无需运行时初始化代码，减少二进制体积和启动时间。"),
        ("这个特性目前的实现状态如何？",
         "已在 nightly 中实验性提供，部分功能（如 `~const`）正在稳定化讨论中。是 Rust 常量求值能力扩展的重要一步。"),
    ],
    "concept/07_future/19_rust_edition_preview.md": [
        ("Rust Edition 2024 相比 2021 有哪些主要变化？",
         "`gen` 块、`if let` 临时生命周期延长、`unsafe_op_in_unsafe_fn` 默认启用、`lifetime_capture_rules` 改进、模式匹配 `|` 操作符等。"),
        ("Edition 迁移工具 `cargo fix --edition` 如何工作？",
         "自动分析代码并应用必要的语法更新，如添加 `unsafe` 块、调整生命周期标注。极大降低了 Edition 迁移的人工成本。"),
        ("为什么 Rust 可以同时支持多个 Edition？",
         "编译器根据 `edition = '...'` 配置选择解析规则。不同 Edition 的 crate 可以无缝互操作，生态逐步迁移。"),
        ("Edition 与 SemVer 有什么关系？",
         "Edition 变化不改变 crate 的 SemVer，因为不同 Edition 可以互操作。但如果 API 本身有 breaking change，仍需升级 major version。"),
        ("下一个 Edition（2027/2028）可能包含什么？",
         "可能包括：更完整的 effect 系统、稳定化的 `gen` 块、`async_drop`、`field projections`、`pin` 语法改进、更灵活的 `self` 类型等。"),
    ],
    "concept/07_future/22_gen_blocks_preview.md": [
        ("`gen` 块与 `async` 块有什么相似之处？",
         "两者都是惰性计算的语法糖，编译为状态机。`async` 返回 `Future`，`gen` 返回 `Iterator`（或更一般的 `Generator`）。"),
        ("`gen` 块中的 `yield` 与 Python/JavaScript 的 `yield` 有什么区别？",
         "语义相似：暂停执行并返回值给调用者。Rust 的 `yield` 编译为状态机转移，保证内存安全（无悬垂引用）。"),
        ("`gen` 块对 `Stream` 的实现有什么帮助？",
         "可以自然地表达异步流：`gen { yield fetch_page(1).await; }`，比手动实现 `Stream` trait 简洁得多。"),
        ("`gen` 块目前的状态是什么？",
         "已在 nightly 中可用（`feature(gen_blocks)`），预计在未来几个版本内稳定化。是 Rust 2024+ 的重要特性。"),
        ("`gen` 块与现有迭代器适配器（`map`、`filter`）有什么关系？",
         "`gen` 块提供了更灵活、更直观的迭代器定义方式，与适配器互补。复杂逻辑用 `gen` 块，简单转换用适配器链。"),
    ],
    "concept/07_future/25_aarch64_sve_sme_preview.md": [
        ("SVE（Scalable Vector Extension）和 SME（Scalable Matrix Extension）是什么？",
         "ARM 的下一代 SIMD 指令集，向量长度在运行时确定（128-2048 位），无需为不同向量大小编译多个版本。SME 扩展了矩阵运算支持。"),
        ("SVE/SME 与 x86 的 AVX-512 有什么区别？",
         "AVX-512 有固定宽度（512 位），需要编译多个版本。SVE 的向量长度可变，同一代码可在不同硬件上利用最优向量宽度。"),
        ("Rust 目前对 SVE/SME 的支持状态如何？",
         "通过 `std::simd`（portable SIMD）和 `std::arch::aarch64` 内联函数提供部分支持。完整的自动向量化支持仍在开发中。"),
        ("SVE/SME 对 Rust 的高性能计算（HPC）和 ML 推理有什么意义？",
         "ARM 服务器（AWS Graviton、Apple Silicon）正在普及。SVE/SME 支持使 Rust 可以在这些平台上达到接近 x86 的峰值性能。"),
        ("Rust 编译器如何利用 SVE 的可变向量长度？",
         "通过 `std::simd` 的抽象，编译器生成与向量长度无关的代码，由硬件决定实际执行宽度。这简化了跨平台 SIMD 编程。"),
    ],
    "concept/07_future/26_rust_in_space.md": [
        ("为什么航天领域对 Rust 感兴趣？",
         "航天软件需要极高的可靠性、确定性的资源使用和内存安全。Rust 的编译期保证减少了运行时的故障模式，适合卫星和探测器软件。"),
        ("Rust 在航天领域相比 Ada/SPARK 有什么优势？",
         "Rust 有更现代的生态（crates.io、cargo）、更活跃的社区和更好的 C 互操作。Ada/SPARK 在形式化验证方面更成熟，但工具链较老。"),
        ("欧洲航天局（ESA）对 Rust 有什么态度？",
         "ESA 正在评估 Rust 用于未来任务，关注其内存安全保证和 Ferrocene 认证路径。Rust 被视为 Ada 的潜在补充。"),
        ("`no_std` 在航天嵌入式系统中有什么用途？",
         "航天设备通常使用裸机或 RTOS，无完整操作系统。`no_std` 使 Rust 可以在这些环境中运行，结合 `alloc` 提供有限的堆分配。"),
        ("辐射硬化（Radiation Hardening）对 Rust 程序有什么特殊要求？",
         "辐射可能导致位翻转（bit flip）。需要使用 ECC 内存、三模冗余（TMR）和错误检测代码。Rust 的类型安全不能防止硬件级错误，但减少了软件漏洞。"),
    ],
    "concept/07_future/borrow_sanitizer.md": [
        ("BorrowSanitizer 与 Miri 在检测能力上有什么区别？",
         "Miri 是解释器，检测广泛的 UB（越界、未对齐、数据竞争）。BorrowSanitizer 是运行时 sanitizer，专注于借用规则违规，速度更快，适合 CI。"),
        ("BorrowSanitizer 基于什么 LLVM 基础设施？",
         "基于 LLVM 的 sanitizer 框架，编译时插入检查代码，运行时通过 shadow memory 追踪引用状态，检测悬垂引用和非法别名。"),
        ("为什么需要 BorrowSanitizer 而不是仅依赖编译器借用检查？",
         "借用检查器是静态分析，保守且可能拒绝合法代码。BorrowSanitizer 动态验证运行时实际行为，补充静态检查的不足。"),
        ("BorrowSanitizer 对 `unsafe` 代码审计有什么帮助？",
         "可在 CI 中自动化检测 `unsafe` 代码的借用违规，减少人工审计负担。特别适用于 FFI 边界和手动内存管理代码。"),
        ("这个工具预计何时可用？",
         "作为 Rust Project Goals 2026 的一部分正在开发中。预计 2026-2027 年在 nightly 中提供实验性支持。"),
    ],
}

def append_at_end(path, qa_list):
    header = "\n\n## 嵌入式测验（Embedded Quiz）\n\n"
    blocks = []
    for i, (q, a) in enumerate(qa_list, 1):
        block = (
            f"### 测验 {i}：{q}（理解层）\n\n"
            f"**题目**: {q}\n\n"
            f"<details>\n"
            f"<summary>✅ 答案与解析</summary>\n\n"
            f"{a}\n"
            f"</details>\n"
        )
        if i < len(qa_list):
            block += "\n---\n\n"
        else:
            block += "\n"
        blocks.append(block)
    new_section = header + "".join(blocks)
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
    content = content.rstrip() + new_section
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    print(f"Updated: {path}")

for path, qa in quizzes.items():
    append_at_end(path, qa)
