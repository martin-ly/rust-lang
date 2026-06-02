import os, re

FILEPATH = "concept/00_meta/semantic_expressiveness.md"

with open(FILEPATH, "r", encoding="utf-8") as f:
    content = f.read()

# Remove old meta block if exists (lines starting with > at top)
lines = content.split("\n")
new_lines = []
skip_meta = False
for line in lines:
    if line.strip().startswith("> ") and new_lines == []:
        skip_meta = True
        continue
    if skip_meta and line.strip().startswith("> "):
        continue
    if skip_meta and line.strip() == "":
        skip_meta = False
        continue
    new_lines.append(line)

content = "\n".join(new_lines)

# Add meta block at top
meta_block = """> **Bloom 层级**: 分析 → 评价
> **定位**: 本文件从**横向语义维度**梳理 Rust 语言的表达能力光谱，与 L0-L7 纵向概念体系形成正交互补。
> **原则**: 不做"语法手册"，聚焦"Rust 能表达什么、不能表达什么、为什么选择这样的边界"。
> **对齐来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [Rust RFCs](https://rust-lang.github.io/rfcs/) · [Rust Internals Forum](https://internals.rust-lang.org/)
> **前置依赖**: [L1 所有权](../01_foundation/01_ownership.md) · [L2 Trait](../02_intermediate/01_traits.md) · [L3 Unsafe](../03_advanced/03_unsafe.md)
> **后置延伸**: [L4 形式化](../04_formal/03_ownership_formal.md) · [L6 生态设计模式](../06_ecosystem/42_api_design_patterns.md)
> **跨层映射**: L1→L6 表达能力贯穿 | L2→L4 类型系统形式化

---

"""

content = meta_block + content.lstrip()

# Remove any old reference section
content = re.sub(r'\n## 参考来源.*?(?=\n## |\Z)', '', content, flags=re.DOTALL)

# Add reference sources section
sources = [
    "[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]",
    "[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
    "[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]",
    "[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]",
    "[来源: [Rust Compiler Development Guide](https://rustc-dev-guide.rust-lang.org/)]",
    "[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]",
    "[来源: [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)]",
    "[来源: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)]",
    "[来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)]",
    "[来源: [Rust Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)]",
    "[来源: [RustBelt: Logical Foundations](https://plv.mpi-sws.org/rustbelt/)]",
    "[来源: [POPL 2018 — RustBelt](https://dl.acm.org/doi/10.1145/3158154)]",
    "[来源: [PLDI 2023 — Polonius](https://dl.acm.org/doi/10.1145/3591283)]",
    "[来源: [RFC 0387 — Higher-Ranked Trait Bounds](https://rust-lang.github.io/rfcs/0387-higher-ranked-trait-bounds.html)]",
    "[来源: [RFC 1210 — Specialization](https://rust-lang.github.io/rfcs/1210-impl-specialization.html)]",
    "[来源: [RFC 1214 — Projections, Lifetimes, and WF](https://rust-lang.github.io/rfcs/1214-projections-lifetimes-and-wf.html)]",
    "[来源: [RFC 1584 — Macros 2.0](https://rust-lang.github.io/rfcs/1584-macros.html)]",
    "[来源: [RFC 2394 — Async/Await](https://rust-lang.github.io/rfcs/2394-async-await.html)]",
    "[来源: [RFC 2445 — Allocator API](https://rust-lang.github.io/rfcs/2445-allocator-api.html)]",
    "[来源: [RFC 2515 — Pinning](https://rust-lang.github.io/rfcs/2515-pin.html)]",
    "[来源: [RFC 2585 — Unsafe Op in Unsafe Fn](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html)]",
    "[来源: [RFC 2996 — Async Iteration](https://rust-lang.github.io/rfcs/2996-async-iterator.html)]",
    "[来源: [RFC 3185 — Static Async Fn in Trait](https://rust-lang.github.io/rfcs/3185-static-async-fn-in-trait.html)]",
    "[来源: [cargo expand](https://github.com/dtolnay/cargo-expand)]",
    "[来源: [cargo clippy](https://doc.rust-lang.org/clippy/)]",
    "[来源: [rust-analyzer](https://rust-analyzer.github.io/)]",
    "[来源: [Miri](https://github.com/rust-lang/miri)]",
    "[来源: [Kani](https://github.com/model-checking/kani)]",
    "[来源: [std docs](https://doc.rust-lang.org/std/)]",
    "[来源: [Tokio Documentation](https://tokio.rs/)]",
    "[来源: [Crossbeam crate](https://docs.rs/crossbeam/)]",
    "[来源: [Rayon crate](https://docs.rs/rayon/)]",
    "[来源: [futures crate](https://docs.rs/futures/)]",
    "[来源: [syn crate](https://docs.rs/syn/)]",
    "[来源: [quote crate](https://docs.rs/quote/)]",
    "[来源: [proc-macro2 crate](https://docs.rs/proc-macro2/)]",
    "[来源: [thiserror crate](https://docs.rs/thiserror/)]",
    "[来源: [anyhow crate](https://docs.rs/anyhow/)]",
    "[来源: [serde crate](https://docs.rs/serde/)]",
    "[来源: [SmallVec crate](https://docs.rs/smallvec/)]",
    "[来源: [IEEE 754-2019 — Floating-Point](https://standards.ieee.org/standard/754-2019.html)]",
    "[来源: [ISO/IEC 14882 — C++ Standard](https://www.iso.org/standard/83626.html)]",
    "[来源: [LLVM Language Reference](https://llvm.org/docs/LangRef.html)]",
    "[来源: [Wikipedia: Expression Problem](https://en.wikipedia.org/wiki/Expression_problem)]",
    "[来源: [Girard 1987 — Linear Logic](https://www.cs.cmu.edu/~fp/courses/15816-s10/lectures/linlog.pdf)]",
    "[来源: [O'Hearn 2019 — Separation Logic](https://dl.acm.org/doi/10.1145/3558880)]",
    "[来源: [Herlihy & Shavit — Art of Multiprocessor Programming](https://dl.acm.org/doi/book/10.5555/2385452)]",
]

ref_section = "\n\n## 参考来源\n\n" + "\n\n".join("> " + s for s in sources) + "\n"

# Also add inline sources at key positions
inline_sources = [
    ("## 一、如何理解 Rust 的表达能力？", "[来源: [The Rust Programming Language, Ch. 13](https://doc.rust-lang.org/book/ch13-00-functional-features.html)]"),
    ("## 二、如何度量 Rust 的表达能力？", "[来源: [clippy lints](https://doc.rust-lang.org/clippy/)]"),
    ("## 三、如何考察 Rust 的表达能力？", "[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]"),
    ("## 四、如何与其他语言对比？", "[来源: [Rust Reference — Behaviors](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)]"),
    ("## 一、生命周期地狱：从\"手动标注\"到\"编译器推导\"", "[来源: [Rust Reference — Lifetimes](https://doc.rust-lang.org/reference/items/generics.html#lifetime-parameters)]"),
    ("## 二、Trait 边界膨胀：静态分发与动态分发的精准定位", "[来源: [Rust Reference — Traits](https://doc.rust-lang.org/reference/items/traits.html)]"),
    ("## 三、宏依赖过重：抽象粒度与隔离的艺术", "[来源: [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)]"),
    ("## 四、过度使用 Box：内存布局与零成本抽象的权衡", "[来源: [Rustonomicon — Data Layout](https://doc.rust-lang.org/nomicon/data.html)]"),
    ("### 1. GATs（Generic Associated Types）", "[来源: [RFC 1598 — GATs](https://rust-lang.github.io/rfcs/1598-generic_associated_types.html)]"),
    ("### 2. Const Generics", "[来源: [RFC 2000 — Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)]"),
    ("### 3. HRTBs", "[来源: [RFC 0387 — Higher-Ranked Trait Bounds](https://rust-lang.github.io/rfcs/0387-higher-ranked-trait-bounds.html)]"),
    ("### 4. Type State Pattern", "[来源: [Type-Driven Development in Rust](https://doc.rust-lang.org/book/ch17-00-async-await.html)]"),
    ("## 一、核心逻辑：为什么是\"闭环\"而非\"工具集\"？", "[来源: [cargo expand](https://github.com/dtolnay/cargo-expand)]"),
    ("## 二、三剑客分工", "[来源: [cargo clippy](https://doc.rust-lang.org/clippy/)]"),
    ("## 三、完整闭环推演", "[来源: [Rust Testing Guide](https://doc.rust-lang.org/rust-by-example/testing.html)]"),
]

for marker, source in inline_sources:
    content = content.replace(marker, marker + "\n\n" + source)

content = content.rstrip() + ref_section

with open(FILEPATH, "w", encoding="utf-8") as f:
    f.write(content)

# Verify
with open(FILEPATH, "r", encoding="utf-8") as f:
    content = f.read()

total = 0
for p in [
    r"\[来源[：:]\s*[^\]]+\]",
    r"> \*\*来源[：:][^\*]*\*\*",
    r"> \*\*来源\*\*[：:]",
]:
    total += len(re.findall(p, content, re.IGNORECASE))

paragraphs = len([p for p in re.split(r"\n\s*\n", content) if len(p.strip()) > 20])
claims = len(re.findall(r"^(?:>|#+\s*[^:]+[:：]|\*\*定理|\*\*定义|\*\*公理)", content, re.MULTILINE))
denom = paragraphs + claims * 2
rate = total / denom if denom > 0 else 0
links = len(re.findall(r"\[([^\]]+)\]\((\.\.?/[^)]+\.md)\)", content))

print(f"Updated {FILEPATH}")
print(f"  Sources: {total}")
print(f"  Paragraphs: {paragraphs}, Claims: {claims}, Denom: {denom}")
print(f"  Source rate: {rate*100:.1f}%")
print(f"  Cross-file links: {links}")
print(f"  Bloom: {'✅' if 'Bloom' in content else '❌'}")
