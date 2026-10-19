# Rust 语言规范预研：从参考文档到形式化规范

**EN**: Rust Specification Preview
**Summary**: Redirect stub for the Rust specification preview feature; the canonical concept now lives in the language specification ecosystem overview.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **状态**: 🧪 Nightly 实验性 / 2026 预览特性跟踪

> **权威来源**: 本文件已转为重定向 stub。完整概念解释与规范生态映射请见：
> [`concept/04_formal/15_language_specification/00_language_specification_overview.md`](../../04_formal/15_language_specification/00_language_specification_overview.md)
> 上游规范工作权威入口：[rust-lang/rust-spec](https://github.com/rust-lang/rust-spec) 与 [Rust Reference](https://doc.rust-lang.org/reference/)。

## ⚠️ 实测反例：本页为索引页，完整实测见 canonical

完整口径见 canonical：[00_language_specification_overview.md](../../04_formal/15_language_specification/00_language_specification_overview.md)（含 compile_fail 围栏）。

口径摘要（rustc 1.99.1 实编译，2026-10-19）——「形式化规范要定义的 UB」在 Rust 的实际落地形态：同一越界读，const 语境编译期硬拒、运行语境静默 UB，这条分界线正是规范化（spec）要精确刻画的对象：

```rust,compile_fail
const A: [i32; 2] = [1, 2];
const B: i32 = A[5]; // const 求值器按规范判 UB: 编译期拒绝
fn main() { println!("{B}"); }
```

```text
error[E0080]: index out of bounds: the length is 2 but the index is 5
  | evaluation of `B` failed here
```

对照：同一 `A[5]` 放进 `unsafe { A.get_unchecked(5) }` 运行语境则编译通过、产物读越界垃圾（三层对比实测见 [04_formal/03_operational_semantics/07_aeneas_symbolic_semantics.md 实测反节](../../04_formal/03_operational_semantics/07_aeneas_symbolic_semantics.md)）。规范预研的价值即在于把「哪些行为属于 E0080 类编译期可判、哪些属于 Miri 类工具判、哪些连 Miri 都只能警告」写成可机检文本——本机双跑给出这条边界的硬/软两个锚点。

