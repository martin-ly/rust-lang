> **内容分级**: [专家级]
>

# 过程宏代码生成优化
>
> **EN**: Procedural Macro Code Generation Optimization
> **Summary**: Optimizing procedural macro output in Rust: readable and debug-friendly token generation, compile-time overhead reduction, monomorphization bloat control, const folding, and measurement with cargo-llvm-lines / cargo-bloat.
>
> **受众**: [专家]
> **层级**: L3 高级概念
> **Bloom 层级**: L3-L5
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: P×Eva — 评估与优化生成代码质量
> **前置概念**: [过程宏（Procedural Macro）](02_proc_macro.md) · [元编程](../../02_intermediate/06_macros_and_metaprogramming/04_metaprogramming.md) · [泛型（Generics）](../../02_intermediate/01_generics/01_generics.md)
> **后置概念**: [生产级宏（Macro）开发](05_production_grade_macro_development.md) · [宏调试与诊断](04_macro_debugging_and_diagnostics.md)
>
> **主要来源**:
> [The Rust Reference](https://doc.rust-lang.org/reference/procedural-macros.html) ·
> [The Rust Performance Book](https://nnethercote.github.io/perf-book/) ·
> [syn crate](https://docs.rs/syn/) ·
> [quote crate](https://docs.rs/quote/) ·
> [proc-macro2 crate](https://docs.rs/proc-macro2/)
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` 权威页。

---

> **来源**: 本文档由 `crates/*/docs/` 合规整改迁移而来。原始 crate 文档现为摘要页，指向本权威页：
> **权威来源**: [concept/03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md](03_proc_macro_code_generation_optimization.md)

---

## 一、核心定位

过程宏（Procedural Macro）在编译期生成代码，其质量直接影响：

- **编译时间**：递归展开、单态化（Monomorphization）膨胀、依赖链长度。
- **二进制大小**：重复生成的泛型（Generics）实现、未消除的死代码。
- **运行时（Runtime）性能**：生成的代码是否可被 LLVM 内联、向量化、常量折叠。
- **可调试性**：错误定位精度、可读性、文档完整性。

本章讨论如何在宏（Macro）实现阶段控制这些因素。

---

## 二、生成代码质量

过程宏的产出是「用户看不见但要编译的代码」，质量三要素：

- **可读性（2.1）**：生成的代码应能通过 `cargo expand` 阅读——标识符用 `format_ident!` 生成有意义的名字（`_myderive_field_0` 优于 `_0`），控制结构直接而非过度嵌套；
- **文档注释（2.2）**：生成的公开项应带 `#[doc = ...]`——`quote! { #[doc = #doc_str] ... }` 把文档注入生成代码，docs.rs 上用户才能理解生成 API；
- **Span 保留（2.3）**：生成代码中引用用户输入的部分（类型名、字段名）应保留原 token 的 span（`quote_spanned!` 或直接插值原 token）——错误信息指向用户代码而非宏内部，这是诊断质量的决定性因素。

质量基准：宏的使用者永远不应该是「看展开才能用」——但出问题时，展开结果必须是可读的。

### 2.1 可读性与文档

```rust
// ❌ 难以阅读
macro_rules! bad_gen {
    ($name:ident) => {
        struct $name{x:i32,y:i32}impl $name{fn new(x:i32,y:i32)->Self{Self{x,y}}}
    };
}

// ✅ 格式化良好
macro_rules! good_gen {
    ($name:ident) => {
        struct $name {
            x: i32,
            y: i32,
        }

        impl $name {
            fn new(x: i32, y: i32) -> Self {
                Self { x, y }
            }
        }
    };
}
```

### 2.2 文档注释

```rust
macro_rules! generate_with_docs {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        struct $name { value: i32 }

        impl $name {
            #[doc = concat!("Creates a new instance of `", stringify!($name), "`")]
            pub fn new(value: i32) -> Self { Self { value } }
        }
    };
}
```

### 2.3 保留 Span 信息

```rust,ignore
use proc_macro2::Span;
use quote::quote_spanned;

fn generate_getter(field: &syn::Field) -> proc_macro2::TokenStream {
    let name = &field.ident;
    let ty = &field.ty;
    let span = field.span();
    quote_spanned! {span=>
        pub fn #name(&self) -> &#ty { &self.#name }
    }
}
```

> **关键洞察**: `quote_spanned!` 让生成的代码错误指向用户输入的字段，而不是宏定义位置，是提升宏用户体验的核心手段 (Source: [quote docs](https://docs.rs/quote/latest/quote/))。

---

## 三、编译时间优化

本节聚焦「编译时间优化」，覆盖避免宏递归爆炸、限制递归深度、减少单态化开销与共享非泛型实现。论述顺序由定义到边界：先明确「编译时间优化」在「过程宏代码生成优化」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。读完后应能用一句话复述「编译时间优化」的判定标准，并指出它在全页论证链中的位置。

### 3.1 避免宏递归爆炸

```rust
// ❌ 递归展开，编译慢
macro_rules! bad_repeat {
    (0, $body:expr) => {};
    ($n:expr, $body:expr) => { $body; bad_repeat!($n - 1, $body); };
}

// ✅ 生成运行时循环
macro_rules! good_repeat {
    ($n:expr, $body:expr) => {
        for _ in 0..$n { $body; }
    };
}
```

### 3.2 限制递归深度

```rust
macro_rules! limited_recursion {
    (@depth 0, $($rest:tt)*) => {
        compile_error!("recursion depth limit exceeded");
    };
    (@depth $d:expr, [$head:expr, $($tail:expr),*]) => {
        $head;
        limited_recursion!(@depth $d - 1, [$($tail),*]);
    };
    (@depth $d:expr, []) => {};
    ([$($items:expr),*]) => {
        limited_recursion!(@depth 100, [$($items),*]);
    };
}
```

### 3.3 减少单态化开销

```rust
// ❌ 过多泛型参数
struct Bad<A, B, C, D, E> { a: A, b: B, c: C, d: D, e: E }

// ✅ 使用关联类型聚合配置
trait Config { type A; type B; type C; type D; type E; }
struct Good<C: Config> { a: C::A, b: C::B, c: C::C, d: C::D, e: C::E }
```

### 3.4 共享非泛型实现

```rust
fn common_logic() { /* 大量共享代码 */ }

macro_rules! generate_impl {
    ($t:ty) => {
        impl MyTrait for $t {
            fn process(&self) { common_logic(); }
        }
    };
}
```

---

## 四、代码膨胀控制

宏生成代码的膨胀控制四个手段：

- **静态 vs 动态分发（4.1）**：为每个类型生成完整实现（derive 的默认）vs 生成「薄壳 + 共享运行时代码」（如 `erased-serde` 模式）——类型数多时后者体积优势显著；
- **条件编译隔离（4.2）**：生成的代码用 `#[cfg(feature = ...)]` 包裹可选部分——serde 的 `derive` feature 即此模式，不用 derive 的用户零成本；
- **常量折叠（4.3）**：生成代码中的常量表达式（如字段数、数组长度）直接写字面量而非表达式——减少编译期求值与代码体积；
- **共享非泛型实现**：生成 `impl Trait for EachType { fn f(&self) { shared_impl(self) } }`——把逻辑体放在单一非泛型函数，每个类型的生成代码只是转发层。

判定准则：先用 `cargo-llvm-lines` 找到膨胀最大的宏展开，再按上述手段逐项优化——不要预防性优化。

### 4.1 静态 vs 动态分发

| 特性 | 静态分发 `impl Trait` | 动态分发 `dyn Trait` |
|:---|:---|:---|
| 性能 | 更快（可内联） | 稍慢（vtable 查找） |
| 二进制大小 | 更大（单态化） | 更小（共享代码） |
| 灵活性 | 编译期确定 | 运行时（Runtime）确定 |
| 适用场景 | 性能关键路径 | 插件系统、抽象接口 |

### 4.2 条件编译隔离

```rust
#[cfg(feature = "simd")]
fn optimized() { /* SIMD 实现 */ }

#[cfg(not(feature = "simd"))]
fn optimized() { /* 标量实现 */ }
```

### 4.3 常量折叠

```rust
const fn factorial(n: u32) -> u32 {
    match n { 0 | 1 => 1, _ => n * factorial(n - 1) }
}

const FACT_10: u32 = factorial(10);
```

---

## 五、性能测量

宏对编译性能的影响必须测量而非推测，四个工具链：

- **`cargo build --timings`（5.1）**：HTML 报告展示每个 crate 的编译时间与并行度——过程宏 crate 在关键路径上（依赖它的 crate 必须等它编译完）；
- **`cargo-llvm-lines`（5.2）**：统计每个函数/泛型实例贡献的 LLVM IR 行数——定位「哪个宏展开生成了最多代码」的第一工具；
- **`cargo-bloat`（5.3）**：二进制体积按 crate/函数分解——宏生成的代码膨胀在最终产物中的占比；
- **Criterion 基准（5.4）**：宏展开后的运行期性能（生成的序列化代码 vs 手写）——验证「零成本」承诺的唯一方式。

测量纪律：宏改动的 PR 应附 timings 前后对比（编译时间）与 llvm-lines 对比（生成量）——宏的性能回归静默且影响所有下游用户。

### 5.1 cargo build --timings

```bash
cargo build --release --timings
# 查看 target/cargo-timings/cargo-timing.html
```

### 5.2 cargo-llvm-lines

```bash
cargo install cargo-llvm-lines
cargo llvm-lines | head -20
```

(Source: [cargo-llvm-lines](https://github.com/dtolnay/cargo-llvm-lines))

### 5.3 cargo-bloat

```bash
cargo install cargo-bloat
cargo bloat --release
```

(Source: [cargo-bloat](https://github.com/RazrFalcon/cargo-bloat))

### 5.4 Criterion 基准测试

```rust,ignore
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_generated(c: &mut Criterion) {
    c.bench_function("generated", |b| {
        b.iter(|| my_generated_function(black_box(42)))
    });
}

criterion_group!(benches, bench_generated);
criterion_main!(benches);
```

---

## 六、实战：优化序列化宏

```rust
// ❌ 每次字段都分配
macro_rules! serialize_bad {
    ($s:ident { $($field:ident),* }) => {
        impl Serialize for $s {
            fn serialize(&self) -> String {
                let mut r = String::new();
                $(r.push_str(&format!("{}: {}, ", stringify!($field), self.$field));)*
                r
            }
        }
    };
}

// ✅ 预计算容量，单次分配
macro_rules! serialize_good {
    ($s:ident { $($field:ident),* }) => {
        impl Serialize for $s {
            fn serialize(&self) -> String {
                let capacity = 0 $(+ stringify!($field).len() + 10)*;
                let mut r = String::with_capacity(capacity);
                $({
                    use std::fmt::Write;
                    let _ = write!(&mut r, "{}: {}, ", stringify!($field), self.$field);
                })*
                r
            }
        }
    };
}
```

---

## 七、优化检查清单

- [ ] 生成的代码已格式化并具有文档注释
- [ ] 关键路径使用 `#[inline]` 提示
- [ ] 避免不必要的堆分配
- [ ] 用迭代替代递归宏展开
- [ ] 提取共享的非泛型实现
- [ ] 用 `cargo llvm-lines` 检查单态化膨胀
- [ ] 用 `cargo bloat` 检查二进制大小
- [ ] 保留原始 Span 以改善错误定位

---

> **权威来源**: [Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html) · [The Rust Performance Book](https://nnethercote.github.io/perf-book/) · [syn/quote/proc-macro2 docs](https://docs.rs/)
>
> **权威来源对齐变更日志**: 2026-07-09 由 `crates/c11_macro_system_proc/docs/tier_04_advanced/03_code_generation_optimization.md` 按 AGENTS.md §6.4 迁移至此

**文档版本**: 1.0
**最后更新**: 2026-07-09
**状态**: ✅ 权威来源对齐完成

## 认知路径

1. **问题识别**: 识别过程宏生成代码对编译时间与二进制体积的潜在影响。
2. **概念建立**: 掌握可读、可调试 token 生成与 monomorphization 膨胀控制技术。
3. **机制推理**: 通过 token 质量 ⟹ 编译期开销 ⟹ 二进制体积的定理链进行优化决策。
4. **边界辨析**: 辨析“生成代码越多越好”等反命题，理解度量驱动优化的必要性。
5. **迁移应用**: 将宏代码生成优化与调试、生产级开发主题链接。

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 精简生成 token ⟹ 缩短编译时间 | 避免冗余展开与重复实现 | 宏使用场景的编译耗时下降 |
| 保留原始 span ⟹ 提升诊断精度 | `quote_spanned!` 与 `Span::call_site` 合理选用 | 用户收到的错误信息定位更准确 |
| 编译期常量折叠 ⟹ 减少运行时开销 | 在宏展开阶段完成可静态求值的计算 | 生成的运行时代码更高效 |

## 反命题

> **反命题 1**: "过程宏生成的代码越多越好" ⟹ 不成立。冗余生成会增加编译负担与二进制体积。
>
> **反命题 2**: "所有生成代码都会 monomorphize" ⟹ 不成立。通过泛型约束与宏生成策略可以减少单态化膨胀。
>
> **反命题 3**: "优化宏输出不需要测量" ⟹ 不成立。应使用 cargo-llvm-lines、cargo-bloat 等工具量化后再优化。
>
## 反向推理

> **反向推理 1**: 观察到大量使用 derive 后编译时间激增 ⟸ 说明需要审计生成代码量与 monomorphization 情况。
>
> **反向推理 2**: 发现 release 二进制异常庞大 ⟸ 说明应检查宏生成的重复实现与未折叠常量。
>
## 过渡段

> **过渡**: 从 token 生成质量过渡到编译期开销，可以理解“写得好”的宏不仅是功能正确，还要控制展开规模。
>
> **过渡**: 从编译期开销过渡到 monomorphization 膨胀，可以建立宏优化与泛型设计之间的联系。
>
> **过渡**: 从膨胀分析过渡到测量工具，可以形成数据驱动的宏性能优化闭环。
>

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Kohlbecker et al.: Hygienic Macro Expansion (LFP 1986, 卫生宏奠基)](https://dl.acm.org/doi/10.1145/319838.319859)
