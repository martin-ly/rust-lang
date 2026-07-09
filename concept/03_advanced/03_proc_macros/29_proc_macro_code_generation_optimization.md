> **内容分级**: [专家级]
>

# 过程宏代码生成优化
>
> **EN**: Procedural Macro Code Generation Optimization
> **Summary**: Optimizing procedural macro output in Rust: readable and debug-friendly token generation, compile-time overhead reduction, monomorphization bloat control, const folding, and measurement with cargo-llvm-lines / cargo-bloat.
>
> **受众**: [专家]
> **层级**: L3 高级概念
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: P×Eva — 评估与优化生成代码质量
> **前置概念**: [过程宏](07_proc_macro.md) · [元编程](../../02_intermediate/06_macros_and_metaprogramming/21_metaprogramming.md) · [泛型](../../02_intermediate/01_generics/02_generics.md)
> **后置概念**: [生产级宏开发](31_production_grade_macro_development.md) · [宏调试与诊断](30_macro_debugging_and_diagnostics.md)
>
> **主要来源**: [The Rust Reference](https://doc.rust-lang.org/reference/procedural-macros.html) · [The Rust Performance Book](https://nnethercote.github.io/perf-book/) · [syn crate](https://docs.rs/syn/) · [quote crate](https://docs.rs/quote/) · [proc-macro2 crate](https://docs.rs/proc-macro2/)
>
> **Rust 版本**: 1.96.1+ (Edition 2024)

---

> **来源**: 本文档由 `crates/*/docs/` 合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：
> **权威来源**: [concept/03_advanced/03_proc_macros/29_proc_macro_code_generation_optimization.md](29_proc_macro_code_generation_optimization.md)

---

## 一、核心定位

过程宏在编译期生成代码，其质量直接影响：

- **编译时间**：递归展开、单态化膨胀、依赖链长度。
- **二进制大小**：重复生成的泛型实现、未消除的死代码。
- **运行时性能**：生成的代码是否可被 LLVM 内联、向量化、常量折叠。
- **可调试性**：错误定位精度、可读性、文档完整性。

本章讨论如何在宏实现阶段控制这些因素。

---

## 二、生成代码质量

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

```rust
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

> **关键洞察**: `quote_spanned!` 让生成的代码错误指向用户输入的字段，而不是宏定义位置，是提升宏用户体验的核心手段。

---

## 三、编译时间优化

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

### 4.1 静态 vs 动态分发

| 特性 | 静态分发 `impl Trait` | 动态分发 `dyn Trait` |
|:---|:---|:---|
| 性能 | 更快（可内联） | 稍慢（vtable 查找） |
| 二进制大小 | 更大（单态化） | 更小（共享代码） |
| 灵活性 | 编译期确定 | 运行时确定 |
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

### 5.3 cargo-bloat

```bash
cargo install cargo-bloat
cargo bloat --release
```

### 5.4 Criterion 基准测试

```rust
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
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-07-09
**状态**: ✅ 权威来源对齐完成
