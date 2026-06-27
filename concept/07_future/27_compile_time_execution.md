# 编译期执行与常量求值

> **代码状态**: ✅ 含可编译示例
>
> **EN**: Compile Time Execution
> **Summary**: Compile Time Execution: emerging Rust language feature or ecosystem trend.
>
> **受众**: [专家]
> **内容分级**: [综述级]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S+P** — StructureProcedure
> **双维定位**: C×Eva — 评估编译期执行的能力边界
> **定位**: 深入探讨 Rust 的**编译期执行**能力——从 `const fn` 到 `const` 泛型（Generics），分析 Rust 如何在编译期完成计算，实现零成本抽象（Zero-Cost Abstraction）。
> **前置概念**: [Generics](../02_intermediate/02_generics.md) · [Type System](../01_foundation/04_type_system.md) · [Trait](../02_intermediate/01_traits.md)
> **后置概念**: [Macros](../03_advanced/04_macros.md) · [Zero Cost Abstractions](../01_foundation/06_zero_cost_abstractions.md)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
---

> **来源**: [Reference — Constant Evaluation](https://doc.rust-lang.org/reference/const_eval.html) · [TRPL — Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
> [Rust Reference — Const Eval](https://doc.rust-lang.org/reference/const_eval.html) ·
> [RFC 2000 — Const Generics](https://rust-lang.github.io/rfcs//2000-const-generics.html) ·
> [Wikipedia — Compile Time](https://en.wikipedia.org/wiki/Compile_time) ·
> [Rust Blog — Const Evaluation](https://blog.rust-lang.org/)
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md)

## 📑 目录

- [编译期执行与常量求值](#编译期执行与常量求值)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 const fn](#11-const-fn)
    - [1.2 const 上下文](#12-const-上下文)
    - [1.3 const 泛型](#13-const-泛型)
  - [二、编译期能力边界](#二编译期能力边界)
    - [2.1 稳定的编译期操作](#21-稳定的编译期操作)
    - [2.2 不稳定特性](#22-不稳定特性)
  - [三、应用模式](#三应用模式)
    - [3.1 编译期计算](#31-编译期计算)
    - [3.2 类型状态机](#32-类型状态机)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)
  - [权威来源索引](#权威来源索引)
  - [十、边界测试：编译期执行的编译错误](#十边界测试编译期执行的编译错误)
    - [10.1 边界测试：`const fn` 的受限操作（编译错误）](#101-边界测试const-fn-的受限操作编译错误)
    - [10.2 边界测试：过程宏的 TokenStream 解析错误（编译错误）](#102-边界测试过程宏的-tokenstream-解析错误编译错误)
    - [10.3 边界测试：`const fn` 中的浮点数限制（编译错误）](#103-边界测试const-fn-中的浮点数限制编译错误)
    - [10.4 边界测试：编译期堆分配的 `const Heap` 展望（编译错误）](#104-边界测试编译期堆分配的-const-heap-展望编译错误)
    - [10.3 边界测试：`const fn` 中的浮点运算精度与确定性（编译错误/运行时差异）](#103-边界测试const-fn-中的浮点运算精度与确定性编译错误运行时差异)
    - [补充定理链](#补充定理链)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：Rust 的常量求值（const evaluation）目前已支持到什么程度？（理解层）](#测验-1rust-的常量求值const-evaluation目前已支持到什么程度理解层)
    - [测验 2：`const fn` 与 C++ 的 `constexpr` 有什么相似之处？（理解层）](#测验-2const-fn-与-c-的-constexpr-有什么相似之处理解层)
    - [测验 3：为什么 Rust 对 `const fn` 的能力限制比 C++ `constexpr` 更严格？（理解层）](#测验-3为什么-rust-对-const-fn-的能力限制比-c-constexpr-更严格理解层)
    - [测验 4：编译期执行对嵌入式开发有什么特别价值？（理解层）](#测验-4编译期执行对嵌入式开发有什么特别价值理解层)
    - [测验 5：Rust 编译期执行的未来方向是什么？（理解层）](#测验-5rust-编译期执行的未来方向是什么理解层)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)

---

## 一、核心概念

### 1.1 const fn

```text
const fn:

  定义: 可在编译期执行的函数
  ├── 返回值可在常量上下文中使用
  ├── 内部限制: 无堆分配、无 mutable static
  ├── 稳定版限制逐步放宽
  └── 目标是"如果能在编译期运行，就能在 const fn 中写"

  代码示例:

  const fn factorial(n: u64) -> u64 {
      let mut result = 1;
      let mut i = 1;
      while i <= n {
          result *= i;
          i += 1;
      }
      result
  }

  const FIVE_FACTORIAL: u64 = factorial(5); // 120

  演进:
  ├── Rust 1.31: 基础 const fn
  ├── Rust 1.46: loop, if, match
  ├── Rust 1.64: let mut, 赋值
  └── 持续扩展中...
```

> **认知功能**: **const fn 是 Rust 编译期编程的核心**——将运行时（Runtime）代码直接提升到编译期执行。
> [来源: [Rust Reference — Const Functions](https://doc.rust-lang.org/reference/items/functions.html#const-functions)]

---

### 1.2 const 上下文

```text
const 上下文:

  定义: 编译期求值的代码位置
  ├── const 声明: const X: T = expr;
  ├── static 声明: static X: T = expr;
  ├── 数组长度: [T; N]
  ├── enum 变体: enum E { V = expr }
  ├── const 泛型参数: Foo<N>
  └── const fn 内部

  代码示例:

  const fn compute_size() -> usize {
      1024 * 1024
  }

  const BUFFER_SIZE: usize = compute_size();
  let buffer = [0u8; BUFFER_SIZE]; // 编译期确定大小

  关键限制:
  ├── 无堆分配
  ├── 无 trait 对象
  ├── 无浮点数比较（不稳定）
  ├── 无 panic（需 const_panic）
  └── 无副作用
```

> **上下文洞察**: **const 上下文是 Rust 编译期的"沙盒"**——安全但有界，逐步扩大能力范围。
> [来源: [Rust Reference — Const Context](https://doc.rust-lang.org/reference/const_eval.html)]

---

### 1.3 const 泛型

```text
Const Generics:

  定义: 以常量值作为泛型参数
  ├── 类型参数: <T>
  ├── 生命周期参数: <'a>
  └── 常量参数: <const N: usize>

  代码示例:

  struct Matrix<T, const ROWS: usize, const COLS: usize> {
      data: [[T; COLS]; ROWS],
  }

  impl<T, const N: usize> Matrix<T, N, N> {
      fn identity() -> Self
      where
          T: Copy + From<u8>,
      {
          let mut data = [[T::from(0); N]; N];
          let mut i = 0;
          while i < N {
              data[i][i] = T::from(1);
              i += 1;
          }
          Self { data }
      }
  }

  let m = Matrix::<i32, 3, 3>::identity();

  优势:
  ├── 编译期已知大小
  ├── 栈分配（无堆分配开销）
  ├── 类型安全（3x3 ≠ 4x4）
  └── 零运行时开销
```

> **泛型洞察**: **Const Generics 是 Rust 类型系统（Type System）的里程碑**——数组大小进入类型系统，实现真正的编译期类型安全。
> [来源: [RFC 2000](https://rust-lang.github.io/rfcs//2000-const-generics.html)]

---

## 二、编译期能力边界

### 2.1 稳定的编译期操作

```text
稳定编译期能力 (Rust 1.96+):

  控制流:
  ├── if / else
  ├── match
  ├── while
  ├── loop
  ├── break / continue
  └── return

  变量:
  ├── let / let mut
  ├── 赋值
  ├── 复合赋值 (+=, -= 等)
  └── 递增/递减

  类型:
  ├── 结构体构造
  ├── 数组构造
  ├── 元组
  ├── 枚举
  └── 指针操作（原始指针）

  函数:
  ├── const fn 调用
  ├── 递归（有限深度）
  ├── 泛型函数
  └── trait 方法（有限支持）
```

> **能力洞察**: **Rust 的编译期能力持续增长**——目标是 Turing-complete 的编译期计算。
> [来源: [Rust Reference — Const Eval](https://doc.rust-lang.org/reference/const_eval.html)]

---

### 2.2 不稳定特性

```text
不稳定编译期特性:

  const_mut_refs:
  ├── const fn 中使用 &mut
  ├── 编译期可变状态
  └── 复杂算法的关键

  const_trait_impl:
  ├── const fn 中调用 trait 方法
  ├── ~const 限定
  └── 泛型编译期计算

  const_for:
  ├── for 循环
  └── IntoIterator 支持

  const_panic:
  ├── 编译期 panic
  ├── const 断言
  └── 编译期错误报告

  inline_const:
  ├── const { expr } 块
  └── 任意位置的编译期计算
```

> **不稳定洞察**: **不稳定特性代表了 Rust 编译期的未来方向**——const trait impl 是最关键的缺失能力。
> [来源: [Rust Unstable Book](https://doc.rust-lang.org/unstable-book/index.html)]

---

## 三、应用模式

### 3.1 编译期计算
>

```text
编译期计算模式:

  查找表:
  const fn lookup(n: usize) -> u32 {
      match n {
          0 => 1,
          1 => 1,
          2 => 2,
          3 => 6,
          4 => 24,
          _ => 0,
      }
  }
  const TABLE: [u32; 5] = [
      lookup(0), lookup(1), lookup(2), lookup(3), lookup(4)
  ];

  编译期配置:
  const fn is_64bit() -> bool {
      usize::BITS == 64
  }

  const MAX_INDEX: usize = if is_64bit() { 1usize << 32 } else { 1usize << 16 };

  类型级计算:
  struct ConstU32<const N: u32>;

  trait Add<const A: u32, const B: u32> {
      const RESULT: u32;
  }

  impl<const A: u32, const B: u32> Add<A, B> for () {
      const RESULT: u32 = A + B;
  }
```

> **计算洞察**: **编译期计算将运行时开销转移到编译期**——牺牲编译时间换取运行时性能。
> [来源: [Rust Const Evaluation](https://doc.rust-lang.org/reference/const_eval.html)]

---

### 3.2 类型状态机
>

```text
类型状态机:

  设计: 编译期跟踪状态转换
  ├── 未初始化 → 初始化
  ├── 打开 → 关闭
  ├── 空闲 → 运行中
  └── 编译期验证状态转换

  代码示例:

  struct File<const OPEN: bool> {
      handle: RawFd,
  }

  impl File<false> {
      fn open(path: &str) -> File<true> {
          // ...
          File { handle }
      }
  }

  impl File<true> {
      fn read(&self, buf: &mut [u8]) -> usize {
          // ...
      }

      fn close(self) -> File<false> {
          // ...
          File { handle: -1 }
      }
  }

  // 编译期验证:
  let f = File::open("file.txt");
  f.read(&mut buf);
  let f = f.close();
  // f.read(&mut buf); // 编译错误！File<false> 无 read 方法
```

> **状态机洞察**: **类型状态机是 Rust 零成本类型安全的极致**——编译期保证正确的状态转换序列。
> [来源: [Type State Pattern](https://rust-unofficial.github.io/patterns/)]

---

## 四、反命题与边界分析

### 4.1 反命题树
>

```mermaid
graph TD
    ROOT["命题: 所有计算都应移到编译期"]
    ROOT --> Q1{"计算结果是否依赖运行时输入?"}
    Q1 -->|是| RUNTIME["✅ 运行时计算必需"]
    Q1 -->|否| Q2{"编译时间是否可接受?"}
    Q2 -->|是| COMPILE["✅ 编译期计算有益"]
    Q2 -->|否| RUNTIME

    style RUNTIME fill:#c8e6c9
    style COMPILE fill:#c8e6c9
```

> **认知功能**: **编译期计算只适用于静态已知的数据**——运行时输入必须用运行时计算。
> [来源: [Rust Performance Book](https://nnethercote.github.io/perf-book/)]

---

### 4.2 边界极限

```text
边界 1: 编译时间
├── 复杂编译期计算增加编译时间
├── 递归深度限制
└── 缓解: 缓存、简化算法

边界 2: 表达能力
├── 当前 const fn 非 Turing-complete
├── 缺少某些控制结构
└── 缓解: 使用宏、build.rs

边界 3: 错误报告
├── 编译期 panic 信息可能不清晰
├── 复杂 const 错误难以调试
└── 缓解: 简化表达式、增量测试

边界 4: 生态兼容性
├── 第三方 crate 可能不支持 const
├── trait 方法调用受限
└── 缓解: 选择支持 const 的 crate

边界 5: 平台差异
├── 编译期结果可能因平台而异
├── usize::BITS 等平台相关值
└── 缓解: 条件编译 #[cfg]
```

> **边界要点**: 编译期执行的边界与**编译时间**、**表达能力**、**错误报告**、**生态兼容性**和**平台差异**相关。

---

## 五、常见陷阱

```text
陷阱 1: const 与 let 混淆
  ❌ 在 const fn 中使用 let 以为会自动是 const
     fn foo() { let x = 5; } // x 是运行时变量

  ✅ const fn 返回 const
     const fn foo() -> i32 { 5 } // 编译期值

陷阱 2: 递归过深
  ❌ 无限递归 const fn
     const fn bad(n: usize) -> usize { bad(n) + 1 }

  ✅ 确保递归有终止条件
     const fn good(n: usize) -> usize {
         if n == 0 { 1 } else { n * good(n - 1) }
     }

陷阱 3: 忽略 const 限制
  ❌ 在 const fn 中使用 Vec
     const fn bad() -> Vec<i32> { vec![1, 2, 3] }

  ✅ 使用数组
     const fn good() -> [i32; 3] { [1, 2, 3] }

陷阱 4: 浮点数比较
  ❌ const fn 中使用 == 比较浮点数（不稳定）
     const fn bad(x: f64) -> bool { x == 0.0 }

  ✅ 使用整数或稳定后使用
     const fn good(x: i64) -> bool { x == 0 }

陷阱 5: 过度使用 const 泛型
  ❌ 为每个可能值创建不同类型
     type M1 = Matrix<f32, 1, 1>;
     type M2 = Matrix<f32, 2, 2>;
     // ... 爆炸性增长

  ✅ 使用动态大小
     type DynMatrix = Matrix<f32, Dynamic, Dynamic>;
```

> **陷阱总结**: 编译期执行的陷阱主要与**const/let 混淆**、**递归**、**限制忽略**、**浮点数**和**泛型（Generics）过度**相关。

---

## 六、来源与延伸阅读

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rust Reference — Const Eval](https://doc.rust-lang.org/reference/const_eval.html) | ✅ 一级 | 官方参考 |
| [RFC 2000](https://rust-lang.github.io/rfcs//2000-const-generics.html) | ✅ 一级 | Const Generics |
| [Rust Blog — Const](https://blog.rust-lang.org/) | ✅ 一级 | 官方博客 |
| [Rust Performance Book](https://nnethercote.github.io/perf-book/) | ✅ 二级 | 性能优化 |
| [Type State Pattern](https://rust-unofficial.github.io/patterns/) | ✅ 二级 | 类型状态 |

---

```rust
fn main() {
    let feature = "preview";
    println!("{}", feature);
}
```

## 相关概念文件

- [Generics](../02_intermediate/02_generics.md) — 泛型
- [Trait](../02_intermediate/01_traits.md) — Trait
- [Macros](../03_advanced/04_macros.md) — 宏（Macro）
- [Zero Cost Abstractions](../01_foundation/06_zero_cost_abstractions.md) — 零成本抽象（Zero-Cost Abstraction）

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 11]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成

---

## 权威来源索引

>
>
>
>
>

---

---

---

> **补充来源**

## 十、边界测试：编译期执行的编译错误

### 10.1 边界测试：`const fn` 的受限操作（编译错误）

```rust,compile_fail
const fn allocate() -> Vec<i32> {
    // ❌ 编译错误: const fn 中不能堆分配
    vec![1, 2, 3]
}

fn main() {
    let v = allocate();
    println!("{:?}", v);
}
```

> **修正**:
> `const fn` 在编译期执行，因此不能使用运行时才可用的功能：堆分配（`Box::new`、`Vec::new`）、I/O、随机数、线程、panic（Rust 1.57+ 允许 `const panic`）。
> `vec![]` 宏（Macro）在底层调用 `Vec::new()` 和堆分配，因此不能在 `const fn` 中使用。
> 编译期计算应使用栈分配类型（数组 `[T; N]`、`const` 值）或 `const` 泛型。
> Rust 的 `const fn` 能力在持续扩展：1.46 允许 `if`/`match`，1.57 允许 `panic`，1.64 允许 `dyn Trait`，未来可能允许有限堆分配（`const Heap` RFC）。
> 这与 C++ 的 `constexpr`（C++20 允许堆分配和虚函数）相比，Rust 更保守——优先保证编译期执行的确定性和可预测性。
> [来源: [Rust Reference — Const Evaluation](https://doc.rust-lang.org/reference/const_eval.html)] ·
> [来源: [Rust RFC 2344](https://rust-lang.github.io/rfcs//2344-const-looping.html)]

### 10.2 边界测试：过程宏的 TokenStream 解析错误（编译错误）

```rust,compile_fail
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    // ❌ 编译错误: 若输入不是合法 struct/enum，syn 解析失败
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    // 若尝试为 union 生成 derive，可能产生不支持的代码
    let expanded = quote! {
        impl Default for #name {
            fn default() -> Self {
                // union 不能有自动 Default
                panic!("not supported")
            }
        }
    };
    expanded.into()
}
```

> **修正**:
> 过程宏（procedural macros）在编译期操作 TokenStream，将 Rust 代码作为数据变换。
> `syn` crate 将 TokenStream 解析为 AST（`DeriveInput`、`ItemFn` 等），解析失败时产生编译错误。
> 过程宏（Procedural Macro）的调试困难：错误信息指向宏生成的代码，而非宏定义本身。
> Rust 1.64+ 的 `Span::error` 和 `proc_macro::Diagnostic` 改善了错误报告。
> 过程宏（Macro）的编译期执行能力强大但风险高：无限循环的宏导致编译器挂起，`quote!` 生成的代码可能有类型错误（在宏调用点报告）。
> 这与 C 的宏预处理器（纯文本替换，无类型检查）或 Lisp 的宏（同像性，编译期执行）不同——Rust 的过程宏在编译期运行完整 Rust 代码，但输出仍需通过类型检查。
> [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch19-06-macros.html)] ·
> [来源: [syn Documentation](https://docs.rs/syn/)]

### 10.3 边界测试：`const fn` 中的浮点数限制（编译错误）

```rust,ignore
const fn compute_area(r: f64) -> f64 {
    // ❌ 编译错误: const fn 中浮点数操作受限
    // 旧版 Rust 禁止浮点数运算，新版允许但仍有约束
    std::f64::consts::PI * r * r
}

fn main() {
    const AREA: f64 = compute_area(2.0);
    println!("{}", AREA);
}
```

> **修正**:
> `const fn` 中的浮点数支持是渐进添加的：
>
> 1) 旧版 Rust 完全禁止 `const fn` 中的浮点运算（因 LLVM 的浮点常数折叠非确定性）；
> 2) Rust 1.83+ 允许基本浮点运算，但 `std::f64::consts::PI` 等常数一直可用；
> 3) 浮点数的 `==` 比较在 `const fn` 中受限（因 NaN 的语义）。
>
> 挑战：浮点数的编译期求值需要与运行期完全一致，但编译器和目标平台的浮点单元可能行为不同（如 FMA 可用性）。
> `rustc` 使用 LLVM 的 APFloat 库进行编译期浮点模拟，确保一致性（Coherence）。
> 这与 C++ 的 `constexpr`（C++23 允许浮点，同样需一致性（Coherence）保证）或 Zig 的 `comptime`（浮点完全支持，因 Zig 自托管编译器控制求值）不同——Rust 的 `const fn` 保守但逐步扩展。
> [来源: [Rust Reference — Const Evaluation](https://doc.rust-lang.org/reference/const_eval.html)] ·
> [来源: [Rust Const Eval Working Group](https://rust-lang.github.io/const-eval/)]

### 10.4 边界测试：编译期堆分配的 `const Heap` 展望（编译错误）

```rust,compile_fail
const fn build_map() -> std::collections::HashMap<i32, i32> {
    // ❌ 编译错误: const fn 不能堆分配
    // let mut map = std::collections::HashMap::new();
    // map.insert(1, 2);
    // map
    std::collections::HashMap::new()
}
```

> **修正**:
> `const fn` 当前禁止堆分配（`Box::new`、`Vec::new`、`HashMap::new`），因为编译期的内存管理复杂：
>
> 1) 分配的内存在编译后如何释放？
> 2) 若 `const` 值嵌入二进制，堆分配的数据需序列化为静态数据；
> 3) 循环引用（Reference）的 `const` 值如何表示？`const Heap` RFC 提议允许编译期堆分配，但将分配的数据"冻结"为静态只读数据（类似 `let s = const { String::from("hello") }` 在编译期创建 `String`，运行期作为 `&'static str` 使用）。
> 这与 C++ 的 `constexpr` new（C++20，允许编译期分配，但对象需在编译期销毁）或 Zig 的 `comptime` 分配器（编译期分配，结果序列化到二进制）类似——Rust 的 `const Heap` 是语言演进的重要方向，使编译期元编程能力接近 Zig 和 C++20。
> [来源: [Rust Const Heap RFC](https://github.com/rust-lang/rfcs/)] ·
> [来源: [Rust Internals Forum](https://internals.rust-lang.org/)]

### 10.3 边界测试：`const fn` 中的浮点运算精度与确定性（编译错误/运行时差异）

```rust,ignore
const fn compute_area(radius: f64) -> f64 {
    // ❌ 编译错误: const fn 中某些数学函数不可用
    // std::f64::consts::PI 可用，但 sin/cos/sqrt 不是 const fn
    radius * radius * std::f64::consts::PI
}

fn main() {
    const AREA: f64 = compute_area(1.0);
    println!("{}", AREA);
}
```

> **修正**:
> `const fn` 的浮点运算：
>
> 1) 四则运算和常量（`PI`、`E`）可用；
> 2) `sin`、`cos`、`sqrt`、`pow` 等非 `const fn`（需运行时计算或查表）；
> 3) 浮点运算在编译期和运行期的结果**可能不同**（编译期使用软件实现，运行期使用 FPU，舍入模式可能不同）。
>
> 确定性要求：安全关键系统需确保编译期和运行期浮点结果一致。
> 未来方向：
>
> 1) `const fn` 扩展更多数学函数；
> 2) 编译期浮点模拟与运行期硬件行为统一；
> 3) `fixed-point` 算术替代（嵌入式常见）。
> 这与 C++ 的 `constexpr`（C++23 支持 `std::sqrt` 等）或 Ada 的浮点模型（严格定义舍入行为）不同——Rust 的 const 浮点运算保守但逐步扩展。
> [来源: [Rust Reference — const fn](https://doc.rust-lang.org/reference/items/functions.html#const-functions)] ·
> [来源: [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754)]
> **过渡**: 编译期执行与常量求值 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。

### 补充定理链

- **定理**: 编译期执行与常量求值 定义 ⟹ 类型安全保证

## 嵌入式测验（Embedded Quiz）

### 测验 1：Rust 的常量求值（const evaluation）目前已支持到什么程度？（理解层）

**题目**: Rust 的常量求值（const evaluation）目前已支持到什么程度？

<details>
<summary>✅ 答案与解析</summary>

`const fn` 支持基本运算、控制流、部分标准库调用。`const_mut_refs` 和 `const_heap` 逐步放宽了historical限制。
</details>

---

### 测验 2：`const fn` 与 C++ 的 `constexpr` 有什么相似之处？（理解层）

**题目**: `const fn` 与 C++ 的 `constexpr` 有什么相似之处？

<details>
<summary>✅ 答案与解析</summary>

两者都允许在编译期执行函数，用于常量初始化、数组大小计算、查找表生成等。减少运行时开销和启动时间。
</details>

---

### 测验 3：为什么 Rust 对 `const fn` 的能力限制比 C++ `constexpr` 更严格？（理解层）

**题目**: 为什么 Rust 对 `const fn` 的能力限制比 C++ `constexpr` 更严格？

<details>
<summary>✅ 答案与解析</summary>

Rust 更保守以确保声音性。C++ `constexpr` 已扩展为几乎完整的 C++ 子集，但带来了复杂的编译期语义和实现负担。
</details>

---

### 测验 4：编译期执行对嵌入式开发有什么特别价值？（理解层）

**题目**: 编译期执行对嵌入式开发有什么特别价值？

<details>
<summary>✅ 答案与解析</summary>

可以在编译期计算查找表、配置结构、校验和，减少运行时代码量和初始化时间。对资源受限设备尤为重要。
</details>

---

### 测验 5：Rust 编译期执行的未来方向是什么？（理解层）

**题目**: Rust 编译期执行的未来方向是什么？

<details>
<summary>✅ 答案与解析</summary>

逐步支持更多标准库功能（`Vec`、`String` 在 const 上下文）、用户自定义类型的 const 构造函数、更强大的 const 泛型计算。
</details>

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **编译期执行与常量求值** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| 编译期执行与常量求值 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| 编译期执行与常量求值 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| 编译期执行与常量求值 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 编译期执行与常量求值 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 编译期执行与常量求值 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: 编译期执行与常量求值 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "编译期执行与常量求值 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。
