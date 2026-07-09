# 可派生 Trait（Derive Traits）

> **内容分级**: [参考级]
> **本节关键术语**: Derive · `Debug` · `PartialEq` · `Eq` · `PartialOrd` · `Ord` · `Clone` · `Copy` · `Hash` · `Default` — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Derivable Traits
> **Summary**: 标准库中可通过 `#[derive(...)]` 自动实现的 trait 参考：行为、默认实现语义、对字段类型的要求及典型使用场景。
> **受众**: [初学者] / [中级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification / Language semantics
> **双维定位**: S×Lang — 语言标准库约定
> **前置依赖**: [Traits](../../01_foundation/02_type_system/04_type_system.md) · [Structs and Enums](../../01_foundation/03_values_and_references/05_reference_semantics.md) · [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md)
> **后置概念**: [Advanced Traits](19_advanced_traits.md) · [Proc Macros](../../03_advanced/03_proc_macros/07_proc_macro.md)
> **定理链**: N/A — 参考级文档
> **主要来源**: [Rust Reference — Derive](https://doc.rust-lang.org/reference/attributes/derive.html) · [TRPL — Appendix C](https://doc.rust-lang.org/book/appendix-03-derivable-traits.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [System F](https://en.wikipedia.org/wiki/System_F) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [TRPL — Appendix C: Derivable Traits](https://doc.rust-lang.org/book/appendix-03-derivable-traits.html)

---

---

## 认知路径

> **认知路径**: 本节从 "可派生 Trait（Derive Traits）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 可派生 Trait（Derive Traits） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 可派生 Trait（Derive Traits） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与可派生 Trait（Derive Traits）的适用边界。
5. **迁移应用**: 将 可派生 Trait（Derive Traits） 与前置/后置概念链接，形成跨层知识网络。

---

> **过渡**: 从 可派生 Trait（Derive Traits） 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。
> **过渡**: 在建立 可派生 Trait（Derive Traits） 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。
> **过渡**: 最后，将 可派生 Trait（Derive Traits） 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: 可派生 Trait（Derive Traits） 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 可派生 Trait（Derive Traits） 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 可派生 Trait（Derive Traits） 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

---

## 反命题决策树

> **反命题 1**: "可派生 Trait（Derive Traits） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。
> **反命题 2**: "忽略 可派生 Trait（Derive Traits） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 可派生 Trait（Derive Traits） 规则被违反的直接信号。
> **反命题 3**: "其他语言对 可派生 Trait（Derive Traits） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 可派生 Trait（Derive Traits） 具有语言特有的形态。

---

> **反向推理 1**: 如果程序在 可派生 Trait（Derive Traits） 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 可派生 Trait（Derive Traits） 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 一、`#[derive]` 的作用

`#[derive(TraitName)]` 可以自动为 struct 或 enum 生成 trait 实现。编译器使用默认实现，其行为通常基于字段的逐字段/逐变体推导。(Source: [Rust Reference — Derive](https://doc.rust-lang.org/reference/attributes/derive.html))

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct User {
    id: u64,
    name: String,
}
```

> **注意**：如果默认行为不满足需求，需要手动实现。例如 `Display` 没有合理的默认用户可见格式，因此不能 derive。

---

## 二、标准库可派生 Trait 一览

### `Debug` — 调试输出

- 启用 `{:?}` 格式化。
- 用于 `assert_eq!` 等宏（Macro）在断言失败时打印值。
- 派生实现按字段顺序输出调试表示。

```rust
#[derive(Debug)]
struct Point { x: i32, y: i32 }

let p = Point { x: 1, y: 2 };
println!("{:?}", p); // Point { x: 1, y: 2 }
```

---

### `PartialEq` / `Eq` — 相等性比较

#### `PartialEq`

- 启用 `==` 和 `!=` 运算符。
- 派生实现：struct 的所有字段都相等时实例相等；enum 的同一变体相等。
- 要求：所有字段实现 `PartialEq`。

```rust
#[derive(PartialEq)]
struct Point { x: i32, y: i32 }

assert!(Point { x: 1, y: 2 } == Point { x: 1, y: 2 });
```

#### `Eq`

- 无方法，仅作为类型契约标记：任意值都等于自身（自反性）。
- 要求类型已实现 `PartialEq`。
- **反例**：`f32`/`f64` 实现 `PartialEq` 但不实现 `Eq`，因为 `NaN != NaN`。
- 用途：`HashMap<K, V>` 的键要求 `K: Eq`。

```rust
#[derive(PartialEq, Eq)]
struct User { id: u64 }
```

---

### `PartialOrd` / `Ord` — 顺序比较

#### `PartialOrd`

- 启用 `<`、`>`、`<=`、`>=` 运算符。
- 派生实现按字段定义顺序比较；enum 按变体定义顺序比较。
- 要求类型实现 `PartialEq`，所有字段实现 `PartialOrd`。
- 可能返回 `None`：例如 `f64::NAN.partial_cmp(&1.0)` 为 `None`。

#### `Ord`

- 保证任意两个值都有有效顺序。
- 要求类型实现 `PartialOrd` 和 `Eq`。
- 用途：`BTreeSet<T>`、`BTreeMap<K, V>` 要求 `T: Ord` / `K: Ord`。

```rust
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct Version { major: u32, minor: u32, patch: u32 }
```

---

### `Clone` / `Copy` — 复制值

#### `Clone`

- 显式创建深拷贝，可能执行任意代码或复制堆数据。
- 派生实现调用每个字段的 `clone`。
- 要求所有字段实现 `Clone`。
- 用途：切片（Slice） `to_vec()` 要求元素实现 `Clone`。

```rust
#[derive(Clone)]
struct Document {
    title: String,
    content: Vec<u8>,
}
```

#### `Copy`

- 通过按位复制栈上的数据来复制值，不执行任意代码。
- 要求所有字段实现 `Copy`，且类型本身实现 `Clone`。
- 通常用于纯标量或简单聚合类型。

```rust
#[derive(Clone, Copy)]
struct Point { x: i32, y: i32 }
```

> **关键区别**：`Copy` 是隐式、廉价的；`Clone` 是显式、可能昂贵的。所有 `Copy` 类型都可以 `Clone`，但反之不成立。(Source: [TRPL — Appendix C](https://doc.rust-lang.org/book/appendix-03-derivable-traits.html))

---

### `Hash` — 哈希映射

- 将任意大小的值映射为固定大小的哈希值。
- 派生实现组合每个字段的 `hash` 结果。
- 要求所有字段实现 `Hash`。
- 用途：`HashMap<K, V>`、`HashSet<T>` 要求键/元素实现 `Hash`（通常还需 `Eq`）。

```rust
#[derive(PartialEq, Eq, Hash)]
struct User { id: u64 }
```

---

### `Default` — 默认值

- 创建类型的默认值。
- 派生实现调用每个字段的 `default()`。
- 要求所有字段实现 `Default`。
- 常与 struct update 语法结合：

```rust
#[derive(Default)]
struct Config {
    debug: bool,
    port: u16,
}

let cfg = Config {
    port: 8080,
    ..Default::default()
};
```

- 用途：`Option::unwrap_or_default()` 在值为 `None` 时返回 `Default::default()`。

---

## 三、派生组合速查表

| Trait | 启用能力 | 字段要求 | 典型容器要求 |
|:---|:---|:---|:---|
| `Debug` | `{:?}` 格式化 | 字段实现 `Debug` | `assert_eq!` 诊断 |
| `PartialEq` | `==` / `!=` | 字段实现 `PartialEq` | `assert_eq!` |
| `Eq` | 自反性契约 | 已实现 `PartialEq` | `HashMap<K, _>` 的 `K` |
| `PartialOrd` | `<` / `>` / `<=` / `>=` | 字段实现 `PartialOrd` + `PartialEq` | `rand::gen_range` |
| `Ord` | 全序比较 | 已实现 `PartialOrd` + `Eq` | `BTreeSet<T>`、 `BTreeMap<K, _>` |
| `Clone` | 显式深拷贝 | 字段实现 `Clone` | `Vec::extend_from_slice`、 `to_vec` |
| `Copy` | 隐式位拷贝 | 字段实现 `Copy` + `Clone` | 赋值/传参无所有权（Ownership）转移 |
| `Hash` | 哈希函数 | 字段实现 `Hash` | `HashMap<K, _>`、 `HashSet<T>` |
| `Default` | 默认值 | 字段实现 `Default` | `unwrap_or_default`、struct update |

---

## 四、常见组合

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
struct User {
    id: u64,
    name: String,
}
```

> 注意：`Copy` 与包含堆分配字段（如 `String`、`Vec`）的类型**不兼容**。

---

## 五、不能 Derive 的 Trait

- `Display`：用户可见格式没有默认语义。
- `From` / `Into` / `TryFrom` / `TryInto`：类型转换需要具体语义决策。
- `Iterator` / `IntoIterator`：需要自定义迭代逻辑。
- `Drop`：需要自定义析构行为。
- `Send` / `Sync`：由编译器自动推导，无需也不能手动 derive。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Traits](../../01_foundation/02_type_system/04_type_system.md) | derive 是 trait 实现的语法糖 |
| [Advanced Traits](19_advanced_traits.md) | 手动实现 trait 替代默认 derive 行为 |
| [Proc Macros](../../03_advanced/03_proc_macros/07_proc_macro.md) | 第三方 derive 通过过程宏（Procedural Macro）实现 |

---

> **权威来源**: [Rust Reference — Derive](https://doc.rust-lang.org/reference/attributes/derive.html) · [TRPL — Appendix C: Derivable Traits](https://doc.rust-lang.org/book/appendix-03-derivable-traits.html) · [Rust Standard Library](https://doc.rust-lang.org/std/index.html)
