# Crate 与源文件（Crates and Source Files）

> **EN**: Crates and Source Files
> **Summary**: Rust 编译模型核心：crate 作为编译、链接、版本控制与运行加载单元；源文件、模块（Module）树、crate 属性与 `main` 函数的规则。
>
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Modules and Paths](11_modules_and_paths.md) · [Attributes and Macros](../09_macros_basics/12_attributes_and_macros.md)
> **后置概念**: [Cargo Workspaces](../../06_ecosystem/01_cargo/78_cargo_workspaces.md) · [Linkage](../../03_advanced/04_ffi/27_linkage.md) · [The Rust Runtime](../../03_advanced/02_unsafe/30_rust_runtime.md)
> **定理链**: Crate → Module Tree → Compilation Unit
> **主要来源**: [Rust Reference — Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html) · [Kohlbecker et al. — Hygienic Macro Expansion](https://doi.org/10.1145/41625.41632) · [Flatt — Binding as Sets of Scopes](https://doi.org/10.1145/2814304.2814305) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [TRPL — Packages and Crates](https://doc.rust-lang.org/book/ch07-01-packages-and-crates.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html)

---

---

## 认知路径

> **认知路径**: 本节从 "Crate 与源文件（Crates and Source F" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Crate 与源文件（Crates and Source F 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Crate 与源文件（Crates and Source F 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Crate 与源文件（Crates and Source F的适用边界。
5. **迁移应用**: 将 Crate 与源文件（Crates and Source F 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Crate 与源文件（Crates and Source F 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Crate 与源文件（Crates and Source F 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Crate 与源文件（Crates and Source F 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Crate 与源文件（Crates and Source F 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Crate 与源文件（Crates and Source F 具有语言特有的形态。

## 一、Crate 是 Rust 的编译单元

Rust 的语义存在清晰的**编译期与运行期阶段区分（phase distinction）**：

- **静态解释**的规则决定编译是否成功。
- **动态解释**的规则决定程序运行时（Runtime）的行为。

编译模型围绕 **crate** 展开：

- 每次编译处理一个源形式的 crate。
- 若编译成功，输出一个二进制形式的 crate：可执行文件或某种库。
- crate 是**编译、链接、版本控制、分发和运行时（Runtime）加载**的基本单元。

一个 crate 包含一棵嵌套的模块（Module）作用域树。这棵树的顶层是一个**匿名模块**；crate 中任意项都有规范的模块路径，表示它在 crate 模块树中的位置。

---

## 二、源文件

- Rust 编译器总是以**单个源文件**作为输入，输出**单个 crate**。
- 源文件扩展名为 `.rs`。
- 一个源文件描述一个模块（Module），模块的名称和在 crate 模块树中的位置由外部决定：要么由引用（Reference）它的源文件中的显式模块项定义，要么由 crate 本身决定。
- 每个源文件都是模块（Module），但并非每个模块都需要独立源文件；模块定义可以嵌套在一个文件内。
- 源文件以零个或多个 **Item** 定义序列组成，文件开头可以有应用于所在模块的属性。
- 匿名 crate 模块还可以拥有应用于整个 crate 的属性。
- 文件内容可以以 shebang 开头。

---

## 三、Crate 级属性示例

```rust
#![crate_name = "projx"]
#![crate_type = "lib"]
#![warn(non_camel_case_types)]
```

常用 crate 级属性：

| 属性 | 作用 |
|:---|:---|
| `crate_name` | 指定 crate 名称 |
| `crate_type` | 指定输出类型：`bin` / `lib` / `dylib` / `cdylib` / `staticlib` / `rlib` |
| `warn` / `deny` / `allow` | 控制 lint 级别 |

---

## 四、`main` 函数

一个包含 `main` 函数的 crate 可以被编译为可执行文件。

### `main` 的约束

- 不接受参数。
- 不能声明 trait bound 或 lifetime bound。
- 不能有 `where` 子句。
- 返回类型必须实现 `Termination` trait。

```rust
fn main() {}

fn main() -> ! {
    std::process::exit(0);
}
```

`main` 也可以是导入的函数：

```rust
mod foo {
    pub fn bar() {
        println!("Hello, world!");
    }
}
use foo::bar as main;
```

### 未捕获的外部 unwind

当来自外部运行时（Runtime）的 unwind（例如 C++ 异常、或不同 panic handler 的 Rust panic）传播到 `main` 之外时，进程会被安全终止。这可能是 abort，且不保证执行 `Drop`。

### `no_main` 属性

`#![no_main]` 禁止为可执行二进制文件生成 `main` 符号，适用于由其他链接对象定义 `main` 的场景（如嵌入式）。

---

## 五、`crate_name` 属性

`#![crate_name = "mycrate"]` 用于在 crate 级别指定 crate 名称。

- 名称不能为空。
- 只能包含 Unicode 字母数字或下划线 `_`。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Modules and Paths](11_modules_and_paths.md) | crate 由模块树组织 |
| [Items](39_items.md) | crate 由各种 item 组成 |
| [Cargo Workspaces](../../06_ecosystem/01_cargo/78_cargo_workspaces.md) | Cargo 在 crate 之上组织 workspace |
| [Linkage](../../03_advanced/04_ffi/27_linkage.md) | crate 输出参与链接 |
| [The Rust Runtime](../../03_advanced/02_unsafe/30_rust_runtime.md) | crate 运行时行为由运行时定义 |
| [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md) | 术语表（元层参考） |
