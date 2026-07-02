> **内容分级**: [研究级]
>
# Application Binary Interface（ABI）

> **EN**: Application Binary Interface
> **Summary**: Rust 编译输出 ABI 的控制机制：`used`、`no_mangle`、`link_section`、`export_name` 属性，及其对符号可见性和对象文件布局的影响。
>
> **受众**: [专家]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification / Systems
> **双维定位**: S×Sys — 语言与二进制接口
> **前置依赖**: [Linkage](../03_advanced/27_linkage.md) · [FFI Advanced](../03_advanced/09_ffi_advanced.md) · [Attributes and Macros](../01_foundation/12_attributes_and_macros.md)
> **后置概念**: [Unsafe Rust](../03_advanced/03_unsafe.md) · [Inline Assembly](../03_advanced/13_inline_assembly.md)
> **定理链**: N/A — 语言规范/平台相关文档
> **主要来源**: [Rust Reference — Application Binary Interface](https://doc.rust-lang.org/reference/items/external-blocks.html#abi) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/) · [System V AMD64 ABI](https://gitlab.com/x86-psABIs/x86-64-ABI) · [ARM Procedure Call Standard](https://developer.arm.com/documentation/ihi0042/latest/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/) · [System V AMD64 ABI](https://gitlab.com/x86-psABIs/x86-64-ABI) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

>
> **来源**: [Rust Reference — Application Binary Interface](https://doc.rust-lang.org/reference/abi.html) · [Rust Reference — extern functions](https://doc.rust-lang.org/reference/items/external-blocks.html) · [Rust Reference — external blocks](https://doc.rust-lang.org/reference/items/external-blocks.html)

---

## 一、什么是 ABI

**ABI（Application Binary Interface）** 定义了编译后的代码在二进制层面如何与其他代码交互，包括：

- 函数调用约定（calling convention）
- 类型布局（size、alignment、padding）
- 符号命名规则（name mangling）
- 对象文件段（section）布局

Rust 默认使用自己的符号命名规则（mangling），并在需要时通过属性控制 ABI 行为。

---

## 二、`#[used]` — 强制保留 static

`#[used]` 只能用于 `static` 项，强制编译器在输出对象文件（`.o`、`.rlib` 等）中保留该变量，即使它在 crate 内未被引用。

> **注意**：`#[used]` 只能影响编译器输出，链接器仍可能在最终链接阶段移除它。

```rust
#[used]
static FOO: u32 = 0;

static BAR: u32 = 0; // 未使用，可能被移除

pub static BAZ: u32 = 0; // 公开可达，会被保留
```

### 使用场景

- 与外部链接器脚本或引导加载程序配合，确保特定符号存在。
- 嵌入/裸机场景中保留中断向量表等关键数据。

---

## 三、`#[unsafe(no_mangle)]` — 禁用符号混淆

`#[unsafe(no_mangle)]` 禁用 Rust 默认的符号名混淆（mangling），使导出符号与项的标识符同名。

```rust
#[unsafe(no_mangle)]
pub extern "C" fn my_function() {}
```

- 项会被公开导出到库或对象文件中（类似 `#[used]` 的效果）。
- 通常与 `extern "C"` 一起使用，以便其他语言通过 C ABI 调用。

> **安全性**：`no_mangle` 是 unsafe 的，因为未混淆的符号可能与其他符号或知名符号冲突，导致未定义行为。

> **Edition 差异**：2024 Edition 之前，`no_mangle` 不需要 `unsafe` 限定；2024 Edition 起必须写为 `#[unsafe(no_mangle)]`。

---

## 四、`#[unsafe(link_section = "...")]` — 指定对象文件段

`#[unsafe(link_section = ".section_name")]` 指定函数或 static 的内容放入对象文件的哪个段。

```rust
#[unsafe(no_mangle)]
#[unsafe(link_section = ".example_section")]
pub static VAR1: u32 = 1;
```

> **安全性**：`link_section` 是 unsafe 的，因为它允许将数据或代码放入不期望的内存段，例如将可变数据放入只读区域。

> **重复声明**：同一项上多次使用 `link_section` 只有第一次有效，`rustc` 会对后续使用发出 future-compatibility 警告。

### 典型场景

- 将中断向量表放入特定段。
- 与自定义链接器脚本配合精确控制内存布局。

---

## 五、`#[unsafe(export_name = "...")]` — 自定义导出符号名

`#[unsafe(export_name = "symbol_name")]` 指定函数或 static 导出的符号名。

```rust
#[unsafe(export_name = "exported_symbol_name")]
pub fn name_in_rust() {}
```

- Rust 代码中仍使用原始标识符 `name_in_rust`。
- 外部链接器或其他语言看到的是 `exported_symbol_name`。

> **安全性**：`export_name` 是 unsafe 的，因为自定义符号名可能与其他符号冲突。

> **空字符串**：Rust 1.97 起，`#[export_name = ""]` 被明确拒绝，避免空符号名导致的链接歧义。

> **重复声明**：同一项上多次使用 `export_name` 只有第一次有效。

---

## 六、ABI 属性对比

| 属性 | 作用 | 适用项 | 是否 unsafe |
|:---|:---|:---|:---:|
| `#[used]` | 强制编译器保留 static | `static` | 否 |
| `#[unsafe(no_mangle)]` | 禁用符号混淆 | 任意项 | 是 |
| `#[unsafe(link_section = "...")]` | 指定对象文件段 | 函数/static | 是 |
| `#[unsafe(export_name = "...")]` | 自定义导出符号名 | 函数/static | 是 |

---

## 七、实践建议

1. **优先使用 `extern "C"` 进行 FFI**：C ABI 是最稳定的跨语言接口。
2. **谨慎使用 `no_mangle` 和 `export_name`**：全局唯一符号名冲突可能导致难以调试的链接错误。
3. **裸机/嵌入式注意段布局**：`link_section` 是精细控制启动代码和向量表的常用手段。
4. **结合 `used` 确保关键符号不被优化掉**：尤其在最终二进制由外部链接器主导时。

---

## 八、关联概念

| 概念 | 关系 |
|:---|:---|
| [Linkage](../03_advanced/27_linkage.md) | ABI 属性影响链接器可见的符号和段 |
| [FFI Advanced](../03_advanced/09_ffi_advanced.md) | FFI 场景是 ABI 控制的主要用例 |
| [Unsafe Rust](../03_advanced/03_unsafe.md) | 多数 ABI 属性需要 `unsafe` |
| [Inline Assembly](../03_advanced/13_inline_assembly.md) | 与底层段/符号控制经常协同使用 |
