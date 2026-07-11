> **内容分级**: [研究级]
>
# Application Binary Interface（ABI）

> **EN**: Application Binary Interface
> **Summary**: Rust 编译输出 ABI 的控制机制：`used`、`no_mangle`、`link_section`、`export_name` 属性，及其对符号可见性和对象文件布局的影响。
>
> **受众**: [专家]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Specification / Systems
> **双维定位**: S×Sys — 语言与二进制接口
> **前置依赖**: [Linkage](../../03_advanced/04_ffi/27_linkage.md) · [FFI Advanced](../../03_advanced/04_ffi/09_ffi_advanced.md) · [Attributes and Macros](../../01_foundation/09_macros_basics/12_attributes_and_macros.md)
> **后置概念**: [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) · [Inline Assembly](../../03_advanced/05_inline_assembly/13_inline_assembly.md)
> **定理链**: N/A — 语言规范/平台相关文档
> **主要来源**: [Rust Reference — Application Binary Interface](https://doc.rust-lang.org/reference/items/external-blocks.html#abi) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/) · [System V AMD64 ABI](https://gitlab.com/x86-psABIs/x86-64-ABI) · [ARM Procedure Call Standard](https://developer.arm.com/documentation/ihi0042/latest/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/) · [System V AMD64 ABI](https://gitlab.com/x86-psABIs/x86-64-ABI) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

>
> **来源**: [Rust Reference — Application Binary Interface](https://doc.rust-lang.org/reference/abi.html) · [Rust Reference — extern functions](https://doc.rust-lang.org/reference/items/external-blocks.html) · [Rust Reference — external blocks](https://doc.rust-lang.org/reference/items/external-blocks.html)

> **Rust 1.97.0 变更提示**：
> Rust 1.97.0 默认启用 v0 symbol mangling 方案，ABI 与符号可见性影响见 [`rust_1_97_stabilized.md`](../../07_future/00_version_tracking/rust_1_97_stabilized.md)。

---

---

## 认知路径

> **认知路径**: 本节从 "Application Binary Interface（A" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Application Binary Interface（A 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Application Binary Interface（A 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Application Binary Interface（A的适用边界。
5. **迁移应用**: 将 Application Binary Interface（A 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Application Binary Interface（A 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Application Binary Interface（A 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Application Binary Interface（A 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Application Binary Interface（A 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Application Binary Interface（A 具有语言特有的形态。

## 一、什么是 ABI

**ABI（Application Binary Interface）** 定义了编译后的代码在二进制层面如何与其他代码交互，包括：

- 函数调用约定（calling convention）
- 类型布局（size、alignment、padding）
- 符号命名规则（name mangling）
- 对象文件段（section）布局

Rust 默认使用自己的符号命名规则（mangling），并在需要时通过属性控制 ABI 行为。

---

## 二、`#[used]` — 强制保留 static

`#[used]` 只能用于 `static` 项，强制编译器在输出对象文件（`.o`、`.rlib` 等）中保留该变量，即使它在 crate 内未被引用（Reference）。

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
| [Linkage](../../03_advanced/04_ffi/27_linkage.md) | ABI 属性影响链接器可见的符号和段 |
| [FFI Advanced](../../03_advanced/04_ffi/09_ffi_advanced.md) | FFI 场景是 ABI 控制的主要用例 |
| [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) | 多数 ABI 属性需要 `unsafe` |
| [Inline Assembly](../../03_advanced/05_inline_assembly/13_inline_assembly.md) | 与底层段/符号控制经常协同使用 |

---

> **权威来源**: [Rust Reference — Application Binary Interface](https://doc.rust-lang.org/reference/items/external-blocks.html#abi) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference — Application Binary Interface](https://doc.rust-lang.org/reference/abi.html) · [Rust Reference — extern functions](https://doc.rust-lang.org/reference/items/external-blocks.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)
> **权威来源对齐变更日志**: 2026-07-10 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch L4](../../00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-10
**状态**: ✅ 权威来源对齐完成 (Batch L4)

---

## Rust 1.97.0 交叉语义（链接 / ABI）

> **Edition / 版本**: Rust 1.97.0+ (Edition 2024)
> **定位**: 本小节把上方「Rust 1.97.0 变更提示」横幅**展开**为 v0 × debuginfo demangle × linker_messages × backtrace 的交互矩阵，并阐明空 `export_name`/`link_name` 校验对 ABI 契约的意义；对应审计缺口（[`GLOBAL_SEMANTIC_CRITICAL_AUDIT_2026_07_11.md`](../../../reports/GLOBAL_SEMANTIC_CRITICAL_AUDIT_2026_07_11.md) §2.4、§4 P2-2 缺口#5）。横幅原文保留。

### A. v0 × debuginfo demangle × linker_messages × backtrace 交互矩阵

阅读方式：行 × 列单元格描述「行特性」在「列特性」维度上的交互；对角线为该特性的**主效应**。v0 默认混淆改变 Rust→Rust 符号名形态；`#[unsafe(no_mangle)]`/`extern "C"`/`#[unsafe(export_name = "...")]` 产生的**字面符号名绕过混淆**，因而不受 v0 影响（ABI 稳定面的边界）。

| 行 ＼ 列 | v0 mangling | debuginfo demangle | linker_messages | backtrace |
|:---|:---|:---|:---|:---|
| **v0 mangling** | 默认混淆方案（Rust→Rust 符号）— 主效应 | v0 符号需新版 demangler（`rustfilt`/GDB 15+/LLDB）方可还原 | 链接「未解析符号」时，v0 混淆名会出现在 linker 输出，需 demangle 才可读 | 旧栈帧打印可能显示混淆名；backtrace 文本**格式可能变化**（发布说明） |
| **debuginfo demangle** | demangle 失败时调试器/profiler 显示原始 v0 名 | debuginfo 携带类型/泛型实例信息，依赖 demangler 还原 — 主效应 | linker 输出的 v0 名可经 `rustfilt` 等 demangle 后处理还原 | panic backtrace 的符号可读性取决于运行期 demangle |
| **linker_messages** | 链接错误中的 v0 名以 warning 形式透传到 rustc 诊断 | 默认未 demangle，原始符号直接显示 | 默认 warn 的特殊 lint（不在 `warnings` group）— 主效应 | 链接阶段告警先于运行期 backtrace，阶段不同但符号同源 |
| **backtrace** | 栈帧符号来自 v0 混淆，文本格式可能变化 | 可读性依赖 demangle；发布说明指「格式可能变化」 | 运行期（backtrace）vs 链接期（linker_messages），共享同一符号名 | 运行期栈回溯 — 主效应 |

⚠ **需专家复核**：demangler 对各工具/平台的**精确最低版本**（GDB 15+、LLDB、`rustfilt` 的 v0 覆盖度）未在版本页逐项给出；矩阵中的版本表述以 [`rust_1_97_stabilized.md`](../../07_future/00_version_tracking/rust_1_97_stabilized.md) §2.7 与发布说明为上限，具体 toolchain 组合请实测复核。

```bash
# 观测 v0 混淆与 demangle：链接期符号 vs 可读名
cargo build --release
nm target/release/lib<name>.so | rustfilt | head     # rustfilt 还原 v0 名
# 触发一条 panic，对比 backtrace 文本格式（RUST_BACKTRACE=1）
RUST_BACKTRACE=1 cargo run
```

### B. 空 `export_name` / `link_name` 校验对 ABI 契约的意义

稳定的 ABI 契约依赖**两侧符号名的确定性**：导出侧（`export_name`/`no_mangle`）必须给出**非空、全局唯一**的字面符号，导入侧（`#[link_name]`/`#[link(name = "...")]`）必须给出**非空、合法**的目标符号/库名。Rust 1.97.0 把两类「空/非法符号名」从「可能被静默接受、链接期才暴露」提升为**编译期硬错误**，等价于把 ABI 契约的可验证性前移到编译期：

- 空 `#[export_name = ""]` → 导出符号名缺失，ABI 契约无法命名 → 拒绝。
- 非法 `#[link_name]` / `#[link(name)]` → 导入侧目标不明确，ABI 绑定无法解析 → 拒绝。

在 Edition 2024 下这些属性均须写在 `#[unsafe(...)]` 内（符号冲突属不安全来源）。迁移判定见 [`migration_197_decision_tree.md`](../../07_future/00_version_tracking/migration_197_decision_tree.md) §3。

```rust,ignore
// Edition 2024 / Rust 1.97.0+ —— ABI 契约两端：导出字面符号 + 导入按名绑定
// 导出侧（cdylib）：固定字面符号，绕过 v0 混淆
#[unsafe(no_mangle)]
pub extern "C" fn ffi_add(a: i32, b: i32) -> i32 { a + b }

// 导入侧：库名与符号名均须非空、合法（否则 1.97+ 编译期报错）
#[link(name = "mynative")]
extern "C" {
    #[link_name = "native_add"]
    fn native_add(a: i32, b: i32) -> i32;
}
```

```rust,ignore
// ❌ Rust 1.97+ 硬错误：空导出符号名破坏 ABI 契约的可命名性
#[unsafe(export_name = "")]
pub fn hook() {}

// ✅ 非空、全局唯一的固定符号名，恢复可验证的 ABI 契约
#[unsafe(export_name = "my_crate_hook_v1")]
pub fn hook() {}
```

### 来源与交叉索引

> **来源**:
> · [Rust 1.97.0 Release Notes](https://releases.rs/docs/1.97.0/)（Compatibility Notes：v0 mangling 默认对 debugger/profiler/backtrace 的影响、Warn on linker output、空 `export_name` 报错、`link_name`/`link(name)` 校验）
> · [`rust_1_97_stabilized.md`](../../07_future/00_version_tracking/rust_1_97_stabilized.md) §2.7（v0 mangling）、§2.8（`linker_messages`）、§7/§7.2（空 `export_name` 与 `link_name` 校验）
> · [Rust Reference — ABI](https://doc.rust-lang.org/reference/abi.html) · [Rust Reference — External Blocks / ABI](https://doc.rust-lang.org/reference/items/external-blocks.html) · [Rust Reference — Linkage](https://doc.rust-lang.org/reference/linkage.html)
>
> **交叉索引（反链）**:
> · 版本事实源：[`rust_1_97_stabilized.md`](../../07_future/00_version_tracking/rust_1_97_stabilized.md)
> · 特性×领域反查矩阵：[`feature_domain_matrix_197.md`](../../07_future/00_version_tracking/feature_domain_matrix_197.md)
> · 兼容性迁移判定树：[`migration_197_decision_tree.md`](../../07_future/00_version_tracking/migration_197_decision_tree.md)
> · 链接权威页（交叉语义）：[`27_linkage.md`](../../03_advanced/04_ffi/27_linkage.md)


---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [verus-lang/verus — SMT 验证器](https://github.com/verus-lang/verus) · [creusot-rs/creusot — Rust 演绎验证](https://github.com/creusot-rs/creusot)
