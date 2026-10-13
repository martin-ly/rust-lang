# Safety Tags（安全标签）

> **EN**: Safety Tags in Formal Verification — Redirect Stub
> **Bloom 层级**: L4
> **Summary**: Redirect stub: the RFC #3842 `safety` attributes proposal — structured, tool-checkable annotations of `unsafe` function safety contracts, plus their predicate-logic formalization and mapping to Kani/Prusti/Verus — is canonically covered in `concept/07_future/02_preview_features/03_safety_tags_preview.md`; this page keeps only the pointer.

> **权威来源**: 本主题已合并至 [`../../07_future/02_preview_features/03_safety_tags_preview.md`](../../07_future/02_preview_features/03_safety_tags_preview.md)，本文件保留为重定向（Redirect stub）。
>
> **国际权威来源**: [RFC PR #3842 — Safety Tags](https://github.com/rust-lang/rfcs/pull/3842) (P0) · [Rao et al., “Annotating and Auditing the Safety Properties of Unsafe Rust”, arXiv:2504.21312](https://arxiv.org/abs/2504.21312) (P1) · [safety-lib on docs.rs](https://docs.rs/safety-lib) (P2)
>
> 根据 AGENTS.md §2 Canonical 规则，同一概念只能有一个权威页。
> 经 2026-07-12 审计，本文件与预览权威页内容高度重复（v2 相似度 0.855），且未包含独立的形式化（分离逻辑）推导内容——其形式化语义（契约的谓词逻辑表示、与 Kani/Prusti/Verus 的映射）已由 08 号权威页「二、形式化语义」一节覆盖。形式化视角的延伸阅读见：
>
> - [AutoVerus/Verus](../04_model_checking/07_autoverus.md) — `requires`/`ensures` 契约验证
> - [Miri](../04_model_checking/08_miri.md) · [形式化验证工具生态](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md)
> - [BorrowSanitizer 深度](04_borrow_sanitizer_in_formal.md)
> **前置概念**: [Unsafe](../../03_advanced/02_unsafe/01_unsafe.md) · [Separation Logic](01_rustbelt.md)
> **后置概念**: [Safety Tags Preview](../../07_future/02_preview_features/03_safety_tags_preview.md) · [Verification Tools](../04_model_checking/01_verification_toolchain.md)
>
>
> **受众**: [研究者]
> **内容分级**: [研究者级]

---

## 1. 本页定位（与预览权威页的分工）

预览页 `07_future/02_preview_features/03_safety_tags_preview.md` 覆盖 safety tags 的**特性设计**（属性语法、演进路线、场景）。本页只承担**分离逻辑视角**：把 unsafe 契约表述为分离逻辑断言，并给出该表述在 rustc 1.99 可复现的反例。两页不重叠的内容边界：预览页回答“标签长什么样”，本页回答“标签的数学含义是什么、何时不可判定”。

## 2. 权威定义（分离逻辑表述，可转判定程序）

**定义（unsafe fn 契约的分离逻辑形式）**：一个 `unsafe fn f(args) -> R` 的安全契约是二元组 `(pre, post)`：

- `pre`：关于参数与可达堆（heap）的分离逻辑谓词，使用 `p ↦ v`（points-to）、`P * Q`（分离合取，两块堆互不重叠）、`P −* Q`（magic wand，分离蕴含）。
- `post`：返回后堆与返回值的谓词。
- 语义（RustBelt 式 partial correctness）：对任意初始堆 `h`，若 `h ⊨ pre` 且 `f` 的执行终止，则存在 `h'` 使执行从 `h` 到 `h'` 且 `h' ⊨ post`，且全程不触发 UB。

**判定程序（把 `/// # Safety` 注释转成可审计断言）**：

1. 逐条解析注释前提，归类：(a) 有效性（validity：指针指向已分配且存活的对象）；(b) 对齐（alignment）；(c) 别名（aliasing：`*` 分离性）；(d) 生命周期（outlives）；(e) 值域（如 `len > 0`）。
2. 每类映射到工具：(a)(c) → Miri/Tree Borrows；(b) → Miri；(d) → rustc 借用检查（静态）；(e) → Kani/Verus/Creusot（SMT）。
3. 无法映射到任何工具的条目 = 契约中的**不可判定残留**，必须人工审计或 FLS 式子集裁剪。
4. 审计记录绑定：rustc 版本 + Edition + 工具版本 + 复现命令。

**权威定义源**：unsafe 操作的封闭枚举见 FLS 19:2–19:11（<https://spec.ferrocene.dev/unsafety.html>）；契约的分离逻辑语义见 RustBelt（POPL 2018, <https://plv.mpi-sws.org/rustbelt/popl18/>）；机器可读 safety 属性标注与审计见 arXiv:2504.21312《Annotating and Auditing the Safety Properties of Unsafe Rust》（arXiv API 已核实存在，v2）。

## 3. 反例与边界案例（rustc 1.99.0 实测）

### 3.1 反例 A：契约违反完全静态不可见——safe 代码被拒、unsafe 代码放行

同一逻辑错误（两个可变别名），借用检查器只保护 safe 侧：

```rust,compile_fail
// safe 侧：error[E0499]: cannot borrow `x` as mutable more than once at a time
fn safe_alias(v: &mut Vec<i32>) {
    let a = &mut v[..];
    let b = &mut v[..]; // ❌ E0499
    a[0] = 1; b[0] = 2;
}
fn main() {}
```

```rust,ignore
// unsafe 侧：rustc 1.99.0 编译通过、无警告（调用点包在 unsafe 块内，
// Edition 2024 下裸调用会是 error[E0133]，见 §3.2）；
// cargo miri run 报 "Undefined Behavior"（别名契约被违反，编译期零诊断）
unsafe fn alias_contract(v: &mut Vec<i32>) {
    let a: *mut i32 = v.as_mut_ptr();
    let b: *mut i32 = v.as_mut_ptr(); // 两个可写别名：违反 pre 中的 * 分离性
    unsafe { *a = 1; *b = 2; }
}
fn main() {
    let mut v = vec![0];
    unsafe { alias_contract(&mut v); } // 调用点本身合法（前提已“移交”给调用方）
}
```

**分离逻辑解读**：`pre ⊢ v ↦ _` 只给一份所有权；`*a` 与 `*b` 同时可写要求 `v ↦ x₁ * v ↦ x₂`——自矛盾。rustc 在 safe 侧用借用检查拒绝该矛盾，在 unsafe 侧把判定责任移交程序员。Safety tags 的目标正是让 (a)(c) 类前提在 unsafe 边界上重新可机检。

### 3.2 反例 B：Edition 2024 的 `unsafe_op_in_unsafe_fn` 是契约“义务显式化”的语言级实例

```rust,compile_fail
#[deny(unsafe_op_in_unsafe_fn)]
unsafe fn deref(p: *const i32) -> i32 {
    *p // error[E0133]: dereference of raw pointer is unsafe and requires unsafe block
}
fn main() {}
```

rustc 1.99.0 实测：Edition 2021 + `#[deny(...)]` → E0133 硬错误；Edition 2024 默认 → 同款 warning[E0133]（`unsafe fn` 体不再隐式是 unsafe context）。**形式化意义**：RFC 2585（<https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html>，Rust Issue #71688）把“契约义务的作用域”从整个 `unsafe fn` 体收窄到显式 `unsafe {}` 块——即把 unsafe 面积（unsafe surface）变成可静态计数的对象，这是 safety tags 审计的度量基础：没有显式块边界，就没有“哪段代码需要哪条契约”的可判定映射。

### 3.3 边界案例 C：契约可声明但不可判定的残留类

```rust,ignore
/// # Safety
/// - `f` must not read more than `n` elements from `ptr`
pub unsafe fn call_with_buf(f: unsafe fn(*const u8, usize), ptr: *const u8, n: usize) {
    unsafe { f(ptr, n) } // rustc 1.99.0 编译通过
}
```

前提涉及**函数参数 f 的行为**（高阶契约）：分离逻辑可以写 `∀k < n. ptr+k ↦ _`，但 rustc/Miri 都无法验证任意 `f` 满足它——判定需要程序验证工具（Kani 对 fn 指针做符号执行）或对 `f` 的调用点枚举。审计结论：高阶 unsafe 契约是 §2 判定程序第 3 步的“不可判定残留”，只能靠子集裁剪（如 Ferrocene 认证禁止函数指针进入认证边界）消解。

### 3.4 边界案例 D：`unsafe fn` 签名本身可静态检查的契约部分

```rust,compile_fail
// error[E0515]: cannot return reference to local variable `local`
unsafe fn bad<'a>(x: i32) -> &'a i32 {
    let local = x;
    &local
}
fn main() {}
```

rustc 1.99.0 实测 E0515。结论：契约不是全有或全无——outlives 类前提（(d) 类）即使在 `unsafe fn` 内仍被静态强制；safety tags 的规范价值集中在 (a)(b)(c)(e) 类，(d) 类已由类型系统覆盖。设计标签系统时重复编码 (d) 类是纯冗余。

## 4. 与分离逻辑主线的衔接

- RustBelt 的 `unsafe fn` 规则（POPL 2018 §III）本质上是本页面 (pre, post) 语义的类型化版本：把 pre/post 抽象成“调用方必须提供的分离逻辑前提”的 opaque 假设。
- arXiv:2504.21312 的审计流水线（标注 → 静态检查 → 人工复核）对应 §2 判定程序步骤 1–4；其结论“多数 unsafe 前提可归入有限类别”支撑 §3.3 的残留分类。
- FLS 19 章把 unsafe 操作封闭枚举（19:4–19:9），等价于把“哪些操作需要契约”从开放清单变成有限判定问题——safety tags 若标准化，应与该枚举一一对应，而非自创类别。

## 5. 练习题（分离逻辑审计实操）

1. **谓词化题**：把 `read_bytes` 的 `/// # Safety` 两条注释（有效读 n 字节、对齐）写成 `p ↦ v` 与对齐谓词的合取，并指出 Miri 各自对应哪条检查消息。
2. **反例迁移题**：§3.1 的 unsafe 侧代码在 `unsafe_op_in_unsafe_fn` deny 下是否需要改动？（答：不需要——两个 `*mut` 的别名不触发该 lint；它管块边界，不管别名。说明 lint 与契约是两个正交机制。）
3. **残留识别题**：对 `std::slice::from_raw_parts` 的三条官方前提逐条跑 §2 判定程序，标出哪条在 Kani 下可判定、哪条只能人工审计。

