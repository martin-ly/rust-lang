# Rust 1.93 兼容性注意事项

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 目录

- [Rust 1.93 兼容性注意事项](#rust-193-兼容性注意事项)
  - [目录](#目录)
  - [破坏性变更（Breaking Changes）](#破坏性变更breaking-changes)
    - [1. deref\_nullptr 从 warn 升级为 deny](#1-deref_nullptr-从-warn-升级为-deny)
    - [2. #\[test\] 在无效位置现在报错](#2-test-在无效位置现在报错)
    - [3. offset\_of! 类型 well-formed 检查](#3-offset_of-类型-well-formed-检查)
    - [4. rustdoc 文档属性校验](#4-rustdoc-文档属性校验)
  - [未来不兼容警告（Future-Incompatibility）](#未来不兼容警告future-incompatibility)
    - [1. ... 函数参数（可变参数）](#1--函数参数可变参数)
    - [2. repr(C) enum discriminant 超出 c\_int/c\_uint](#2-reprc-enum-discriminant-超出-c_intc_uint)
    - [3. repr(transparent) 忽略 repr(C) 类型](#3-reprtransparent-忽略-reprc-类型)
  - [平台特定变更](#平台特定变更)
    - [Emscripten panic=unwind ABI 变更](#emscripten-panicunwind-abi-变更)
    - [musl 1.2.5 更新](#musl-125-更新)
  - [Cargo 变更](#cargo-变更)
    - [CARGO\_CFG\_DEBUG\_ASSERTIONS](#cargo_cfg_debug_assertions)
    - [cargo publish](#cargo-publish)
  - [常见问题与解决方案](#常见问题与解决方案)
  - [参考资源](#参考资源)

---

## 破坏性变更（Breaking Changes）

### 1. deref_nullptr 从 warn 升级为 deny

**变更**：`deref_nullptr` lint 从默认警告升级为默认拒绝。

**影响**：对空指针解引用的代码将无法通过编译。

**解决方案**：

```rust
// ❌ 1.93 之前可能仅警告，1.93 将报错
let ptr: *const i32 = std::ptr::null();
let _ = unsafe { *ptr };

// ✅ 正确做法：在使用前检查指针有效性
if !ptr.is_null() {
    let _ = unsafe { *ptr };
}
```

**参考**：[PR #148122](https://github.com/rust-lang/rust/pull/148122)

---

### 2. #[test] 在无效位置现在报错

**变更**：`#[test]` 属性在无意义的位置（如 trait 方法、结构体上）之前被忽略，现在会报错。

**影响**：可能影响 rustdoc 生成，以及误用 `#[test]` 的代码。

**解决方案**：

```rust
// ❌ 无效：在 trait 方法上使用 #[test]
trait Foo {
    #[test]  // 1.93 将报错
    fn bar() {}
}

// ❌ 无效：在结构体上使用 #[test]
#[test]  // 1.93 将报错
struct TestStruct;

// ✅ 正确：仅在任何函数上使用 #[test]
#[test]
fn my_test() {
    assert_eq!(1 + 1, 2);
}
```

**参考**：[PR #147841](https://github.com/rust-lang/rust/pull/147841)

---

### 3. offset_of! 类型 well-formed 检查

**变更**：`offset_of!` 宏中的用户类型现在会检查是否 well-formed。

**影响**：若类型不满足约束，可能产生新的编译错误。

**参考**：[Issue #150465](https://github.com/rust-lang/rust/issues/150465)

---

### 4. rustdoc 文档属性校验

**变更**：若 `html_favicon_url`、`html_logo_url`、`html_playground_url`、`issue_tracker_base_url` 或 `html_no_source` 有缺失值、意外值或类型错误，rustdoc 将发出 deny-by-default lint `rustdoc::invalid_doc_attributes`。

**解决方案**：检查并修正 crate 级文档属性配置。

---

## 未来不兼容警告（Future-Incompatibility）

### 1. ... 函数参数（可变参数）

**变更**：在 `extern` 块外使用 `...` 作为函数参数且无模式，将产生未来不兼容警告。

**影响**：C-style 可变参数应仅在 `extern` 块中使用；1.93 已稳定 `system` ABI 的 C-style variadic，应使用正确语法。

**参考**：[PR #143619](https://github.com/rust-lang/rust/pull/143619)

---

### 2. repr(C) enum discriminant 超出 c_int/c_uint

**变更**：`repr(C)` 枚举的判别值若超出 `c_int` 或 `c_uint` 范围，将产生未来不兼容警告。

**影响**：FFI 中与 C 互操作的枚举需确保判别值在 C 类型范围内。

**参考**：[PR #147017](https://github.com/rust-lang/rust/pull/147017)

---

### 3. repr(transparent) 忽略 repr(C) 类型

**变更**：在 `repr(transparent)` 中忽略 `repr(C)` 类型将产生未来不兼容警告。

**参考**：[PR #147185](https://github.com/rust-lang/rust/pull/147185)

---

## 平台特定变更

### Emscripten panic=unwind ABI 变更

**变更**：Emscripten 目标在 `panic=unwind` 下，unwinding ABI 从 JS 异常处理 ABI 改为 wasm 异常处理 ABI。

**影响**：若将 C/C++ 目标文件与 Rust 对象链接，现在必须向链接器传递 `-fwasm-exceptions`。

**Nightly 回退**：可使用 `-Zwasm-emscripten-eh=false -Zbuild-std` 恢复旧行为，但未来版本将移除。

**参考**：[PR #147224](https://github.com/rust-lang/rust/pull/147224)

---

### musl 1.2.5 更新

**变更**：所有 `*-linux-musl` 目标更新到 musl 1.2.5。musl 1.2.4 移除了若干遗留兼容性符号。

**影响**：使用旧版本 `libc` crate（< 0.2.146）的项目可能编译失败。

**解决方案**：确保 `libc >= 0.2.146`。

```toml
[dependencies]
libc = "0.2.146"  # 或更新版本
```

---

## Cargo 变更

### CARGO_CFG_DEBUG_ASSERTIONS

**变更**：Cargo 在更多情况下设置 `CARGO_CFG_DEBUG_ASSERTIONS` 环境变量。

**影响**：依赖 `static-init` 1.0.1–1.0.3 的 crate 可能编译失败，错误为 "failed to resolve: use of unresolved module or unlinked crate `parking_lot`"。

**参考**：[Issue #150646](https://github.com/rust-lang/rust/issues/150646#issuecomment-3718964342)

---

### cargo publish

**变更**：当 `build.build-dir` 未设置时，`cargo publish` 不再将 `.crate` 文件作为用户可访问的最终产物输出。

---

## 常见问题与解决方案

| 问题 | 解决方案 |
| :--- | :--- || deref_nullptr 编译错误 | 在使用前检查指针非空 |
| #[test] 在错误位置 | 仅将 #[test] 用于裸函数 |
| musl 链接错误 | 升级 libc 到 0.2.146+ |
| Emscripten 链接错误 | 传递 -fwasm-exceptions 给链接器 |
| static-init 编译失败 | 升级 static-init 或检查依赖 |
| rustdoc 文档属性错误 | 修正 html_favicon_url 等属性配置 |

---

## 参考资源

- [Rust 1.93.0 Release Notes](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/)
- [Rust 1.93.0 详细 Changelog](https://releases.rs/docs/1.93.0/)
- [Rust 1.93 vs 1.92 对比](./05_rust_1.93_vs_1.92_comparison.md)
- [Rust 平台支持](https://doc.rust-lang.org/rustc/platform-support.html)

---

**最后对照 releases.rs**: 2026-02-14
