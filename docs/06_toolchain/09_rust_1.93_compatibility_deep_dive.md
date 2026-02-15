# Rust 1.93 兼容性深度解析

> **文档版本**: 1.0
> **创建日期**: 2026-02-12
> **权威来源**: [releases.rs/docs/1.93.0](https://releases.rs/docs/1.93.0/)
> **用途**: 专项说明 pin_v2、Emscripten、#[test]、offset_of!、deref_nullptr、可变参数、repr(C) 等兼容性变更

---

## 目录

- [Rust 1.93 兼容性深度解析](#rust-193-兼容性深度解析)
  - [目录](#目录)
  - [pin\_v2 内置属性](#pin_v2-内置属性)
  - [Emscripten unwinding ABI 变更](#emscripten-unwinding-abi-变更)
  - [#\[test\] 属性严格化](#test-属性严格化)
  - [offset\_of! 类型检查](#offset_of-类型检查)
  - [deref\_nullptr deny-by-default](#deref_nullptr-deny-by-default)
  - [... 可变参数 future-incompat](#-可变参数-future-incompat)
  - [repr(C) enum 判别值警告](#reprc-enum-判别值警告)
  - [repr(transparent) 忽略 repr(C) 警告](#reprtransparent-忽略-reprc-警告)
  - [相关文档](#相关文档)

---

## pin_v2 内置属性

**变更**：Rust 1.93 将 `pin_v2` 引入内置属性命名空间。

**影响**：若用户代码中定义了与 `pin_v2` 同名的项，可能产生命名冲突。此为内部实现变更，多数用户不受影响。

**参考**：[PR #139751](https://github.com/rust-lang/rust/pull/139751)

---

## Emscripten unwinding ABI 变更

**变更**：在 Emscripten 目标上，使用 `panic=unwind` 编译时，unwinding ABI 从 **JS 异常处理 ABI** 改为 **wasm 异常处理 ABI**。

**影响范围**：

- 将 C/C++ 目标文件与 Rust 对象链接的项目
- 依赖 Emscripten 进行 C 互操作的项目

**解决方案**：

```bash
# 链接时传递 -fwasm-exceptions 给链接器
clang -fwasm-exceptions -o output.wasm rust_obj.o c_obj.o
```

**Nightly 回退**（临时）：

```bash
rustc -Z wasm-emscripten-eh=false -Z build-std ...
```

注意：未来版本将移除该选项。

**WASM 模块影响**：若使用 `wasm32-unknown-emscripten` 且 `panic=unwind`，需确保 C/C++ 侧也使用 wasm 异常处理 ABI。

**参考**：[PR #147224](https://github.com/rust-lang/rust/pull/147224)

---

## #[test] 属性严格化

**变更**：`#[test]`  previously 在无意义位置（trait 方法、结构体、类型等）被忽略；Rust 1.93 起将**报错**。

**无效位置示例**：

```rust
// ❌ 1.93 报错：trait 方法上
trait MyTrait {
    #[test]
    fn test_method() {}
}

// ❌ 1.93 报错：结构体上
#[test]
struct TestStruct;

// ❌ 1.93 报错：impl 块内非测试函数
impl Foo {
    #[test]
    fn bar() {}
}
```

**正确用法**：

```rust
// ✅ 仅在任何（非 trait/impl）函数上使用
#[test]
fn my_test() {
    assert_eq!(2 + 2, 4);
}

#[cfg(test)]
mod tests {
    #[test]
    fn another_test() {}
}
```

**rustdoc 影响**：若 crate 中误用 `#[test]`，rustdoc 生成可能失败。检查并修正所有 `#[test]` 使用位置。

**参考**：[PR #147841](https://github.com/rust-lang/rust/pull/147841)

---

## offset_of! 类型检查

**变更**：`offset_of!` 宏中的用户类型现在会进行 **well-formed** 检查。

**影响**：若类型不满足约束（如未实现 Send、包含非法生命周期等），将产生新的编译错误。

**示例**：

```rust
struct NotWellFormed<T: ?Sized>(T);  // 可能有问题

// 1.93 可能报错：类型不满足 well-formed
let off = core::mem::offset_of!(NotWellFormed<dyn Send>, 0);
```

**解决**：确保传入 `offset_of!` 的类型满足语言要求的 well-formed 约束。

**参考**：[Issue #150465](https://github.com/rust-lang/rust/issues/150465)

---

## deref_nullptr deny-by-default

**变更**：`deref_nullptr` lint 从 **warn-by-default** 升级为 **deny-by-default**。

**影响**：对空指针解引用的代码将**无法通过编译**（在默认 lint 配置下）。

**错误示例**：

```rust
let ptr: *const i32 = std::ptr::null();
let _ = unsafe { *ptr };  // ❌ 1.93 默认 deny，编译失败
```

**正确做法**：

```rust
if !ptr.is_null() {
    let _ = unsafe { *ptr };
}

// 或使用 ptr.as_ref()（Option 返回）
if let Some(val) = unsafe { ptr.as_ref() } {
    let _ = val;
}
```

**临时放宽**（不推荐）：

```rust
#[allow(deref_nullptr)]
fn legacy_code() { ... }
```

**参考**：[PR #148122](https://github.com/rust-lang/rust/pull/148122)

---

## ... 可变参数 future-incompat

**变更**：在 `extern` 块外使用 `...` 作为函数参数且无模式，将产生 **future-incompatibility** 警告。

**背景**：Rust 1.93 稳定了 `system` ABI 的 C-style variadic，正确用法应仅在 `extern` 块中。

**错误示例**：

```rust
// ❌ 未来不兼容
fn my_print(fmt: *const u8, ...) {  // ... 在非 extern 中
    // ...
}
```

**正确用法**：

```rust
// ✅ 在 extern 块中声明
extern "system" {
    fn printf(format: *const u8, ...);
}
```

**参考**：[PR #143619](https://github.com/rust-lang/rust/pull/143619)

---

## repr(C) enum 判别值警告

**变更**：`repr(C)` 枚举的判别值若超出 `c_int` 或 `c_uint` 范围，将产生 **future-incompatibility** 警告。

**影响**：FFI 中与 C 互操作的枚举需确保判别值在 C 类型范围内。

**示例**：

```rust
#[repr(C)]
enum LargeDiscriminant {
    A = 0,
    B = i32::MAX as isize + 1,  // ⚠️ 可能超出 c_int 范围
}
```

**解决**：保持判别值在 `i32::MIN..=i32::MAX`（或 `u32` 范围）内。

**参考**：[PR #147017](https://github.com/rust-lang/rust/pull/147017)

---

## repr(transparent) 忽略 repr(C) 警告

**变更**：在 `repr(transparent)` 中忽略 `repr(C)` 类型将产生 future-incompatibility 警告。

**示例**：

```rust
#[repr(transparent)]
struct Wrapper(OtherReprC);  // 若 OtherReprC 为 repr(C) 且被忽略
```

**解决**：检查 `repr(transparent)` 的包装类型，确保符合 [Reference](https://doc.rust-lang.org/reference/type-layout.html#transparent-representations) 要求。

**参考**：[PR #147185](https://github.com/rust-lang/rust/pull/147185)

---

## 相关文档

- [Rust 1.93 兼容性注意事项](./06_rust_1.93_compatibility_notes.md)
- [Rust 1.93 vs 1.92 对比](./05_rust_1.93_vs_1.92_comparison.md)
- [Rust 1.93 完整变更清单](./07_rust_1.93_full_changelog.md)
- [releases.rs 1.93.0](https://releases.rs/docs/1.93.0/)

---

**最后对照 releases.rs**: 2026-02-14
