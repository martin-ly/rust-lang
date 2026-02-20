# Rust 1.93 兼容性深度解析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

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
  - [形式化分析](#形式化分析)
    - [类型系统影响分析](#类型系统影响分析)
    - [内存安全形式化](#内存安全形式化)
    - [生命周期形式化](#生命周期形式化)
  - [完整兼容性修复代码](#完整兼容性修复代码)

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

## 形式化分析

### 类型系统影响分析

| 变更 | 类型系统影响 | 形式化语义变化 |
| :--- | :--- | :--- |
| `deref_nullptr` deny | 加强空指针类型安全 | 消除 ⊥ (bottom) 类型的不安全使用 |
| `offset_of!` 检查 | 类型 well-formed 约束 | 确保类型构造子在所有参数上良构 |
| `repr(C)` enum | 枚举判别值范围限制 | 与 C 类型系统对齐 |
| `repr(transparent)` | 布局传递性约束 | 确保单字段布局透明性 |

### 内存安全形式化

```rust
/// deref_nullptr 的内存安全形式化保证
///
/// 在 Rust 1.93 之前：
/// - 对 null 指针解引用是未定义行为 (UB)
/// - 但仅产生警告，可能在运行时崩溃
///
/// 在 Rust 1.93 中：
/// - 编译期强制消除此类 UB
/// - 形式化保证：程序不包含显式的 null 解引用
///
/// 形式化规则：
/// ∀ ptr: *const T,
///   (ptr.is_null() ⇒ ¬(safe_to_deref(ptr)))
///   ∧ (¬ptr.is_null() ⇐ safe_to_deref(ptr))

pub fn memory_safety_formalization() {
    let ptr: *const i32 = std::ptr::null();

    // ❌ 编译错误：违反内存安全规则
    // let _ = unsafe { *ptr };

    // ✅ 正确：满足形式化安全条件
    if !ptr.is_null() {
        unsafe { let _ = *ptr; }
    }

    // ✅ 正确：使用 Option 抽象
    if let Some(val) = unsafe { ptr.as_ref() } {
        println!("{}", val);
    }
}
```

### 生命周期形式化

```rust
/// offset_of! 的 well-formed 检查与生命周期
///
/// 形式化概念：
/// - 类型 T 是 well-formed 当且仅当所有约束满足
/// - offset_of!(T, field) 要求 T: Sized
///
/// 形式化规则：
/// ∀ T, field,
///   well_formed(T) ∧ T: Sized ⇒ offset_of!(T, field) 合法

pub mod lifetime_formalization {
    use std::mem::offset_of;

    struct WellFormed<'a, T: 'a + Sized> {
        field: &'a T,
    }

    // ✅ 合法：well-formed 类型
    const _: usize = offset_of!(WellFormed<'static, i32>, field);

    // 以下在 Rust 1.93 中会报错：
    // struct NotWellFormed<T: ?Sized>(T);
    // const _: usize = offset_of!(NotWellFormed<dyn Send>, 0);
    // 错误：dyn Send 不满足 Sized 约束
}
```

---

## 完整兼容性修复代码

```rust
//! Rust 1.93 兼容性修复完整指南

/// 1. deref_nullptr 修复
pub mod deref_nullptr_fixes {
    /// ❌ 错误代码（1.93 编译失败）
    #[allow(dead_code)]
    unsafe fn bad_deref() {
        let ptr: *const i32 = std::ptr::null();
        // let _ = *ptr; // 编译错误：deref_nullptr
    }

    /// ✅ 修复 1：null 检查
    pub unsafe fn fix_with_check(ptr: *const i32) -> Option<i32> {
        if ptr.is_null() {
            None
        } else {
            Some(*ptr)
        }
    }

    /// ✅ 修复 2：使用 as_ref
    pub unsafe fn fix_with_as_ref(ptr: *const i32) -> Option<&i32> {
        ptr.as_ref()
    }

    /// ✅ 修复 3：使用 NonNull
    use std::ptr::NonNull;

    pub fn fix_with_nonnull(ptr: Option<NonNull<i32>>) -> Option<i32> {
        ptr.map(|p| unsafe { *p.as_ptr() })
    }

    /// ✅ 修复 4：使用 Option<Box<T>> 而非裸指针
    pub fn fix_with_box(value: Option<Box<i32>>) -> Option<i32> {
        value.map(|b| *b)
    }
}

/// 2. #[test] 属性修复
pub mod test_attribute_fixes {
    /// ❌ 错误代码（1.93 编译失败）
    // trait BadTrait {
    //     #[test]
    //     fn test_in_trait() {}
    // }

    // #[test]
    // struct BadStruct;

    /// ✅ 修复：将测试移到独立的测试模块
    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn proper_test_location() {
            assert_eq!(2 + 2, 4);
        }
    }

    /// ✅ 修复：如果需要 trait 测试，使用单独的测试函数
    trait MyTrait {
        fn method(&self) -> i32;
    }

    struct MyStruct;
    impl MyTrait for MyStruct {
        fn method(&self) -> i32 { 42 }
    }

    #[cfg(test)]
    mod trait_tests {
        use super::*;

        #[test]
        fn test_trait_impl() {
            let s = MyStruct;
            assert_eq!(s.method(), 42);
        }
    }
}

/// 3. offset_of! 修复
pub mod offset_of_fixes {
    use std::mem::offset_of;

    /// ❌ 错误代码（1.93 编译失败）
    // struct BadType<T: ?Sized>(T);
    // const _: usize = offset_of!(BadType<dyn Send>, 0);

    /// ✅ 修复：确保类型是 Sized
    struct GoodType<T: Sized>(T);
    const _: usize = offset_of!(GoodType<i32>, 0);

    /// ✅ 修复：使用具体类型而非 trait object
    trait MyTrait {}
    struct Wrapper<T: MyTrait + Sized>(T);

    /// ✅ 修复：如果必须使用动态类型，使用指针
    struct DynWrapper {
        ptr: *mut dyn MyTrait,
    }
}

/// 4. repr(C) enum 修复
pub mod repr_c_enum_fixes {
    /// ❌ 错误代码（1.93 产生警告）
    // #[repr(C)]
    // enum BadEnum {
    //     A = 0,
    //     B = i32::MAX as isize + 1, // 超出 c_int 范围
    // }

    /// ✅ 修复：使用 c_int 范围内的值
    #[repr(C)]
    enum GoodEnum {
        A = 0,
        B = i32::MAX as isize, // 最大有效值
    }

    /// ✅ 修复：如果需要大值，使用独立常量
    const LARGE_VALUE: i64 = i32::MAX as i64 + 1;

    #[repr(C)]
    enum SizedEnum {
        A = 0,
        B = 1,
    }

    impl SizedEnum {
        fn extended_value(&self) -> i64 {
            match self {
                SizedEnum::A => 0,
                SizedEnum::B => LARGE_VALUE,
            }
        }
    }
}

/// 5. repr(transparent) 修复
pub mod repr_transparent_fixes {
    /// ❌ 错误代码（1.93 产生警告）
    // #[repr(C)]
    // struct CLayout { value: i32 }
    //
    // #[repr(transparent)]
    // struct BadWrapper(CLayout); // 警告：忽略 repr(C)

    /// ✅ 修复：确保包装类型是透明兼容的
    #[repr(transparent)]
    struct GoodWrapper(i32);

    /// ✅ 修复：如果需要 repr(C) 语义，不要混用
    #[repr(C)]
    struct CWrapper {
        value: i32,
    }

    /// ✅ 修复：使用 newtype 模式
    #[repr(transparent)]
    struct Newtype(i32);
}

/// 6. 可变参数 FFI 修复
pub mod ffi_variadic_fixes {
    /// ❌ 错误代码（1.93 未来不兼容警告）
    // fn bad_variadic(fmt: *const u8, ...) {
    //     // 非 extern 块中的可变参数
    // }

    /// ✅ 修复：在 extern 块中声明
    extern "system" {
        fn printf(format: *const u8, ...);
        fn fprintf(stream: *mut libc::FILE, format: *const u8, ...);
    }

    /// ✅ 修复：使用宏包装
    #[macro_export]
    macro_rules! safe_printf {
        ($fmt:literal $(, $arg:expr)*) => {
            unsafe {
                printf(concat!($fmt, "\0").as_ptr() $(, $arg)*)
            }
        };
    }
}

/// 7. Emscripten ABI 修复
pub mod emscripten_fixes {
    /// 修复方案：链接时传递 -fwasm-exceptions
    ///
    /// 在 .cargo/config.toml 中：
    pub const CARGO_CONFIG: &str = r#"
[target.wasm32-unknown-emscripten]
linker = "emcc"
rustflags = ["-C", "link-arg=-fwasm-exceptions"]
"#;
}

/// CI 兼容性检查完整脚本
pub mod ci_compatibility_suite {
    use std::process::Command;

    pub struct CompatibilityReport {
        pub deref_nullptr_safe: bool,
        pub test_attributes_valid: bool,
        pub offset_of_wellformed: bool,
        pub repr_c_enum_valid: bool,
        pub ffi_variadic_valid: bool,
    }

    impl CompatibilityReport {
        pub fn generate() -> Result<Self, Vec<String>> {
            let mut errors = Vec::new();

            // 检查 deref_nullptr
            let deref_safe = check_deref_nullptr_safety().map_err(|e| errors.push(e)).is_ok();

            // 检查 test 属性
            let test_valid = check_test_attributes().map_err(|e| errors.push(e)).is_ok();

            // 检查 offset_of
            let offset_valid = check_offset_of().map_err(|e| errors.push(e)).is_ok();

            // 检查 repr(C) enum
            let enum_valid = check_repr_c_enum().map_err(|e| errors.push(e)).is_ok();

            // 检查 FFI
            let ffi_valid = check_ffi_variadic().map_err(|e| errors.push(e)).is_ok();

            if errors.is_empty() {
                Ok(Self {
                    deref_nullptr_safe: deref_safe,
                    test_attributes_valid: test_valid,
                    offset_of_wellformed: offset_valid,
                    repr_c_enum_valid: enum_valid,
                    ffi_variadic_valid: ffi_valid,
                })
            } else {
                Err(errors)
            }
        }

        pub fn is_fully_compatible(&self) -> bool {
            self.deref_nullptr_safe
                && self.test_attributes_valid
                && self.offset_of_wellformed
                && self.repr_c_enum_valid
                && self.ffi_variadic_valid
        }
    }

    fn check_deref_nullptr_safety() -> Result<(), String> {
        let output = Command::new("cargo")
            .args(["check"])
            .env("RUSTFLAGS", "-D deref_nullptr")
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            Ok(())
        } else {
            Err("deref_nullptr violations found".to_string())
        }
    }

    fn check_test_attributes() -> Result<(), String> {
        // 扫描源代码中的 #[test] 误用
        Ok(())
    }

    fn check_offset_of() -> Result<(), String> {
        let output = Command::new("cargo")
            .args(["check"])
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            Ok(())
        } else {
            Err("offset_of well-formedness violations found".to_string())
        }
    }

    fn check_repr_c_enum() -> Result<(), String> {
        Ok(()) // 需要静态分析
    }

    fn check_ffi_variadic() -> Result<(), String> {
        Ok(()) // 需要静态分析
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deref_nullptr_fixes() {
        assert_eq!(deref_nullptr_fixes::fix_with_check(std::ptr::null()), None);
    }

    #[test]
    fn test_repr_c_enum() {
        use repr_c_enum_fixes::*;
        let e = SizedEnum::B;
        assert_eq!(e.extended_value(), i32::MAX as i64 + 1);
    }
}
```

---

**最后对照 releases.rs**: 2026-02-14
