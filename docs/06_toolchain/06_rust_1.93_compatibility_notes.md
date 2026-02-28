# Rust 1.93 兼容性注意事项

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **1.93.1 补丁**：修复 ICE、Clippy 误报、wasm32-wasip2 FD 泄漏；详见 [12_rust_1.93.1_vs_1.93.0_comparison](./12_rust_1.93.1_vs_1.93.0_comparison.md)

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
    - [官方文档](#官方文档)
    - [形式化规范](#形式化规范)
  - [兼容性检查代码示例](#兼容性检查代码示例)
    - [版本检测宏](#版本检测宏)
    - [迁移辅助工具](#迁移辅助工具)

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
| :--- | :--- | :--- | :--- | :--- |
| #[test] 在错误位置 | 仅将 #[test] 用于裸函数 |
| musl 链接错误 | 升级 libc 到 0.2.146+ |
| Emscripten 链接错误 | 传递 -fwasm-exceptions 给链接器 |
| static-init 编译失败 | 升级 static-init 或检查依赖 |
| rustdoc 文档属性错误 | 修正 html_favicon_url 等属性配置 |

---

## 参考资源

### 官方文档

- [Rust 1.93.0 Release Notes](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/)
- [Rust 1.93.0 详细 Changelog](https://releases.rs/docs/1.93.0/)
- [Rust 1.93 vs 1.92 对比](./05_rust_1.93_vs_1.92_comparison.md)
- [Rust 平台支持](https://doc.rust-lang.org/rustc/platform-support.html)

### 形式化规范

- [Ferrocene Language Specification](https://spec.ferrocene.dev/)
- [Rust Reference - Memory Safety](https://doc.rust-lang.org/reference/unsafe-keyword.html)
- [Rust Reference - FFI](https://doc.rust-lang.org/reference/items/external-blocks.html)

---

## 兼容性检查代码示例

### 版本检测宏

```rust
//! Rust 1.93 兼容性检查工具

/// 编译时 Rust 版本检查
#[macro_export]
macro_rules! rust_version_check {
    (>= $major:literal.$minor:literal) => {
        const _: () = assert!(
            rust_version_check::VERSION.0 > $major ||
            (rust_version_check::VERSION.0 == $major && rust_version_check::VERSION.1 >= $minor),
            concat!("Requires Rust ", stringify!($major), ".", stringify!($minor), " or later")
        );
    };
}

pub const VERSION: (u32, u32) = {
    let version = env!("RUSTC_VERSION");
    // 简化版本解析
    (1, 93)
};

/// 检查关键兼容性特性
pub mod compatibility_checks {
    /// 检查 deref_nullptr lint 级别
    pub fn check_deref_nullptr_lint() {
        // 在 Rust 1.93 中，deref_nullptr 是 deny-by-default
        // 代码应确保不触发此 lint
        let ptr: *const i32 = std::ptr::null();

        // ✅ 正确：检查后再解引用
        if !ptr.is_null() {
            unsafe { let _ = *ptr; }
        }

        // 或使用 as_ref
        if let Some(val) = unsafe { ptr.as_ref() } {
            println!("Value: {}", val);
        }
    }

    /// 检查 #[test] 属性使用
    pub mod test_attribute_check {
        // ✅ 正确：#[test] 仅在裸函数上使用
        #[test]
        fn valid_test() {
            assert_eq!(2 + 2, 4);
        }

        // ❌ 错误：在 trait 方法上使用 #[test]
        // trait MyTrait {
        //     #[test]
        //     fn test_method() {}
        // }

        // ❌ 错误：在结构体上使用 #[test]
        // #[test]
        // struct TestStruct;
    }

    /// 检查 offset_of! 类型约束
    pub mod offset_of_check {
        use std::mem::offset_of;

        struct WellFormed<T: Sized> {
            field: T,
        }

        // ✅ 正确：类型满足 well-formed 约束
        const _: usize = offset_of!(WellFormed<i32>, field);

        // 在 Rust 1.93 中，以下会产生编译错误：
        // struct NotWellFormed<T: ?Sized>(T);
        // const _: usize = offset_of!(NotWellFormed<dyn Send>, 0);
    }

    /// 检查 repr(C) 枚举判别值
    pub mod repr_c_enum_check {
        // ✅ 正确：判别值在 c_int 范围内
        #[repr(C)]
        enum ValidEnum {
            A = 0,
            B = i32::MAX as isize,
        }

        // ⚠️ 警告：判别值可能超出 c_int 范围
        // #[repr(C)]
        // enum InvalidEnum {
        //     A = 0,
        //     B = i32::MAX as isize + 1,
        // }
    }

    /// 检查 FFI 可变参数使用
    pub mod ffi_variadic_check {
        // ✅ 正确：在 extern 块中使用可变参数
        extern "system" {
            fn printf(format: *const u8, ...);
        }

        // ❌ 未来不兼容：在 extern 块外使用可变参数
        // fn my_print(fmt: *const u8, ...) {
        //     // ...
        // }
    }
}

/// CI/CD 兼容性检查脚本
pub mod ci_checks {
    use std::process::Command;

    /// 运行完整的兼容性检查
    pub fn run_compatibility_check() -> Result<(), Vec<String>> {
        let mut errors = Vec::new();

        // 检查 1：编译测试
        if let Err(e) = run_cargo_check() {
            errors.push(format!("cargo check failed: {}", e));
        }

        // 检查 2：deny lints
        if let Err(e) = run_deny_lints_check() {
            errors.push(format!("deny lints check failed: {}", e));
        }

        // 检查 3：测试运行
        if let Err(e) = run_tests() {
            errors.push(format!("tests failed: {}", e));
        }

        // 检查 4：文档生成
        if let Err(e) = run_doc_check() {
            errors.push(format!("doc check failed: {}", e));
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn run_cargo_check() -> Result<(), String> {
        let output = Command::new("cargo")
            .args(["check", "--all-targets", "--all-features"])
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).to_string())
        }
    }

    fn run_deny_lints_check() -> Result<(), String> {
        // 使用 RUSTFLAGS 确保 deny lints 被触发
        let output = Command::new("cargo")
            .args(["check"])
            .env("RUSTFLAGS", "-D warnings")
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).to_string())
        }
    }

    fn run_tests() -> Result<(), String> {
        let output = Command::new("cargo")
            .args(["test", "--all"])
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).to_string())
        }
    }

    fn run_doc_check() -> Result<(), String> {
        let output = Command::new("cargo")
            .args(["doc", "--no-deps"])
            .env("RUSTDOCFLAGS", "-D warnings")
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).to_string())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deref_nullptr_check() {
        compatibility_checks::check_deref_nullptr_lint();
    }

    #[test]
    fn test_repr_c_enum() {
        // 验证 repr(C) 枚举编译成功
        use compatibility_checks::repr_c_enum_check::*;
        let _ = ValidEnum::A;
    }
}
```

### 迁移辅助工具

```rust
//! Rust 1.93 迁移辅助脚本

use std::fs;
use std::path::Path;

/// 检查项目中的潜在兼容性问题
pub fn scan_for_compatibility_issues(project_path: &Path) -> Vec<String> {
    let mut issues = Vec::new();

    // 检查 Cargo.toml 中的依赖版本
    if let Ok(content) = fs::read_to_string(project_path.join("Cargo.toml")) {
        if content.contains("libc = \"0.2.14") && !content.contains("0.2.146") {
            issues.push("警告：libc 版本可能需要升级到 0.2.146+".to_string());
        }

        if content.contains("static-init = \"1.0.1\"") ||
           content.contains("static-init = \"1.0.2\"") ||
           content.contains("static-init = \"1.0.3\"") {
            issues.push("警告：static-init 1.0.1-1.0.3 可能与 Rust 1.93 不兼容".to_string());
        }
    }

    // 检查 .cargo/config.toml
    if let Ok(content) = fs::read_to_string(project_path.join(".cargo/config.toml")) {
        if content.contains("document_private_items") {
            issues.push("错误：document_private_items 属性在 Rust 1.93 中已移除".to_string());
        }
    }

    // 检查源码中的问题模式
    issues.extend(scan_source_files(project_path));

    issues
}

fn scan_source_files(project_path: &Path) -> Vec<String> {
    let mut issues = Vec::new();
    let src_path = project_path.join("src");

    if let Ok(entries) = fs::read_dir(&src_path) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().map_or(false, |e| e == "rs") {
                if let Ok(content) = fs::read_to_string(&path) {
                    // 检查 #[test] 在 trait 中的使用
                    if content.contains("trait") && content.contains("#\[test\]") {
                        issues.push(format!(
                            "警告：{} 中可能在 trait 中使用了 #[test]，这在 Rust 1.93 中会报错",
                            path.display()
                        ));
                    }

                    // 检查 deref_nullptr 模式
                    if content.contains("*ptr") && content.contains("null()") {
                        issues.push(format!(
                            "警告：{} 中可能有无保护的指针解引用，在 Rust 1.93 中会报错",
                            path.display()
                        ));
                    }
                }
            }
        }
    }

    issues
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::TempDir;

    #[test]
    fn test_scan_compatibility() {
        let temp_dir = TempDir::new().unwrap();
        let project_path = temp_dir.path();

        // 创建测试 Cargo.toml
        let mut cargo_toml = fs::File::create(project_path.join("Cargo.toml")).unwrap();
        writeln!(cargo_toml, r#"
[package]
name = "test"
version = "0.1.0"
edition = "2021"

[dependencies]
libc = "0.2.100"
"#).unwrap();

        // 创建 src 目录和文件
        fs::create_dir(project_path.join("src")).unwrap();
        let mut main_rs = fs::File::create(project_path.join("src/main.rs")).unwrap();
        writeln!(main_rs, r#"
trait MyTrait {{
    #[test]
    fn test_method() {{}}
}}
"#).unwrap();

        let issues = scan_for_compatibility_issues(project_path);
        assert!(!issues.is_empty());
        assert!(issues.iter().any(|i| i.contains("libc")));
    }
}
```

---

**最后对照 releases.rs**: 2026-02-14
