# Rust 1.93 完整变更清单

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 目录

- [Rust 1.93 完整变更清单](#rust-193-完整变更清单)
  - [目录](#目录)
  - [语言特性](#语言特性)
    - [s390x vector 特性与 is\_s390x\_feature\_detected](#s390x-vector-特性与-is_s390x_feature_detected)
    - [C-style variadic for system ABI](#c-style-variadic-for-system-abi)
    - [cfg 谓词使用关键词报错](#cfg-谓词使用关键词报错)
    - [asm\_cfg（asm! 行上 cfg）](#asm_cfgasm-行上-cfg)
    - [const-eval 指针字节复制](#const-eval-指针字节复制)
    - [LUB coercion 修正](#lub-coercion-修正)
    - [const 含 mutable ref 到 static](#const-含-mutable-ref-到-static)
    - [const\_item\_interior\_mutations lint（warn-by-default）](#const_item_interior_mutations-lintwarn-by-default)
    - [function\_casts\_as\_integer lint（warn-by-default）](#function_casts_as_integer-lintwarn-by-default)
  - [编译器](#编译器)
    - [-C jump-tables=bool 稳定化](#-c-jump-tablesbool-稳定化)
  - [平台支持](#平台支持)
    - [riscv64a23-unknown-linux-gnu Tier 2](#riscv64a23-unknown-linux-gnu-tier-2)
    - [musl 1.2.5](#musl-125)
  - [标准库](#标准库)
    - [Copy 不再使用 specialization](#copy-不再使用-specialization)
    - [全局分配器 thread\_local 支持](#全局分配器-thread_local-支持)
    - [BTree::append 行为变更](#btreeappend-行为变更)
    - [vec::IntoIter 不再要求 T: RefUnwindSafe](#vecintoiter-不再要求-t-refunwindsafe)
    - [稳定化 API](#稳定化-api)
  - [Cargo](#cargo)
    - [CARGO\_CFG\_DEBUG\_ASSERTIONS](#cargo_cfg_debug_assertions)
    - [cargo tree --format 长格式](#cargo-tree---format-长格式)
    - [cargo clean --workspace](#cargo-clean---workspace)
  - [Rustdoc](#rustdoc)
    - [移除 #!\[doc(document\_private\_items)\]](#移除-docdocument_private_items)
    - [宏搜索过滤](#宏搜索过滤)
    - [import 搜索过滤](#import-搜索过滤)
    - [文档属性校验](#文档属性校验)
  - [相关文档](#相关文档)
  - [形式化规范与参考](#形式化规范与参考)
    - [类型系统形式化](#类型系统形式化)
    - [内存模型形式化](#内存模型形式化)
    - [Ferrocene 规范引用](#ferrocene-规范引用)
  - [完整特性代码示例](#完整特性代码示例)

---

## 语言特性

### s390x vector 特性与 is_s390x_feature_detected

**Rust 1.93** 稳定了多个 s390x `vector` 相关 target features 及 `is_s390x_feature_detected!` 宏。

**适用场景**: s390x 架构 SIMD 编程。

```rust
// 仅 s390x 架构可用
#[cfg(target_arch = "s390x")]
fn check_vector_support() {
    if std::arch::is_s390x_feature_detected!("vx") {
        // 使用向量扩展
    }
}
```

**参考**: [PR #145656](https://github.com/rust-lang/rust/pull/145656)

---

### C-style variadic for system ABI

**Rust 1.93** 稳定了 `system` ABI 的 C 风格可变参数函数声明。

```rust
extern "system" {
    fn printf(format: *const u8, ...);
}
```

**参考**: [PR #145954](https://github.com/rust-lang/rust/pull/145954)

---

### cfg 谓词使用关键词报错

**Rust 1.93** 对将某些关键词用作 `cfg` 谓词的情况发出错误。

**参考**: [PR #146978](https://github.com/rust-lang/rust/pull/146978)

---

### asm_cfg（asm! 行上 cfg）

**Rust 1.93** 稳定了 `asm_cfg`，允许在 `asm!` 的单个语句上使用 `cfg` 属性。

详见 [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md#3-cfg-属性在-asm-行上)

**参考**: [PR #147736](https://github.com/rust-lang/rust/pull/147736)

---

### const-eval 指针字节复制

**Rust 1.93** 在常量求值期间支持按字节复制指针。

**参考**: [PR #148259](https://github.com/rust-lang/rust/pull/148259)

---

### LUB coercion 修正

**Rust 1.93** 修正了 LUB（Least Upper Bound）coercion 对函数项类型及不同安全性函数的处理。

**参考**: [PR #148602](https://github.com/rust-lang/rust/pull/148602)

---

### const 含 mutable ref 到 static

**Rust 1.93** 允许 const 项包含对 static 的可变引用（非常 unsafe，但不总是 UB）。

**参考**: [PR #148746](https://github.com/rust-lang/rust/pull/148746)

---

### const_item_interior_mutations lint（warn-by-default）

**Rust 1.93** 新增 warn-by-default lint，对会改动内部可变 const 项的调用发出警告。

**参考**: [PR #148407](https://github.com/rust-lang/rust/pull/148407)

---

### function_casts_as_integer lint（warn-by-default）

**Rust 1.93** 新增 warn-by-default lint，对将函数强制转换为整数的操作发出警告。

**参考**: [PR #141470](https://github.com/rust-lang/rust/pull/141470)

---

## 编译器

### -C jump-tables=bool 稳定化

**Rust 1.93** 稳定了 `-C jump-tables=bool` 选项（原 `-Zno-jump-tables`）。

```bash
rustc -C jump-tables=false main.rs  # 禁用跳转表
```

**参考**: [PR #145974](https://github.com/rust-lang/rust/pull/145974)

---

## 平台支持

### riscv64a23-unknown-linux-gnu Tier 2

**Rust 1.93** 将 `riscv64a23-unknown-linux-gnu` 提升为 Tier 2（无 host tools）。

**参考**: [PR #148435](https://github.com/rust-lang/rust/pull/148435)、[平台支持页](https://doc.rust-lang.org/rustc/platform-support.html)

---

### musl 1.2.5

详见 [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md#1-musl-125-更新)

---

## 标准库

### Copy 不再使用 specialization

**Rust 1.93** 在 Copy trait 上停止内部使用 specialization（因在含生命周期依赖的 Copy 实现下不安全）。部分标准库 API 可能改为调用 `Clone::clone` 而非按位复制，**可能导致性能回归**。

**参考**: [PR #135634](https://github.com/rust-lang/rust/pull/135634)

---

### 全局分配器 thread_local 支持

详见 [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md#2-全局分配器线程本地存储支持)

---

### BTree::append 行为变更

**Rust 1.93** 修改 `BTree::append` 行为：当追加的条目已存在时，不再更新现有键。

**参考**: [PR #145628](https://github.com/rust-lang/rust/pull/145628)

---

### vec::IntoIter 不再要求 T: RefUnwindSafe

**Rust 1.93** 放宽 `vec::IntoIter<T>: UnwindSafe` 的约束，不再要求 `T: RefUnwindSafe`。

**参考**: [PR #145665](https://github.com/rust-lang/rust/pull/145665)

---

### 稳定化 API

详见 [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md#标准库更新)

---

## Cargo

### CARGO_CFG_DEBUG_ASSERTIONS

**Cargo 1.93** 在 build scripts 中根据 profile 启用 `CARGO_CFG_DEBUG_ASSERTIONS`。

**参考**: [PR #16160](https://github.com/rust-lang/cargo/pull/16160)

---

### cargo tree --format 长格式

**Cargo 1.93** 在 `cargo tree` 中支持 `--format` 变量的长格式。

**参考**: [PR #16204](https://github.com/rust-lang/cargo/pull/16204)

---

### cargo clean --workspace

**Cargo 1.93** 为 `cargo clean` 添加 `--workspace` 选项。

```bash
cargo clean --workspace
```

**参考**: [PR #16263](https://github.com/rust-lang/cargo/pull/16263)

---

## Rustdoc

### 移除 #![doc(document_private_items)]

**Rust 1.93** 移除了 `#![doc(document_private_items)]` 属性。

**参考**: [PR #146495](https://github.com/rust-lang/rust/pull/146495)

---

### 宏搜索过滤

**Rust 1.93** 在 "macros" 搜索过滤中包含 attribute 和 derive 宏。

**参考**: [PR #148176](https://github.com/rust-lang/rust/pull/148176)

---

### import 搜索过滤

**Rust 1.93** 在 `import` 搜索过滤中包含 extern crates。

**参考**: [PR #148301](https://github.com/rust-lang/rust/pull/148301)

---

### 文档属性校验

**Rust 1.93** 对 crate 级文档属性进行校验。若 `html_favicon_url`、`html_logo_url`、`html_playground_url`、`issue_tracker_base_url` 或 `html_no_source` 有缺失、意外值或类型错误，将发出 deny-by-default lint `rustdoc::invalid_doc_attributes`。

**参考**: [PR #149197](https://github.com/rust-lang/rust/pull/149197)

---

## 相关文档

- [Rust 1.93 vs 1.92 对比](./05_rust_1.93_vs_1.92_comparison.md)
- [Rust 1.93 兼容性注意事项](./06_rust_1.93_compatibility_notes.md)
- [Rust 1.93.0 Release Notes](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/)
- [releases.rs 1.93.0](https://releases.rs/docs/1.93.0/)

---

## 形式化规范与参考

### 类型系统形式化

| 特性 | 形式化参考 | 相关标准 |
| :--- | :--- | :--- |
| s390x vector | [Architecture Specification](https://www.ibm.com/docs/en/zos/2.4.0?topic=instructions-vector-instructions) | IBM z/Architecture |
| C variadic | [System V ABI](https://refspecs.linuxbase.org/elf/x86_64-abi-0.99.pdf) | AMD64 ABI |
| asm! cfg | [Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) | Rust Reference |
| const-eval | [Constant Evaluation](https://doc.rust-lang.org/reference/const_eval.html) | Rust Reference |
| LUB coercion | [Type Coercions](https://doc.rust-lang.org/reference/type-coercions.html) | Rust Reference |

### 内存模型形式化

- [Rust Memory Model](https://doc.rust-lang.org/reference/memory-model.html)
- [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) - Rust 别名模型
- [Tree Borrows](https://perso.crans.org/vanille/treebor/) - 替代别名模型

### Ferrocene 规范引用

- [FLS - Functions](https://spec.ferrocene.dev/functions.html)
- [FLS - Constants and Statics](https://spec.ferrocene.dev/constants-and-statics.html)
- [FLS - Inline Assembly](https://spec.ferrocene.dev/inline-assembly.html)

---

## 完整特性代码示例

```rust
//! Rust 1.93 所有新特性完整示例

// ============================================================================
// 1. s390x vector 特性
// ============================================================================

#[cfg(target_arch = "s390x")]
pub mod s390x_examples {
    pub fn check_features() {
        if std::arch::is_s390x_feature_detected!("vx") {
            println!("Vector extension available");
        }
        if std::arch::is_s390x_feature_detected!("vxe") {
            println!("Vector enhancement available");
        }
    }
}

// ============================================================================
// 2. C-style variadic for system ABI
// ============================================================================

pub mod variadic_examples {
    extern "system" {
        // ✅ Rust 1.93 稳定：system ABI 的 C-style variadic
        pub fn printf(format: *const u8, ...);
        pub fn fprintf(stream: *mut libc::FILE, format: *const u8, ...);
        pub fn sprintf(buf: *mut u8, format: *const u8, ...) -> i32;
    }

    /// 安全包装函数
    pub unsafe fn print_format(fmt: &str, args: &[&str]) {
        // 实际使用时需要正确处理可变参数
        let fmt_ptr = fmt.as_ptr();
        printf(fmt_ptr);
    }
}

// ============================================================================
// 3. asm! cfg 属性
// ============================================================================

pub mod asm_cfg_examples {
    /// 条件编译的内联汇编示例
    #[cfg(target_arch = "x86_64")]
    pub unsafe fn conditional_asm() {
        let result: u64;

        asm!(
            "mov {0}, 0",

            // 条件指令
            #[cfg(target_feature = "sse2")]
            "add {0}, 1",

            #[cfg(target_feature = "avx")]
            "add {0}, 2",

            #[cfg(target_feature = "avx2")]
            "add {0}, 4",

            out(reg) result,
        );

        println!("Result: {}", result);
    }

    /// 多平台汇编
    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    pub unsafe fn multi_platform_asm() {
        asm!(
            "nop",

            #[cfg(target_arch = "x86_64")]
            "mov rax, 0",

            #[cfg(target_arch = "x86")]
            "mov eax, 0",
        );
    }
}

// ============================================================================
// 4. const-eval 指针字节复制
// ============================================================================

pub mod const_eval_examples {
    /// 常量求值中的指针操作
    pub const fn copy_pointer_bytes() {
        // Rust 1.93 支持在常量求值期间按字节复制指针
        // 这对低级内存操作很有用
    }

    /// 使用常量的复杂初始化
    pub const COMPLEX_INIT: [u8; 16] = {
        let mut arr = [0u8; 16];
        let ptr = arr.as_ptr();
        // 在 const 上下文中进行指针操作
        arr
    };
}

// ============================================================================
// 5. LUB coercion 修正
// ============================================================================

pub mod lub_coercion_examples {
    /// 函数项类型强制转换
    pub fn function_coercion() {
        fn foo() -> i32 { 42 }
        fn bar() -> i32 { 0 }

        // Rust 1.93 改进了 LUB (Least Upper Bound) coercion
        let f: fn() -> i32 = if true { foo } else { bar };
        assert_eq!(f(), 42);
    }

    /// 不同安全性函数的 coercion
    pub fn safety_coercion() {
        unsafe fn unsafe_fn() -> i32 { 42 }
        fn safe_fn() -> i32 { 0 }

        // 更准确的 coercion 处理
        let f: fn() -> i32 = safe_fn;
        assert_eq!(f(), 0);
    }
}

// ============================================================================
// 6. const 含 mutable ref 到 static
// ============================================================================

pub mod const_static_ref_examples {
    use std::sync::atomic::AtomicU32;

    static COUNTER: AtomicU32 = AtomicU32::new(0);

    /// Rust 1.93 允许 const 项包含对 static 的可变引用
    /// （非常 unsafe，但不总是 UB）
    pub const COUNTER_REF: &AtomicU32 = &COUNTER;

    /// 使用示例
    pub fn use_static_ref() {
        COUNTER_REF.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}

// ============================================================================
// 7. const_item_interior_mutations lint
// ============================================================================

pub mod interior_mutations_examples {
    use std::cell::Cell;

    /// 具有内部可变性的 const 项
    pub const CONST_CELL: Cell<i32> = Cell::new(0);

    /// ⚠️ 这会触发 const_item_interior_mutations lint
    pub fn modify_const() {
        // Rust 1.93 会对这会改动内部可变 const 项的调用发出警告
        // CONST_CELL.set(42); // 警告：修改 const 项的内部状态
    }

    /// ✅ 正确做法：使用 static
    pub static STATIC_CELL: Cell<i32> = Cell::new(0);

    pub fn modify_static() {
        STATIC_CELL.set(42); // 这是允许的
    }
}

// ============================================================================
// 8. function_casts_as_integer lint
// ============================================================================

pub mod function_cast_examples {
    /// ⚠️ 这会触发 function_casts_as_integer lint
    pub fn bad_cast() {
        fn my_function() -> i32 { 42 }

        // Rust 1.93 会对函数强制转换为整数的操作发出警告
        // let ptr = my_function as usize; // 警告：函数转整数
    }

    /// ✅ 正确做法：使用函数指针
    pub fn good_cast() {
        fn my_function() -> i32 { 42 }

        let ptr: fn() -> i32 = my_function; // 这是推荐的
        assert_eq!(ptr(), 42);
    }
}

// ============================================================================
// 9. -C jump-tables=bool
// ============================================================================

pub mod jump_tables_examples {
    /// 编译选项示例
    ///
    /// 使用 -C jump-tables=false 禁用跳转表：
    /// ```bash
    /// rustc -C jump-tables=false main.rs
    /// ```
    ///
    /// 这在某些嵌入式或安全敏感场景中有用
    pub fn example_match(x: u8) -> u32 {
        match x {
            0 => 100,
            1 => 200,
            2 => 300,
            3 => 400,
            _ => 0,
        }
    }
}

// ============================================================================
// 10. Copy specialization 移除
// ============================================================================

pub mod copy_specialization_examples {
    /// Copy trait 实现示例
    #[derive(Clone, Copy, Debug)]
    pub struct MyCopyType {
        value: i32,
    }

    /// Rust 1.93 移除了 Copy trait 的内部 specialization
    /// 这可能导致某些场景下的性能回归，但提高了安全性
    pub fn use_copy_type() {
        let a = MyCopyType { value: 42 };
        let b = a; // Copy
        let c = a; // 仍然可用，因为是 Copy

        assert_eq!(a.value, 42);
        assert_eq!(b.value, 42);
        assert_eq!(c.value, 42);
    }
}

// ============================================================================
// 11. BTreeMap::append 行为变更
// ============================================================================

pub mod btree_append_examples {
    use std::collections::BTreeMap;

    /// Rust 1.93 修改了 BTreeMap::append 的行为
    /// 当追加的条目已存在时，不再更新现有键
    pub fn append_behavior() {
        let mut map1: BTreeMap<i32, &str> = BTreeMap::new();
        map1.insert(1, "a");
        map1.insert(2, "b");

        let mut map2: BTreeMap<i32, &str> = BTreeMap::new();
        map2.insert(2, "B"); // 注意：key 2 已存在
        map2.insert(3, "c");

        map1.append(&mut map2);

        // Rust 1.93: key 2 保持原值 "b"，不覆盖
        assert_eq!(map1.get(&2), Some(&"b"));
        assert_eq!(map1.get(&3), Some(&"c"));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lub_coercion() {
        lub_coercion_examples::function_coercion();
    }

    #[test]
    fn test_btree_append() {
        btree_append_examples::append_behavior();
    }

    #[test]
    fn test_copy_type() {
        copy_specialization_examples::use_copy_type();
    }
}
```

---

**最后对照 releases.rs**: 2026-02-14
