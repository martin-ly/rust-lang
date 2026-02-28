# Rust 1.89→1.93 累积特性总览

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 总览表

| 版本 | 发布日期 | 语言 | 库 | 兼容性 | 平台 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 1.90 | 2025-09 | - | - | LLD 默认 | x86_64-apple-darwin 等 |
| 1.91 | 2025-10 | dangling_pointers_from_locals | - | warn-by-default | aarch64-pc-windows-msvc Tier 1 |
| 1.92 | 2025-12 | Never 类型 Lint 严格化 | Box/Rc/Arc::new_zeroed、迭代器特化 | deny-by-default | musl 预告 |
| 1.93 | 2026-01 | s390x、C variadic、LUB coercion、asm_cfg | MaybeUninit、String/Vec、VecDeque、Duration、char、fmt | deref_nullptr、#[test]、offset_of、repr(C) enum | musl 1.2.5、riscv64a23 Tier 2 |
| 1.93.1 | 2026-02 | 无（补丁版） | 无 | ICE/Clippy/WASM 回归修复 | - |

---

## 语言特性累积（1.89→1.93）

| 特性 | 版本 | 说明 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| dangling_pointers_from_locals | 1.91 | 局部悬垂指针 lint |
| Never 类型 Lint 严格化 | 1.92 | never_type_fallback_flowing_into_unsafe、dependency_on_unit_never_type_fallback |
| s390x C-style variadic | 1.93 | variadic 函数调用 |
| LUB coercion | 1.93 | 最小上界强制转换 |
| asm_cfg | 1.93 | cfg 属性在 asm! 行上 |
| const_item_interior_mutations | 1.93 | const 项内部可变 |
| function_casts_as_integer | 1.93 | 函数指针转整数 |

---

## 标准库 API 累积（1.89→1.93）

| 类别 | 版本 | API |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| MaybeUninit | 1.93 | 新方法（write_copy_of_slice 等） |
| String/Vec | 1.93 | into_raw_parts、from_raw_parts |
| VecDeque | 1.93 | pop_front_if、pop_back_if |
| 整数 | 1.93 | unchecked_add、unchecked_sub 等 |
| 切片 | 1.93 | slice.as_array() |
| Duration | 1.93 | from_nanos_u128 |
| char | 1.93 | MAX_LEN_UTF8、MAX_LEN_UTF16 |
| fmt | 1.93 | fmt::from_fn |

### 行为变更（1.93）

| 变更 | 影响 |
| :--- | :--- | :--- | :--- | :--- |
| BTreeMap::append | 相同 key 不再覆盖，保留目标 |
| vec::IntoIter | 实现 RefUnwindSafe |

---

## 兼容性变更累积（1.89→1.93）

| 变更 | 版本 | 详情 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| dangling_pointers_from_locals | 1.91 | warn-by-default |
| Never 类型 Lint | 1.92 | deny-by-default |
| deref_nullptr | 1.93 | deny-by-default |
| #[test] 无效位置 | 1.93 | 报错 |
| offset_of! 类型检查 | 1.93 | 更严格 |
| ... 可变参数 | 1.93 | future-incompat |
| repr(C) enum 警告 | 1.93 | 新警告 |
| pin_v2 | 1.93 | Pin API 变更 |
| Emscripten unwinding | 1.93 | ABI 变更 |

---

## 平台支持累积（1.89→1.93）

| 平台 | 版本 | 变更 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| aarch64-pc-windows-msvc | 1.91 | Tier 1 |
| musl 1.2.5 | 1.93 | DNS 解析改进 |
| riscv64a23-unknown-linux-gnu | 1.93 | Tier 2 |

---

## 工具链累积

| 工具 | 1.93 变更 |
| :--- | :--- | :--- | :--- | :--- |
| Clippy | 新 lint |
| Rustfmt | 格式化规则 |

---

## 相关文档

| 文档 | 路径 |
| :--- | :--- | :--- | :--- | :--- |
| 1.93 vs 1.92 | [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md) |
| 1.93.1 vs 1.93.0 | [12_rust_1.93.1_vs_1.93.0_comparison.md](./12_rust_1.93.1_vs_1.93.0_comparison.md) |
| 1.93 兼容性深度 | [09_rust_1.93_compatibility_deep_dive.md](./09_rust_1.93_compatibility_deep_dive.md) |
| 1.93 完整变更 | [07_rust_1.93_full_changelog.md](./07_rust_1.93_full_changelog.md) |
| 发布追踪清单 | [../07_project/RUST_RELEASE_TRACKING_CHECKLIST.md](../07_project/RUST_RELEASE_TRACKING_CHECKLIST.md) |

---

## 累积特性代码示例

```rust
//! Rust 1.89→1.93 累积特性使用示例

use std::collections::VecDeque;
use std::mem::MaybeUninit;
use std::time::Duration;

/// 累积 API 使用最佳实践
pub mod cumulative_api_usage {
    use super::*;

    /// 1.92+：使用 new_zeroed 创建零初始化容器
    pub fn create_zeroed_containers() {
        // 1.92+ 零初始化 API
        let _boxed = Box::<[u8; 1024]>::new_zeroed();
        let _rc = std::rc::Rc::<[u8; 256]>::new_zeroed();
        let _arc = std::sync::Arc::<[u8; 128]>::new_zeroed();
    }

    /// 1.93+：使用 MaybeUninit 新 API 安全初始化
    pub fn safe_maybe_uninit_init() {
        let src = [1, 2, 3, 4, 5];
        let mut dst = [MaybeUninit::<i32>::uninit(); 5];

        // 1.93+ write_copy_of_slice
        MaybeUninit::write_copy_of_slice(&mut dst, &src);

        // 安全地获取引用和丢弃
        unsafe {
            let _ref = dst[0].assume_init_ref();
            for item in &mut dst {
                item.assume_init_drop();
            }
        }
    }

    /// 1.93+：String/Vec 原始部分操作
    pub fn raw_parts_manipulation() {
        let s = String::with_capacity(100);
        let (ptr, len, cap) = s.into_raw_parts();

        // FFI 操作...

        let _s = unsafe { String::from_raw_parts(ptr, len, cap) };
    }

    /// 1.93+：VecDeque 条件弹出
    pub fn conditional_queue_operations() {
        let mut queue = VecDeque::from([1, 2, 3, 4, 5]);

        // 仅当元素大于 2 时弹出
        while let Some(val) = queue.pop_front_if(|&x| x > 2) {
            println!("Popped: {}", val);
        }
    }

    /// 1.93+：Duration 高精度创建
    pub fn high_precision_duration() {
        let nanos: u128 = 1_500_000_000;
        let duration = Duration::from_nanos_u128(nanos);
        assert_eq!(duration.as_millis(), 1500);
    }
}

/// 累积兼容性处理
pub mod cumulative_compatibility {
    /// 处理 1.90+ LLD 链接器
    pub fn lld_compatibility() {
        // 检查链接器配置
        // 在 .cargo/config.toml 中：
        let _config = r#"
[target.x86_64-unknown-linux-gnu]
# Rust 1.90+ 默认使用 LLD
# 如需回退：
# linker = "cc"
"#;
    }

    /// 处理 1.91+ dangling_pointers lint
    pub fn avoid_dangling_pointers() -> Box<i32> {
        // 不使用 &local as *const _
        Box::new(42)
    }

    /// 处理 1.92+ Never 类型严格化
    pub fn handle_never_type(result: Result<i32, !>) -> i32 {
        match result {
            Ok(x) => x,
            Err(e) => e,
        }
    }

    /// 处理 1.93+ deref_nullptr deny
    pub fn safe_null_deref(ptr: *const i32) -> Option<i32> {
        if ptr.is_null() {
            None
        } else {
            Some(unsafe { *ptr })
        }
    }
}

/// 形式化类型系统示例
pub mod formal_type_system {
    /// 1.91+：const 上下文生命周期
    ///
    /// 形式化：允许在 const 上下文中引用非 static 常量
    /// ∀ T: Sized, const C: T, ∃ 'a: 'a ⊢ &'a C: &'a T
    pub const CONST_VALUE: i32 = 42;
    pub const CONST_REF: &i32 = &CONST_VALUE; // 1.91+

    /// 1.93+：LUB coercion 修正
    ///
    /// 形式化：改进类型推导的上界计算
    /// lub(fn() -> A, fn() -> B) = fn() -> lub(A, B)
    pub fn lub_coercion_example() {
        fn f1() -> i32 { 1 }
        fn f2() -> i32 { 2 }

        let f: fn() -> i32 = if true { f1 } else { f2 };
        assert_eq!(f(), 1);
    }

    /// 1.93+：offset_of well-formed
    ///
    /// 形式化：offset_of!(T, field) requires well_formed(T) ∧ T: Sized
    pub struct WellFormed<T: Sized> { value: T }
    pub const OFFSET: usize = std::mem::offset_of!(WellFormed<i32>, value);
}

/// 累积迁移检查
pub struct CumulativeMigrationChecker;

impl CumulativeMigrationChecker {
    /// 检查从 1.89 到 1.93 的所有变更
    pub fn check_all(from_version: (u32, u32), to_version: (u32, u32)) -> Vec<&'static str> {
        let mut recommendations = Vec::new();

        // 1.90 变更
        if from_version < (1, 90) && to_version >= (1, 90) {
            recommendations.extend([
                "检查 LLD 链接器兼容性",
                "测试 cargo publish --workspace",
                "验证 x86_64-apple-darwin 支持状态",
            ]);
        }

        // 1.91 变更
        if from_version < (1, 91) && to_version >= (1, 91) {
            recommendations.extend([
                "修复 dangling_pointers_from_locals 警告",
                "考虑 aarch64-pc-windows-msvc 目标支持",
                "使用 const 上下文新特性",
            ]);
        }

        // 1.92 变更
        if from_version < (1, 92) && to_version >= (1, 92) {
            recommendations.extend([
                "处理 Never 类型 lint 严格化",
                "准备 musl 1.2.5 升级",
                "使用 Box/Rc/Arc::new_zeroed",
            ]);
        }

        // 1.93 变更
        if from_version < (1, 93) && to_version >= (1, 93) {
            recommendations.extend([
                "修复 deref_nullptr deny lint",
                "检查 #[test] 属性使用位置",
                "升级 libc 到 0.2.146+",
                "验证 offset_of! 类型 well-formed",
                "更新 repr(C) enum 判别值范围",
                "检查 repr(transparent) 兼容性",
                "使用 MaybeUninit/VecDeque/整数新 API",
                "配置 Emscripten -fwasm-exceptions",
            ]);
        }

        recommendations
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cumulative_api() {
        cumulative_api_usage::safe_maybe_uninit_init();
    }

    #[test]
    fn test_compatibility() {
        assert_eq!(cumulative_compatibility::avoid_dangling_pointers(), Box::new(42));
    }

    #[test]
    fn test_migration_checker() {
        let recs = CumulativeMigrationChecker::check_all((1, 89), (1, 93));
        assert!(recs.len() >= 15);
    }
}
```

---

## 形式化参考链接

| 概念 | 形式化文档 |
| :--- | :--- |
| 类型系统 | [Rust Type System](https://doc.rust-lang.org/reference/type-system.html) |
| 生命周期 | [Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html) |
| 内存模型 | [Memory Model](https://doc.rust-lang.org/reference/memory-model.html) |
| FFI | [External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html) |
| Ferrocene | [FLS](https://spec.ferrocene.dev/) |

---

**最后对照 releases.rs**: 2026-02-14
