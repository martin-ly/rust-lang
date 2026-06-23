//! Rust 1.97 特性代码示例
//! **编译要求**: Rust 1.97.0+ stable
//! **来源**: [releases.rs](https://releases.rs/) · [Rust Standard Library Tracking](https://github.com/rust-lang/rust/labels/T-libs-api)
//!
//! 本文件覆盖 Rust 1.97 稳定版引入的标准库新 API。

use std::collections::VecDeque;

// ============================================================================
// 0. NonZero 位操作 API (Rust 1.97 稳定)
// ============================================================================

/// `NonZero` 整数新增位查询方法：`highest_one` / `lowest_one` / `bit_width`
///
/// 这些 API 避免了在查询前对零值进行特殊处理，因为 `NonZero` 类型本身已保证非零。
pub fn demo_nonzero_bit_ops() {
    // 1.97+ 实际用法:
    // let n = NonZeroU32::new(0b10100).unwrap();
    // assert_eq!(n.highest_one(), 4);          // 最高 set bit 的索引
    // assert_eq!(n.lowest_one(), 2);           // 最低 set bit 的索引
    // assert_eq!(n.bit_width(), NonZeroU32::new(5).unwrap()); // 表示 self 所需的最少位数

    // 当前等效实现 (Rust 1.96):
    let n: u32 = 0b10100;
    assert_eq!(u32::BITS - 1 - n.leading_zeros(), 4);
    assert_eq!(n.trailing_zeros(), 2);
    assert_eq!(u32::BITS - n.leading_zeros(), 5);
}

// ============================================================================
// 0b. char::is_control() const 稳定化 (Rust 1.97)
// ============================================================================

/// `char::is_control()` 在 Rust 1.97 中变为 `const fn`
///
/// 使得字符分类可在编译期常量/静态项中使用。
pub fn demo_char_is_control_const() {
    // 1.97+ 实际用法:
    // const SPACE_CTRL: bool = ' '.is_control(); // false
    // const NUL_CTRL: bool = '\0'.is_control();  // true

    // 当前等效实现 (Rust 1.96):
    let space_ctrl: bool = ' '.is_control();
    let nul_ctrl: bool = '\0'.is_control();
    assert!(!space_ctrl);
    assert!(nul_ctrl);
}

// ============================================================================
// 1. VecDeque::truncate_front / retain_back
// ============================================================================

/// `VecDeque::truncate_front(n)` — 截断前部，保留后部 `n` 个元素
///
/// 与 `truncate(n)`（保留前部 `n` 个，截断后部）互补，实现双端队列的对称操作。
///
/// ```text
/// 原始: [1, 2, 3, 4, 5]
/// truncate(2)       → [1, 2]      (保留前 2)
/// truncate_front(2) → [4, 5]      (保留后 2)
/// ```
pub fn demo_vecdeque_truncate_front() {
    let mut deque: VecDeque<i32> = [1, 2, 3, 4, 5].into_iter().collect();

    // 1.97+: 截断前部，保留后部 2 个元素
    // deque.truncate_front(2);
    // assert_eq!(deque.make_contiguous(), &[4, 5]);

    // 当前等效实现:
    while deque.len() > 2 {
        deque.pop_front();
    }
    assert_eq!(deque.make_contiguous(), &[4, 5]);
}

/// `VecDeque::retain_back(f)` — 从尾部开始保留满足条件的元素
///
/// 与 `retain`（从头部开始）互补，在某些场景下能更早终止遍历。
///
/// ⚠️ 状态更新 (2026-06-09): PR #151973 "Stabilize retain_back from truncate_front"
/// 的 FCP 已完成，但 nightly 1.98.0 验证中 `retain_back` 方法尚不存在
///（feature gate `vec_deque_retain_back` 亦不存在）。可能从该 PR 中
/// 被移除或推迟至 1.98+。下方等效实现仍具教学价值。
pub fn demo_vecdeque_retain_back() {
    let mut deque: VecDeque<i32> = [1, 2, 3, 4, 5].into_iter().collect();

    // 1.97+: 从尾部保留偶数（结果: [2, 4]，从头部视角）
    // deque.retain_back(|x| x % 2 == 0);
    // assert_eq!(deque.make_contiguous(), &[2, 4]);

    // 当前等效实现（从尾部遍历）:
    let len = deque.len();
    for i in (0..len).rev() {
        if deque[i] % 2 != 0 {
            deque.remove(i);
        }
    }
    assert_eq!(deque.make_contiguous(), &[2, 4]);
}

// ============================================================================
// 2. 浮点代数优化属性 (float_algebraic)
// ============================================================================

/// `#[optimize(fast_math)]` / `float_algebraic` 允许编译器重组浮点运算
///
/// ⚠️ 这会打破 IEEE 754 的严格语义，仅在可接受精度损失的场景使用。
///
/// 1.98 状态: 已合并至 master (PR #157029)，因晚于 1.97 beta cutoff，进入 1.98
#[allow(dead_code)]
pub fn demo_float_algebraic() {
    // 未来语法（示意）:
    // #[float_algebraic]
    // fn fast_sum(a: f64, b: f64, c: f64) -> f64 {
    //     (a + b) + c  // 编译器可能重排为 a + (b + c)
    // }

    // 当前等效做法: 使用 `fast-math` LLVM 标志（nightly-only，不稳定）
    let a = 1.0_f64;
    let b = 1e-16_f64;
    let c = -1.0_f64;

    // 严格 IEEE 754: (a + b) + c ≈ 1e-16
    let strict = (a + b) + c;
    // 代数重排: a + (b + c) ≈ 0.0（因为 b + c 在舍入后可能为 -1.0）

    println!("strict (a+b)+c = {}", strict);
    println!("注意: float_algebraic 允许编译器选择后者，可能改变结果");
}

// ============================================================================
// 3. RandomSource / DefaultRandomSource 抽象（等待 t-libs-api）
// ============================================================================

/// `RandomSource` trait 提供可插拔的随机数源抽象
///
/// 1.98 状态: 等待 t-libs-api 决策 (PR #157168)
/// 设计目标: 允许 `rand::thread_rng()`、`getrandom`、`OsRng` 等通过统一 trait 接入标准库 API。
#[allow(dead_code)]
pub fn demo_random_source_concept() {
    // 概念性伪代码:
    // use std::random::{RandomSource, DefaultRandomSource};
    //
    // fn shuffle<T, R: RandomSource>(vec: &mut [T], rng: &mut R) { ... }
    //
    // let mut rng = DefaultRandomSource::new();
    // shuffle(&mut data, &mut rng);

    println!("RandomSource / DefaultRandomSource: 等待 1.97+ 稳定化");
}

// ============================================================================
// 4. C-variadic function definitions（PFCP）
// ============================================================================

/// C 可变参数函数定义稳定化
///
/// 1.97 状态: PFCP (PR #155942)
/// 用途: 不再需要通过 `extern "C"` 声明 + 手写 C wrapper 来定义可变参数函数。
/// 典型场景: 内核 printk、嵌入式日志、FFI 回调。
#[allow(dead_code)]
pub extern "C" fn demo_c_variadic_definition(_fmt: *const u8) {
    // 未来稳定后:
    // pub unsafe extern "C" fn my_printf(fmt: *const u8, args: ...) { ... }

    // 当前限制: C variadic 定义仍需要 nightly feature `c_variadic`
    println!("C-variadic fn definitions: 等待 1.97+ 稳定化，当前需 `#![feature(c_variadic)]`");
}

// ============================================================================
// 5. box_vec_non_null（PFCP 中）
// ============================================================================

/// `Box::into_raw_non_null` / `Vec::into_raw_parts_non_null` 提供非空指针转换
///
/// 1.98 状态: PFCP (PR #157226)
/// 设计目标: 允许 `Box<T>` 和 `Vec<T>` 直接转换为 `NonNull<T>`，避免空指针检查开销。
#[allow(dead_code)]
pub fn demo_box_vec_non_null() {
    // 概念性伪代码 (1.97+ 稳定后):
    // use std::ptr::NonNull;
    // let boxed = Box::new(42);
    // let ptr: NonNull<i32> = Box::into_raw_non_null(boxed);
    //
    // let vec = vec![1, 2, 3];
    // let (ptr, len, cap): (NonNull<i32>, usize, usize) = Vec::into_raw_parts_non_null(vec);

    // 当前等效实现:
    let boxed = Box::new(42);
    let ptr = Box::into_raw(boxed);
    let non_null = std::ptr::NonNull::new(ptr).expect("Box::into_raw never returns null");
    println!("Box -> NonNull: {:?}", non_null);

    let vec = vec![1, 2, 3];
    let (ptr, len, cap) = (vec.as_ptr(), vec.len(), vec.capacity());
    std::mem::forget(vec);
    let non_null = std::ptr::NonNull::new(ptr.cast_mut()).expect("Vec ptr is non-null");
    println!("Vec -> NonNull: {:?}, len={}, cap={}", non_null, len, cap);
}

// ============================================================================
// 5b. Box::as_ptr / Box::as_mut_ptr（1.98 已确认）
// ============================================================================

/// `Box::as_ptr` / `Box::as_mut_ptr` — 不物化引用的原始指针访问
///
/// 1.98 状态: 已合并至 master (PR #157876)。此前为 nightly-only `box_as_ptr`。
/// 关键保证: 该方法不会 materialize 对底层内存的引用，因此在 aliasing model 中
/// 与 `Box::leak` / `Box::as_ref` 不同，可与其它 raw pointer 操作安全交错。
#[allow(dead_code)]
pub fn demo_box_as_ptr() {
    // 1.98+ 实际用法:
    // let mut boxed = Box::new(42);
    // let ptr: *mut i32 = boxed.as_mut_ptr();
    // unsafe { *ptr = 100; }
    // assert_eq!(*boxed, 100);

    // 当前等效实现 (Rust 1.96): 使用 Box::into_raw 会转移所有权，需要恢复
    let mut boxed = Box::new(42);
    let ptr = Box::into_raw(boxed);
    unsafe {
        *ptr = 100;
        boxed = Box::from_raw(ptr); // 恢复所有权
    }
    assert_eq!(*boxed, 100);
}

// ============================================================================
// 6. int_format_into（1.98 已确认）
// ============================================================================

/// 整数格式化到现有缓冲区，避免堆分配
///
/// 1.98 状态: 已合并至 master (PR #152544)，因晚于 1.97 beta cutoff 进入 1.98。
/// 设计目标: `write!(buf, "{}", x)` 的零分配替代方案，用于 `no_std` 和嵌入式场景。
#[allow(dead_code)]
pub fn demo_int_format_into() {
    // 概念性伪代码 (1.97+ 稳定后):
    // let mut buf = [0u8; 20];
    // let n = 12345i32;
    // let written = n.format_into(&mut buf);
    // assert_eq!(&buf[..written], b"12345");

    // 当前等效实现 (使用 itoa 或手动格式化):
    let mut buf = [0u8; 20];
    let n = 12345i32;
    let s = n.to_string();
    let bytes = s.as_bytes();
    buf[..bytes.len()].copy_from_slice(bytes);
    println!(
        "formatted: {:?}",
        std::str::from_utf8(&buf[..bytes.len()]).unwrap()
    );
}

// ============================================================================
// 7. NonZero::from_str_radix（1.98 已确认）
// ============================================================================

/// `NonZero<T>::from_str_radix` — 按指定进制解析非零整数
///
/// 1.98 状态: 已合并至 master (PR #157877)，将进入 1.98。
/// 与 `T::from_str_radix` 不同：若解析结果为 0，返回 `Err(ParseIntError::kind() == InvalidDigit)`。
#[allow(dead_code)]
pub fn demo_nonzero_from_str_radix() {
    // 1.98+ 实际用法:
    // let n = NonZeroU32::from_str_radix("1a", 16).unwrap();
    // assert_eq!(n.get(), 26);
    // assert!(NonZeroU32::from_str_radix("0", 10).is_err());

    // 当前等效实现 (Rust 1.96):
    let parsed = u32::from_str_radix("1a", 16)
        .ok()
        .and_then(std::num::NonZeroU32::new);
    assert_eq!(parsed.unwrap().get(), 26);

    let zero = "0".parse::<u32>().ok().and_then(std::num::NonZeroU32::new);
    assert!(zero.is_none());
}

// ============================================================================
// 8. core::range::{RangeFull, RangeTo}（1.98 已确认）
// ============================================================================

/// `core::range::RangeFull` / `RangeTo` / `legacy::*` — `core::range` 类型补全
///
/// 1.98 状态: 已合并至 master (PR #156629)，将进入 1.98。
/// 设计目标: 将 `std::ops::RangeFull`、`std::ops::RangeTo` 等类型迁移到 `core::range`，
/// 使 `no_std` 环境也能使用这些范围类型；`legacy::*` 为旧类型提供兼容重导出。
#[allow(dead_code)]
pub fn demo_core_range_completion() {
    // 1.98+ 实际用法:
    // use core::range::{RangeFull, RangeTo};
    // let full: RangeFull = ..;
    // let to: RangeTo<i32> = ..5;

    // 当前等效实现 (Rust 1.96): 仍使用 std::ops
    let _full = ..;
    let _to = ..4;
    let slice = [1, 2, 3, 4, 5];
    assert_eq!(&slice[_to], &[1, 2, 3, 4]);
}

// ============================================================================
// 9. proc_macro_value（等待 review）
// ============================================================================

/// `proc_macro_value` 允许过程宏在编译期产生值（而不仅是 token 流）
///
/// 1.97 状态: 等待 review (PR #152092)
/// 用途: 为 `const` 泛型和编译期计算提供更强大的元编程能力。
#[allow(dead_code)]
pub fn demo_proc_macro_value_concept() {
    // 概念性伪代码:
    // #[derive(ConstValue)]
    // struct MyConfig { threshold: u32 }
    //
    // const CONFIG: MyConfig = MyConfig::const_value(); // 由宏在编译期生成

    println!("proc_macro_value: 等待 1.97+ 稳定化");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nonzero_bit_ops() {
        demo_nonzero_bit_ops();
    }

    #[test]
    fn test_char_is_control_const() {
        demo_char_is_control_const();
    }

    #[test]
    fn test_vecdeque_truncate_front() {
        demo_vecdeque_truncate_front();
    }

    #[test]
    fn test_vecdeque_retain_back() {
        demo_vecdeque_retain_back();
    }

    #[test]
    fn test_box_vec_non_null() {
        demo_box_vec_non_null();
    }

    #[test]
    fn test_box_as_ptr() {
        demo_box_as_ptr();
    }

    #[test]
    fn test_int_format_into() {
        demo_int_format_into();
    }

    #[test]
    fn test_nonzero_from_str_radix() {
        demo_nonzero_from_str_radix();
    }

    #[test]
    fn test_core_range_completion() {
        demo_core_range_completion();
    }
}

/// Nightly 预览测试 — 使用 `cargo test -- --ignored` 运行
///
/// 这些测试需要 nightly toolchain 和对应的 feature gate。
/// 在 1.97 稳定后，将取消注释的代码移入主测试模块并删除等效实现。
#[cfg(test)]
#[cfg(nightly)]
mod nightly_tests {
    use std::collections::VecDeque;

    #[test]
    #[ignore = "nightly-only: requires #![feature(vec_deque_truncate_front)]"]
    fn test_truncate_front_nightly() {
        let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3, 4, 5]);
        deque.truncate_front(2);
        assert_eq!(deque.make_contiguous(), &[4, 5]);
    }
}
