//! Kani 模型检查示例。
//!
//! 使用 `#[cfg(kani)]` 包裹验证代码，普通 `cargo check` 会跳过这些函数；
//! 只有在 Kani 运行时（`cargo kani --example kani_example`）才会编译并验证。
#![allow(dead_code, unexpected_cfgs)]

#[cfg(kani)]
mod proofs {
    //! Kani 证明函数。

    /// 在输入有界时，`u32` 加法不应溢出。
    #[kani::proof]
    fn safe_add_no_overflow() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        kani::assume(a < 1_000_000);
        kani::assume(b < 1_000_000);
        let c = a + b;
        kani::assert(c >= a && c >= b);
    }

    /// 越界输入下 `checked_add` 返回 `None`，演示反例边界。
    #[kani::proof]
    fn safe_add_overflow_counterexample() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        kani::assume(a > u32::MAX - 10);
        kani::assume(b > 10);
        let c = a.checked_add(b);
        kani::assert(c.is_none(), "overflow should be detected by checked_add");
    }

    /// 合法下标访问数组不应 panic。
    #[kani::proof]
    fn index_within_bounds() {
        let arr = [10, 20, 30, 40];
        let idx: usize = kani::any();
        kani::assume(idx < arr.len());
        let _value = arr[idx];
    }

    /// 越界下标访问数组应 panic；使用 `#[kani::should_panic]` 标记期望失败。
    #[kani::proof]
    #[kani::should_panic]
    fn index_out_of_bounds() {
        let arr = [10, 20, 30];
        let idx: usize = kani::any();
        kani::assume(idx >= arr.len());
        let _value = arr[idx]; // expected out-of-bounds panic
    }
}

#[cfg(not(kani))]
fn main() {
    println!("This example is intended to be run with Kani (`cargo kani --example kani_example`).");
}
