// Rust 1.97.0 API 可用性探测程序
// 用法（在 Rust 1.97.0+ 环境下）:
//   rustc --edition 2024 scripts/probe_rust_197_apis.rs -o /tmp/probe_197 && /tmp/probe_197
// 若某个 API 未稳定，编译会失败并指出具体行。

use std::collections::VecDeque;
use std::num::NonZeroU32;

fn main() {
    println!("Probing Rust 1.97.0 APIs...");

    // Probe 1: VecDeque::truncate_front
    {
        let mut deque: VecDeque<i32> = [1, 2, 3, 4, 5].into_iter().collect();
        deque.truncate_front(2);
        assert_eq!(deque.make_contiguous(), &[4, 5]);
        println!("✅ VecDeque::truncate_front");
    }

    // Probe 2: VecDeque::retain_back
    {
        let mut deque: VecDeque<i32> = [1, 2, 3, 4, 5].into_iter().collect();
        deque.retain_back(|x| x % 2 == 0);
        assert_eq!(deque.make_contiguous(), &[2, 4]);
        println!("✅ VecDeque::retain_back");
    }

    // Probe 3: NonZero bit ops
    {
        let n = NonZeroU32::new(0b10100).unwrap();
        let _ = n.highest_one();
        let _ = n.lowest_one();
        let _ = n.bit_width();
        println!("✅ NonZero bit ops (highest_one/lowest_one/bit_width)");
    }

    // Probe 4: const char::is_control
    {
        const _SPACE_CTRL: bool = ' '.is_control();
        const _NUL_CTRL: bool = '\0'.is_control();
        println!("✅ const char::is_control");
    }

    println!("Probe complete.");
}
