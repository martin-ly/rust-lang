#![allow(clippy::incompatible_msrv)]

//! Rust 1.93 Thread/Concurrency Features
//!
//! This module demonstrates thread-safe initialization patterns introduced
//! in Rust 1.93, including `MaybeUninit` buffer initialization and
//! `String::into_raw_parts` for cross-thread ownership transfer.
//!
//! # Features Demonstrated
//! - `MaybeUninit::uninit()` for uninitialized thread-safe buffers
//! - `String::into_raw_parts` / `from_raw_parts` for zero-copy transfer
//! - `Arc<Vec<T>>` shared memory layout inspection

use std::mem::MaybeUninit;
use std::sync::Arc;
use std::thread;

pub fn thread_safe_buffer_init() -> [i32; 4] {
    let mut buf = [MaybeUninit::uninit(); 4];

    let handles: Vec<_> = (0..4)
        .map(|i| {
            let mut slot = MaybeUninit::uninit();
            thread::spawn(move || {
                slot.write(i * 10);
                slot
            })
        })
        .collect();

    for (i, h) in handles.into_iter().enumerate() {
        let slot = h.join().unwrap();
        buf[i] = slot;
    }

    // SAFETY: 每个线程都已经写入对应的 slot
    unsafe {
        [
            buf[0].assume_init_read(),
            buf[1].assume_init_read(),
            buf[2].assume_init_read(),
            buf[3].assume_init_read(),
        ]
    }
}

/// 使用 `String::into_raw_parts` 跨线程传递所有权（通过重建）
/// `String::into_raw_parts` thread ownership （）
pub fn string_cross_thread(s: String) -> String {
    let (ptr, len, cap) = s.into_raw_parts();
    let ptr = ptr as usize;

    thread::spawn(move || {
        // SAFETY: ptr 来自合法 String，且在同一进程内传递
        let s = unsafe { String::from_raw_parts(ptr as *mut u8, len, cap) };
        s.to_uppercase()
    })
    .join()
    .unwrap()
}

/// 使用 `Arc<Vec<T>>` 结合 `into_raw_parts` 演示共享内存布局
/// `Arc<Vec<T>>` `into_raw_parts` demonstration shared memory layout
/// Use `Arc<Vec<T>>` 结合 `into_raw_parts` Demonstration ofshared memorylayout
pub fn shared_vec_layout<T: Send + 'static>(v: Vec<T>) -> (usize, usize, usize) {
    let (ptr, len, cap) = v.into_raw_parts();
    let meta = (ptr as usize, len, cap);
    let arc = Arc::new(unsafe { Vec::from_raw_parts(ptr, len, cap) });
    let _ = Arc::clone(&arc);
    // arc 在此处 drop，会安全释放 Vec
    meta
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thread_safe_buffer() {
        let result = thread_safe_buffer_init();
        assert_eq!(result, [0, 10, 20, 30]);
    }

    #[test]
    fn test_string_cross_thread() {
        let s = String::from("hello threads");
        assert_eq!(string_cross_thread(s), "HELLO THREADS");
    }

    #[test]
    fn test_shared_vec_layout() {
        let v = vec![1, 2, 3, 4];
        let (_, len, cap) = shared_vec_layout(v);
        assert_eq!(len, 4);
        assert!(cap >= 4);
    }
}
