//! # Unsafe Rust 练习 / Unsafe Rust Exercises
//!
//! 本模块提供 7 道循序渐进的 unsafe Rust 编程练习，覆盖原始指针、
//! `unsafe` 函数与块、`MaybeUninit`、`UnsafeCell`、FFI 语法以及
//! 安全抽象封装等核心主题。
//!
//! This module provides 7 progressive unsafe Rust exercises covering raw
//! pointers, `unsafe` functions and blocks, `MaybeUninit`, `UnsafeCell`, FFI
//! syntax, and safe abstraction wrappers.
//!
//! ## 运行测试 / Running Tests
//!
//! ```bash
//! cd e:/_src/rust-lang
//! cargo test -p exercises --test l3_unsafe_rust
//! ```

#![allow(unsafe_code)]

use std::cell::UnsafeCell;
use std::mem::{self, MaybeUninit};

/// 练习 1：原始指针基础 / Raw pointer basics
///
/// 将可变引用 `&mut i32` 同时转换为 `*const i32` 与 `*mut i32`，
/// 读取旧值后将目标位置的值翻倍，并返回旧值。
///
/// Converts a mutable reference into both a `*const i32` and a `*mut i32`,
/// reads the old value, doubles it in place, and returns the old value.
pub fn read_and_double(value: &mut i32) -> i32 {
    // TODO: 将 `value` 转换为 `*const i32` 与 `*mut i32`。
    // TODO: Convert `value` into a `*const i32` and a `*mut i32`.
    let r: *const i32 = value;
    let w: *mut i32 = value;

    // SAFETY: `r` 与 `w` 均来自同一个有效的可变引用，且不会并发使用。
    // SAFETY: Both pointers are derived from a single live mutable reference
    // and are not used concurrently.
    unsafe {
        let old = *r;
        *w = old * 2;
        old
    }
}

/// 练习 2：`unsafe fn` 与 `unsafe` 块 / `unsafe fn` and `unsafe` blocks
///
/// 接受一个原始可变指针，将其指向的值加 1，并返回新值。
///
/// Accepts a raw mutable pointer, increments the value it points to by 1,
/// and returns the new value.
///
/// # Safety
///
/// `ptr` 必须是非空、正确对齐且指向一个有效的 `i32`。
/// `ptr` must be non-null, properly aligned, and point to a valid `i32`.
pub unsafe fn increment_raw_pointer(ptr: *mut i32) -> i32 {
    // TODO: 在 `unsafe` 块中解引用 `ptr` 并自增。
    // TODO: Dereference `ptr` inside an `unsafe` block and increment it.

    // SAFETY: 调用者保证 `ptr` 指向一个有效且对齐的 `i32`。
    // SAFETY: The caller guarantees `ptr` points to a valid, aligned `i32`.
    unsafe {
        *ptr += 1;
        *ptr
    }
}

/// 练习 3a：通过 `std::slice::from_raw_parts` 重建只读切片
///
/// 使用原始指针和长度重建一个临时切片，然后复制其内容到 `Vec`。
///
/// Reconstructs a temporary slice from a raw pointer and length, then clones
/// its contents into a `Vec`.
pub fn clone_via_raw_parts<T: Copy>(slice: &[T]) -> Vec<T> {
    // TODO: 使用 `slice.as_ptr()` 和 `slice.len()` 重建切片，再 `to_vec()`。
    // TODO: Reconstruct the slice with `slice.as_ptr()` and `slice.len()`,
    // then call `to_vec()`.

    // SAFETY: `slice.as_ptr()` 与 `slice.len()` 来自有效的 Rust 切片，满足
    // `from_raw_parts` 的前提条件。
    // SAFETY: The pointer and length come from a valid Rust slice, satisfying
    // the preconditions of `from_raw_parts`.
    unsafe {
        let reconstructed = std::slice::from_raw_parts(slice.as_ptr(), slice.len());
        reconstructed.to_vec()
    }
}

/// 练习 3b：通过 `std::slice::from_raw_parts_mut` 清零前缀
///
/// 将可变切片的前 `n` 个字节置为 0。
///
/// Zeros out the first `n` bytes of a mutable slice.
///
/// # Panics
///
/// 当 `n > slice.len()` 时 panic / Panics if `n > slice.len()`.
pub fn zero_prefix(slice: &mut [u8], n: usize) {
    assert!(n <= slice.len(), "n 超出切片长度 / n is out of slice bounds");

    // TODO: 使用 `from_raw_parts_mut` 获取前 `n` 字节的可变切片并清零。
    // TODO: Obtain a mutable slice of the first `n` bytes using
    // `from_raw_parts_mut` and zero them.

    // SAFETY: `slice.as_mut_ptr()` 指向 `slice.len()` 个有效且已初始化的
    // 字节，`n <= slice.len()` 保证不会越界。
    // SAFETY: The pointer points to `slice.len()` valid initialized bytes, and
    // `n <= slice.len()` guarantees we stay in bounds.
    unsafe {
        let prefix = std::slice::from_raw_parts_mut(slice.as_mut_ptr(), n);
        for byte in prefix.iter_mut() {
            *byte = 0;
        }
    }
}

/// 练习 4：`MaybeUninit` 与未初始化内存 / `MaybeUninit`
///
/// 使用 `MaybeUninit<T>` 分配 `[T; N]` 的内存空间，避免先默认值初始化
/// 再覆盖。若填充过程中发生 panic，已初始化的元素会被正确 drop。
///
/// Allocates space for `[T; N]` using `MaybeUninit<T>` to avoid initializing
/// with a default value first. If a panic occurs during filling, already
/// initialized elements are properly dropped.
pub fn init_array_from_fn<T, const N: usize>(mut f: impl FnMut(usize) -> T) -> [T; N] {
    // TODO: 创建 `[MaybeUninit<T>; N]`，用闭包填充，并安全地转换为 `[T; N]`。
    // TODO: Create `[MaybeUninit<T>; N]`, fill it with the closure, and safely
    // convert it to `[T; N]`.

    // 步骤 1：分配未初始化的数组槽位。
    // Step 1: Allocate uninitialized array slots.
    let array: [MaybeUninit<T>; N] = std::array::from_fn(|_| MaybeUninit::uninit());

    // 步骤 2：定义 drop 守卫，在 panic 时清理已写入的元素。
    // Step 2: Define a drop guard to clean up written elements on panic.
    struct Guard<T, const N: usize> {
        array: [MaybeUninit<T>; N],
        initialized: usize,
    }

    impl<T, const N: usize> Drop for Guard<T, N> {
        fn drop(&mut self) {
            // SAFETY: `0..self.initialized` 范围内的元素都已被 `write()` 初始化。
            // SAFETY: Elements in `0..self.initialized` have been initialized
            // via `write()`.
            unsafe {
                for i in 0..self.initialized {
                    self.array[i].assume_init_drop();
                }
            }
        }
    }

    let mut guard = Guard { array, initialized: 0 };

    // 步骤 3：填充数组。
    // Step 3: Fill the array.
    for i in 0..N {
        guard.array[i].write(f(i));
        guard.initialized += 1;
    }

    // 步骤 4：提取数组并阻止守卫执行 drop。
    // Step 4: Extract the array and prevent the guard from running its drop.
    let initialized = guard.initialized;
    assert_eq!(initialized, N, "数组未完全初始化 / array not fully initialized");

    // SAFETY: 守卫拥有数组的所有权，这里通过 `ptr::read` 将其取出。
    // SAFETY: The guard owns the array; we read it out before forgetting the guard.
    let array = unsafe { std::ptr::read(&guard.array) };
    mem::forget(guard);

    // SAFETY: `[MaybeUninit<T>; N]` 与 `[T; N]` 具有相同的内存布局，且所有
    // N 个元素都已被初始化。
    // SAFETY: `[MaybeUninit<T>; N]` and `[T; N]` have identical layout, and all
    // N elements have been initialized.
    unsafe { mem::transmute_copy(&array) }
}

/// 练习 5：`UnsafeCell` 与内部可变性 / `UnsafeCell` interior mutability
///
/// 通过 `&UnsafeCell<i32>` 修改内部值并返回新值，演示内部可变性。
///
/// Mutates the interior value through a shared `&UnsafeCell<i32>` and returns
/// the new value, demonstrating interior mutability.
pub fn increment_shared_counter(counter: &UnsafeCell<i32>) -> i32 {
    // TODO: 使用 `UnsafeCell::get()` 获取 `*mut i32`，自增并返回新值。
    // TODO: Use `UnsafeCell::get()` to get a `*mut i32`, increment it, and
    // return the new value.

    // SAFETY: 本函数通过独占的 `&UnsafeCell` 访问其内部值，调用者需保证在
    // 访问期间没有其他线程/别名违反借用规则。
    // SAFETY: We access the interior through an exclusive `&UnsafeCell`; the
    // caller must ensure no other alias violates borrowing rules during access.
    unsafe {
        let ptr = counter.get();
        *ptr += 1;
        *ptr
    }
}

/// 练习 6：FFI / `extern "C"` 调用桩（无真实 C 依赖）
///
/// 这是一个由 Rust 实现、使用 C 调用约定的函数，仅用于演示 FFI 调用语法。
///
/// A Rust-implemented function with the C calling convention, used only to
/// demonstrate FFI call syntax without a real C dependency.
unsafe extern "C" fn ffi_add_one(x: i32) -> i32 {
    x + 1
}

/// 安全封装：调用 Rust 实现的 `extern "C"` 桩函数。
///
/// Safe wrapper that calls the Rust-implemented `extern "C"` stub.
pub fn call_ffi_add_one(x: i32) -> i32 {
    // TODO: 在 `unsafe` 块中调用 `ffi_add_one`。
    // TODO: Call `ffi_add_one` inside an `unsafe` block.

    // SAFETY: `ffi_add_one` 是本项目定义的纯 Rust 函数，行为确定且无副作用。
    // SAFETY: `ffi_add_one` is a pure Rust function defined in this crate with
    // deterministic behavior and no side effects.
    unsafe { ffi_add_one(x) }
}

/// 练习 7：安全抽象——手写 `split_at_mut` / Safe abstraction
///
/// 使用原始指针和 `slice::from_raw_parts_mut` 实现 `split_at_mut`，
/// 函数本身是 safe 的，调用者无需写 `unsafe`。
///
/// Implements `split_at_mut` using raw pointers and
/// `slice::from_raw_parts_mut`. The function itself is safe, so callers do not
/// need to write `unsafe`.
///
/// # Panics
///
/// 当 `mid > slice.len()` 时 panic / Panics if `mid > slice.len()`.
pub fn safe_split_at_mut<T>(slice: &mut [T], mid: usize) -> (&mut [T], &mut [T]) {
    assert!(mid <= slice.len(), "mid 索引越界 / mid index out of bounds");

    // TODO: 使用 `as_mut_ptr()`、`pointer::add` 和 `from_raw_parts_mut`
    // 构造两个不重叠的可变切片。
    // TODO: Use `as_mut_ptr()`, `pointer::add`, and `from_raw_parts_mut` to
    // build two non-overlapping mutable slices.

    let ptr = slice.as_mut_ptr();
    let len = slice.len();

    // SAFETY: `ptr` 来自有效的 `&mut [T]`，`mid <= len` 保证两个切片不重叠
    // 且都在原切片范围内。返回的可变引用生命周期与原切片相同。
    // SAFETY: `ptr` comes from a valid `&mut [T]`, and `mid <= len` guarantees
    // the two slices are non-overlapping and within the original slice. The
    // returned mutable references share the lifetime of the original slice.
    unsafe {
        let left = std::slice::from_raw_parts_mut(ptr, mid);
        let right = std::slice::from_raw_parts_mut(ptr.add(mid), len - mid);
        (left, right)
    }
}
