//! 原地初始化与固定初始化稳定 Rust 模式示例
//!
//! 覆盖:
//! - `MaybeUninit::write` / `assume_init`
//! - `Box::new_uninit` / `Box::write`
//! - `pin!` 栈固定
//! - 手动 `PhantomPinned` 自引用结构
//!
//! 运行: `cargo run -p c03_control_fn --example in_place_init_patterns`

use std::marker::PhantomPinned;
use std::mem::MaybeUninit;
use std::pin::{pin, Pin};

/// 示例 1: MaybeUninit 基础模式
fn maybeuninit_write_assume_init() {
    let mut slot: MaybeUninit<String> = MaybeUninit::uninit();
    slot.write(String::from("hello"));
    let s: String = unsafe { slot.assume_init() };
    assert_eq!(s, "hello");
}

/// 示例 2: 数组原地初始化
fn array_in_place_init() -> [i32; 5] {
    let mut arr: [MaybeUninit<i32>; 5] = [const { MaybeUninit::uninit() }; 5];
    for i in 0..5 {
        arr[i].write((i * i) as i32);
    }
    // Safety: 每个元素都已写入有效 i32
    unsafe { std::mem::transmute_copy(&arr) }
}

/// 示例 3: Box::new_uninit 在堆上原地初始化
fn box_new_uninit() {
    let mut b: Box<MaybeUninit<String>> = Box::new_uninit();
    b.write(String::from("heap-born"));
    let s: Box<String> = unsafe { b.assume_init() };
    assert_eq!(s.as_str(), "heap-born");
}

/// 示例 4: pin! 宏栈固定
fn pin_macro_stack_pin() {
    struct StackPinned {
        data: String,
        ptr: *const String,
        _pin: PhantomPinned,
    }

    let mut p: Pin<&mut StackPinned> = pin!(StackPinned {
        data: String::from("stack"),
        ptr: std::ptr::null(),
        _pin: PhantomPinned,
    });

    let ptr: *const String = &p.data;
    unsafe {
        p.as_mut().get_unchecked_mut().ptr = ptr;
    }

    assert_eq!(unsafe { &*p.ptr }, "stack");
}

/// 示例 5: 手动 PhantomPinned 自引用结构
struct SelfRef {
    data: String,
    ptr: *const String,
    _pin: PhantomPinned,
}

impl SelfRef {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut b: Pin<Box<Self>> = Box::pin(Self {
            data,
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });

        // Safety: b 已被 Pin 固定，其地址在 Pin 生命周期内不变
        let ptr: *const String = &b.data;
        unsafe {
            b.as_mut().get_unchecked_mut().ptr = ptr;
        }
        b
    }

    fn data(self: Pin<&Self>) -> &String {
        // Safety: ptr 指向 self.data，且 self 已被 Pin 固定
        unsafe { &*self.ptr }
    }
}

fn manual_phantom_pinned() {
    let s = SelfRef::new(String::from("pinned"));
    assert_eq!(s.as_ref().data(), "pinned");
}

fn main() {
    maybeuninit_write_assume_init();
    let squares = array_in_place_init();
    assert_eq!(squares, [0, 1, 4, 9, 16]);
    box_new_uninit();
    pin_macro_stack_pin();
    manual_phantom_pinned();

    println!("All in-place initialization patterns passed.");
}
