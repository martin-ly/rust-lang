//! Unsafe Rust 模式专题演示
//! Unsafe Rust demonstration
//! Unsafe Rust 模式专题Demonstration of
//! 覆盖常见 unsafe 编程模式，每个模式附带 SAFETY 注释：
//! unsafe ， SAFETY ：
//! - addr_of_mut!（未初始化字段地址获取）
//! - addr_of_mut!（field ）
//! - unsafe trait / unsafe impl（自定义不安全 trait）
//!
//! 运行：cargo run --example unsafe_patterns_demo -p c03_control_fn

use std::mem::{ManuallyDrop, MaybeUninit};
use std::ptr::NonNull;

// ============================================================
// 1. NonNull<T> — 协变 + 非空指针
// ============================================================

struct IntrusiveNode {
    value: i32,
    next: Option<NonNull<IntrusiveNode>>,
}

fn demo_non_null() {
    println!("=== NonNull<T> 侵入式链表 ===");

    let mut a = Box::new(IntrusiveNode {
        value: 1,
        next: None,
    });
    let mut b = Box::new(IntrusiveNode {
        value: 2,
        next: None,
    });

    // SAFETY: Box::as_mut() returns a valid, non-null, unique reference.
    let a_ptr = NonNull::new(Box::as_mut(&mut a)).unwrap();
    b.next = Some(a_ptr);

    // Traverse through NonNull without unsafe deref (only needed for actual access).
    let head = NonNull::new(Box::as_mut(&mut b)).unwrap();
    // SAFETY: We know head is valid because we just created it.
    unsafe {
        println!("头节点值: {}", head.as_ref().value);
        if let Some(next) = head.as_ref().next {
            println!("下一个节点值: {}", next.as_ref().value);
        }
    }
    println!("✅ NonNull<T> 保证非空且协变");
}

// ============================================================
// 2. addr_of_mut! — 未初始化结构体字段地址
// ============================================================

#[repr(C)]
struct RawPacket {
    header: u32,
    payload: [u8; 4],
}

fn demo_addr_of_mut() {
    println!("\n=== addr_of_mut! 未初始化字段地址 ===");

    let mut packet = MaybeUninit::<RawPacket>::uninit();

    // SAFETY: addr_of_mut! 不会创建引用，只是获取裸指针地址，
    // 因此即使目标未初始化也是安全的。
    let header_ptr = unsafe { std::ptr::addr_of_mut!((*packet.as_mut_ptr()).header) };
    let payload_ptr = unsafe { std::ptr::addr_of_mut!((*packet.as_mut_ptr()).payload) };

    // Now we can safely write through the pointers.
    unsafe {
        header_ptr.write(0xDEAD_BEEF);
        payload_ptr.write([0x01, 0x02, 0x03, 0x04]);
    }

    // SAFETY: All fields have been initialized.
    let packet = unsafe { packet.assume_init() };
    assert_eq!(packet.header, 0xDEAD_BEEF);
    assert_eq!(packet.payload, [0x01, 0x02, 0x03, 0x04]);
    println!("✅ addr_of_mut! 安全获取未初始化字段地址");
}

// ============================================================
// 3. ManuallyDrop<T> — 控制 Drop 时机
// ============================================================

struct LoudDrop(&'static str);

impl Drop for LoudDrop {
    fn drop(&mut self) {
        println!("  [Drop] {} 被释放", self.0);
    }
}

fn demo_manually_drop() {
    println!("\n=== ManuallyDrop<T> 控制 Drop ===");

    let mut item = ManuallyDrop::new(LoudDrop("重要资源"));

    // 使用 item...
    println!("  使用: {}", item.0);

    // 决定不调用 Drop，而是手动提取内部值。
    // SAFETY: We promise not to use `item` after this, and we prevent the automatic Drop.
    let inner = unsafe { ManuallyDrop::take(&mut item) };
    println!("  手动提取: {}", inner.0);
    // inner 现在会在作用域结束时正常 Drop。
    println!("✅ ManuallyDrop<T> 成功转移所有权");
}

// ============================================================
// 4. unsafe trait / unsafe impl — 自定义不安全 trait
// ============================================================

/// # Safety
/// 且不会被修改导致对象状态不一致。
/// and is to state 。
unsafe trait AsBytes {
    fn as_bytes(&self) -> &[u8];
}

#[repr(C)]
struct FixedHeader {
    magic: u32,
    version: u16,
    flags: u16,
}

// SAFETY: FixedHeader 是 #[repr(C)]，字段顺序固定，
// 且所有字段都是简单数值类型，字节表示安全。
unsafe impl AsBytes for FixedHeader {
    fn as_bytes(&self) -> &[u8] {
        // SAFETY: FixedHeader 是 Pod-like，任何字节模式都合法。
        unsafe {
            std::slice::from_raw_parts(
                (self as *const Self).cast::<u8>(),
                std::mem::size_of::<Self>(),
            )
        }
    }
}

fn demo_unsafe_trait() {
    println!("\n=== unsafe trait / unsafe impl ===");

    let header = FixedHeader {
        magic: 0x1234_5678,
        version: 1,
        flags: 0x0003,
    };

    let bytes = header.as_bytes();
    println!("  字节表示 (len={}): {:02x?}", bytes.len(), bytes);
    assert_eq!(bytes.len(), 8);
    println!("✅ unsafe trait 实现满足安全契约");
}

// ============================================================
// 5. MaybeUninit 条件初始化数组
// ============================================================

fn demo_maybe_uninit_array() {
    println!("\n=== MaybeUninit 条件初始化数组 ===");

    const N: usize = 5;
    let mut buffer: [MaybeUninit<i32>; N] = unsafe { MaybeUninit::uninit().assume_init() };

    // 条件初始化前 3 个元素
    for (i, slot) in buffer.iter_mut().enumerate().take(3) {
        slot.write(i as i32 * 10);
    }

    // SAFETY: We know indices 0..3 are initialized.
    let initialized = unsafe {
        [
            buffer[0].assume_init(),
            buffer[1].assume_init(),
            buffer[2].assume_init(),
        ]
    };

    assert_eq!(initialized, [0, 10, 20]);

    // 必须手动 Drop 未初始化的元素（这里都是整数，无 Drop，所以安全）。
    // 如果是非 Copy 类型，需要逐个判断并调用 MaybeUninit::assume_init_drop。
    println!("✅ MaybeUninit 条件初始化数组安全完成");
}

// ============================================================
// main
// ============================================================

fn main() {
    demo_non_null();
    demo_addr_of_mut();
    demo_manually_drop();
    demo_unsafe_trait();
    demo_maybe_uninit_array();
    println!("\n🎉 所有 unsafe 模式演示通过！");
}
