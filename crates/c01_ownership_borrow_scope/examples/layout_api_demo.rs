//! Rust 1.95.0 `Layout` 新 API 专题示例
//!
//! Rust 1.95.0 为 `std::alloc::Layout` 新增了四个方法：
//! - `dangling_ptr`: 获取悬空但合规的指针
//! - `repeat`: 计算重复 N 次的布局
//! - `repeat_packed`: 紧凑重复布局（无填充）
//! - `extend_packed`: 紧凑扩展布局
//!
//! 这些方法对编写自定义分配器、FFI 封装和 unsafe 代码非常有价值。
//!
//! 权威来源: https://releases.rs/docs/1.95.0/
//!
//! 运行方式:
//! ```bash
//! cargo run --example layout_api_demo -p c01_ownership_borrow_scope
//! ```

use std::alloc::{alloc, dealloc, Layout};
use std::mem;

// ==================== 示例 1: Layout::dangling_ptr ====================

/// `dangling_ptr` 返回一个对齐正确但不可解引用的指针
///
/// 这是 `NonNull::dangling()` 的指针版本，用于 ZST（零大小类型）
/// 或作为占位指针。
fn demo_dangling_ptr() {
    println!("--- Layout::dangling_ptr ---");

    let layout_i32 = Layout::new::<i32>();
    let dangling = layout_i32.dangling_ptr().as_ptr();

    println!("  Layout::new::<i32>().dangling_ptr() = {:p}", dangling);
    println!("  指针对齐: {}", (dangling as usize).is_multiple_of(mem::align_of::<i32>()));

    // dangling_ptr 返回 NonNull<u8>，保证非空且对齐正确
    assert!(!dangling.is_null());
    assert!((dangling as usize).is_multiple_of(mem::align_of::<i32>()));

    // ZST 场景: Vec<T> 在空时使用 dangling ptr 作为起始指针
    let layout_zst = Layout::new::<()>();
    let zst_dangling = layout_zst.dangling_ptr().as_ptr();
    println!("  Layout::new::<()>().dangling_ptr() = {:p} (ZST)", zst_dangling);
}

// ==================== 示例 2: Layout::repeat ====================

/// `repeat` 计算重复 N 次的布局，包含元素间填充
fn demo_layout_repeat() {
    println!("\n--- Layout::repeat ---");

    // 假设一个结构体：8 字节数据 + 4 字节填充（对齐到 8）
    #[repr(C)]
    struct Item {
        a: u64,
        b: u32,
    }
    // Item 大小为 12，但对齐为 8，所以实际占用 16 字节（含尾部填充）

    let item_layout = Layout::new::<Item>();
    println!("  Item 布局: size={}, align={}", item_layout.size(), item_layout.align());

    // repeat(5): 5 个 Item 的数组布局
    let (array_layout, item_offset) = item_layout.repeat(5).unwrap();
    println!("  5 个 Item 的数组布局: size={}, align={}", array_layout.size(), array_layout.align());
    println!("  每个 Item 的偏移步长: {} 字节", item_offset);

    // 验证: 步长 >= Item 大小，且是对齐的倍数
    assert!(item_offset >= mem::size_of::<Item>());
    assert!(item_offset.is_multiple_of(mem::align_of::<Item>()));
}

// ==================== 示例 3: Layout::repeat_packed ====================

/// `repeat_packed` 计算紧凑重复布局，元素间无填充
///
/// ⚠️ 仅用于已知元素间不需要对齐填充的场景（如 C struct packing、字节流）
fn demo_layout_repeat_packed() {
    println!("\n--- Layout::repeat_packed ---");

    #[repr(C)]
    struct Header {
        magic: u32,
        version: u16,
        flags: u16,
    }

    let header_layout = Layout::new::<Header>();
    println!("  Header 布局: size={}, align={}", header_layout.size(), header_layout.align());

    // repeat_packed: 3 个 Header 紧密排列，总大小 = size * 3
    let packed_layout = header_layout.repeat_packed(3).unwrap();
    println!(
        "  3 个 Header 紧凑布局: size={}, align={}",
        packed_layout.size(),
        packed_layout.align()
    );

    assert_eq!(packed_layout.size(), mem::size_of::<Header>() * 3);
    assert_eq!(packed_layout.align(), mem::align_of::<Header>());
}

// ==================== 示例 4: Layout::extend_packed ====================

/// `extend_packed` 将两个布局紧凑拼接
///
/// 用于在已知上下文中追加字段而不关心填充。
fn demo_layout_extend_packed() {
    println!("\n--- Layout::extend_packed ---");

    let header = Layout::new::<u32>(); // 4 字节
    let payload = Layout::new::<[u8; 12]>(); // 12 字节
    let checksum = Layout::new::<u32>(); // 4 字节

    // 紧凑拼接: header + payload
    // extend_packed 返回 Result<Layout, LayoutError>
    // 第二个布局的起始偏移 = 第一个布局的 size
    let combined = header.extend_packed(payload).unwrap();
    let payload_offset = header.size();
    println!(
        "  header + payload: size={}, align={}, payload_offset={}",
        combined.size(),
        combined.align(),
        payload_offset
    );

    // 再拼接 checksum
    let full_layout = combined.extend_packed(checksum).unwrap();
    let checksum_offset = combined.size();
    println!(
        "  full packet: size={}, align={}, checksum_offset={}",
        full_layout.size(),
        full_layout.align(),
        checksum_offset
    );

    assert_eq!(payload_offset, 4);
    assert_eq!(checksum_offset, 16);
    assert_eq!(full_layout.size(), 20);
}

// ==================== 示例 5: 自定义分配器场景 ====================

/// 结合 `repeat` 和 `dangling_ptr` 实现一个简陋的 bump allocator
fn demo_custom_allocator() {
    println!("\n--- 自定义分配器: Layout::repeat + dangling_ptr ---");

    unsafe {
        // 分配一个可以容纳 10 个 u64 的内存块
        let elem_layout = Layout::new::<u64>();
        let (block_layout, step) = elem_layout.repeat(10).unwrap();
        let ptr = alloc(block_layout);
        assert!(!ptr.is_null());

        println!("  分配块: {:p}, 大小={}, 步长={}", ptr, block_layout.size(), step);

        // 初始化元素
        for i in 0..10 {
            let elem_ptr = ptr.add(i * step) as *mut u64;
            elem_ptr.write(i as u64 * 10);
        }

        // 读取验证
        print!("  内容: [");
        for i in 0..10 {
            let elem_ptr = ptr.add(i * step) as *mut u64;
            if i > 0 {
                print!(", ");
            }
            print!("{}", elem_ptr.read());
        }
        println!("]");

        // 清理
        dealloc(ptr, block_layout);
    }
}

// ==================== 示例 6: FFI 封装 — 解析 C 结构体数组 ====================

/// 使用 `repeat_packed` 处理 C 语言导出的紧凑结构体数组
fn demo_ffi_parsing() {
    println!("\n--- FFI: C 紧凑结构体数组解析 ---");

    // 模拟 C 结构体:
    // struct RawPoint { uint16_t x; uint16_t y; } // 4 字节，无填充
    #[repr(C, packed)]
    struct RawPoint {
        x: u16,
        y: u16,
    }

    let point_layout = Layout::new::<RawPoint>();
    let array_layout = point_layout.repeat_packed(3).unwrap();

    println!("  RawPoint: size={}, align={}", mem::size_of::<RawPoint>(), mem::align_of::<RawPoint>());
    println!(
        "  3 个 RawPoint 紧凑数组布局: size={}, align={}",
        array_layout.size(),
        array_layout.align()
    );

    // 模拟从 C 接收的字节流
    let raw_bytes: [u8; 12] = [
        0x01, 0x00, 0x02, 0x00, // point 0: (1, 2)
        0x03, 0x00, 0x04, 0x00, // point 1: (3, 4)
        0x05, 0x00, 0x06, 0x00, // point 2: (5, 6)
    ];

    unsafe {
        let points = raw_bytes.as_ptr() as *const RawPoint;
        for i in 0..3 {
            let p = points.add(i);
            // packed 结构体字段可能未对齐，必须使用 ptr::read_unaligned
            let x = std::ptr::addr_of!((*p).x).read_unaligned();
            let y = std::ptr::addr_of!((*p).y).read_unaligned();
            println!("  Point {}: x={}, y={}", i, x, y);
        }
    }
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 `Layout` 新 API 专题演示\n");

    demo_dangling_ptr();
    demo_layout_repeat();
    demo_layout_repeat_packed();
    demo_layout_extend_packed();
    demo_custom_allocator();
    demo_ffi_parsing();

    println!("\n✅ `Layout` 新 API 演示完成！");
    println!("   关键要点:");
    println!("   - dangling_ptr(): 返回对齐正确的悬空指针，用于 ZST/占位");
    println!("   - repeat(n): 计算含填充的重复布局，返回 (Layout, 步长)");
    println!("   - repeat_packed(n): 紧凑无填充重复，适用于已知场景");
    println!("   - extend_packed(other): 紧凑拼接两个布局");
    println!("   - 所有方法对自定义分配器、FFI、序列化都极为有用");
}
