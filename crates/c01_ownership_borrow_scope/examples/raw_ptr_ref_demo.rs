//! Rust 1.95.0 裸指针 `as_ref_unchecked` / `as_mut_unchecked` 专题示例
//!
//! Rust 1.95.0 稳定化了以下裸指针方法：
//! - `<*const T>::as_ref_unchecked()` -> `&T`
//! - `<*mut T>::as_ref_unchecked()` -> `&T`
//! - `<*mut T>::as_mut_unchecked()` -> `&mut T`
//!
//! 这些方法将裸指针直接转换为引用，无需手动解引用。
//! ⚠️ 调用者必须保证指针非空且对齐正确，否则触发 UB。
//!
//! 权威来源: https://releases.rs/docs/1.95.0/
//!
//! 运行方式:
//! ```bash
//! cargo run --example raw_ptr_ref_demo -p c01_ownership_borrow_scope
//! ```

// ==================== 示例 1: *const T::as_ref_unchecked ====================

/// 将 `*const T` 直接转为 `&T`
fn demo_const_ptr_as_ref() {
    println!("--- *const T::as_ref_unchecked ---");

    let value: i32 = 42;
    let ptr: *const i32 = &value;

    // as_ref_unchecked: 直接获取 &i32，无需手动解引用
    unsafe {
        let r: &i32 = ptr.as_ref_unchecked();
        println!("  指针: {:p}", ptr);
        println!("  引用: {:p}, 值: {}", r as *const i32, *r);
        assert_eq!(*r, 42);
    }

    // 与旧写法对比
    unsafe {
        let r_old: &i32 = &*ptr; // 旧写法: 先解引用再取引用
        let r_new: &i32 = ptr.as_ref_unchecked(); // 新写法
        assert_eq!(r_old, r_new);
        println!("  旧写法 (&*ptr) 与新写法 (as_ref_unchecked) 等价 ✅");
    }
}

// ==================== 示例 2: *mut T::as_ref_unchecked / as_mut_unchecked ====================

/// 将 `*mut T` 转为 `&T` 或 `&mut T`
fn demo_mut_ptr_as_ref_mut() {
    println!("\n--- *mut T::as_ref_unchecked / as_mut_unchecked ---");

    let mut value: String = String::from("hello");
    let ptr: *mut String = &mut value;

    unsafe {
        // as_ref_unchecked: 获取不可变引用
        let r: &String = ptr.as_ref_unchecked();
        println!("  as_ref_unchecked: {}", r);
        assert_eq!(r, "hello");

        // as_mut_unchecked: 获取可变引用
        let m: &mut String = ptr.as_mut_unchecked();
        m.push_str(" world");
        println!("  as_mut_unchecked 修改后: {}", m);
        assert_eq!(m, "hello world");
    }

    // 验证原始变量确实被修改
    assert_eq!(value, "hello world");
}

// ==================== 示例 3: FFI 边界 — C 字符串处理 ====================

/// 在 FFI 场景中使用 `as_ref_unchecked`
fn demo_ffi_c_string() {
    println!("\n--- FFI: C 字符串指针转换 ---");

    // 模拟从 C 接收的字符串指针（已知非空且有效）
    let c_str: *const u8 = c"Rust 1.95".as_ptr() as *const u8;

    unsafe {
        // as_ref_unchecked 将 *const u8 转为 &u8
        let first_char: &u8 = c_str.as_ref_unchecked();
        println!("  首字节: {} ('{}')", first_char, *first_char as char);
        assert_eq!(*first_char, b'R');

        // 遍历前 5 个字符
        print!("  前 5 字节: [");
        for i in 0..5 {
            let byte = c_str.add(i).as_ref_unchecked();
            if i > 0 {
                print!(", ");
            }
            print!("'{}'", *byte as char);
        }
        println!("]");
    }
}

// ==================== 示例 4: 自定义容器 — 裸指针数组索引 ====================

/// 实现一个简陋的裸指针切片视图
fn demo_raw_slice_view() {
    println!("\n--- 自定义容器: 裸指针切片视图 ---");

    struct RawSliceView<T> {
        ptr: *const T,
        #[allow(dead_code)]
        len: usize,
    }

    impl<T> RawSliceView<T> {
        /// 获取指定索引的引用（unsafe: 调用者需保证索引有效）
        unsafe fn get_unchecked(&self, index: usize) -> &T {
            // SAFETY: 调用者保证索引在有效范围内
            unsafe { self.ptr.add(index).as_ref_unchecked() }
        }
    }

    let data = [10, 20, 30, 40, 50];
    let view = RawSliceView {
        ptr: data.as_ptr(),
        len: data.len(),
    };

    unsafe {
        println!("  索引 0: {}", view.get_unchecked(0));
        println!("  索引 2: {}", view.get_unchecked(2));
        println!("  索引 4: {}", view.get_unchecked(4));
        assert_eq!(*view.get_unchecked(2), 30);
    }
}

// ==================== 示例 5: 与 Option<&T> 转换对比 ====================

/// 对比 `as_ref()` (Option) 与 `as_ref_unchecked()` (直接)
fn demo_option_vs_unchecked() {
    println!("\n--- as_ref() Option 版 vs as_ref_unchecked() ---");

    let value: f64 = std::f64::consts::PI;
    let ptr: *const f64 = &value;
    let null_ptr: *const f64 = std::ptr::null();

    // Option 版本: 安全，但需要解包
    let opt_ref: Option<&f64> = unsafe { ptr.as_ref() };
    println!("  ptr.as_ref(): {:?}", opt_ref);
    assert_eq!(opt_ref, Some(&std::f64::consts::PI));

    let null_opt: Option<&f64> = unsafe { null_ptr.as_ref() };
    println!("  null.as_ref(): {:?}", null_opt);
    assert_eq!(null_opt, None);

    // Unchecked 版本: 无开销，但调用者必须保证非空
    unsafe {
        let direct_ref: &f64 = ptr.as_ref_unchecked();
        println!("  ptr.as_ref_unchecked(): {}", direct_ref);
        assert_eq!(*direct_ref, std::f64::consts::PI);
    }

    println!("  ✅ 性能: as_ref_unchecked 避免 Option 分支");
    println!("  ⚠️  安全: 必须保证指针非空且对齐，否则 UB");
}

// ==================== 示例 6: 内存映射结构体字段访问 ====================

/// 从基址指针计算字段偏移并获取引用
fn demo_field_offset_access() {
    println!("\n--- 内存映射: 字段偏移访问 ---");

    #[repr(C)]
    struct Packet {
        magic: u32,
        version: u16,
        payload_len: u16,
    }

    let packet = Packet {
        magic: 0xDEAD_BEEF,
        version: 1,
        payload_len: 128,
    };

    let base: *const Packet = &packet;

    unsafe {
        // 直接获取整个结构体引用
        let pkt_ref: &Packet = base.as_ref_unchecked();
        println!("  完整包: magic={:08X}, version={}, len={}",
                 pkt_ref.magic, pkt_ref.version, pkt_ref.payload_len);

        // 获取 version 字段的引用（通过指针算术）
        let version_ptr: *const u16 = (base as *const u8).add(4) as *const u16;
        let version_ref: &u16 = version_ptr.as_ref_unchecked();
        println!("  version 字段 (偏移 4): {}", version_ref);

        assert_eq!(*version_ref, 1);
    }
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 裸指针 `as_ref_unchecked` / `as_mut_unchecked` 专题演示\n");

    demo_const_ptr_as_ref();
    demo_mut_ptr_as_ref_mut();
    demo_ffi_c_string();
    demo_raw_slice_view();
    demo_option_vs_unchecked();
    demo_field_offset_access();

    println!("\n✅ 裸指针 `as_ref_unchecked` / `as_mut_unchecked` 演示完成！");
    println!("   关键要点:");
    println!("   - *const T::as_ref_unchecked() -> &T: 裸指针直接转不可变引用");
    println!("   - *mut T::as_ref_unchecked() -> &T: 同上");
    println!("   - *mut T::as_mut_unchecked() -> &mut T: 裸指针直接转可变引用");
    println!("   - 比 &*ptr 更简洁，比 as_ref() 更高效（无 Option 分支）");
    println!("   - ⚠️ 调用者必须保证指针非空且对齐，否则立即 UB");
}
