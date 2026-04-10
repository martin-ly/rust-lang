//! Miri 测试模块 - 类型系统内存安全验证
//!
//! 本模块包含用于 Miri 测试的 unsafe 代码示例，验证类型系统的内存安全性。
//! 运行方式:
//!   cargo miri test miri_tests
//!   MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test miri_tests

use std::mem::MaybeUninit;
use std::ptr::NonNull;

// ==================== 基本 Unsafe 类型操作测试 ====================

/// 测试 1: MaybeUninit 基本使用
/// 验证未初始化内存的正确处理
#[test]
fn test_maybeuninit_basic() {
    let mut x = MaybeUninit::<i32>::uninit();
    
    unsafe {
        x.as_mut_ptr().write(42);
        assert_eq!(x.assume_init(), 42);
    }
}

/// 测试 2: MaybeUninit 数组初始化
/// 逐步初始化数组元素
#[test]
fn test_maybeuninit_array() {
    let mut arr: [MaybeUninit<i32>; 5] = unsafe {
        MaybeUninit::uninit().assume_init()
    };
    
    // 逐个初始化
    for (i, elem) in arr.iter_mut().enumerate() {
        elem.write(i as i32 * 10);
    }
    
    // 转换为初始化后的数组
    unsafe {
        let init_arr: [i32; 5] = std::mem::transmute_copy(&arr);
        assert_eq!(init_arr, [0, 10, 20, 30, 40]);
    }
    
    // 防止 Drop 调用（i32 无 Drop，但为了模式完整性）
    std::mem::forget(arr);
}

/// 测试 3: NonNull 指针基本操作
#[test]
fn test_nonnull_basic() {
    let mut x = 42;
    let ptr = NonNull::new(&mut x as *mut i32).unwrap();
    
    unsafe {
        *ptr.as_ptr() = 100;
    }
    
    assert_eq!(x, 100);
}

/// 测试 4: 裸指针别名规则
/// Tree Borrows: OK，只要遵循别名规则
#[test]
fn test_raw_pointer_alias() {
    let mut x = 0;
    let ptr1 = &mut x as *mut i32;
    let ptr2 = ptr1; // 复制裸指针
    
    unsafe {
        *ptr1 = 1;
        *ptr2 = 2; // 通过别名写入
    }
    
    assert_eq!(x, 2);
}

// ==================== ManuallyDrop 测试 ====================

use std::mem::ManuallyDrop;

struct DropTracker<'a>(&'a mut bool);

impl<'a> Drop for DropTracker<'a> {
    fn drop(&mut self) {
        *self.0 = true;
    }
}

/// 测试 5: ManuallyDrop 阻止自动 Drop
#[test]
fn test_manually_drop() {
    let mut dropped = false;
    
    {
        let _manual = ManuallyDrop::new(DropTracker(&mut dropped));
        // 不会自动调用 Drop
    }
    
    assert!(!dropped); // 确认没有自动 Drop
    
    // 手动调用 Drop
    unsafe {
        ManuallyDrop::drop(&mut ManuallyDrop::new(DropTracker(&mut dropped)));
    }
    assert!(dropped);
}

/// 测试 6: ManuallyDrop 内部值访问
#[test]
fn test_manually_drop_access() {
    let manual = ManuallyDrop::new(vec![1, 2, 3]);
    
    assert_eq!(manual.len(), 3);
    assert_eq!(manual[0], 1);
    
    // 使用 into_inner 取出值
    let vec = unsafe { ManuallyDrop::into_inner(manual) };
    assert_eq!(vec, vec![1, 2, 3]);
}

// ==================== 类型转换和内存操作 ====================

/// 测试 7: transmute 基础
/// 谨慎使用 transmute，确保类型大小相同
#[test]
fn test_transmute_basic() {
    let bytes: [u8; 4] = [0x00, 0x00, 0x00, 0x01];
    
    // 小端序系统下，这是 1
    let value: u32 = unsafe { std::mem::transmute(bytes) };
    
    // 验证字节序
    if cfg!(target_endian = "little") {
        assert_eq!(value, 0x01000000);
    } else {
        assert_eq!(value, 0x00000001);
    }
}

/// 测试 8: addr_of! 和 addr_of_mut!
/// 获取字段地址而不创建引用
#[repr(C)]
struct Packed {
    a: u8,
    b: u32,
}

#[test]
fn test_addr_of() {
    let packed = Packed { a: 1, b: 42 };
    
    unsafe {
        let a_ptr = std::ptr::addr_of!(packed.a);
        let b_ptr = std::ptr::addr_of!(packed.b);
        
        assert_eq!(*a_ptr, 1);
        assert_eq!(*b_ptr, 42);
    }
}

// ==================== 自引用结构测试 ====================

use std::pin::Pin;
use std::marker::PhantomPinned;

/// 自引用结构示例
struct SelfReferential {
    data: String,
    ptr_to_data: *const String,
    _pin: PhantomPinned,
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            ptr_to_data: std::ptr::null(),
            _pin: PhantomPinned,
        });
        
        let ptr = &boxed.data as *const String;
        boxed.ptr_to_data = ptr;
        
        Box::into_pin(boxed)
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
    
    fn get_via_ptr(&self) -> &str {
        unsafe { &*self.ptr_to_data }
    }
}

/// 测试 9: 自引用结构通过 Pin 保证安全
#[test]
fn test_self_referential() {
    let self_ref = SelfReferential::new(String::from("Hello"));
    
    assert_eq!(self_ref.get_data(), "Hello");
    assert_eq!(self_ref.get_via_ptr(), "Hello");
}

// ==================== 联合体测试 ====================

/// 联合体示例 - 用于 FFI 或低级内存操作
#[repr(C)]
union IntOrFloat {
    i: i32,
    f: f32,
}

/// 测试 10: 联合体基本操作
#[test]
fn test_union_basic() {
    let u = IntOrFloat { i: 1065353216 }; // f32::to_bits() for 1.0
    
    unsafe {
        assert_eq!(u.i, 1065353216);
        assert!((u.f - 1.0).abs() < f32::EPSILON); // 位模式表示 1.0
    }
}

// ==================== FFI 类型测试 ====================

use std::ffi::c_void;
use std::os::raw::{c_int, c_char};

/// 测试 11: 外部类型指针操作
#[test]
fn test_ffi_pointer() {
    let mut value: c_int = 42;
    let ptr: *mut c_int = &mut value;
    let void_ptr: *mut c_void = ptr as *mut c_void;
    
    unsafe {
        let back_to_int: *mut c_int = void_ptr as *mut c_int;
        assert_eq!(*back_to_int, 42);
    }
}

// ==================== 对齐和内存布局 ====================

/// 测试 12: 对齐检查
#[repr(align(16))]
struct Aligned16(u8);

#[test]
fn test_alignment() {
    let aligned = Aligned16(42);
    let ptr = &aligned as *const Aligned16;
    
    assert_eq!(ptr as usize % 16, 0); // 16 字节对齐
}

/// 测试 13: 读取未对齐数据
#[test]
fn test_unaligned_read() {
    let bytes: [u8; 8] = [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    
    unsafe {
        // 从可能未对齐的地址读取
        let ptr = bytes.as_ptr().offset(1) as *const u32;
        let _value = ptr.read_unaligned();
    }
}

// ==================== 同步原语 Unsafe 操作 ====================

use std::sync::atomic::{AtomicUsize, Ordering};

/// 测试 14: 原子操作内存序
#[test]
fn test_atomic_operations() {
    let atomic = AtomicUsize::new(0);
    
    // Relaxed 排序 - 最弱保证
    atomic.store(1, Ordering::Relaxed);
    let val = atomic.load(Ordering::Relaxed);
    
    assert_eq!(val, 1);
    
    // SeqCst - 最强排序
    atomic.fetch_add(1, Ordering::SeqCst);
    assert_eq!(atomic.load(Ordering::SeqCst), 2);
}

// ==================== 边界情况测试 ====================

/// 测试 15: 零大小类型的指针操作
#[test]
fn test_zst_pointers() {
    struct Zst;
    
    let zst = Zst;
    let ptr = &zst as *const Zst;
    
    // ZST 指针可以相等但地址可能相同
    let zst2 = Zst;
    let ptr2 = &zst2 as *const Zst;
    
    // ZST 的解引用是安全的
    unsafe {
        let _ = *ptr;
        let _ = *ptr2;
    }
}

/// 测试 16: 空指针检查（Miri 会检测）
#[test]
fn test_null_check() {
    let ptr: *const i32 = std::ptr::null();
    assert!(ptr.is_null());
    
    let non_null: *const i32 = &42;
    assert!(!non_null.is_null());
}

// ==================== Miri 特定测试 ====================

/// 测试 17: Tree Borrows 与共享引用
/// 验证共享引用的兼容性
#[test]
fn test_tree_borrows_shared_ref() {
    let x = 42;
    let r1 = &x;
    let r2 = &x;
    
    // 多个共享引用共存
    assert_eq!(*r1, 42);
    assert_eq!(*r2, 42);
    
    // 重新借用
    let r3 = &*r1;
    assert_eq!(*r3, 42);
}

/// 测试 18: 内部可变性与 Miri
use std::cell::RefCell;

#[test]
fn test_interior_mutability() {
    let cell = RefCell::new(0);
    
    {
        let mut borrow = cell.borrow_mut();
        *borrow = 42;
    }
    
    assert_eq!(*cell.borrow(), 42);
}

// ==================== 应该被 Miri 检测的错误（标记为 ignore） ====================

/// 测试 19: 使用已释放内存（应该 UB）
#[test]
#[ignore = "This test should fail with use-after-free"]
fn test_use_after_free() {
    let ptr = {
        let data = Box::new(42);
        &*data as *const i32
    };
    
    unsafe {
        let _ = *ptr; // UB!
    }
}

/// 测试 20: 双释放（应该 UB）
#[test]
#[ignore = "This test should fail with double-free"]
fn test_double_free() {
    let data = Box::new(42);
    let ptr = Box::into_raw(data);
    
    unsafe {
        Box::from_raw(ptr); // 第一次释放
        Box::from_raw(ptr); // 第二次释放 - UB!
    }
}

/// 测试 21: 越界访问（应该 UB）
#[test]
#[ignore = "This test should fail with out-of-bounds"]
fn test_out_of_bounds() {
    let arr = [1, 2, 3];
    let ptr = arr.as_ptr();
    
    unsafe {
        let _ = *ptr.offset(10); // 越界 - UB!
    }
}

// ==================== 辅助模块 ====================

#[cfg(test)]
mod utils {
    use super::*;
    
    /// 安全包装：将 &[u8] 转换为 &str（带验证）
    pub fn safe_bytes_to_str(bytes: &[u8]) -> Option<&str> {
        std::str::from_utf8(bytes).ok()
    }
    
    /// 安全包装：MaybeUninit 数组初始化辅助
    pub fn init_array<T, const N: usize>(
        arr: &mut [MaybeUninit<T>; N],
        f: impl Fn(usize) -> T,
    ) {
        for (i, elem) in arr.iter_mut().enumerate() {
            elem.write(f(i));
        }
    }
}
