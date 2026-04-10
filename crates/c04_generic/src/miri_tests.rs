//! Miri 测试模块 - 泛型和 Trait 边界内存安全验证
//!
//! 本模块包含用于 Miri 测试的泛型和 Trait 相关代码示例。
//!
//! 运行方式:
//!   cargo miri test miri_tests
//!   MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test miri_tests

use std::marker::PhantomData;
use std::mem::{self, MaybeUninit};
use std::ptr;

// ==================== 泛型内存操作 ====================

/// 测试 1: 泛型 transmute（安全包装）
fn safe_transmute<T, U>(value: T) -> U
where
    T: Copy,
    U: Copy,
{
    assert_eq!(mem::size_of::<T>(), mem::size_of::<U>());
    
    unsafe {
        let result = ptr::read(&value as *const T as *const U);
        mem::forget(value);
        result
    }
}

#[test]
fn test_generic_transmute() {
    let bytes: [u8; 4] = [0x01, 0x00, 0x00, 0x00];
    let val: u32 = safe_transmute(bytes);
    
    if cfg!(target_endian = "little") {
        assert_eq!(val, 1);
    } else {
        assert_eq!(val, 0x01000000);
    }
}

/// 测试 2: 泛型 MaybeUninit 数组初始化
fn init_array_generic<T, const N: usize>(f: impl Fn(usize) -> T) -> [T; N] {
    let mut arr: [MaybeUninit<T>; N] = unsafe {
        MaybeUninit::uninit().assume_init()
    };
    
    for (i, elem) in arr.iter_mut().enumerate() {
        elem.write(f(i));
    }
    
    unsafe {
        let result = ptr::read(&arr as *const _ as *const [T; N]);
        mem::forget(arr);
        result
    }
}

#[test]
fn test_generic_array_init() {
    let arr: [i32; 5] = init_array_generic(|i| i as i32 * 10);
    assert_eq!(arr, [0, 10, 20, 30, 40]);
}

// ==================== PhantomData ====================

/// 测试 3: PhantomData 标记所有权
struct PtrWithLifetime<'a, T> {
    ptr: *const T,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> PtrWithLifetime<'a, T> {
    fn new(reference: &'a T) -> Self {
        Self {
            ptr: reference,
            _marker: PhantomData,
        }
    }
    
    unsafe fn dereference(&self) -> &'a T {
        &*self.ptr
    }
}

#[test]
fn test_phantomdata_lifetime() {
    let data = 42;
    let ptr = PtrWithLifetime::new(&data);
    
    unsafe {
        assert_eq!(*ptr.dereference(), 42);
    }
}

/// 测试 4: PhantomData 标记 Send/Sync
struct NonSend<T> {
    data: T,
    _marker: PhantomData<*const ()>, // *const () 不是 Send
}

impl<T> NonSend<T> {
    fn new(data: T) -> Self {
        Self {
            data,
            _marker: PhantomData,
        }
    }
}

#[test]
fn test_phantomdata_send_sync() {
    let non_send = NonSend::new(42);
    assert_eq!(non_send.data, 42);
}

// ==================== 泛型 Trait 边界 ====================

/// 测试 5: Sized 边界
fn require_sized<T: Sized>(value: T) -> T {
    value
}

#[test]
fn test_sized_bound() {
    assert_eq!(require_sized(42), 42);
}

/// 测试 6: ?Sized 宽松边界
trait MyTrait {
    fn do_something(&self) -> i32;
}

impl MyTrait for i32 {
    fn do_something(&self) -> i32 {
        *self * 2
    }
}

fn use_trait_object<T: MyTrait + ?Sized>(val: &T) -> i32 {
    val.do_something()
}

#[test]
fn test_unsized_bound() {
    let x = 21;
    assert_eq!(use_trait_object(&x), 42);
    
    // 使用 trait object
    let obj: &dyn MyTrait = &x;
    assert_eq!(use_trait_object(obj), 42);
}

// ==================== 关联类型 ====================

trait Container {
    type Item;
    fn get(&self) -> Option<&Self::Item>;
}

struct Wrapper<T>(T);

impl<T> Container for Wrapper<T> {
    type Item = T;
    
    fn get(&self) -> Option<&Self::Item> {
        Some(&self.0)
    }
}

/// 测试 7: 关联类型内存布局
#[test]
fn test_associated_type() {
    let wrapper = Wrapper(42);
    assert_eq!(wrapper.get(), Some(&42));
}

// ==================== 泛型生命周期 ====================

/// 测试 8: 复杂生命周期边界
struct Borrowed<'a, 'b, T, U>
where
    T: 'a,
    U: 'b,
{
    first: &'a T,
    second: &'b U,
}

impl<'a, 'b, T, U> Borrowed<'a, 'b, T, U> {
    fn new(first: &'a T, second: &'b U) -> Self {
        Self { first, second }
    }
}

#[test]
fn test_complex_lifetimes() {
    let x = 1;
    let y = 2;
    let borrowed = Borrowed::new(&x, &y);
    
    assert_eq!(*borrowed.first, 1);
    assert_eq!(*borrowed.second, 2);
}

// ==================== 泛型常量 ====================

/// 测试 9: 常量泛型
struct ArrayWrapper<T, const N: usize> {
    data: [T; N],
}

impl<T: Default + Copy, const N: usize> ArrayWrapper<T, N> {
    fn new() -> Self {
        Self {
            data: [T::default(); N],
        }
    }
}

#[test]
fn test_const_generic() {
    let arr: ArrayWrapper<i32, 5> = ArrayWrapper::new();
    assert_eq!(arr.data, [0; 5]);
}

/// 测试 10: 复杂常量泛型表达式
fn split_array<T, const N: usize>(arr: [T; N]) -> ([T; N/2], [T; N-N/2])
where
    T: Default + Copy,
{
    let mut first: [T; N/2] = [T::default(); N/2];
    let mut second: [T; N-N/2] = [T::default(); N-N/2];
    
    for (i, elem) in arr.into_iter().enumerate() {
        if i < N/2 {
            first[i] = elem;
        } else {
            second[i - N/2] = elem;
        }
    }
    
    (first, second)
}

#[test]
fn test_const_generic_expr() {
    let arr = [1, 2, 3, 4, 5, 6];
    let (first, second) = split_array(arr);
    
    assert_eq!(first, [1, 2, 3]);
    assert_eq!(second, [4, 5, 6]);
}

// ==================== 泛型特化模式 ====================

/// 测试 11: Drop 泛型实现
struct GenericDrop<T>(Option<T>);

impl<T> GenericDrop<T> {
    fn new(val: T) -> Self {
        Self(Some(val))
    }
    
    fn take(&mut self) -> Option<T> {
        self.0.take()
    }
}

impl<T> Drop for GenericDrop<T> {
    fn drop(&mut self) {
        // 清理逻辑
        let _ = self.0.take();
    }
}

#[test]
fn test_generic_drop() {
    {
        let mut g = GenericDrop::new(42);
        assert_eq!(g.take(), Some(42));
        // Drop 时 self.0 已经是 None
    }
}

// ==================== 高阶 Trait 边界 (HRTB) ====================

trait Callable {
    fn call(&self, input: i32) -> i32;
}

impl<F> Callable for F
where
    F: Fn(i32) -> i32,
{
    fn call(&self, input: i32) -> i32 {
        self(input)
    }
}

/// 测试 12: 闭包 Trait 边界
#[test]
fn test_closure_trait_bound() {
    let double: &dyn Callable = &|x: i32| x * 2;
    assert_eq!(double.call(21), 42);
}

// ==================== 泛型与 unsafe ====================

/// 测试 13: 泛型裸指针操作
fn generic_ptr_write<T>(ptr: *mut T, value: T) {
    unsafe {
        ptr::write(ptr, value);
    }
}

fn generic_ptr_read<T: Copy>(ptr: *const T) -> T {
    unsafe {
        ptr::read(ptr)
    }
}

#[test]
fn test_generic_ptr_ops() {
    let mut x = 0i32;
    generic_ptr_write(&mut x, 42);
    assert_eq!(generic_ptr_read(&x), 42);
}

/// 测试 14: 泛型内存替换
fn generic_replace<T>(dest: &mut T, src: T) -> T {
    unsafe {
        let result = ptr::read(dest);
        ptr::write(dest, src);
        result
    }
}

#[test]
fn test_generic_replace() {
    let mut x = 10;
    let old = generic_replace(&mut x, 20);
    
    assert_eq!(old, 10);
    assert_eq!(x, 20);
}

// ==================== 类型擦除 ====================

/// 测试 15: 类型擦除与 vtable
struct TypeErased {
    data: *mut (),
    drop_fn: unsafe fn(*mut ()),
}

impl TypeErased {
    fn new<T>(value: T) -> Self {
        let boxed = Box::new(value);
        let data = Box::into_raw(boxed) as *mut ();
        
        unsafe fn drop_fn<T>(ptr: *mut ()) {
            let _ = Box::from_raw(ptr as *mut T);
        }
        
        Self {
            data,
            drop_fn: drop_fn::<T>,
        }
    }
}

impl Drop for TypeErased {
    fn drop(&mut self) {
        unsafe {
            (self.drop_fn)(self.data);
        }
    }
}

#[test]
fn test_type_erasure() {
    let erased = TypeErased::new(42i32);
    drop(erased);
}

// ==================== 默认类型参数 ====================

/// 测试 16: 默认类型参数
struct Config<T = i32, const N: usize = 10> {
    data: [T; N],
}

impl<T: Default + Copy, const N: usize> Config<T, N> {
    fn new() -> Self {
        Self {
            data: [T::default(); N],
        }
    }
}

#[test]
fn test_default_type_params() {
    let config: Config = Config::new();
    assert_eq!(config.data, [0; 10]);
}
