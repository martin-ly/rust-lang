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

/// 测试目的: 验证泛型 transmute（安全包装）
/// 测试场景: 将字节数组转换为整数
/// 预期结果: 应该正确转换并返回
fn safe_transmute<T, U>(value: T) -> U
where
    T: Copy,
    U: Copy,
{
    assert_eq!(mem::size_of::<T>(), mem::size_of::<U>());
    
    unsafe {
        let result = ptr::read(&value as *const T as *const U);
        let _ = value;
        result
    }
}

/// 测试目的: 验证泛型 transmute 功能
/// 测试场景: 将 [u8; 4] 转换为 u32
/// 预期结果: 应该正确解析字节序
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

/// 测试目的: 验证泛型 MaybeUninit 数组初始化
/// 测试场景: 使用闭包初始化泛型数组
/// 预期结果: 应该正确初始化所有元素
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

/// 测试目的: 验证泛型数组初始化
/// 测试场景: 初始化 [i32; 5] 数组
/// 预期结果: 应该正确初始化并返回
#[test]
fn test_generic_array_init() {
    let arr: [i32; 5] = init_array_generic(|i| i as i32 * 10);
    assert_eq!(arr, [0, 10, 20, 30, 40]);
}

// ==================== PhantomData ====================

/// 带生命周期的裸指针包装
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
        // SAFETY: 调用者保证指针有效
        unsafe { &*self.ptr }
    }
}

/// 测试目的: 验证 PhantomData 生命周期标记
/// 测试场景: 使用 PtrWithLifetime 访问数据
/// 预期结果: 应该能够安全解引用
#[test]
fn test_phantomdata_lifetime() {
    let data = 42;
    let ptr = PtrWithLifetime::new(&data);
    
    unsafe {
        assert_eq!(*ptr.dereference(), 42);
    }
}

/// 使用 PhantomData 禁用 Send
struct NonSend<T> {
    data: T,
    _marker: PhantomData<*const ()>,
}

impl<T> NonSend<T> {
    fn new(data: T) -> Self {
        Self {
            data,
            _marker: PhantomData,
        }
    }
}

/// 测试目的: 验证 NonSend 类型
/// 测试场景: 创建和使用 NonSend 包装的类型
/// 预期结果: 应该能够正常使用数据
#[test]
fn test_phantomdata_send_sync() {
    let non_send = NonSend::new(42);
    assert_eq!(non_send.data, 42);
}

// ==================== 泛型 Trait 边界 ====================

/// 要求类型实现 Sized
fn require_sized<T: Sized>(value: T) -> T {
    value
}

/// 测试目的: 验证 Sized 边界约束
/// 测试场景: 传递 i32 到要求 Sized 的函数
/// 预期结果: 应该正常工作
#[test]
fn test_sized_bound() {
    assert_eq!(require_sized(42), 42);
}

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

/// 测试目的: 验证 ?Sized 边界
/// 测试场景: 传递具体类型和 trait object
/// 预期结果: 两者都应该工作
#[test]
fn test_unsized_bound() {
    let x = 21;
    assert_eq!(use_trait_object(&x), 42);
    
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

/// 测试目的: 验证关联类型内存布局
/// 测试场景: 使用关联类型访问数据
/// 预期结果: 应该正确获取数据
#[test]
fn test_associated_type() {
    let wrapper = Wrapper(42);
    assert_eq!(wrapper.get(), Some(&42));
}

// ==================== 泛型生命周期 ====================

/// 包含多个生命周期参数的结构体
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

/// 测试目的: 验证复杂生命周期
/// 测试场景: 创建包含多个引用的结构体
/// 预期结果: 应该正确访问两个字段
#[test]
fn test_complex_lifetimes() {
    let x = 1;
    let y = 2;
    let borrowed = Borrowed::new(&x, &y);
    
    assert_eq!(*borrowed.first, 1);
    assert_eq!(*borrowed.second, 2);
}

// ==================== 泛型常量 ====================

/// 使用常量泛型的数组包装
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

/// 测试目的: 验证常量泛型
/// 测试场景: 创建 ArrayWrapper<i32, 5>
/// 预期结果: 应该创建正确大小的数组
#[test]
fn test_const_generic() {
    let arr: ArrayWrapper<i32, 5> = ArrayWrapper::new();
    assert_eq!(arr.data, [0; 5]);
}

/// 测试目的: 验证常量泛型数组分割
/// 测试场景: 分割数组为两部分
/// 预期结果: 应该正确分割数组
fn split_array<T, const N: usize>(arr: [T; N]) -> (Vec<T>, Vec<T>)
where
    T: Copy,
{
    let mid = N / 2;
    let mut first = Vec::with_capacity(mid);
    let mut second = Vec::with_capacity(N - mid);
    
    for (i, elem) in arr.into_iter().enumerate() {
        if i < mid {
            first.push(elem);
        } else {
            second.push(elem);
        }
    }
    
    (first, second)
}

/// 测试目的: 验证数组分割
/// 测试场景: 分割 [i32; 6] 数组
/// 预期结果: 应该正确分割为两部分
#[test]
fn test_const_generic_expr() {
    let arr = [1, 2, 3, 4, 5, 6];
    let (first, second) = split_array(arr);
    
    assert_eq!(first, vec![1, 2, 3]);
    assert_eq!(second, vec![4, 5, 6]);
}

// ==================== 泛型特化模式 ====================

/// 带泛型的 Drop 实现
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

/// 测试目的: 验证泛型 Drop
/// 测试场景: 创建 GenericDrop 并取出值
/// 预期结果: Drop 时应该安全处理 None
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

/// 测试目的: 验证闭包 Trait 边界
/// 测试场景: 使用 trait object 调用闭包
/// 预期结果: 应该正确调用并返回结果
#[test]
fn test_closure_trait_bound() {
    let double: &dyn Callable = &|x: i32| x * 2;
    assert_eq!(double.call(21), 42);
}

// ==================== 泛型与 unsafe ====================

/// 泛型裸指针写入
fn generic_ptr_write<T>(ptr: *mut T, value: T) {
    unsafe {
        ptr::write(ptr, value);
    }
}

/// 泛型裸指针读取
fn generic_ptr_read<T: Copy>(ptr: *const T) -> T {
    unsafe {
        ptr::read(ptr)
    }
}

/// 测试目的: 验证泛型指针操作
/// 测试场景: 使用泛型函数读写指针
/// 预期结果: 应该正确读写值
#[test]
fn test_generic_ptr_ops() {
    let mut x = 0i32;
    generic_ptr_write(&mut x, 42);
    assert_eq!(generic_ptr_read(&x), 42);
}

/// 泛型内存替换
fn generic_replace<T>(dest: &mut T, src: T) -> T {
    unsafe {
        let result = ptr::read(dest);
        ptr::write(dest, src);
        result
    }
}

/// 测试目的: 验证泛型替换
/// 测试场景: 替换变量的值
/// 预期结果: 应该返回旧值并设置新值
#[test]
fn test_generic_replace() {
    let mut x = 10;
    let old = generic_replace(&mut x, 20);
    
    assert_eq!(old, 10);
    assert_eq!(x, 20);
}

// ==================== 类型擦除 ====================

/// 类型擦除结构
struct TypeErased {
    data: *mut (),
    drop_fn: unsafe fn(*mut ()),
}

impl TypeErased {
    fn new<T>(value: T) -> Self {
        let boxed = Box::new(value);
        let data = Box::into_raw(boxed) as *mut ();
        
        unsafe fn drop_fn<T>(ptr: *mut ()) {
            // SAFETY: ptr 是由 Box::into_raw 创建的
            unsafe {
                let _ = Box::from_raw(ptr as *mut T);
            }
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

/// 测试目的: 验证类型擦除
/// 测试场景: 创建 TypeErased 并丢弃
/// 预期结果: 应该正确调用析构函数
#[test]
fn test_type_erasure() {
    let erased = TypeErased::new(42i32);
    drop(erased);
}

// ==================== 默认类型参数 ====================

/// 带默认类型参数的 Config
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

/// 测试目的: 验证默认类型参数
/// 测试场景: 使用默认类型参数创建 Config
/// 预期结果: 应该使用默认类型 i32 和大小 10
#[test]
fn test_default_type_params() {
    let config: Config = Config::new();
    assert_eq!(config.data, [0; 10]);
}
