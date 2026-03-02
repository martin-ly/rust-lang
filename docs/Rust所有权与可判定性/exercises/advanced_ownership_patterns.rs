//! Rust高级所有权模式示例
//! 
//! 本文件展示Rust所有权系统的高级用法，包括：
//! - 复杂的生命周期管理
//! - 自引用结构
//! - 零成本抽象
//! - 内存布局优化

// ============================================
// 1. 复杂生命周期模式
// ============================================

/// 模式1: 多个生命周期参数
/// 
/// 'a 和 'b 可能有不同的生命周期
/// 返回的生命周期 'a 与输入 s1 绑定
fn select_string<'a, 'b>(s1: &'a str, s2: &'b str, flag: bool) -> &'a str {
    if flag { s1 } else { s2 }
}

/// 模式2: 生命周期省略的局限性
/// 
/// 以下函数无法使用生命周期省略规则
/// 需要显式标注
fn longest_with_suffix<'a>(s1: &'a str, s2: &'a str, suffix: &str) -> &'a str {
    let s = if s1.len() > s2.len() { s1 } else { s2 };
    // suffix 的生命周期与返回值无关
    println!("Suffix: {}", suffix);
    s
}

/// 模式3: 泛型生命周期约束
struct Parser<'a, 'b: 'a> {
    input: &'a str,
    delimiter: &'b str,
}

impl<'a, 'b: 'a> Parser<'a, 'b> {
    fn new(input: &'a str, delimiter: &'b str) -> Self {
        Self { input, delimiter }
    }
    
    fn parse(&self) -> Vec<&'a str> {
        self.input.split(self.delimiter).collect()
    }
}

// ============================================
// 2. 自引用结构模式
// ============================================

use std::pin::Pin;
use std::marker::PhantomPinned;

/// 模式4: 使用Pin的自引用结构
/// 
/// 这是安全的自引用实现方式
struct SelfReferential {
    data: String,
    // 使用原始指针存储自引用
    ptr: *const str,
    // PhantomPinned禁止Unpin，确保不会被移动
    _pin: PhantomPinned,
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });
        
        // 设置自引用
        let ptr = &boxed.data[..] as *const str;
        boxed.ptr = ptr;
        
        Pin::from(boxed)
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
    
    /// 获取自引用
    /// 
    /// # Safety
    /// 必须在Pin的保护下调用
    fn get_ref(self: Pin<&Self>) -> &str {
        unsafe { &*self.ptr }
    }
}

/// 模式5: 使用ouroboros crate的安全自引用
/// 
/// 这是生产环境推荐的做法
mod ouroboros_example {
    use ouroboros::self_referencing;
    
    #[self_referencing]
    struct Parser {
        data: String,
        #[borrows(data)]
        slice: &'this str,
    }
    
    fn use_parser() {
        let parser = ParserBuilder {
            data: String::from("hello world"),
            slice_builder: |data: &String| data.split_whitespace().next().unwrap(),
        }.build();
        
        // 使用parser.with_slice访问slice
        parser.with_slice(|slice| println!("{}", slice));
    }
}

// ============================================
// 3. 零成本抽象模式
// ============================================

/// 模式6: 迭代器链的零成本抽象
fn zero_cost_iterator_chain(data: &[i32]) -> i32 {
    data
        .iter()
        .filter(|&&x| x % 2 == 0)      // 过滤偶数
        .map(|x| x * x)                 // 平方
        .take(10)                       // 取前10个
        .sum()                          // 求和
    // 编译后等价于手写循环，无运行时开销
}

/// 模式7: 泛型单态化示例
fn generic_monomorphization() {
    fn process<T: AsRef<[u8]>>(data: T) -> usize {
        data.as_ref().len()
    }
    
    // 编译器为每种类型生成独立版本
    let _ = process(vec![1u8, 2, 3]);       // process::<Vec<u8>>
    let _ = process(&[1u8, 2, 3]);          // process::<&[u8]>
    let _ = process("hello");               // process::<&str>
}

/// 模式8: const泛型的零成本抽象
struct Array<T, const N: usize> {
    data: [T; N],
}

impl<T: Default + Copy, const N: usize> Array<T, N> {
    fn new() -> Self {
        Self { data: [T::default(); N] }
    }
    
    fn len(&self) -> usize {
        N  // 编译时常量，无运行时开销
    }
}

// ============================================
// 4. 内存布局优化
// ============================================

/// 模式9: 使用NonNull优化Option<Box<T>>
use std::ptr::NonNull;

struct OptimizedOption<T> {
    ptr: NonNull<T>,
}

impl<T> OptimizedOption<T> {
    fn new(value: T) -> Self {
        let boxed = Box::new(value);
        Self {
            ptr: NonNull::new(Box::into_raw(boxed)).unwrap(),
        }
    }
    
    fn as_ref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

/// 模式10: 手动内存布局控制
#[repr(C)]
struct PacketHeader {
    version: u8,
    flags: u8,
    length: u16,
    timestamp: u32,
}

/// 模式11: 使用MaybeUninit避免初始化开销
use std::mem::MaybeUninit;

fn uninitialized_array() {
    let mut arr: [MaybeUninit<i32>; 1024] = unsafe {
        MaybeUninit::uninit().assume_init()
    };
    
    // 按需初始化
    for (i, elem) in arr.iter_mut().enumerate() {
        elem.write(i as i32);
    }
    
    // 使用unsafe转换为正常数组
    let arr: [i32; 1024] = unsafe {
        std::mem::transmute::<_, [i32; 1024]>(arr)
    };
}

// ============================================
// 5. 智能指针自定义
// ============================================

use std::ops::{Deref, DerefMut};

/// 模式12: 自定义智能指针
struct MyBox<T> {
    ptr: NonNull<T>,
}

impl<T> MyBox<T> {
    fn new(value: T) -> Self {
        let boxed = Box::new(value);
        Self {
            ptr: NonNull::new(Box::into_raw(boxed)).unwrap(),
        }
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> DerefMut for MyBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        unsafe {
            let _ = Box::from_raw(self.ptr.as_ptr());
        }
    }
}

// ============================================
// 6. 类型擦除与动态分发
// ============================================

/// 模式13: 手动vtable实现（类似dyn Trait）
trait Drawable {
    fn draw(&self);
    fn area(&self) -> f64;
}

struct VTable {
    draw: fn(*const ()),
    area: fn(*const ()) -> f64,
    drop: fn(*mut ()),
}

struct DynDrawable {
    data: *mut (),
    vtable: &'static VTable,
}

impl DynDrawable {
    fn draw(&self) {
        (self.vtable.draw)(self.data)
    }
    
    fn area(&self) -> f64 {
        (self.vtable.area)(self.data)
    }
}

impl Drop for DynDrawable {
    fn drop(&mut self) {
        (self.vtable.drop)(self.data)
    }
}

// ============================================
// 7. 高级Drop模式
// ============================================

/// 模式14: 确定性析构顺序
struct ResourceA;
struct ResourceB;
struct ResourceC;

impl Drop for ResourceA {
    fn drop(&mut self) { println!("A dropped"); }
}

impl Drop for ResourceB {
    fn drop(&mut self) { println!("B dropped"); }
}

impl Drop for ResourceC {
    fn drop(&mut self) { println!("C dropped"); }
}

fn drop_order() {
    let _a = ResourceA;
    let _b = ResourceB;
    let _c = ResourceC;
    // 析构顺序: C, B, A (LIFO)
}

/// 模式15: 使用ManuallyDrop控制析构
use std::mem::ManuallyDrop;

struct ControlledDrop<T> {
    data: ManuallyDrop<T>,
}

impl<T> ControlledDrop<T> {
    fn new(data: T) -> Self {
        Self { data: ManuallyDrop::new(data) }
    }
    
    fn take(&mut self) -> T {
        unsafe { ManuallyDrop::take(&mut self.data) }
    }
    
    fn manual_drop(&mut self) {
        unsafe { ManuallyDrop::drop(&mut self.data) }
    }
}

// ============================================
// 8. 编译期计算
// ============================================

/// 模式16: const fn编译期计算
const fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

const FIB_10: u32 = fibonacci(10); // 编译期计算

/// 模式17: const泛型约束
struct Buffer<T, const SIZE: usize> {
    data: [T; SIZE],
}

impl<T: Default + Copy, const SIZE: usize> Buffer<T, SIZE> {
    const fn new() -> Self {
        Self { data: [T::default(); SIZE] }
    }
    
    const fn capacity() -> usize {
        SIZE
    }
}

// ============================================
// 测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_self_referential() {
        let data = String::from("hello");
        let sr = SelfReferential::new(data);
        assert_eq!(sr.get_data(), "hello");
        assert_eq!(sr.get_ref(), "hello");
    }
    
    #[test]
    fn test_zero_cost_iterator() {
        let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let sum = zero_cost_iterator_chain(&data);
        assert_eq!(sum, 4 + 16 + 36 + 64 + 100); // 偶数平方和
    }
    
    #[test]
    fn test_const_generic() {
        let arr: Array<i32, 10> = Array::new();
        assert_eq!(arr.len(), 10);
    }
    
    #[test]
    fn test_my_box() {
        let mut b = MyBox::new(42);
        assert_eq!(*b, 42);
        *b = 100;
        assert_eq!(*b, 100);
    }
}

fn main() {
    println!("高级所有权模式示例");
    println!("FIB(10) = {}", FIB_10);
    
    // 自引用结构示例
    let sr = SelfReferential::new(String::from("self reference"));
    println!("Data: {}", sr.get_data());
    println!("Ref: {}", sr.get_ref());
    
    // Drop顺序示例
    drop_order();
}
