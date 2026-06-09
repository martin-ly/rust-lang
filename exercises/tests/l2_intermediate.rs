//! L2 进阶概念可运行测验
//!
//! 覆盖 Trait、泛型、生命周期标注核心概念
//! 运行: cargo test -p exercises --test l2_intermediate

// ============================================================================
// 测验 1: Trait 定义与实现
// ============================================================================

trait Greet {
    fn greet(&self) -> String;
}

struct Person {
    name: String,
}

impl Greet for Person {
    fn greet(&self) -> String {
        format!("Hello, {}!", self.name)
    }
}

#[test]
fn test_trait_impl() {
    let p = Person {
        name: String::from("Alice"),
    };
    assert_eq!(p.greet(), "Hello, Alice!");
}

// ============================================================================
// 测验 2: Trait Bound
// ============================================================================

fn print_debug<T: std::fmt::Debug>(value: T) -> String {
    format!("{:?}", value)
}

#[test]
fn test_trait_bound() {
    assert_eq!(print_debug(42), "42");
    assert_eq!(print_debug("hello"), "\"hello\"");
}

// ============================================================================
// 测验 3: 默认实现
// ============================================================================

trait Counter {
    fn count(&self) -> i32;
    fn count_twice(&self) -> i32 {
        self.count() * 2
    }
}

struct Three;

impl Counter for Three {
    fn count(&self) -> i32 {
        3
    }
}

#[test]
fn test_default_impl() {
    let t = Three;
    assert_eq!(t.count(), 3);
    assert_eq!(t.count_twice(), 6);
}

// ============================================================================
// 测验 4: Orphan Rule（在当前 crate 中可行）
// ============================================================================

trait MyTrait {
    fn my_id(&self) -> &'static str;
}

// 为外部类型实现自定义 trait 是允许的（Orphan Rule 满足）
impl MyTrait for String {
    fn my_id(&self) -> &'static str {
        "String"
    }
}

#[test]
fn test_orphan_rule_local_trait() {
    let s = String::from("test");
    assert_eq!(s.my_id(), "String");
}

// ============================================================================
// 测验 5: Trait 对象与对象安全
// ============================================================================

trait Drawable {
    fn draw(&self) -> String;
}

impl Drawable for i32 {
    fn draw(&self) -> String {
        format!("drawing number: {}", self)
    }
}

impl Drawable for String {
    fn draw(&self) -> String {
        format!("drawing text: {}", self)
    }
}

fn render(item: &dyn Drawable) -> String {
    item.draw()
}

#[test]
fn test_trait_object() {
    let n: i32 = 42;
    let s = String::from("hello");
    assert_eq!(render(&n), "drawing number: 42");
    assert_eq!(render(&s), "drawing text: hello");
}

// ============================================================================
// 测验 6: 泛型函数（需要 Trait Bound）
// ============================================================================

fn largest<T: PartialOrd>(a: T, b: T) -> T {
    if a > b { a } else { b }
}

#[test]
fn test_generic_function() {
    assert_eq!(largest(1, 2), 2);
    assert_eq!(largest(3.0, 2.5), 3.0);
    assert_eq!(largest("a", "z"), "z");
}

// ============================================================================
// 测验 7: 泛型结构体
// ============================================================================

struct Point<T> {
    x: T,
    y: T,
}

#[test]
fn test_generic_struct() {
    let p1 = Point { x: 1, y: 2 };
    let p2 = Point { x: 1.0, y: 2.0 };
    assert_eq!(p1.x + p1.y, 3);
    assert_eq!(p2.x + p2.y, 3.0);
    // Point<i32> 和 Point<f64> 是完全不同的类型
}

// ============================================================================
// 测验 8: 多个 Trait Bound
// ============================================================================

fn process<T>(item: T) -> String
where
    T: Clone + std::fmt::Debug,
{
    let copy = item.clone();
    format!("{:?}", copy)
}

#[test]
fn test_multiple_trait_bounds() {
    assert_eq!(process(42i32), "42");
    assert_eq!(process(String::from("hi")), "\"hi\"");
}

// ============================================================================
// 测验 9: 关联类型
// ============================================================================

trait Container {
    type Item;
    fn get(&self) -> Option<&Self::Item>;
}

struct Wrapper<T>(T);

impl<T> Container for Wrapper<T> {
    type Item = T;
    fn get(&self) -> Option<&T> {
        Some(&self.0)
    }
}

#[test]
fn test_associated_type() {
    let w = Wrapper(42);
    assert_eq!(w.get(), Some(&42));
}

// ============================================================================
// 测验 10: 生命周期标注
// ============================================================================

fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

#[test]
fn test_lifetime_annotation() {
    let s1 = String::from("longer text");
    let s2 = "short";
    let result = longest(&s1, s2);
    assert_eq!(result, "longer text");
}

// ============================================================================
// 测验 11: HRTB (Higher-Ranked Trait Bounds)
// ============================================================================

fn call_with_ref<F>(f: F) -> i32
where
    F: for<'a> Fn(&'a i32) -> &'a i32,
{
    let x = 42;
    let r = f(&x);
    *r
}

#[test]
fn test_hrtb() {
    let result = call_with_ref(|x| x);
    assert_eq!(result, 42);
}

// ============================================================================
// 测验 12: 泛型与 trait 组合：迭代器适配器模式
// ============================================================================

fn sum_even<T>(iter: T) -> i32
where
    T: Iterator<Item = i32>,
{
    iter.filter(|x| x % 2 == 0).sum()
}

#[test]
fn test_generic_iterator() {
    let v = vec![1, 2, 3, 4, 5, 6];
    assert_eq!(sum_even(v.into_iter()), 12); // 2 + 4 + 6
}

// ============================================================================
// 测验 13: 新类型（Newtype）零成本抽象
// ============================================================================

use std::mem;

#[test]
fn test_newtype_zero_cost() {
    #[allow(dead_code)]
    struct Kilometers(f64);
    #[allow(dead_code)]
    struct Miles(f64);

    assert_eq!(mem::size_of::<Kilometers>(), mem::size_of::<f64>());
    assert_eq!(mem::size_of::<Miles>(), mem::size_of::<f64>());
    assert_eq!(mem::align_of::<Kilometers>(), mem::align_of::<f64>());
}

// ============================================================================
// 测验 14: Niche Value Optimization (Option<&T>)
// ============================================================================

#[test]
fn test_niche_value_optimization() {
    assert_eq!(mem::size_of::<&u32>(), mem::size_of::<Option<&u32>>());
    assert_eq!(
        mem::size_of::<Box<u32>>(),
        mem::size_of::<Option<Box<u32>>>()
    );
    // Option<u32> 有额外 tag，所以更大
    assert!(mem::size_of::<Option<u32>>() > mem::size_of::<u32>());
}

// ============================================================================
// 测验 15: 闭包可变捕获
// ============================================================================

#[test]
fn test_closure_mut_capture() {
    let mut count = 0;
    let mut inc = || {
        count += 1;
    };
    inc();
    inc();
    assert_eq!(count, 2);
}

// ============================================================================
// 测验 16: 模块与 use
// ============================================================================

mod test_api {
    pub fn helper() -> i32 {
        42
    }
    pub const VALUE: i32 = 99;
}

#[test]
fn test_module_use() {
    use test_api::helper;
    assert_eq!(helper(), 42);
    assert_eq!(test_api::VALUE, 99);
}
