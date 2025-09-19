//! Rust 1.90 语言要点演示（类型系统视角）
//!
//! 说明：
//! - 本示例以“可编译、可运行”的最小片段，串联 Rust 1.90 常用语法与类型系统用法。
//! - 每个小节均给出中文注释，强调“何时使用、为何如此、边界与陷阱”。
//! - 若需更系统化覆盖，请结合 `docs/RUST_190_COMPREHENSIVE_GUIDE.md` 查阅。

fn main() {
    println!("Rust 1.90 类型系统与语法要点演示启动…");

    // 1) 常量泛型（Const Generics）基础与占位推断（示意）
    demo_const_generics();

    // 2) 模式解构与结构体/枚举匹配
    demo_struct_destructure();
    demo_enum_match_exhaustive();

    // 3) 字符串与切片的类型界限：&str / String / &[u8]
    demo_string_and_slices();

    // 4) 生命周期标注风格与易混点（仅注释讲解，代码给出等价显式写法）
    let life_out = demo_lifetime_explicit(&42);
    println!("lifetime demo -> {}", life_out);

    // 5) 条件编译与目标特性（target_feature / cfg）
    demo_cfg_target_feature();

    // 6) type alias 与 impl Trait（返回位置）：封装复杂类型签名
    println!("sum_three -> {}", sum_three(1, 2, 3));

    // 7) newtype 与类型等价/透明封装（Deref 不等价于子类型）
    demo_newtype_and_equivalence();

    println!("演示完成。");
}

// --------------------------- 1) 常量泛型 ---------------------------

/// 使用常量泛型参数 N 描述固定长度数组的处理。
/// - 好处：在类型层面编码“长度”信息，避免运行期开销；
/// - 限制：N 必须是编译期常量（usize 等），表达式需可在编译期求值。
fn sum_array<const N: usize>(arr: [i32; N]) -> i32 {
    arr.iter().sum()
}

fn demo_const_generics() {
    // 显式传入：sum_array::<3>(...)
    let a = [1, 2, 3];
    let s1 = sum_array::<3>(a);

    // 在许多情形下，编译器可从实参推断 N：
    // 注意：推断能力依上下文而定，此处可直接省略显式::<N>
    let b = [4, 5, 6, 7];
    let s2 = sum_array(b);

    println!("const generics -> s1: {}, s2: {}", s1, s2);
}

// ----------------- 2) 模式解构与结构体/枚举匹配 -----------------

#[derive(Debug, Clone, Copy)]
struct Point { x: i32, y: i32 }

fn demo_struct_destructure() {
    let p = Point { x: 10, y: -4 };

    // 结构体解构到同名变量
    let Point { x, y } = p;
    assert_eq!(x, 10);
    assert_eq!(y, -4);

    // 带重命名的解构
    let Point { x: px, y: py } = p;
    println!("struct destructure -> ({}, {}) / ({}, {})", x, y, px, py);
}

#[derive(Debug)]
enum Shape {
    Circle { r: f64 },
    Rect { w: f64, h: f64 },
}

fn area(s: &Shape) -> f64 {
    match s {
        Shape::Circle { r } => core::f64::consts::PI * r * r,
        Shape::Rect { w, h } => w * h,
    }
}

fn demo_enum_match_exhaustive() {
    let c = Shape::Circle { r: 2.0 };
    let r = Shape::Rect { w: 3.0, h: 4.0 };
    println!("enum match -> circle: {:.2}, rect: {:.2}", area(&c), area(&r));
}

// --------------- 3) 字符串与切片：&str / String / &[u8] ---------------

fn takes_str(s: &str) -> usize { s.len() }
fn takes_bytes(b: &[u8]) -> usize { b.len() }

fn demo_string_and_slices() {
    let owned = String::from("你好, Rust 1.90");
    let s_len = takes_str(&owned);            // &String -> &str 自动解引用
    let b_len = takes_bytes(owned.as_bytes());
    println!("strings/slices -> len(str): {}, len(bytes): {}", s_len, b_len);
}

// ------- 4) 生命周期标注风格：显式写法与等价推断（讲解性示例） -------

/// 返回与入参引用“相同生命周期”的引用。
/// - 普通场景下编译器的省略规则可推断；
/// - 教学上可显式写出，帮助理解“借用不超过被借用者的活跃期”。
fn demo_lifetime_explicit<'a>(x: &'a i32) -> &'a i32 { x }

// ---------------- 5) 条件编译与目标特性：target_feature ----------------

#[allow(unused_variables)]
fn demo_cfg_target_feature() {
    // 根据平台/编译目标开启分支；
    // 注意：下述分支仅作演示，不要求实际平台具备对应特性。
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        println!("cfg -> x86/x86_64 平台分支");
        // 也可进一步基于 target_feature 区分指令集：
        #[cfg(target_feature = "sse2")]
        println!("cfg(target_feature = sse2) 命中");
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    {
        println!("cfg -> 非 x86 家族平台分支");
    }
}

// --------- 6) type alias 与 impl Trait（返回位置，用于隐藏类型） ---------

type ThreeTuple = (i32, i32, i32);

fn build_three(a: i32, b: i32, c: i32) -> ThreeTuple { (a, b, c) }

fn sum_three(a: i32, b: i32, c: i32) -> impl core::fmt::Display {
    let (x, y, z) = build_three(a, b, c);
    x + y + z
}

// ---------------- 7) newtype 与等价性：透明封装而非子类型 ----------------

use core::ops::Deref;

struct UserId(u64); // newtype：在类型层次上区分“语义”，防止误用

impl Deref for UserId {
    type Target = u64;
    fn deref(&self) -> &Self::Target { &self.0 }
}

fn demo_newtype_and_equivalence() {
    let id = UserId(42);
    // Deref 便捷访问底层值，但并不意味着“子类型”关系（不可替代所有 u64 位置）。
    let same: u64 = *id; // 通过解引用获取 u64 拷贝
    println!("newtype -> {}", same);
}


