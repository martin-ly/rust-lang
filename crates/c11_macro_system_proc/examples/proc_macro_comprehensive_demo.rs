//! Proc-Macro 综合演示
//!
//! 运行方式：
//!   cargo run --example proc_macro_comprehensive_demo -p c11_macro_system_proc

use c11_macro_system_proc::{AutoClone, Builder, conditional, debug_print, serializable, timed};

// ============================================================
// 1. Builder 派生宏 —— 自动生成 Builder 模式
// ============================================================

#[derive(Builder, Debug, PartialEq)]
struct ServerConfig {
    host: String,
    port: u16,
    workers: usize,
}

fn demo_builder() {
    println!("=== Builder 派生宏 ===");
    let config = ServerConfig::builder()
        .host("127.0.0.1".to_string())
        .port(8080)
        .workers(4)
        .build()
        .expect("构建配置失败");

    assert_eq!(config.host, "127.0.0.1");
    assert_eq!(config.port, 8080);
    assert_eq!(config.workers, 4);
    println!("✅ Builder 模式正常工作: {:?}", config);
}

// ============================================================
// 2. AutoClone 派生宏 —— 自动实现 Clone
// ============================================================

#[derive(AutoClone, Debug)]
struct Point {
    x: f64,
    y: f64,
    label: String,
}

fn demo_auto_clone() {
    println!("\n=== AutoClone 派生宏 ===");
    let p1 = Point {
        x: 1.0,
        y: 2.0,
        label: "A".to_string(),
    };
    let p2 = p1.clone();
    assert_eq!(p1.x, p2.x);
    assert_eq!(p1.label, p2.label);
    println!("✅ AutoClone 正常工作: {:?}", p2);
}

// ============================================================
// 3. debug_print 属性宏 —— 保留完整函数签名，自动注入调试打印
// ============================================================

#[debug_print]
fn compute_sum(a: i32, b: i32) -> i32 {
    a + b
}

#[debug_print]
async fn async_greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

fn demo_debug_print() {
    println!("\n=== debug_print 属性宏 ===");
    let result = compute_sum(3, 5);
    assert_eq!(result, 8);
    println!("✅ debug_print 保留签名 + 注入调试打印，返回值: {}", result);
}

// ============================================================
// 4. timed 属性宏 —— 保留完整函数签名，自动计时
// ============================================================

#[timed]
fn slow_computation(n: u64) -> u64 {
    let mut sum = 0u64;
    for i in 0..n {
        sum += i;
    }
    sum
}

fn demo_timed() {
    println!("\n=== timed 属性宏 ===");
    let result = slow_computation(1_000_000);
    println!("✅ timed 宏计时完成，计算结果: {}", result);
}

// ============================================================
// 5. serializable 函数宏 —— 为结构体生成 Debug + to_json
// ============================================================

serializable! {
    struct User {
        id: u32,
        name: String,
        active: bool,
    }
}

fn demo_serializable() {
    println!("\n=== serializable 函数宏 ===");
    let user = User {
        id: 42,
        name: "Alice".to_string(),
        active: true,
    };
    println!("✅ serializable 生成 Debug: {:?}", user);
    println!("✅ serializable 生成 to_json: {}", user.to_json());
}

// ============================================================
// 6. conditional 函数宏 —— 编译期条件分支选择
// ============================================================

fn demo_conditional() {
    println!("\n=== conditional 函数宏 ===");

    let message = conditional! {
        #[cfg(debug_assertions)]
        "调试模式构建"

        #[cfg(not(debug_assertions))]
        "发布模式构建"
    };

    println!("✅ conditional 编译期分支选择: {}", message);
}

// ============================================================
// main
// ============================================================

fn main() {
    demo_builder();
    demo_auto_clone();
    demo_debug_print();
    demo_timed();
    demo_serializable();
    demo_conditional();

    println!("\n🎉 所有过程宏演示通过！");
}
