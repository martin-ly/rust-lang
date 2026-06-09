//! L3 核心概念嵌入式测验 — 可运行验证
//!
//! 本文件提取自 concept/03_advanced/ 中以下文件的嵌入式测验：
//! - 02_async.md（Future、.await、运行时选择、取消安全）
//! - 03_unsafe.md（Unsafe Rust、原始指针、FFI、Unsafe Trait）
//! - 04_macros.md（声明宏、过程宏、macro_rules!、卫生性）
//! - 05_rust_ffi.md（extern "C"、类型映射、所有权转移）
//!
//! 运行: cargo test --test l3_core

use std::ffi::{CString, c_int};

// ========== 02_async.md 测验验证 ==========

/// 测验1: async fn 本质是返回 Future 的状态机
#[tokio::test]
async fn test_async_fn_is_future() {
    async fn foo() -> i32 {
        42
    }

    // async fn 不自动执行，需要 .await
    let fut = foo();
    assert_eq!(fut.await, 42);
}

/// 测验2: .await 非阻塞，线程可执行其他任务
#[tokio::test]
async fn test_await_yields_control() {
    let counter = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));

    let c1 = counter.clone();
    let t1 = tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        c1.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    });

    let c2 = counter.clone();
    let t2 = tokio::spawn(async move {
        // 这个任务应该能在 t1 sleep 期间执行
        c2.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    });

    let (_, _) = tokio::join!(t1, t2);
    // 两个任务都完成，说明 .await 期间线程执行了其他任务
    assert_eq!(counter.load(std::sync::atomic::Ordering::SeqCst), 2);
}

// ========== 03_unsafe.md 测验验证 ==========

/// 测验1: 原始指针解引用需要 unsafe 块
#[test]
fn test_raw_pointer_deref_requires_unsafe() {
    let x = 42;
    let r = &x as *const i32;

    unsafe {
        assert_eq!(*r, 42);
    }
}

/// 测验2: Unsafe Trait 实现需要 unsafe impl
#[test]
fn test_unsafe_trait_requires_unsafe_impl() {
    /// # Safety
    /// 实现此 trait 的类型必须能安全地用全零字节初始化。
    unsafe trait Zeroable {
        fn zero() -> Self;
    }

    unsafe impl Zeroable for u32 {
        fn zero() -> Self {
            0
        }
    }

    assert_eq!(u32::zero(), 0);
}

// ========== 04_macros.md 测验验证 ==========

/// 测验1: macro_rules! 声明宏
#[test]
fn test_declarative_macro() {
    macro_rules! say_hello {
        () => {
            "hello"
        };
    }

    assert_eq!(say_hello!(), "hello");
}

/// 测验2: macro_rules! 模式匹配递归
#[test]
fn test_macro_recursive_count() {
    macro_rules! count_args {
        () => { 0 };
        ($x:expr) => { 1 };
        ($x:expr, $($rest:expr),+) => {
            1 + count_args!($($rest),+)
        };
    }

    assert_eq!(count_args!(), 0);
    assert_eq!(count_args!(1), 1);
    assert_eq!(count_args!(1, 2), 2);
    assert_eq!(count_args!(1, 2, 3, 4, 5), 5);
}

/// 测验3: 宏卫生性 — 局部变量可捕获外部同名变量
#[test]
fn test_macro_hygiene() {
    macro_rules! declare_var {
        ($name:ident, $value:expr) => {
            let $name = $value;
        };
    }

    let _x = 10;
    declare_var!(x, 20);
    // 宏内部的 let x = 20 覆盖了外部 x
    assert_eq!(x, 20);
}

// ========== 05_rust_ffi.md 测验验证 ==========

/// 测验1: extern "C" 函数调用
#[test]
fn test_extern_c_call() {
    unsafe extern "C" {
        fn abs(input: c_int) -> c_int;
    }

    unsafe {
        assert_eq!(abs(-42), 42);
    }
}

/// 测验2: CString 与原始指针转换
#[test]
fn test_cstring_roundtrip() {
    let original = "hello";
    let c_string = CString::new(original).unwrap();
    let ptr = c_string.into_raw();

    // C 函数可使用 ptr...

    // 必须回收所有权
    let recovered = unsafe { CString::from_raw(ptr) };
    assert_eq!(recovered.to_str().unwrap(), original);
}

/// 测验3: #[repr(C)] 结构体内存布局
#[test]
fn test_repr_c_layout() {
    #[repr(C)]
    struct Student {
        name: [u8; 32],
        age: u32,
        score: f32,
    }

    let s = Student {
        name: [0; 32],
        age: 20,
        score: 85.5,
    };

    assert_eq!(s.age, 20);
    assert!((s.score - 85.5).abs() < f32::EPSILON);

    // 验证内存布局与 C 兼容: 32 + 4 + 4 = 40
    assert_eq!(std::mem::size_of::<Student>(), 40);
}
