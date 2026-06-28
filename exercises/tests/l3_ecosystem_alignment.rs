//! L3 生态对齐与版本跟踪嵌入式测验 — 可运行验证
//!
//! 主题覆盖：
//! - Rust 1.97 特性等价行为（VecDeque、Box/NonNull、格式化、随机源）
//! - 异步运行时生态迁移（async-std 归档 → Tokio / smol）
//! - Web 框架演进（Axum 0.8 路径语法）
//! - WASI 目标重命名
//! - 形式化工具概念（Safety Tags、BorrowSanitizer、Verus/AutoVerus 思维模型）
//!
//! 运行: cargo test --test l3_ecosystem_alignment

use std::collections::VecDeque;

// ========== Rust 1.97 标准库特性（等效实现验证）==========

/// 测验1: VecDeque::truncate_front 保留尾部 n 个元素
/// 1.97+ 将直接使用 `deque.truncate_front(2)`。
#[test]
fn test_vecdeque_truncate_front_retains_back() {
    let mut deque: VecDeque<i32> = [1, 2, 3, 4, 5].into_iter().collect();

    // 等效实现（1.97 前）
    while deque.len() > 2 {
        deque.pop_front();
    }

    assert_eq!(deque.make_contiguous(), &[4, 5]);
}

/// 测验2: Box::into_raw + NonNull 提供对堆分配的非空指针
/// 对应 `box_vec_non_null` 系列 API（预期 API 为 `Box::into_non_null`）的设计动机。
#[test]
fn test_box_into_non_null_concept() {
    let b = Box::new(42i32);
    let raw = Box::into_raw(b);
    let maybe_null = std::ptr::NonNull::new(raw);

    assert!(maybe_null.is_some());
    let nn = maybe_null.unwrap();
    unsafe {
        assert_eq!(*nn.as_ptr(), 42);
        // 回收所有权，避免泄漏
        let _ = Box::from_raw(nn.as_ptr());
    }
}

/// 测验3: 整数格式化为字符串的零分配替代思路
/// 1.97 `int_format_into` 允许将数字直接写入已有缓冲区。
#[test]
fn test_int_format_into_buffer() {
    let n = 2026i32;
    let mut buf = String::with_capacity(8);
    // 等效实现（1.97 前使用 write! / format!）
    use std::fmt::Write;
    write!(&mut buf, "{}", n).unwrap();

    assert_eq!(buf, "2026");
    assert!(buf.capacity() >= 4);
}

/// 测验4: RandomSource trait 概念 — 统一随机字节来源抽象
/// 在标准库 `RandomSource` 稳定前，可用 `getrandom` 风格的 fill_bytes 语义理解。
#[test]
fn test_random_source_trait_concept() {
    // 概念：RandomSource 提供 `fill_bytes(&mut self, dest: &mut [u8])`
    fn fill_with_os_random(dest: &mut [u8]) {
        // 教学等价：实际 RandomSource 可能内部调用 OS random。
        // 这里用确定性伪随机模拟接口语义。
        let mut seed = 0x12345678u32;
        for byte in dest.iter_mut() {
            seed = seed.wrapping_mul(1103515245).wrapping_add(12345);
            *byte = (seed >> 16) as u8;
        }
    }

    let mut buf = [0u8; 16];
    fill_with_os_random(&mut buf);

    // 16 字节全为零的概率可忽略（伪随机种子非零）
    assert!(buf.iter().any(|&b| b != 0));
}

// ========== 异步运行时生态迁移 ==========

/// 测验5: async-std 已归档，新项目应使用 Tokio 的 spawn/join
#[tokio::test]
async fn test_async_std_replaced_by_tokio_spawn() {
    let handle = tokio::spawn(async { 42 });
    assert_eq!(handle.await.unwrap(), 42);
}

/// 测验6: smol 作为 async-std 的轻量替代方案，语义同样是 block_on + spawn
/// 由于本 crate 未引入 smol，使用 tokio 的等价 API 验证 "替代运行时" 概念。
#[tokio::test]
async fn test_smol_as_async_std_alternative() {
    // smol 风格：smol::block_on(async { smol::spawn(...).detach(); rx.recv().await })
    // tokio 等价实现：
    let (tx, mut rx) = tokio::sync::mpsc::channel::<i32>(1);
    tokio::spawn(async move { tx.send(7).await.unwrap() });

    assert_eq!(rx.recv().await, Some(7));
}

// ========== Web 框架演进 ==========

/// 测验7: Axum 0.8 路径参数语法从 `/:id` 改为 `/{id}`
#[test]
fn test_axum_08_path_syntax() {
    // 0.7 及以前: "/users/:id"
    // 0.8 及以后: "/users/{id}"
    let axum_07_route = "/users/:id";
    let axum_08_route = "/users/{id}";

    assert_ne!(axum_07_route, axum_08_route);
    assert!(axum_08_route.contains('{'));
    assert!(axum_08_route.contains('}'));
}

// ========== WASI 目标迁移 ==========

/// 测验8: 旧目标 wasm32-wasi 已重命名为 wasm32-wasip1
#[test]
fn test_wasi_target_renamed() {
    let legacy = "wasm32-wasi";
    let preview1 = "wasm32-wasip1";
    let preview2 = "wasm32-wasip2";

    assert_ne!(legacy, preview1);
    assert!(preview1.ends_with("wasip1"));
    assert!(preview2.ends_with("wasip2"));
}

// ========== 形式化工具与安全概念 ==========

/// 测验9: Safety Tags 概念 — 用 unsafe trait 标记需要人工验证的契约
#[test]
fn test_safety_tags_concept_unsafe_trait() {
    /// # Safety
    /// 实现者必须保证 `as_ptr` 返回合法非空指针，且 `len` 与所指缓冲区匹配。
    unsafe trait ContiguousMemory {
        fn as_ptr(&self) -> *const u8;
        fn len(&self) -> usize;
    }

    unsafe impl ContiguousMemory for [u8; 4] {
        fn as_ptr(&self) -> *const u8 {
            self.as_slice().as_ptr()
        }
        fn len(&self) -> usize {
            self.as_slice().len()
        }
    }

    let data = [1u8, 2, 3, 4];
    // 通过 trait 方法调用，验证 Safety Tag 契约的接口语义
    assert_eq!(ContiguousMemory::len(&data), 4);
    assert!(!ContiguousMemory::as_ptr(&data).is_null());
}

/// 测验10: BorrowSanitizer / Stacked Borrows 概念 — 别名违规可在运行时被检测
/// RefCell 在运行时的借用检查是 BorrowSanitizer/Miri catch aliasing bugs 的教学类比。
#[test]
#[should_panic(expected = "already mutably borrowed")]
fn test_borrow_sanitizer_aliasing_concept() {
    let x = std::cell::RefCell::new(42);

    let _r1 = x.borrow_mut();
    // 在已有可变借用时尝试不可变借用，运行时 panic
    let _r2 = x.borrow();

    unreachable!("不会执行到这里");
}

/// 测验11: Verus / AutoVerus 概念 — 使用前置/后置条件表达不变量
/// （本测验展示 Verus 风格的前置/后置条件思维模型，非真实 Verus 语法）
#[test]
fn test_verus_style_spec_concept() {
    /// 要求: `a > 0 && b > 0`
    /// 保证: `返回 >= a && 返回 >= b`
    fn lcm_like(a: u64, b: u64) -> u64 {
        assert!(a > 0 && b > 0, "precondition violated");
        let result = a * b / gcd(a, b);
        assert!(result >= a && result >= b, "postcondition violated");
        result
    }

    fn gcd(a: u64, b: u64) -> u64 {
        if b == 0 { a } else { gcd(b, a % b) }
    }

    assert_eq!(lcm_like(4, 6), 12);
    assert_eq!(lcm_like(5, 7), 35);
}

/// 测验12: Rust Project Goals 2026 关键主题记忆
#[test]
fn test_rust_project_goals_2026_themes() {
    let goals = [
        "Async Closure",
        "Async Iteration",
        "Pin Ergonomics",
        "Return Type Notation",
        "BorrowSanitizer",
        "Safety Tags",
    ];

    assert!(goals.contains(&"Pin Ergonomics"));
    assert!(goals.contains(&"BorrowSanitizer"));
    assert!(goals.contains(&"Safety Tags"));
}
