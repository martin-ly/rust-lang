//! Rust 关键字效应模式：用 async、Result、const 模拟受限的代数效应
//!
//! 本示例对应概念页 `concept/04_formal/07_concurrency_semantics/04_algebraic_effects.md`，
//! 展示 Rust 没有通用代数效应处理器时，如何通过关键字和类型系统显式管理副作用。

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker, RawWaker, RawWakerVTable};

// ============================================================================
// 1. async/await 作为“结构化并发”效应
// ============================================================================

async fn fetch_and_double(x: u32) -> u32 {
    // `await` 挂起当前计算，把续延交给 executor——这是关键字效应的典型形态。
    let y = async { x + 1 }.await;
    y * 2
}

/// 一个最小化的块级 executor，仅用于教学；生产环境请使用 tokio/async-std。
fn block_on<F: Future>(mut fut: F) -> F::Output {
    let waker = dummy_waker();
    let mut cx = Context::from_waker(&waker);
    // SAFETY: 我们在这个单线程、不移动的块级 executor 中轮询 Future。
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(v) => return v,
            Poll::Pending => {
                // 真实 executor 会在这里挂起线程或调度其他任务；
                // 最小示例直接再次轮询（busy loop），仅作演示。
            }
        }
    }
}

fn dummy_waker() -> Waker {
    const VTABLE: RawWakerVTable = RawWakerVTable::new(
        |_| RawWaker::new(std::ptr::null(), &VTABLE),
        |_| {},
        |_| {},
        |_| {},
    );
    let raw = RawWaker::new(std::ptr::null(), &VTABLE);
    // SAFETY: VTable 中的 clone/wake 都是 no-op，且数据指针未被解引用。
    unsafe { Waker::from_raw(raw) }
}

// ============================================================================
// 2. Result<T, E> + ? 作为“可恢复失败”效应
// ============================================================================

#[derive(Debug, PartialEq)]
enum ParseError {
    Empty,
    NotNumber,
}

fn parse_add_one(s: &str) -> Result<i32, ParseError> {
    if s.is_empty() {
        return Err(ParseError::Empty);
    }
    let n: i32 = s.parse().map_err(|_| ParseError::NotNumber)?;
    Ok(n + 1)
}

// ============================================================================
// 3. const fn / const 上下文作为“编译期计算”效应
// ============================================================================

const fn factorial(n: u32) -> u32 {
    let mut acc = 1;
    let mut i = 1;
    while i <= n {
        acc *= i;
        i += 1;
    }
    acc
}

const FACT_5: u32 = factorial(5);

// ============================================================================
// 4. 组合：async 函数返回 Result，显式叠加两种效应
// ============================================================================

async fn async_compute(s: &str) -> Result<i32, ParseError> {
    let n = parse_add_one(s)?;
    Ok(async { n * 2 }.await)
}

fn main() {
    // async
    assert_eq!(block_on(fetch_and_double(3)), 8);

    // Result
    assert_eq!(parse_add_one("7"), Ok(8));
    assert_eq!(parse_add_one("abc"), Err(ParseError::NotNumber));

    // const
    assert_eq!(FACT_5, 120);

    // combined
    assert_eq!(block_on(async_compute("5")), Ok(12));
    assert_eq!(block_on(async_compute("xyz")), Err(ParseError::NotNumber));

    println!("All keyword-effect patterns passed.");
}
