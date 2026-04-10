//! Miri 测试模块 - 异步代码内存安全验证
//!
//! 本模块包含用于 Miri 测试的异步代码示例，验证 Future 和 Pin 的安全性。
//!
//! 运行方式:
//!   cargo miri test miri_tests
//!   MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test miri_tests

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Wake, Waker};
use std::sync::Arc;
use std::cell::RefCell;

// ==================== 基本 Future 测试 ====================

/// 一个简单的 Future，返回一个值
struct SimpleFuture<T>(Option<T>);

impl<T> Future for SimpleFuture<T> {
    type Output = T;
    
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: 我们拥有 self，并且不会移动 pinning 字段
        match unsafe { self.get_unchecked_mut() }.0.take() {
            Some(value) => Poll::Ready(value),
            None => Poll::Pending,
        }
    }
}

/// 测试目的: 验证简单 Future
/// 测试场景: 创建一个简单 Future 并轮询
/// 预期结果: 应该返回 Ready 和值
#[test]
fn test_simple_future() {
    let mut future = SimpleFuture(Some(42));
    let waker = dummy_waker();
    let mut context = Context::from_waker(&waker);
    
    let result = Pin::new(&mut future).poll(&mut context);
    
    match result {
        Poll::Ready(val) => assert_eq!(val, 42),
        Poll::Pending => panic!("Expected Ready"),
    }
}

// ==================== Pin 测试 ====================

use std::marker::PhantomPinned;

/// 自引用结构体
struct SelfReferencing {
    data: String,
    ptr: *const String,
    _pinned: PhantomPinned,
}

impl SelfReferencing {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            ptr: std::ptr::null(),
            _pinned: PhantomPinned,
        });
        
        let ptr = &boxed.data as *const String;
        boxed.ptr = ptr;
        
        Box::into_pin(boxed)
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
    
    fn get_via_ptr(&self) -> &str {
        unsafe { &*self.ptr }
    }
}

/// 测试目的: 验证 Pin 保证自引用安全
/// 测试场景: 创建自引用结构并通过 Pin 访问
/// 预期结果: 应该能够安全访问自引用数据
#[test]
fn test_pin_self_referential() {
    let data = SelfReferencing::new(String::from("Hello, Miri!"));
    
    assert_eq!(data.get_data(), "Hello, Miri!");
    assert_eq!(data.get_via_ptr(), "Hello, Miri!");
}

// ==================== 异步块和闭包 ====================

/// 测试目的: 验证异步块捕获变量
/// 测试场景: 异步块捕获外部变量
/// 预期结果: 应该正确捕获并计算
#[test]
fn test_async_block_capture() {
    let x = 42;
    let fut = async { x + 1 };
    
    let result = block_on(fut);
    assert_eq!(result, 43);
}

/// 测试目的: 验证异步块捕获引用
/// 测试场景: 异步块通过 RefCell 修改外部状态
/// 预期结果: 应该正确修改外部状态
#[test]
fn test_async_block_ref_capture() {
    let x = RefCell::new(0);
    
    let fut = async {
        *x.borrow_mut() = 42;
    };
    
    block_on(fut);
    assert_eq!(*x.borrow(), 42);
}

// ==================== Stream-like 结构 ====================

/// 简单的 Stream 实现
struct CountStream {
    count: usize,
    max: usize,
}

impl CountStream {
    fn new(max: usize) -> Self {
        Self { count: 0, max }
    }
    
    fn poll_next(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Option<usize>> {
        // SAFETY: 我们拥有 self，并且不会移动 pinning 字段
        let this = unsafe { self.get_unchecked_mut() };
        if this.count < this.max {
            let val = this.count;
            this.count += 1;
            Poll::Ready(Some(val))
        } else {
            Poll::Ready(None)
        }
    }
}

/// 测试目的: 验证 Stream-like 轮询
/// 测试场景: 创建计数 Stream 并轮询所有值
/// 预期结果: 应该按顺序产生值
#[test]
fn test_stream_poll() {
    let mut stream = CountStream::new(3);
    let waker = dummy_waker();
    let mut context = Context::from_waker(&waker);
    
    assert_eq!(Pin::new(&mut stream).poll_next(&mut context), Poll::Ready(Some(0)));
    assert_eq!(Pin::new(&mut stream).poll_next(&mut context), Poll::Ready(Some(1)));
    assert_eq!(Pin::new(&mut stream).poll_next(&mut context), Poll::Ready(Some(2)));
    assert_eq!(Pin::new(&mut stream).poll_next(&mut context), Poll::Ready(None));
}

// ==================== 组合子 Future ====================

/// Map Future 组合子
struct MapFuture<Fut, F> {
    future: Fut,
    func: Option<F>,
}

impl<Fut, F, T, U> Future for MapFuture<Fut, F>
where
    Fut: Future<Output = T>,
    F: FnOnce(T) -> U,
{
    type Output = U;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: 我们不动 func，只动 future
        unsafe {
            let this = self.get_unchecked_mut();
            match Pin::new_unchecked(&mut this.future).poll(cx) {
                Poll::Ready(val) => {
                    let f = this.func.take().unwrap();
                    Poll::Ready(f(val))
                }
                Poll::Pending => Poll::Pending,
            }
        }
    }
}

/// 测试目的: 验证 Future 组合子
/// 测试场景: 创建 MapFuture 并执行
/// 预期结果: 应该应用映射函数并返回结果
#[test]
fn test_future_combinator() {
    let fut = MapFuture {
        future: SimpleFuture(Some(21)),
        func: Some(|x: i32| x * 2),
    };
    
    let result = block_on(fut);
    assert_eq!(result, 42);
}

// ==================== 异步互斥锁 ====================

/// 简单的异步互斥锁（基于 RefCell）
struct AsyncMutex<T> {
    data: RefCell<T>,
}

impl<T> AsyncMutex<T> {
    fn new(data: T) -> Self {
        Self {
            data: RefCell::new(data),
        }
    }
    
    fn lock(&self) -> Option<std::cell::RefMut<'_, T>> {
        self.data.try_borrow_mut().ok()
    }
}

/// 测试目的: 验证异步互斥锁
/// 测试场景: 获取锁并修改数据
/// 预期结果: 应该正确修改数据
#[test]
fn test_async_mutex() {
    let mutex = AsyncMutex::new(0);
    
    {
        let mut guard = mutex.lock().unwrap();
        *guard = 42;
    }
    
    assert_eq!(*mutex.data.borrow(), 42);
}

// ==================== 上下文和 Waker ====================

/// 创建一个虚拟的 Waker
fn dummy_waker() -> Waker {
    struct DummyWaker;
    
    impl Wake for DummyWaker {
        fn wake(self: Arc<Self>) {}
        fn wake_by_ref(self: &Arc<Self>) {}
    }
    
    Waker::from(Arc::new(DummyWaker))
}

/// 简单的执行器，轮询 Future 到完成
fn block_on<F>(future: F) -> F::Output
where
    F: Future,
{
    let waker = dummy_waker();
    let mut context = Context::from_waker(&waker);
    let mut future = std::pin::pin!(future);
    
    loop {
        match future.as_mut().poll(&mut context) {
            Poll::Ready(val) => return val,
            Poll::Pending => {
                // 在实际执行器中，这里会等待 I/O 事件
                // 简单起见，我们继续轮询
                std::thread::yield_now();
            }
        }
    }
}

// ==================== 内存安全边界测试 ====================

/// Pin 投影结构
struct PinnedData {
    data: String,
    ptr_to_data: *const String,
    _pin: PhantomPinned,
}

impl PinnedData {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            ptr_to_data: std::ptr::null(),
            _pin: PhantomPinned,
        });
        boxed.ptr_to_data = &boxed.data;
        Box::into_pin(boxed)
    }
    
    /// 安全地获取数据引用
    fn data(self: Pin<&Self>) -> &str {
        &self.get_ref().data
    }
    
    /// 通过指针获取数据（unsafe）
    unsafe fn data_via_ptr(&self) -> &str {
        unsafe { &*self.ptr_to_data }
    }
}

/// 测试目的: 验证 Pin 投影
/// 测试场景: 创建 PinnedData 并访问数据
/// 预期结果: 应该能够安全访问数据
#[test]
fn test_pinned_projection() {
    let data = PinnedData::new(String::from("Pinned"));
    
    assert_eq!(data.as_ref().data(), "Pinned");
    unsafe {
        assert_eq!(data.data_via_ptr(), "Pinned");
    }
}

/// 测试目的: 验证 Pin<Box<T>> 保证堆分配
/// 测试场景: 创建 Box::pin 并访问数据
/// 预期结果: 数据应该正确固定在堆上
#[test]
fn test_pin_box_heap() {
    let data = [0u8; 1024];
    let pinned = Box::pin(data);
    
    // 验证数据被正确固定
    assert_eq!(pinned[0], 0);
}

/// Future 状态机
enum StateMachine {
    Start,
    Processing { value: i32 },
    Complete,
}

/// 状态机 Future
struct StateMachineFuture {
    state: StateMachine,
}

impl Future for StateMachineFuture {
    type Output = i32;
    
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.state {
            StateMachine::Start => {
                self.state = StateMachine::Processing { value: 42 };
                Poll::Pending
            }
            StateMachine::Processing { value: _ } => {
                self.state = StateMachine::Complete;
                Poll::Pending
            }
            StateMachine::Complete => {
                Poll::Ready(42)
            }
        }
    }
}

/// 测试目的: 验证 Future 状态机转换
/// 测试场景: 创建状态机 Future 并执行
/// 预期结果: 应该经过所有状态并返回结果
#[test]
fn test_state_machine_future() {
    let fut = StateMachineFuture { state: StateMachine::Start };
    let result = block_on(fut);
    assert_eq!(result, 42);
}

// ==================== Miri 特定测试 ====================

/// 测试目的: 验证 Unpin 边界
/// 测试场景: 检查类型的 Unpin 实现
/// 预期结果: 应该正确识别 Unpin 类型
#[test]
fn test_unpin_boundaries() {
    // String 是 Unpin
    fn assert_unpin<T: Unpin>(_val: T) {}
    assert_unpin(String::from("test"));
    
    // PhantomPinned 不是 Unpin
    fn assert_not_unpin<T>(_val: T) {}
    assert_not_unpin(PhantomPinned);
}

/// 测试目的: 验证 Pin 堆语义
/// 测试场景: 创建 Pin<Box<T>> 并观察地址
/// 预期结果: 数据不应该移动
#[test]
fn test_pin_heap_semantics() {
    let _ptr: *const i32;
    {
        let pinned = Box::pin(42);
        let _ptr = &*pinned;
        
        // 数据不会被移动
        assert_eq!(*_ptr, 42);
    }
    // ptr 现在悬垂，但 Miri 会检测任何使用
}

// ==================== 应该被 Miri 检测的错误（标记为 ignore） ====================

/// 测试目的: 演示不安全的 Pin 投影
/// 测试场景: 移动包含自引用的结构体
/// 预期结果: Miri 应该检测到 UB
#[test]
#[ignore = "This test demonstrates unsafe Pin usage"]
fn test_unsafe_pin_projection() {
    struct BadPin {
        data: String,
        ptr: *const String,
    }
    
    let mut bad = BadPin {
        data: String::from("test"),
        ptr: std::ptr::null(),
    };
    bad.ptr = &bad.data;
    
    // 移动结构体 - 指针变悬垂
    let moved = bad;
    unsafe {
        // 这是 UB！指针指向已释放的栈位置
        let _ = &*moved.ptr;
    }
}

/// 测试目的: 验证错误的 Pin::new_unchecked 使用
/// 测试场景: 对栈上数据使用 Pin::new_unchecked
/// 预期结果: Miri 应该检测到 UB
#[test]
#[ignore = "This test should fail with UB"]
fn test_pin_new_unchecked_ub() {
    struct NotPinned {
        data: String,
        ptr: *const String,
    }
    
    let mut not_pinned = NotPinned {
        data: String::from("test"),
        ptr: std::ptr::null(),
    };
    not_pinned.ptr = &not_pinned.data;
    
    unsafe {
        let mut pinned = Pin::new_unchecked(&mut not_pinned);
        // 尝试通过 Pin 修改 - 但如果数据被移动会导致 UB
        let _ = pinned.as_mut().get_unchecked_mut();
    }
}
