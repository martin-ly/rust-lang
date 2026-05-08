#![forbid(unsafe_code)]

//! Pin、自引用结构与高级所有权模式
//!
//! 本模块涵盖 `Pin<P>` 的语义、自引用结构的安全隐患与替代方案、
//! Pin projection 的概念，以及所有权决策树。
//!
//! ## 核心内容 / Core Contents
//!
//! - **PinFundamentals**: `Pin<P>` 基础，`Unpin` vs `!Unpin`，栈固定与堆固定
//! - **SelfReferentialPatterns**: 自引用结构模式与安全替代方案
//! - **PinProjectConcept**: Pin projection 规则与 `pin-project` crate 概念
//! - **OwnershipDecisionTree**: `&T` / `&mut T` / `Box<T>` / `Rc<T>` / `Arc<T>` / `Cow<T>` 决策树

use std::borrow::Cow;
use std::cell::RefCell;
use std::marker::PhantomPinned;
use std::pin::Pin;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

// ---------------------------------------------------------------------------
// PinFundamentals
// ---------------------------------------------------------------------------

/// `Pin<P>` 基础：为什么需要固定、Unpin vs !Unpin、栈固定与堆固定
///
/// # 核心概念 / Key Concepts
///
/// - `Pin<P>` 包装指针 `P`，保证 `P` 指向的值不会被移动（除非实现 `Unpin`）
/// - `Unpin` 是 auto trait：几乎所有类型都自动实现，只有显式包含 `PhantomPinned` 的类型不是
/// - `pin!` 宏（Rust 1.68+）用于栈固定；`Box::pin` 用于堆固定
/// - 固定契约：一旦进入 `Pin`，实际内存地址不得改变
pub struct PinFundamentals;

impl PinFundamentals {
    /// 返回 `Pin<P>` 的定义与存在理由
    pub fn what_is_pin() -> &'static str {
        "Pin<P> 是一个包装指针的指针，保证其指向的值在内存中的地址不会被移动。 \
         它用于自引用结构、异步 Future 等场景，确保内部指针不会悬垂。"
    }

    /// 解释 `Unpin` 与 `!Unpin`（PhantomPinned）的区别
    pub fn unpin_vs_phantom_pinned() -> (&'static str, &'static str) {
        (
            "Unpin: 绝大多数 Rust 类型自动实现，即使被 Pin 包裹也可以安全移动",
            "!Unpin: 显式包含 PhantomPinned 的类型，被 Pin 后禁止移动，用于自引用场景",
        )
    }

    /// 演示 `pin!` 宏进行栈固定（Rust 1.68+ stable）
    ///
    /// 栈固定将值分配在栈上并通过 `Pin<&mut T>` 引用，生命周期受限于当前作用域。
    pub fn demonstrate_stack_pinning() -> String {
        let data = PinnedBuffer::new(String::from("stack-pinned"));
        let pinned: Pin<&mut PinnedBuffer> = std::pin::pin!(data);
        pinned.as_ref().get_content()
    }

    /// 演示 `Box::pin` 进行堆固定
    ///
    /// 堆固定将值分配在堆上并返回 `Pin<Box<T>>`，可以跨作用域传递。
    pub fn demonstrate_heap_pinning() -> String {
        let pinned: Pin<Box<PinnedBuffer>> =
            Box::pin(PinnedBuffer::new(String::from("heap-pinned")));
        pinned.as_ref().get_content()
    }

    /// 解释固定契约：一旦 pinned，内存地址不得改变
    pub fn pin_contract() -> &'static str {
        "固定契约：当值被 Pin<&mut T> 或 Pin<Box<T>> 包裹后，其实际内存地址不得改变，除非 T: \
         Unpin。违反此契约会导致自引用指针悬垂，属于未定义行为。"
    }

    /// 演示 `Unpin` 类型可以从 `Pin<&mut T>` 中获取可变引用
    ///
    /// `String: Unpin`，因此 `Pin::get_mut` 可用。
    pub fn unpin_allows_get_mut() -> bool {
        let s = String::from("hello");
        let mut pinned = std::pin::pin!(s);
        let r: &mut String = Pin::get_mut(pinned.as_mut());
        r.push_str(" world");
        *r == *"hello world"
    }

    /// 演示 `!Unpin` 类型无法从 `Pin<&mut T>` 中获取可变引用
    ///
    /// `PinnedBuffer` 包含 `PhantomPinned`，因此 `Pin::get_mut` 不可用。
    /// 这里仅返回说明，实际调用 `Pin::get_mut` 会导致编译错误。
    pub fn not_unpin_denies_get_mut() -> bool {
        let buf = PinnedBuffer::new(String::from("hello"));
        let mut _pinned = std::pin::pin!(buf);
        // 以下代码会编译失败，因为 PinnedBuffer: !Unpin
        // let _r = Pin::get_mut(_pinned.as_mut());
        true
    }
}

/// 一个显式 `!Unpin` 的类型，用于配合 `PinFundamentals` 演示固定语义
pub struct PinnedBuffer {
    content: String,
    _pin: PhantomPinned,
}

impl PinnedBuffer {
    /// 创建新的固定缓冲区
    pub fn new(content: String) -> Self {
        Self {
            content,
            _pin: PhantomPinned,
        }
    }

    /// 通过 `Pin<&Self>` 只读访问内容
    ///
    /// 由于 `!Unpin` 类型无法从 `Pin<&Self>` 安全返回字段引用（生命周期限制），
    /// 这里返回克隆后的 `String`。
    pub fn get_content(self: Pin<&Self>) -> String {
        self.as_ref().content.clone()
    }
}

// ---------------------------------------------------------------------------
// SelfReferentialPatterns
// ---------------------------------------------------------------------------

/// 自引用结构模式：为什么 safe Rust 中无法直接实现，以及安全替代方案
///
/// # 自引用问题 / The Self-Reference Problem
///
/// 自引用结构包含指向自身的引用。当结构体被移动时，内存地址改变，
/// 但内部引用仍指向旧地址，导致悬垂指针。
/// Rust 借用检查器无法在编译时证明自引用的安全性，因此禁止在 safe Rust 中直接构造。
pub struct SelfReferentialPatterns;

impl SelfReferentialPatterns {
    /// 解释自引用结构在 safe Rust 中不安全的原因
    pub fn why_self_referential_is_unsafe() -> &'static str {
        "自引用结构包含指向自身的引用。当结构体被移动时，其内存地址改变，但内部引用仍指向旧地址，\
         导致悬垂指针。Rust 的借用检查器无法在编译时证明这种自引用是安全的，因此禁止在 safe Rust \
         中直接构造。"
    }

    /// 模式 1：侵入式链表节点（概念性）
    ///
    /// C/C++ 中常见：节点包含指向同一块内存中其他节点的指针。
    /// Safe Rust 替代方案：使用 `Vec<Node>` + `usize` 索引，或 `Rc<RefCell<Node>>` + `Weak`。
    pub fn intrusive_linked_list_concept() -> &'static str {
        "侵入式链表：节点包含指向同一块内存中其他节点的指针。Safe Rust 替代：使用 Vec<Node> + \
         usize 索引，或 Rc<RefCell<Node>> + Weak。"
    }

    /// 模式 2：解析器引用自身缓冲区（概念性 + 安全替代）
    ///
    /// 原始想法：解析器持有 `String` 并存储指向其内部切片的 `&str`。
    /// 安全替代：存储 `(buffer: String, token_start: usize, token_end: usize)`，
    /// 在需要时通过索引动态获取切片。
    pub fn parser_own_buffer_concept() -> &'static str {
        "解析器持有 String 缓冲区并引用其中切片：移动解析器后切片悬垂。安全替代：存储 (buffer: \
         String, token_start: usize, token_end: usize)。"
    }

    /// 模式 3：生成器状态机（async/await 脱糖概念）
    ///
    /// `async fn` 编译后脱糖为实现 `Future` 的状态机。
    /// 状态机可能包含跨 `await` 点的局部变量引用，形成自引用。
    /// `Pin` 保证 `Future` 在轮询时不会被移动，从而使这些引用有效。
    pub fn generator_state_machine_concept() -> &'static str {
        "async fn 编译后会脱糖为实现了 Future 的状态机。状态机可能包含跨 await \
         点的局部变量引用，形成自引用。Pin 保证 Future 在轮询时不会被移动，从而使这些引用有效。"
    }

    /// 安全替代方案：使用索引代替指针
    ///
    /// 不存储 `&str`，而是存储字节索引，按需切片。
    pub fn safe_workaround_indices() -> String {
        let buf = String::from("hello world");
        let start = 0usize;
        let end = 5usize;
        let token = &buf[start..end];
        token.to_string()
    }

    /// 安全替代方案：使用 `Rc<RefCell<T>>` 实现单线程共享所有权
    ///
    /// 当需要共享所有权且需要内部可变性时，使用引用计数 + 运行时借用检查。
    pub fn safe_workaround_rc_refcell() -> i32 {
        let shared = Rc::new(RefCell::new(42));
        {
            let mut borrow = shared.borrow_mut();
            *borrow += 1;
        }
        *shared.borrow()
    }

    /// 安全替代方案：使用 `Arc<T>` 实现共享所有权（只读）
    pub fn safe_workaround_arc_readonly() -> i32 {
        let shared = Arc::new(100);
        let clone = Arc::clone(&shared);
        // 模拟跨作用域/线程传递
        *clone
    }
}

// ---------------------------------------------------------------------------
// PinProjectConcept
// ---------------------------------------------------------------------------

/// Pin Projection 概念：从固定结构体中投影字段
///
/// # 什么是 Pin Projection / What is Pin Projection
///
/// 当你拥有一个 `Pin<&mut MyStruct>` 时，你可能希望获取某个字段的
/// `Pin<&mut Field>`。这个过程称为 **pin projection**。
///
/// # 安全规则 / Safety Rules
///
/// 1. 只有被显式标记为固定的字段才能被投影为 `Pin`
/// 2. 被投影的字段不应实现 `Unpin`（否则无需固定）
/// 3. `Drop` 实现必须尊重固定状态
/// 4. 不能为被固定字段提供 `&mut T` 访问（会打破固定契约）
pub struct PinProjectConcept;

impl PinProjectConcept {
    /// 解释 pin projection 的定义
    pub fn what_is_pin_projection() -> &'static str {
        "Pin projection 是指从 Pin<&mut Struct> 获取到其某个字段的 Pin<&mut \
         Field>。这是实现自引用结构时必不可少的操作。"
    }

    /// 安全 pin projection 规则说明
    pub fn safe_projection_rules() -> &'static str {
        "安全规则：1. 只有被显式标记为固定的字段才能被投影为 Pin。2. 被投影的字段不能实现 \
         Unpin（否则无需固定）。3. Drop 实现必须尊重固定状态（Drop 被调用时值可能仍处于 pinned \
         状态）。4. 不能为被固定字段提供 &mut T 访问（会打破固定契约）。"
    }

    /// `pin-project` / `pin-project-lite` crate 概念
    ///
    /// 这些 crate 通过过程宏自动生成安全的 pin projection 方法，
    /// 避免手写 `unsafe` 代码。
    pub fn pin_project_crate_concept() -> &'static str {
        "pin-project 和 pin-project-lite 通过过程宏自动生成安全的 pin projection \
         方法。它们会检查字段属性，确保只有标记 #[pin] 的字段才被投影为 Pin，并生成符合 Rust \
         安全要求的代码，避免手写 unsafe。"
    }

    /// 何时安全 vs 何时不安全
    pub fn when_safe_vs_unsafe() -> (&'static str, &'static str) {
        (
            "安全：使用 pin-project 宏，且遵守 structural pinning 规则。",
            "不安全：手写 projection 但未保证字段不移动，或未正确实现 Drop。",
        )
    }
}

/// 配合 `PinProjectConcept` 演示的结构体
///
/// 此结构体是 `!Unpin`，因此方法需要 `Pin<&Self>`。
/// 注意：我们没有手动实现 pin projection 方法，因为安全实现需要
/// `pin-project` 宏或 `unsafe` 代码；这里仅作为概念展示。
pub struct ProjectDemo {
    /// 普通 Unpin 字段
    pub name: String,
    /// 逻辑上需要固定的字段
    pub pinned_data: String,
    /// 显式 !Unpin 标记
    pub _marker: PhantomPinned,
}

impl ProjectDemo {
    /// 创建实例
    pub fn new(name: String, data: String) -> Self {
        Self {
            name,
            pinned_data: data,
            _marker: PhantomPinned,
        }
    }

    /// 通过 `Pin<&Self>` 安全读取 name
    ///
    /// 只读借用不会破坏固定契约，因此可以在 safe Rust 中完成。
    /// 返回克隆后的 `String` 以绕过 `!Unpin` 字段引用的生命周期限制。
    pub fn get_name(self: Pin<&Self>) -> String {
        self.as_ref().name.clone()
    }

    /// 通过 `Pin<&Self>` 安全读取 pinned_data
    pub fn get_pinned_data(self: Pin<&Self>) -> String {
        self.as_ref().pinned_data.clone()
    }
}

// ---------------------------------------------------------------------------
// OwnershipDecisionTree
// ---------------------------------------------------------------------------

/// 所有权决策树：不同场景下选择正确的指针类型
///
/// # 决策要点 / Decision Points
///
/// - 临时只读？→ `&T`
/// - 临时独占修改？→ `&mut T`
/// - 堆分配、单一所有权？→ `Box<T>`
/// - 单线程共享所有权？→ `Rc<T>`
/// - 多线程共享所有权？→ `Arc<T>`
/// - 读多写少、避免不必要克隆？→ `Cow<'a, T>`
pub struct OwnershipDecisionTree;

impl OwnershipDecisionTree {
    /// 返回各指针类型的适用场景
    pub fn reference_vs_smart_pointers() -> Vec<(&'static str, &'static str)> {
        vec![
            ("&T", "只读临时借用，无所有权，零开销"),
            ("&mut T", "独占可变借用，无所有权，编译期排他"),
            ("Box<T>", "堆分配单一所有权，确定性释放"),
            ("Rc<T>", "单线程共享所有权（引用计数）"),
            ("Arc<T>", "多线程共享所有权（原子引用计数）"),
            ("Cow<'a, T>", "写时克隆，优先借用，必要时获取所有权"),
        ]
    }

    /// 演示 `Cow<'a, T>` 的写时克隆优化
    ///
    /// 当不需要修改时，`Cow::Borrowed` 零成本引用原始数据；
    /// 仅在需要修改时才进行克隆。
    pub fn demonstrate_cow(input: &str) -> String {
        let mut cow: Cow<'_, str> = Cow::Borrowed(input);
        if input.contains("modify") {
            cow.to_mut().push_str(" [modified]");
        }
        cow.into_owned()
    }

    /// 单线程共享可变性：`Rc<RefCell<T>>`
    ///
    /// `Rc` 提供共享所有权，`RefCell` 提供运行时借用检查的可变性。
    pub fn demonstrate_rc_refcell() -> i32 {
        let data: Rc<RefCell<i32>> = Rc::new(RefCell::new(10));
        *data.borrow_mut() += 5;
        *data.borrow()
    }

    /// 多线程共享可变性：`Arc<Mutex<T>>`
    ///
    /// `Arc` 提供跨线程共享所有权，`Mutex` 提供线程安全的互斥访问。
    pub fn demonstrate_arc_mutex() -> i32 {
        let data: Arc<Mutex<i32>> = Arc::new(Mutex::new(20));
        let clone = Arc::clone(&data);
        let handle = std::thread::spawn(move || {
            let mut guard = clone.lock().unwrap();
            *guard += 5;
        });
        handle.join().unwrap();
        *data.lock().unwrap()
    }

    /// 返回决策树建议列表
    pub fn decision_tree_advice() -> Vec<(&'static str, &'static str)> {
        vec![
            ("需要只读访问？", "使用 &T"),
            ("需要独占修改？", "使用 &mut T"),
            ("需要堆分配或递归类型？", "使用 Box<T>"),
            ("需要单线程共享所有权？", "使用 Rc<T>"),
            ("需要多线程共享所有权？", "使用 Arc<T>"),
            ("需要单线程共享可变性？", "使用 Rc<RefCell<T>>"),
            (
                "需要多线程共享可变性？",
                "使用 Arc<Mutex<T>> 或 Arc<RwLock<T>>",
            ),
            ("读多写少且需要克隆优化？", "使用 Cow<'a, T>"),
        ]
    }
}

// ---------------------------------------------------------------------------
// AsyncStateMachineConcept — Pin 在异步状态机中的核心作用
// ---------------------------------------------------------------------------

/// 展示 `Pin` 在 async/await 状态机中的必要性
///
/// async fn 编译后变成实现 `Future` 的状态机结构体，
/// 该结构体可能自引用（保存 .await 点的局部变量指针），
/// 因此 `Future::poll` 接收 `Pin<&mut Self>`。
pub struct AsyncStateMachineConcept;

impl AsyncStateMachineConcept {
    /// 解释为什么 Future::poll 需要 Pin
    pub fn why_future_uses_pin() -> &'static str {
        r#"async fn 编译后的状态机可能包含自引用：

```rust
// 源代码
async fn example() {
    let x = 42;
    let ptr = &x;          // 自引用!
    some_async().await;    // 可能挂起，状态机被移动后再恢复
    println!("{}", *ptr);  // 如果移动过，ptr 悬垂!
}
```

编译器生成的状态机：
```rust
enum ExampleFuture {
    Start,
    WaitingOnSomeAsync { x: i32, ptr: *const i32 }, // 自引用!
    Done,
}
```

因此 `Future::poll` 签名是：
```rust
fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<T>;
```

`Pin` 保证状态机在 .await 点之间不会被移动，
从而自引用指针始终有效。"#
    }

    /// 返回 async/await → Pin 的关系总结
    pub fn async_await_pin_summary() -> &'static str {
        "async/await 语法糖 → 编译器生成状态机 → 状态机可能自引用 → \
         必须用 Pin 保证不移动 → Future::poll 接收 Pin<&mut Self>"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // PinFundamentals
    // -----------------------------------------------------------------------

    #[test]
    fn test_what_is_pin() {
        assert!(!PinFundamentals::what_is_pin().is_empty());
    }

    #[test]
    fn test_unpin_vs_phantom_pinned() {
        let (unpin, not_unpin) = PinFundamentals::unpin_vs_phantom_pinned();
        assert!(unpin.contains("Unpin"));
        assert!(not_unpin.contains("PhantomPinned"));
    }

    #[test]
    fn test_stack_pinning() {
        assert_eq!(PinFundamentals::demonstrate_stack_pinning(), "stack-pinned");
    }

    #[test]
    fn test_heap_pinning() {
        assert_eq!(PinFundamentals::demonstrate_heap_pinning(), "heap-pinned");
    }

    #[test]
    fn test_pin_contract() {
        assert!(PinFundamentals::pin_contract().contains("固定契约"));
    }

    #[test]
    fn test_unpin_allows_get_mut() {
        assert!(PinFundamentals::unpin_allows_get_mut());
    }

    #[test]
    fn test_not_unpin_denies_get_mut() {
        assert!(PinFundamentals::not_unpin_denies_get_mut());
    }

    #[test]
    fn test_pinned_buffer_via_pin() {
        let buf = PinnedBuffer::new(String::from("test"));
        let pinned = std::pin::pin!(buf);
        assert_eq!(pinned.as_ref().get_content(), "test");
    }

    // -----------------------------------------------------------------------
    // SelfReferentialPatterns
    // -----------------------------------------------------------------------

    #[test]
    fn test_why_self_referential_is_unsafe() {
        assert!(!SelfReferentialPatterns::why_self_referential_is_unsafe().is_empty());
    }

    #[test]
    fn test_intrusive_linked_list_concept() {
        let s = SelfReferentialPatterns::intrusive_linked_list_concept();
        assert!(s.contains("侵入式") || s.contains("Vec"));
    }

    #[test]
    fn test_parser_own_buffer_concept() {
        let s = SelfReferentialPatterns::parser_own_buffer_concept();
        assert!(s.contains("索引") || s.contains("usize"));
    }

    #[test]
    fn test_generator_state_machine_concept() {
        let s = SelfReferentialPatterns::generator_state_machine_concept();
        assert!(s.contains("Future") || s.contains("Pin"));
    }

    #[test]
    fn test_safe_workaround_indices() {
        assert_eq!(SelfReferentialPatterns::safe_workaround_indices(), "hello");
    }

    #[test]
    fn test_safe_workaround_rc_refcell() {
        assert_eq!(SelfReferentialPatterns::safe_workaround_rc_refcell(), 43);
    }

    #[test]
    fn test_safe_workaround_arc_readonly() {
        assert_eq!(SelfReferentialPatterns::safe_workaround_arc_readonly(), 100);
    }

    // -----------------------------------------------------------------------
    // PinProjectConcept
    // -----------------------------------------------------------------------

    #[test]
    fn test_what_is_pin_projection() {
        assert!(!PinProjectConcept::what_is_pin_projection().is_empty());
    }

    #[test]
    fn test_safe_projection_rules() {
        assert!(!PinProjectConcept::safe_projection_rules().is_empty());
    }

    #[test]
    fn test_pin_project_crate_concept() {
        let s = PinProjectConcept::pin_project_crate_concept();
        assert!(s.contains("pin-project"));
    }

    #[test]
    fn test_when_safe_vs_unsafe() {
        let (safe, unsafe_) = PinProjectConcept::when_safe_vs_unsafe();
        assert!(safe.contains("安全"));
        assert!(unsafe_.contains("不安全"));
    }

    #[test]
    fn test_project_demo_get_name() {
        let demo = ProjectDemo::new(String::from("demo"), String::from("data"));
        let pinned = std::pin::pin!(demo);
        assert_eq!(pinned.as_ref().get_name(), "demo");
    }

    #[test]
    fn test_project_demo_get_pinned_data() {
        let demo = ProjectDemo::new(String::from("demo"), String::from("secret"));
        let pinned = std::pin::pin!(demo);
        assert_eq!(pinned.as_ref().get_pinned_data(), "secret");
    }

    // -----------------------------------------------------------------------
    // OwnershipDecisionTree
    // -----------------------------------------------------------------------

    #[test]
    fn test_reference_vs_smart_pointers() {
        let list = OwnershipDecisionTree::reference_vs_smart_pointers();
        assert_eq!(list.len(), 6);
        assert!(list.iter().any(|(k, _)| *k == "Box<T>"));
    }

    #[test]
    fn test_demonstrate_cow_no_clone() {
        let result = OwnershipDecisionTree::demonstrate_cow("hello");
        assert_eq!(result, "hello");
    }

    #[test]
    fn test_demonstrate_cow_with_clone() {
        let result = OwnershipDecisionTree::demonstrate_cow("please modify this");
        assert_eq!(result, "please modify this [modified]");
    }

    #[test]
    fn test_demonstrate_rc_refcell() {
        assert_eq!(OwnershipDecisionTree::demonstrate_rc_refcell(), 15);
    }

    #[test]
    fn test_demonstrate_arc_mutex() {
        assert_eq!(OwnershipDecisionTree::demonstrate_arc_mutex(), 25);
    }

    #[test]
    fn test_decision_tree_advice() {
        let advice = OwnershipDecisionTree::decision_tree_advice();
        assert!(!advice.is_empty());
        assert!(advice.iter().any(|(_, v)| v.contains("Cow")));
    }

    // -----------------------------------------------------------------------
    // AsyncStateMachineConcept
    // -----------------------------------------------------------------------

    #[test]
    fn test_why_future_uses_pin() {
        let s = AsyncStateMachineConcept::why_future_uses_pin();
        assert!(s.contains("Pin"));
        assert!(s.contains("Future"));
        assert!(s.contains("状态机"));
    }

    #[test]
    fn test_async_await_pin_summary() {
        let s = AsyncStateMachineConcept::async_await_pin_summary();
        assert!(s.contains("Pin"));
        assert!(s.contains("Future"));
    }
}
