//! # Rust 1.95.0+ 特性练习
//!
//! 本模块提供 Rust 1.95.0 引入的新特性的 hands-on 练习。
//! 每道练习题包含：题目描述、起始代码（stub）、参考实现、测试用例。

use std::collections::VecDeque;
use std::sync::atomic::{AtomicIsize, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

// ============================================================
// IfLetGuardsExercises
// ============================================================

/// Token 类型，用于词法分析器练习
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    /// 数字字符串
    Number(String),
    /// 标识符
    Identifier(String),
    /// 符号
    Symbol(char),
    /// 空白
    Whitespace,
}

/// # IfLetGuards 练习
///
/// 练习使用 `if let` 守卫（match guards）简化嵌套 match，
/// 使代码更扁平、更易读。
///
/// `if let` 守卫允许在 match 的 arm guard 中直接使用 `if let` 绑定变量。
pub struct IfLetGuardsExercises;

impl IfLetGuardsExercises {
    /// ## 练习 01: 词法分析器 Token 过滤
    ///
    /// 使用 `if let` 守卫重写嵌套的 match，过滤出有效的 Token。
    ///
    /// ### 题目
    /// 给定一组 `Token`，只保留其中表示有效整数的 `Token::Number`，
    /// 并且该整数必须能被成功解析为 `u32`。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn filter_valid_tokens(tokens: &[Token]) -> Vec<u32> {
    ///     let mut result = Vec::new();
    ///     for token in tokens {
    ///         // TODO: 使用 if let 守卫替代嵌套 match/if let
    ///     }
    ///     result
    /// }
    /// ```
    pub fn exercise_01_lexer_token_filter(tokens: &[Token]) -> Vec<u32> {
        let mut result = Vec::new();
        for token in tokens {
            match token {
                Token::Number(s) if let Ok(n) = s.parse::<u32>() => {
                    result.push(n);
                }
                _ => {}
            }
        }
        result
    }

    /// ## 练习 02: 解析并验证
    ///
    /// 使用 `if let` 守卫解析字符串并验证数值范围。
    ///
    /// ### 题目
    /// 将字符串解析为整数，并仅保留在 [10, 100] 范围内的值。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn parse_and_validate(inputs: &[&str]) -> Vec<i32> {
    ///     // TODO: 使用 if let 守卫
    /// }
    /// ```
    pub fn exercise_02_parse_and_validate(inputs: &[&str]) -> Vec<i32> {
        let mut result = Vec::new();
        for input in inputs {
            match input {
                s if let Ok(n) = s.parse::<i32>() && (10..=100).contains(&n) => {
                    result.push(n);
                }
                _ => {}
            }
        }
        result
    }

    /// ## 练习 03: 扁平化嵌套 Result<Option<T>>
    ///
    /// 使用 `if let` 守卫从嵌套的 `Result<Option<i32>, &str>` 中提取有效值。
    ///
    /// ### 题目
    /// 给定一组嵌套结果，仅提取 `Result` 为 `Ok` 且内部 `Option` 为 `Some` 的值。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn flatten_results(values: &[Result<Option<i32>, &str>]) -> Vec<i32> {
    ///     // TODO: 使用 if let 守卫
    /// }
    /// ```
    pub fn exercise_03_nested_result_option(values: &[Result<Option<i32>, &str>]) -> Vec<i32> {
        let mut result = Vec::new();
        for value in values {
            match value {
                Ok(opt) if let Some(n) = opt => {
                    result.push(*n);
                }
                _ => {}
            }
        }
        result
    }

    /// ## 练习 04: 小型状态机
    ///
    /// 使用 `if let` 守卫实现一个简单状态机。
    ///
    /// ### 题目
    /// 实现一个门的状态机：Closed -> Opened -> Closed。
    /// 输入事件为 `Event::PressButton(Option<String>)`，
    /// 仅当提供正确密码 `"secret"` 时门才会打开。
    /// 返回转换后的新状态。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn transition(state: DoorState, event: &Event) -> DoorState {
    ///     // TODO: 使用 if let 守卫
    /// }
    /// ```
    pub fn exercise_04_state_machine(state: DoorState, event: &Event) -> DoorState {
        match (state, event) {
            (DoorState::Closed, Event::PressButton(pass))
                if let Some(p) = pass && p == "secret" =>
            {
                DoorState::Opened
            }
            (DoorState::Opened, Event::PressButton(_)) => DoorState::Closed,
            (s, _) => s,
        }
    }
}

/// 门状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DoorState {
    /// 关闭
    Closed,
    /// 打开
    Opened,
}

/// 事件
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// 按下按钮，可选携带密码
    PressButton(Option<String>),
}

// ============================================================
// CfgSelectExercises
// ============================================================

/// # cfg_select! 练习
///
/// 练习使用 `cfg_select!` 宏根据编译时配置选择不同代码路径。
///
/// `cfg_select!` 是 Rust 1.95 稳定化的宏，类似于 `cfg!`，
/// 但可以在表达式位置返回不同平台的值。
pub struct CfgSelectExercises;

impl CfgSelectExercises {
    /// ## 练习 01: 平台配置
    ///
    /// 使用 `cfg_select!` 根据目标平台返回不同的配置字符串。
    ///
    /// ### 题目
    /// 返回当前平台的名称字符串：
    /// - Windows -> "windows"
    /// - Linux   -> "linux"
    /// - macOS   -> "macos"
    /// - 其他    -> "unknown"
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn exercise_01_platform_config() -> &'static str {
    ///     // TODO: 使用 cfg_select!
    /// }
    /// ```
    pub fn exercise_01_platform_config() -> &'static str {
        std::cfg_select! {
            target_os = "windows" => { "windows" }
            target_os = "linux" => { "linux" }
            target_os = "macos" => { "macos" }
            _ => { "unknown" }
        }
    }

    /// ## 练习 02: 特性标志
    ///
    /// 使用 `cfg_select!` 根据是否启用 `test` 配置返回不同值。
    ///
    /// ### 题目
    /// 在测试配置下返回 42，否则返回 0。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn exercise_02_feature_flags() -> i32 {
    ///     // TODO: 使用 cfg_select!
    /// }
    /// ```
    pub fn exercise_02_feature_flags() -> i32 {
        std::cfg_select! {
            test => { 42 }
            _ => { 0 }
        }
    }
}

// ============================================================
// AtomicUpdateExercises
// ============================================================

/// # Atomic Update 练习
///
/// 练习使用 `AtomicUsize::update` 和 `AtomicIsize::update`
/// 以及 `try_update` 进行无锁原子操作。
///
/// 这些 API 在 Rust 1.95 中稳定化，避免了显式的 compare-and-swap 循环。
pub struct AtomicUpdateExercises;

impl AtomicUpdateExercises {
    /// ## 练习 01: 线程安全计数器
    ///
    /// 使用 `AtomicUsize::update` 实现一个多线程安全计数器。
    ///
    /// ### 题目
    /// 启动 4 个线程，每个线程对共享计数器执行 1000 次自增操作。
    /// 使用 `AtomicUsize::update` 完成自增。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn exercise_01_counter() -> usize {
    ///     // TODO
    /// }
    /// ```
    pub fn exercise_01_counter() -> usize {
        let counter = Arc::new(AtomicUsize::new(0));
        let mut handles = Vec::new();

        for _ in 0..4 {
            let c = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                for _ in 0..1000 {
                    let _ = c.update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1);
                }
            });
            handles.push(handle);
        }

        for h in handles {
            h.join().unwrap();
        }

        counter.load(Ordering::Relaxed)
    }

    /// ## 练习 02: 简单信号量
    ///
    /// 使用 `AtomicIsize::update` 实现一个允许最多 N 个许可的信号量。
    ///
    /// ### 题目
    /// 实现 `acquire`：如果当前许可数 > 0，则减 1 并返回 true；
    /// 否则返回 false。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub struct SimpleSemaphore(AtomicIsize);
    ///
    /// impl SimpleSemaphore {
    ///     pub fn acquire(&self) -> bool {
    ///         // TODO: 使用 AtomicIsize::update
    ///     }
    /// }
    /// ```
    pub fn exercise_02_semaphore() -> bool {
        struct SimpleSemaphore(AtomicIsize);

        impl SimpleSemaphore {
            pub fn new(permits: isize) -> Self {
                Self(AtomicIsize::new(permits))
            }

            pub fn acquire(&self) -> bool {
                let result = self
                    .0
                    .update(Ordering::SeqCst, Ordering::SeqCst, |old| if old > 0 { old - 1 } else { old });
                result > 0
            }
        }

        let sem = SimpleSemaphore::new(2);
        assert!(sem.acquire());
        assert!(sem.acquire());
        !sem.acquire()
    }

    /// ## 练习 03: 条件原子操作
    ///
    /// 使用 `try_update` 实现条件自增：仅当当前值小于上限时才自增。
    ///
    /// ### 题目
    /// 给定一个上限 `max`，仅当计数器当前值 < max 时才 +1。
    /// 返回是否成功自增。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn exercise_03_try_update(counter: &AtomicUsize, max: usize) -> bool {
    ///     // TODO: 使用 try_update
    /// }
    /// ```
    pub fn exercise_03_try_update(counter: &AtomicUsize, max: usize) -> bool {
        counter
            .try_update(
                Ordering::Relaxed,
                Ordering::Relaxed,
                |old| if old < max { Some(old + 1) } else { None },
            )
            .is_ok()
    }
}

// ============================================================
// CollectionMutRefExercises
// ============================================================

/// # 集合可变引用练习
///
/// 练习使用 `Vec::push_mut` 和 `VecDeque::insert_mut`
/// 在插入元素后立即获取其可变引用，避免二次查找。
///
/// 这些 API 在 Rust 1.95 中稳定化。
pub struct CollectionMutRefExercises;

impl CollectionMutRefExercises {
    /// ## 练习 01: Vec push_mut
    ///
    /// 使用 `Vec::push_mut` 插入元素并立即修改。
    ///
    /// ### 题目
    /// 向 Vec 插入一个初始值为 0 的元素，然后通过返回的可变引用将其设为 42。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn exercise_01_vec_push_mut() -> Vec<i32> {
    ///     let mut vec = vec![1, 2, 3];
    ///     // TODO: 使用 push_mut
    /// }
    /// ```
    pub fn exercise_01_vec_push_mut() -> Vec<i32> {
        let mut vec = vec![1, 2, 3];
        let r = vec.push_mut(0);
        *r = 42;
        vec
    }

    /// ## 练习 02: VecDeque insert_mut
    ///
    /// 使用 `VecDeque::insert_mut` 在队首插入并立即修改。
    ///
    /// ### 题目
    /// 在 `VecDeque` 的索引 0 处插入 `"hello"`，然后通过可变引用将其改为 `"world"`。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn exercise_02_vecdeque_insert_mut() -> VecDeque<String> {
    ///     let mut deque = VecDeque::from(["a", "b", "c"]);
    ///     // TODO: 使用 insert_mut
    /// }
    /// ```
    pub fn exercise_02_vecdeque_insert_mut() -> VecDeque<String> {
        let mut deque = VecDeque::from(["a".to_string(), "b".to_string(), "c".to_string()]);
        let r = deque.insert_mut(0, "hello".to_string());
        *r = "world".to_string();
        deque
    }
}

// ============================================================
// ColdPathExercises
// ============================================================

/// # cold_path 练习
///
/// 练习使用 `std::hint::cold_path()` 标记不太可能执行的分支，
/// 帮助编译器优化热路径。
///
/// `cold_path` 在 Rust 1.95 中稳定化。
pub struct ColdPathExercises;

impl ColdPathExercises {
    /// ## 练习 01: 错误分支标记
    ///
    /// 在不太可能发生的错误分支上标记 `cold_path`。
    ///
    /// ### 题目
    /// 实现一个除法函数：除数极少为 0，因此在除零分支上标记 `cold_path`。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn exercise_01_error_branch(a: i32, b: i32) -> Option<i32> {
    ///     // TODO
    /// }
    /// ```
    pub fn exercise_01_error_branch(a: i32, b: i32) -> Option<i32> {
        if b == 0 {
            std::hint::cold_path();
            return None;
        }
        Some(a / b)
    }

    /// ## 练习 02: 边界情况处理
    ///
    /// 在解析器的边界情况分支上标记 `cold_path`。
    ///
    /// ### 题目
    /// 解析一个非空字符串的前缀数字。空字符串属于边界情况，极少出现。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn exercise_02_boundary_case(input: &str) -> Option<u32> {
    ///     // TODO
    /// }
    /// ```
    pub fn exercise_02_boundary_case(input: &str) -> Option<u32> {
        if input.is_empty() {
            std::hint::cold_path();
            return None;
        }
        input.split_whitespace().next()?.parse().ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --------------------------------------------------------
    // IfLetGuardsExercises tests
    // --------------------------------------------------------
    #[test]
    fn test_exercise_01_lexer_token_filter() {
        let tokens = vec![
            Token::Number("42".to_string()),
            Token::Number("abc".to_string()),
            Token::Identifier("x".to_string()),
            Token::Number("100".to_string()),
            Token::Symbol('+'),
            Token::Number("99999999999999999999".to_string()),
        ];
        let result = IfLetGuardsExercises::exercise_01_lexer_token_filter(&tokens);
        assert_eq!(result, vec![42, 100]);
    }

    #[test]
    fn test_exercise_02_parse_and_validate() {
        let inputs = vec!["5", "50", "100", "101", "abc", "75"];
        let result = IfLetGuardsExercises::exercise_02_parse_and_validate(&inputs);
        assert_eq!(result, vec![50, 100, 75]);
    }

    #[test]
    fn test_exercise_03_nested_result_option() {
        let values = vec![Ok(Some(1)), Ok(None), Err("error"), Ok(Some(42))];
        let result = IfLetGuardsExercises::exercise_03_nested_result_option(&values);
        assert_eq!(result, vec![1, 42]);
    }

    #[test]
    fn test_exercise_04_state_machine() {
        use super::{DoorState, Event};

        let state = DoorState::Closed;
        let event = Event::PressButton(Some("secret".to_string()));
        assert_eq!(
            IfLetGuardsExercises::exercise_04_state_machine(state, &event),
            DoorState::Opened
        );

        let state = DoorState::Closed;
        let event = Event::PressButton(Some("wrong".to_string()));
        assert_eq!(
            IfLetGuardsExercises::exercise_04_state_machine(state, &event),
            DoorState::Closed
        );

        let state = DoorState::Opened;
        let event = Event::PressButton(None);
        assert_eq!(
            IfLetGuardsExercises::exercise_04_state_machine(state, &event),
            DoorState::Closed
        );
    }

    // --------------------------------------------------------
    // CfgSelectExercises tests
    // --------------------------------------------------------
    #[test]
    fn test_exercise_01_platform_config() {
        let platform = CfgSelectExercises::exercise_01_platform_config();
        assert!(!platform.is_empty());
    }

    #[test]
    fn test_exercise_02_feature_flags() {
        let value = CfgSelectExercises::exercise_02_feature_flags();
        assert_eq!(value, 42);
    }

    // --------------------------------------------------------
    // AtomicUpdateExercises tests
    // --------------------------------------------------------
    #[test]
    fn test_exercise_01_counter() {
        let result = AtomicUpdateExercises::exercise_01_counter();
        assert_eq!(result, 4000);
    }

    #[test]
    fn test_exercise_02_semaphore() {
        assert!(AtomicUpdateExercises::exercise_02_semaphore());
    }

    #[test]
    fn test_exercise_03_try_update() {
        let counter = AtomicUsize::new(0);
        assert!(AtomicUpdateExercises::exercise_03_try_update(&counter, 5));
        assert_eq!(counter.load(Ordering::Relaxed), 1);

        assert!(!AtomicUpdateExercises::exercise_03_try_update(&counter, 1));
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    // --------------------------------------------------------
    // CollectionMutRefExercises tests
    // --------------------------------------------------------
    #[test]
    fn test_exercise_01_vec_push_mut() {
        let vec = CollectionMutRefExercises::exercise_01_vec_push_mut();
        assert_eq!(vec, vec![1, 2, 3, 42]);
    }

    #[test]
    fn test_exercise_02_vecdeque_insert_mut() {
        let deque = CollectionMutRefExercises::exercise_02_vecdeque_insert_mut();
        let expected = VecDeque::from([
            "world".to_string(),
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
        ]);
        assert_eq!(deque, expected);
    }

    // --------------------------------------------------------
    // ColdPathExercises tests
    // --------------------------------------------------------
    #[test]
    fn test_exercise_01_error_branch() {
        assert_eq!(ColdPathExercises::exercise_01_error_branch(10, 2), Some(5));
        assert_eq!(ColdPathExercises::exercise_01_error_branch(10, 0), None);
    }

    #[test]
    fn test_exercise_02_boundary_case() {
        assert_eq!(
            ColdPathExercises::exercise_02_boundary_case("42 is the answer"),
            Some(42)
        );
        assert_eq!(ColdPathExercises::exercise_02_boundary_case(""), None);
    }
}
