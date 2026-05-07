//! # Rust 1.96 特性跟踪模块（含历史特性复习与 1.96 前瞻）

use std::ops::RangeInclusive;

/// `if let` guards (Rust 1.95 稳定，非 1.96 新特性) 在所有权管理中的应用
///
/// `if let` guards 允许在 match arm 上直接进行模式匹配和条件判断，
/// 减少嵌套层级，使代码更扁平、更易读。
pub struct OwnershipIfLetGuardExamples;

impl OwnershipIfLetGuardExamples {
    /// 解析并验证资源句柄
    pub fn parse_handle(handle: Option<&str>) -> Result<u64, &'static str> {
        match handle {
            Some(s) if let Ok(id) = s.parse::<u64>() => Ok(id),
            Some(_) => Err("无效的资源句柄格式"),
            None => Err("资源句柄为空"),
        }
    }

    /// 检查嵌套所有权转移状态
    pub fn check_transfer_status(status: Option<Result<&str, &str>>) -> &'static str {
        match status {
            Some(Ok(new_owner)) if !new_owner.is_empty() => "转移成功",
            Some(Ok(_)) => "所有者名为空",
            Some(Err(_)) => "转移失败",
            None => "未开始转移",
        }
    }
}

/// if let guards (Rust 1.95 稳定) 在所有权管理中的应用
pub struct OwnershipGuardExamples;

impl OwnershipGuardExamples {
    /// 检查可选所有权
    pub fn check_optional_ownership<T>(opt: Option<Option<T>>) -> &'static str
    where
        T: Clone,
    {
        match opt {
            Some(Some(_)) => "nested_some",
            Some(None) => "inner_none",
            None => "outer_none",
        }
    }

    /// 资源所有权验证
    pub fn validate_resource_owner(
        resource: &str,
        owner: Option<&str>,
        pending: Option<&str>,
    ) -> Result<(), String> {
        match (owner, pending) {
            (Some(current), _) if current == resource => Ok(()),
            (None, Some(pending_owner)) if pending_owner == resource => {
                Err("资源正在转移中".to_string())
            }
            (Some(_), _) => Err("资源被其他所有者持有".to_string()),
            (None, None) => Err("资源无所有者".to_string()),
            (None, Some(_)) => Err("资源待分配".to_string()),
        }
    }

    /// 借用状态检查
    pub fn check_borrow_status(mutable_borrows: usize, immutable_borrows: usize) -> &'static str {
        match (mutable_borrows, immutable_borrows) {
            (0, 0) => "未借用",
            (0, n) if n > 0 && n <= 3 => "少量不可变借用",
            (0, n) if n > 3 => "大量不可变借用",
            (1, 0) => "单一可变借用",
            (m, n) if m > 0 && n > 0 => "借用冲突",
            _ => "未知状态",
        }
    }
}

/// Range 类型应用（标准库基础特性）
pub struct OwnershipRangeExamples;

impl OwnershipRangeExamples {
    /// 安全的切片借用
    pub fn safe_slice_borrow<T>(data: &[T], range: RangeInclusive<usize>) -> Option<&[T]>
    where
        T: Copy,
    {
        let start = *range.start();
        let end = *range.end();

        if start > end || end >= data.len() {
            return None;
        }

        Some(&data[start..=end])
    }

    /// 前缀借用
    pub fn prefix_borrow<T>(data: &[T], end: usize) -> &[T]
    where
        T: Copy,
    {
        let end = end.min(data.len().saturating_sub(1));
        &data[..=end]
    }

    /// 所有权边界检查
    pub fn check_ownership_bounds(index: usize, valid_range: RangeInclusive<usize>) -> bool {
        valid_range.contains(&index)
    }

    /// 生命周期阶段
    pub fn get_lifetime_stage(age_seconds: u64) -> &'static str {
        match age_seconds {
            0..=60 => " newborn",
            61..=3600 => "young",
            3601..=86400 => "mature",
            _ => "aged",
        }
    }

    /// 资源池索引分配
    pub fn allocate_resource_range(
        pool_size: usize,
        requested: usize,
    ) -> Option<RangeInclusive<usize>> {
        if requested == 0 || requested > pool_size {
            return None;
        }

        Some(0..=requested - 1)
    }
}

/// 元组类型应用（泛型编程基础）
pub struct TupleCoercionExamples;

impl TupleCoercionExamples {
    /// 返回不同类型的引用
    pub fn get_mixed_references(data: &[i32]) -> (&[i32], &'static str, Option<&i32>) {
        let first = data.first();
        (data, "slice", first)
    }

    /// 所有权转移
    pub fn transfer_ownership_tuple() -> (String, Vec<i32>, Box<i32>) {
        let s = String::from("owned");
        let v = vec![1, 2, 3];
        let b = Box::new(42);
        (s, v, b)
    }

    /// 借用和拥有的混合
    pub fn mixed_ownership_tuple(borrowed: &str) -> (String, &str, Option<String>) {
        let owned = borrowed.to_uppercase();
        (owned, borrowed, Some(String::from("extra")))
    }
}

/// 实际应用示例
pub struct PracticalApplications;

impl PracticalApplications {
    /// 资源可用性检查
    pub fn check_resource_availability(
        resources: &[Option<String>],
        index: usize,
    ) -> Result<String, String> {
        match resources.get(index) {
            Some(opt) => match opt {
                Some(resource) => {
                    if resource.starts_with("available:") {
                        Ok(resource.clone())
                    } else {
                        Err("资源不可用".to_string())
                    }
                }
                None => Err("资源槽位为空".to_string()),
            },
            None => Err("索引越界".to_string()),
        }
    }

    /// 安全内存区域划分
    pub fn define_safe_memory_region(
        total_size: usize,
        reserved_start: usize,
        reserved_end: usize,
    ) -> Option<(RangeInclusive<usize>, RangeInclusive<usize>)> {
        if reserved_start > reserved_end || reserved_end >= total_size {
            return None;
        }

        let reserved = reserved_start..=reserved_end;
        let available_start = reserved_end + 1;

        if available_start >= total_size {
            return Some((reserved, 0..=0));
        }

        let available = available_start..=total_size - 1;
        Some((reserved, available))
    }

    /// 带元数据的所有权转移
    pub fn transfer_with_metadata(data: Vec<u8>) -> (Vec<u8>, usize, Result<(), String>) {
        let len = data.len();
        let result = if len > 0 {
            Ok(())
        } else {
            Err("空数据".to_string())
        };
        (data, len, result)
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.95+ 特性跟踪演示");
    println!("========================================\n");

    // Range 类型演示
    println!("=== Range 类型演示 ===");
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    if let Some(slice) = OwnershipRangeExamples::safe_slice_borrow(&data, 2..=5) {
        println!("切片借用 [2..=5]: {:?}", slice);
    }

    let prefix = OwnershipRangeExamples::prefix_borrow(&data, 3);
    println!("前缀借用 [..=3]: {:?}", prefix);

    let is_valid = OwnershipRangeExamples::check_ownership_bounds(5, 0..=10);
    println!("索引5在范围[0..=10]内: {}", is_valid);

    let stage = OwnershipRangeExamples::get_lifetime_stage(3600);
    println!("生命周期阶段 (3600秒): {}", stage);

    if let Some(range) = OwnershipRangeExamples::allocate_resource_range(100, 10) {
        println!("分配资源范围: {:?}", range);
    }

    // 元组类型应用演示
    println!("\n=== 元组 coercion 演示 ===");
    let (s, v, b) = TupleCoercionExamples::transfer_ownership_tuple();
    println!("所有权转移: s={}, v={:?}, b={}", s, v, b);

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
pub fn get_rust_196_ownership_info() -> String {
    "Rust 1.95+ 特性跟踪:\n- RangeInclusive / RangeToInclusive 完整支持\n- 元组元素 coercion\n- \
     生命周期推断改进"
        .to_string()
}

// ============================================================================
// Rust 1.96 新特性：`core::pin::pin!` 宏 — 栈上固定 (1.96 stable)
// ============================================================================

/// # `core::pin::pin!` 宏
///
/// Rust 1.96.0 稳定了 `core::pin::pin!` 宏，允许在栈上创建固定值，
/// 无需 `Box::pin` 的堆分配开销。
///
/// ## 所有权意义
/// `pin!` 使得自引用结构可以在栈上安全构造，
/// 避免了将所有权转移到堆上的性能损失。
/// 这是所有权系统与 `Pin` 契约的关键结合点。
pub struct PinMacroExamples;

impl PinMacroExamples {
    /// 在栈上固定自引用结构
    ///
    /// `pin!` 返回的 `Pin<&mut T>` 保证被固定的值在内存中不会移动，
    /// 直到 `Pin` 被丢弃。
    pub fn stack_pin_example() {
        // 使用 core::pin::pin! 在栈上固定值
        let pinned = std::pin::pin!(42);
        assert_eq!(*pinned, 42);
    }

    /// 与异步 Future 结合：栈上固定 future 避免 Box
    pub fn pin_future_on_stack<F>(_future: F) -> std::pin::Pin<&'static mut F>
    where
        F: std::future::Future,
    {
        // 实际用法：let pinned = pin!(future);
        // 此处返回类型仅作演示
        todo!("实际使用场景中，pin! 在调用点创建 Pin")
    }
}

// ============================================================================
// Rust 1.96 新特性：`NonNull::new` const 支持 (1.96 stable)
// ============================================================================

/// # `NonNull::new` 的 `const` 支持
///
/// Rust 1.96.0 使 `NonNull::new` 成为 `const fn`，
/// 允许在常量上下文中安全构造非空裸指针。
///
/// ## 所有权意义
/// `NonNull` 是 `*mut T` 的类型安全包装，保证指针非空。
/// const 支持使得编译期内存布局计算更加精确。
use std::ptr::NonNull;

pub struct ConstNonNullExamples;

impl ConstNonNullExamples {
    /// 编译期构造 NonNull 常量
    ///
    /// 使用静态引用的地址作为有效指针来源。
    pub const CONST_PTR: Option<NonNull<i32>> = {
        const VALUE: i32 = 0;
        NonNull::new(&VALUE as *const i32 as *mut i32)
    };

    /// 验证 NonNull 的常量构造
    pub fn demonstrate_const_nonnull() {
        // 在 const 上下文中初始化 NonNull
        const VALUE: i32 = 42;
        const PTR: Option<NonNull<i32>> = NonNull::new(&VALUE as *const i32 as *mut i32);
        assert!(PTR.is_some());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_check_optional_ownership() {
        assert_eq!(
            OwnershipGuardExamples::check_optional_ownership(Some(Some(42))),
            "nested_some"
        );
        assert_eq!(
            OwnershipGuardExamples::check_optional_ownership(Some(None::<i32>)),
            "inner_none"
        );
        assert_eq!(
            OwnershipGuardExamples::check_optional_ownership::<i32>(None),
            "outer_none"
        );
    }

    #[test]
    fn test_validate_resource_owner() {
        assert!(OwnershipGuardExamples::validate_resource_owner("r1", Some("r1"), None).is_ok());
        assert!(OwnershipGuardExamples::validate_resource_owner("r1", Some("r2"), None).is_err());
    }

    #[test]
    fn test_safe_slice_borrow() {
        let data = vec![1, 2, 3, 4, 5];
        assert_eq!(
            OwnershipRangeExamples::safe_slice_borrow(&data, 1..=3),
            Some(&[2, 3, 4][..])
        );
        assert_eq!(
            OwnershipRangeExamples::safe_slice_borrow(&data, 10..=20),
            None
        );
    }

    #[test]
    fn test_prefix_borrow() {
        let data = vec![1, 2, 3, 4, 5];
        assert_eq!(OwnershipRangeExamples::prefix_borrow(&data, 2), &[1, 2, 3]);
    }

    #[test]
    fn test_check_ownership_bounds() {
        assert!(OwnershipRangeExamples::check_ownership_bounds(5, 0..=10));
        assert!(!OwnershipRangeExamples::check_ownership_bounds(15, 0..=10));
    }

    #[test]
    fn test_transfer_ownership_tuple() {
        let (s, v, b) = TupleCoercionExamples::transfer_ownership_tuple();
        assert_eq!(s, "owned");
        assert_eq!(v, vec![1, 2, 3]);
        assert_eq!(*b, 42);
    }

    #[test]
    fn test_transfer_with_metadata() {
        let data = vec![1, 2, 3];
        let (data, len, result) = PracticalApplications::transfer_with_metadata(data);
        assert_eq!(len, 3);
        assert!(result.is_ok());
        assert_eq!(data, vec![1, 2, 3]);
    }

    #[test]
    fn test_parse_handle() {
        assert_eq!(
            OwnershipIfLetGuardExamples::parse_handle(Some("42")),
            Ok(42)
        );
        assert_eq!(
            OwnershipIfLetGuardExamples::parse_handle(Some("abc")),
            Err("无效的资源句柄格式")
        );
        assert_eq!(
            OwnershipIfLetGuardExamples::parse_handle(None),
            Err("资源句柄为空")
        );
    }

    #[test]
    fn test_check_transfer_status() {
        assert_eq!(
            OwnershipIfLetGuardExamples::check_transfer_status(Some(Ok("user1"))),
            "转移成功"
        );
        assert_eq!(
            OwnershipIfLetGuardExamples::check_transfer_status(Some(Ok(""))),
            "所有者名为空"
        );
        assert_eq!(
            OwnershipIfLetGuardExamples::check_transfer_status(Some(Err("timeout"))),
            "转移失败"
        );
        assert_eq!(
            OwnershipIfLetGuardExamples::check_transfer_status(None),
            "未开始转移"
        );
    }

    #[test]
    fn test_get_rust_196_ownership_info() {
        let info = get_rust_196_ownership_info();
        assert!(!info.is_empty());
    }
}

/// if let guards 反模式与边界情况专题
pub mod anti_patterns_and_edge_cases {
    /// 展示 if let guards 的反模式和边界情况
    pub struct IfLetGuardAntiPatterns;

    impl IfLetGuardAntiPatterns {
        /// ❌ 不推荐：过度复杂化简单条件
        /// 对于简单的 Option 检查，使用过多的 if let guards 反而增加认知负担
        pub fn overcomplicated_simple_check(opt: Option<i32>) -> &'static str {
            // ❌ 反例：本可以用更简洁的 match，却用了过度复杂且重叠的 guard
            match opt {
                Some(n) if n > 0 && n < 100 && n % 2 == 0 => "small_even",
                Some(n) if n > 0 && n < 100 && n % 2 == 1 => "small_odd",
                Some(n) if n >= 100 && n % 2 == 0 => "large_even",
                Some(n) if n >= 100 && n % 2 == 1 => "large_odd",
                Some(0) => "zero",
                Some(_) => "negative", // 实际上永远不会到达，因为前面已覆盖所有 >=0
                None => "none",
            }
        }

        /// ✅ 推荐：简单条件使用清晰的分层 match
        pub fn clean_simple_check(opt: Option<i32>) -> &'static str {
            match opt {
                None => "none",
                Some(0) => "zero",
                Some(n) if n < 0 => "negative",
                Some(n) if n < 100 && n % 2 == 0 => "small_even",
                Some(n) if n < 100 => "small_odd",
                Some(n) if n % 2 == 0 => "large_even",
                Some(_) => "large_odd",
            }
        }

        /// ⚠️ 边界情况：guard 中绑定变量的作用域边界
        /// 在 match guard 中绑定的变量只在 guard 和对应 arm 体中可用
        pub fn guard_binding_scope(result: Result<&str, &str>) -> String {
            match result {
                // guard 中绑定的 n 可以在 arm 体中使用
                Ok(s) if let Ok(n) = s.parse::<i32>() => format!("parsed: {}", n),
                Ok(s) => format!("not a number: {}", s),
                Err(e) => format!("error: {}", e),
            }
        }

        /// ⚠️ 边界情况：guard 失败后回退到下一个 match arm
        /// 如果 guard 失败，会回退到下一个 arm，而不是跳过整个 match
        pub fn guard_fallback_behavior(input: Option<&str>) -> &'static str {
            match input {
                // 先尝试解析为 i32 且值大于 100
                Some(s)
                    if let Ok(n) = s.parse::<i32>()
                        && n > 100 =>
                {
                    "big_number"
                }
                // guard 失败（解析失败或 n <= 100）时回退到这里
                Some(s) if s.starts_with("special") => "special_string",
                Some(_) => "other_string",
                None => "none",
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_overcomplicated_simple_check() {
            assert_eq!(
                IfLetGuardAntiPatterns::overcomplicated_simple_check(Some(50)),
                "small_even"
            );
            assert_eq!(
                IfLetGuardAntiPatterns::overcomplicated_simple_check(Some(0)),
                "zero"
            );
            assert_eq!(
                IfLetGuardAntiPatterns::overcomplicated_simple_check(None),
                "none"
            );
        }

        #[test]
        fn test_clean_simple_check() {
            assert_eq!(
                IfLetGuardAntiPatterns::clean_simple_check(Some(50)),
                "small_even"
            );
            assert_eq!(IfLetGuardAntiPatterns::clean_simple_check(Some(0)), "zero");
            assert_eq!(IfLetGuardAntiPatterns::clean_simple_check(None), "none");
        }

        #[test]
        fn test_guard_binding_scope() {
            assert_eq!(
                IfLetGuardAntiPatterns::guard_binding_scope(Ok("42")),
                "parsed: 42"
            );
            assert_eq!(
                IfLetGuardAntiPatterns::guard_binding_scope(Ok("abc")),
                "not a number: abc"
            );
            assert_eq!(
                IfLetGuardAntiPatterns::guard_binding_scope(Err("fail")),
                "error: fail"
            );
        }

        #[test]
        fn test_guard_fallback_behavior() {
            assert_eq!(
                IfLetGuardAntiPatterns::guard_fallback_behavior(Some("200")),
                "big_number"
            );
            assert_eq!(
                IfLetGuardAntiPatterns::guard_fallback_behavior(Some("special_one")),
                "special_string"
            );
            assert_eq!(
                IfLetGuardAntiPatterns::guard_fallback_behavior(Some("hello")),
                "other_string"
            );
            assert_eq!(
                IfLetGuardAntiPatterns::guard_fallback_behavior(None),
                "none"
            );
        }
    }
}
