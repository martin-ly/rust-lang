//! # Rust 1.96.0 所有权与借用新特性实现模块

use std::ops::RangeInclusive;

/// if let guards 在所有权管理中的应用
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
    pub fn check_borrow_status(
        mutable_borrows: usize,
        immutable_borrows: usize,
    ) -> &'static str {
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

/// RangeInclusive 在所有权管理中的应用
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

/// 元组 coercion 示例
pub struct TupleCoercionExamples;

impl TupleCoercionExamples {
    /// 返回不同类型的引用
    pub fn get_mixed_references<'a>(
        data: &'a [i32],
    ) -> (&'a [i32], &'static str, Option<&'a i32>) {
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
    pub fn mixed_ownership_tuple<'a>(
        borrowed: &'a str,
    ) -> (String, &'a str, Option<String>) {
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
    pub fn transfer_with_metadata(
        data: Vec<u8>,
    ) -> (Vec<u8>, usize, Result<(), String>) {
        let len = data.len();
        let result = if len > 0 { Ok(()) } else { Err("空数据".to_string()) };
        (data, len, result)
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 所有权新特性演示");
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

    // 元组 coercion 演示
    println!("\n=== 元组 coercion 演示 ===");
    let (s, v, b) = TupleCoercionExamples::transfer_ownership_tuple();
    println!("所有权转移: s={}, v={:?}, b={}", s, v, b);

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
pub fn get_rust_196_ownership_info() -> String {
    "Rust 1.96.0 所有权和借用新特性:\n\
        - RangeInclusive / RangeToInclusive 完整支持\n\
        - 元组元素 coercion\n\
        - 生命周期推断改进"
        .to_string()
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
            OwnershipGuardExamples::check_optional_ownership(Some(None)),
            "inner_none"
        );
        assert_eq!(
            OwnershipGuardExamples::check_optional_ownership(None),
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
        assert_eq!(OwnershipRangeExamples::safe_slice_borrow(&data, 10..=20), None);
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
    fn test_get_rust_196_ownership_info() {
        let info = get_rust_196_ownership_info();
        assert!(info.contains("Rust 1.96.0"));
    }
}
