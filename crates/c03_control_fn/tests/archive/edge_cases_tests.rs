//! 控制流与函数模块边界情况测试套件 / Control Flow and Functions Module Edge Cases Test Suite

use c03_control_fn::*;

/// 测试空循环边界情况
#[test]
fn test_empty_loops() {
    // 空循环测试
    let result = control_flow_loop(0);
    assert_eq!(result, 0);

    // 空循环迭代器
    let empty_vec: Vec<i32> = vec![];
    let count = empty_vec.iter().count();
    assert_eq!(count, 0);

    // 空范围循环
    let mut sum = 0;
    for _ in 0..0 {
        sum += 1;
    }
    assert_eq!(sum, 0);
}

/// 测试单次迭代边界情况
#[test]
fn test_single_iteration() {
    // 单次迭代循环
    let result = control_flow_loop(1);
    assert_eq!(result, 1);

    // 单元素迭代器
    let single = vec![42];
    let count = single.iter().count();
    assert_eq!(count, 1);
    assert_eq!(single[0], 42);

    // 单次范围循环
    let mut sum = 0;
    for i in 0..1 {
        sum += i;
    }
    assert_eq!(sum, 0);
}

/// 测试大值循环边界情况
#[test]
fn test_large_value_loops() {
    // 大值循环
    let large_value = 100000;
    let result = control_flow_loop(large_value);
    assert!(result >= large_value);

    // 大范围循环
    let mut count = 0;
    for _ in 0..10000 {
        count += 1;
    }
    assert_eq!(count, 10000);
}

/// 测试边界分支情况
#[test]
fn test_boundary_branches() {
    // 测试边界值分支
    assert!(control_flow_branch(0).is_ok());
    assert!(control_flow_branch(100).is_ok());
    assert!(control_flow_branch(-1).is_err());

    // 测试边界匹配
    let match_result_zero = control_flow_match(Some(0));
    assert_eq!(match_result_zero, 0);

    let match_result_none = control_flow_match(None);
    assert_eq!(match_result_none, 0);

    // 测试边界条件
    let boundary_values = vec![i32::MIN, -1, 0, 1, i32::MAX];
    for val in boundary_values {
        let result = control_flow_branch(val);
        if val >= 0 && val <= 100 {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
        }
    }
}

/// 测试错误路径
#[test]
fn test_error_paths() {
    // 测试无效输入
    assert!(control_flow_branch(-1).is_err());
    assert!(control_flow_branch(101).is_err());

    // 测试错误状态
    let error_result = control_flow_branch(-100);
    assert!(error_result.is_err());

    // 测试None值处理
    let none_result = control_flow_match(None);
    assert_eq!(none_result, 0);
}

/// 测试资源耗尽情况
#[test]
fn test_resource_exhaustion() {
    // 测试大量循环
    let very_large = 1000000;
    let result = control_flow_loop(very_large);
    assert!(result >= very_large);

    // 测试大量分支
    let mut success_count = 0;
    for i in 0..10000 {
        if control_flow_branch(i).is_ok() {
            success_count += 1;
        }
    }
    assert!(success_count > 0);
}

/// 测试边界值组合
#[test]
fn test_boundary_value_combinations() {
    // 测试最小值和最大值
    assert!(control_flow_branch(i32::MIN).is_err());
    assert!(control_flow_branch(i32::MAX).is_err());

    // 测试零值
    assert!(control_flow_branch(0).is_ok());
    let zero_loop = control_flow_loop(0);
    assert_eq!(zero_loop, 0);

    // 测试边界范围内的值
    for i in 0..=100 {
        assert!(control_flow_branch(i).is_ok());
    }
}
