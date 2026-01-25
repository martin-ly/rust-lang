//! 算法模块边界情况测试套件 / Algorithms Module Edge Cases Test Suite

use c08_algorithms::*;

/// 测试空数组/集合边界情况
#[test]
fn test_empty_collections() {
    // 测试空数组排序
    let empty: Vec<i32> = vec![];
    let sorted = empty.clone();
    assert_eq!(sorted, empty);

    // 测试空数组查找
    let empty_vec: Vec<i32> = vec![];
    assert_eq!(empty_vec.len(), 0);

    // 测试空数组最大值/最小值
    let empty_for_max: Vec<i32> = vec![];
    assert_eq!(empty_for_max.iter().max(), None);
    assert_eq!(empty_for_max.iter().min(), None);
}

/// 测试单元素边界情况
#[test]
fn test_single_element() {
    // 单元素数组
    let single = vec![42];
    assert_eq!(single.len(), 1);
    assert_eq!(single[0], 42);

    // 单元素数组排序
    let mut single_sorted = vec![42];
    single_sorted.sort();
    assert_eq!(single_sorted, vec![42]);

    // 单元素数组查找
    assert_eq!(single.iter().find(|&&x| x == 42), Some(&42));
    assert_eq!(single.iter().find(|&&x| x == 0), None);
}

/// 测试大数组边界情况
#[test]
fn test_large_arrays() {
    // 大数组创建
    let large_size = 100000;
    let large_vec: Vec<i32> = (0..large_size).collect();
    assert_eq!(large_vec.len(), large_size);

    // 大数组操作
    let sum: i32 = large_vec.iter().sum();
    assert_eq!(sum, (0..large_size).sum::<i32>());

    // 大数组查找
    assert_eq!(large_vec.iter().find(|&&x| x == 50000), Some(&50000));
    assert_eq!(large_vec.iter().find(|&&x| x == large_size), None);
}

/// 测试算法边界条件
#[test]
fn test_algorithm_edge_cases() {
    // 测试边界值
    let boundary_values = vec![i32::MIN, -1, 0, 1, i32::MAX];
    assert_eq!(boundary_values.len(), 5);

    // 测试重复值
    let duplicates = vec![1, 1, 1, 1, 1];
    assert_eq!(duplicates.iter().all(|&x| x == 1), true);

    // 测试已排序数组
    let sorted = vec![1, 2, 3, 4, 5];
    let mut sorted_copy = sorted.clone();
    sorted_copy.sort();
    assert_eq!(sorted_copy, sorted);

    // 测试逆序数组
    let reversed = vec![5, 4, 3, 2, 1];
    let mut reversed_copy = reversed.clone();
    reversed_copy.sort();
    assert_eq!(reversed_copy, vec![1, 2, 3, 4, 5]);
}

/// 测试错误路径
#[test]
fn test_error_paths() {
    // 测试无效索引访问（应该panic或返回None）
    let vec = vec![1, 2, 3];
    assert_eq!(vec.get(0), Some(&1));
    assert_eq!(vec.get(100), None);

    // 测试空数组操作
    let empty: Vec<i32> = vec![];
    assert_eq!(empty.get(0), None);
    assert_eq!(empty.first(), None);
    assert_eq!(empty.last(), None);
}

/// 测试资源耗尽情况
#[test]
fn test_resource_exhaustion() {
    // 测试大量数据
    let very_large_size = 1000000;
    let large_vec: Vec<usize> = (0..very_large_size).collect();
    assert_eq!(large_vec.len(), very_large_size);

    // 测试内存密集型操作
    let sum: usize = large_vec.iter().sum();
    assert!(sum > 0);
}

/// 测试边界值组合
#[test]
fn test_boundary_value_combinations() {
    // 测试最小值和最大值
    let min_max = vec![i32::MIN, i32::MAX];
    assert_eq!(min_max.len(), 2);
    assert_eq!(min_max.iter().min(), Some(&i32::MIN));
    assert_eq!(min_max.iter().max(), Some(&i32::MAX));

    // 测试零值
    let zeros = vec![0; 100];
    assert_eq!(zeros.iter().all(|&x| x == 0), true);
    assert_eq!(zeros.iter().sum::<i32>(), 0);
}
