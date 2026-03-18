//! Miri 测试模块 - Tree Borrows 验证
//!
//! 本模块包含用于 Miri 测试的代码示例，验证 Tree Borrows 模型的行为。
//! 运行方式:
//!   MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test miri_tests

// ==================== Tree Borrows 通过测试 ====================

/// 测试 1: 基本重新借用后使用父引用
/// SB: UB
/// TB: OK
#[test]
fn test_1_basic_reborrow() {
    let mut x = 0;
    let y = &mut x;
    let z = &mut *y;
    
    *z = 1;
    *y = 2;  // Tree Borrows: OK
    
    assert_eq!(x, 2);
}

/// 测试 2: 多次重新借用链
/// SB: UB
/// TB: OK
#[test]
fn test_2_reborrow_chain() {
    let mut x = 0;
    let a = &mut x;
    let b = &mut *a;
    let c = &mut *b;
    let d = &mut *c;
    
    *d = 1;
    *c = 2;
    *b = 3;
    *a = 4;
    
    assert_eq!(x, 4);
}

/// 测试 3: 循环中的重新借用
/// SB: OK
/// TB: OK
#[test]
fn test_3_loop_reborrow() {
    let mut data = vec![1, 2, 3, 4, 5];
    let mut_ref = &mut data;
    
    for i in 0..mut_ref.len() {
        let elem = &mut mut_ref[i];
        *elem *= 2;
    }
    
    // 循环后仍然可以使用 mut_ref
    mut_ref.push(6);
    
    assert_eq!(mut_ref, &[2, 4, 6, 8, 10, 6]);
}

/// 测试 4: 切片分割
/// SB: 条件 OK
/// TB: OK
#[test]
fn test_4_slice_split() {
    let mut data = [1, 2, 3, 4, 5];
    
    // 分割为不重叠的切片
    let (left, right) = data.split_at_mut(2);
    
    left[0] = 10;
    right[0] = 50;  // 修改 data[3]
    
    assert_eq!(data, [10, 2, 3, 50, 5]);
}

/// 测试 5: 重叠切片（不真正重叠访问）
/// SB: OK
/// TB: OK
#[test]
fn test_5_overlapping_slices_no_conflict() {
    let mut data = [1, 2, 3, 4, 5];
    
    let left = &mut data[..2];  // [1, 2]
    let right = &mut data[3..]; // [4, 5] - 不重叠
    
    left[0] = 10;
    right[0] = 50;
    
    assert_eq!(data, [10, 2, 3, 50, 5]);
}

/// 测试 6: Vec 迭代时 push（容量足够）
/// SB: OK (如果容量足够)
/// TB: OK
#[test]
fn test_6_vec_push_while_iter() {
    let mut vec = Vec::with_capacity(10);
    vec.extend([1, 2, 3]);
    
    let iter = vec.iter();
    
    // push 可能重新分配，但在容量足够时是安全的
    if vec.capacity() > vec.len() {
        vec.push(4);
    }
    
    let sum: i32 = iter.copied().sum();
    assert!(sum >= 6); // 1+2+3
}

/// 测试 7: 裸指针直接创建后的别名
/// SB: 可能 UB
/// TB: OK
#[test]
fn test_7_raw_pointer_alias() {
    let mut x = 0;
    let ptr = std::ptr::addr_of_mut!(x);
    
    unsafe {
        *ptr = 1;
    }
    
    x = 2;  // Tree Borrows: OK
    
    unsafe {
        assert_eq!(*ptr, 2);
    }
}

/// 测试 8: 指针算术访问相邻字段
/// SB: UB
/// TB: OK (container_of 模式)
#[repr(C)]
struct Container {
    header: u32,
    data: u8,
}

#[test]
fn test_8_pointer_arithmetic_fields() {
    let mut container = Container {
        header: 1,
        data: 2,
    };
    
    unsafe {
        let data_ptr = &mut container.data as *mut u8;
        // 访问相邻的 header (通过负偏移)
        let header_ptr = (data_ptr as *mut u8).sub(4) as *mut u32;
        *header_ptr = 100;
        
        assert_eq!(container.header, 100);
    }
}

/// 测试 9: 函数参数重新借用
/// SB: OK
/// TB: OK
#[test]
fn test_9_fn_arg_reborrow() {
    fn inner(v: &mut Vec<i32>) {
        if let Some(first) = v.first_mut() {
            *first = 42;
        }
        // v 仍然有效
        v.push(100);
    }
    
    let mut data = vec![1, 2, 3];
    inner(&mut data);
    
    assert_eq!(data[0], 42);
    assert_eq!(data[3], 100);
}

/// 测试 10: 匹配中的重新借用
/// SB: OK
/// TB: OK
#[test]
fn test_10_match_reborrow() {
    enum Node {
        Leaf(i32),
        Branch(Box<Node>, Box<Node>),
    }
    
    fn increment_all(node: &mut Node) {
        match node {
            Node::Leaf(n) => {
                **n += 1;
            }
            Node::Branch(left, right) => {
                increment_all(left);
                increment_all(right);
            }
        }
    }
    
    let mut tree = Node::Branch(
        Box::new(Node::Leaf(1)),
        Box::new(Node::Leaf(2)),
    );
    
    increment_all(&mut tree);
    
    if let Node::Branch(l, r) = tree {
        if let (Node::Leaf(lv), Node::Leaf(rv)) = (l.as_ref(), r.as_ref()) {
            assert_eq!(*lv, 2);
            assert_eq!(*rv, 3);
        }
    }
}

// ==================== 边界测试 ====================

/// 测试 11: 零大小类型
#[test]
fn test_11_zero_sized_types() {
    struct Zst;
    
    let mut x = Zst;
    let r1 = &mut x;
    let r2 = &mut *r1;
    
    // 使用 r2
    let _ = r2;
    
    // 使用 r1 (父引用)
    let _ = r1;  // Tree Borrows: OK
}

/// 测试 12: 空切片
#[test]
fn test_12_empty_slice() {
    let mut data: [i32; 0] = [];
    let _slice = &mut data[..];
    // 空切片操作
}

/// 测试 13: 嵌套结构体
#[test]
fn test_13_nested_struct() {
    struct Outer {
        inner: Inner,
    }
    
    struct Inner {
        value: i32,
    }
    
    let mut outer = Outer { inner: Inner { value: 0 } };
    let outer_ref = &mut outer;
    let inner_ref = &mut outer_ref.inner;
    
    inner_ref.value = 42;
    
    // outer_ref 仍然有效
    outer_ref.inner.value = 100;  // Tree Borrows: OK
    
    assert_eq!(outer.inner.value, 100);
}

/// 测试 14: 数组 windows (Rust 1.94)
#[test]
fn test_14_array_windows() {
    let data = [1, 2, 3, 4, 5];
    
    let sum: i32 = data.array_windows::<2>()
        .map(|&[a, b]| a + b)
        .sum();
    
    assert_eq!(sum, (1+2) + (2+3) + (3+4) + (4+5));
}

/// 测试 15: 迭代器与可变引用
#[test]
fn test_15_iterator_mut() {
    let mut data = vec![1, 2, 3, 4, 5];
    
    for item in data.iter_mut() {
        *item *= 2;
    }
    
    assert_eq!(data, vec![2, 4, 6, 8, 10]);
}

// ==================== 明确 UB 测试（应该失败） ====================

/// 测试 16: 使用已释放内存（应该 UB）
/// 这个测试在 Miri 下应该失败
#[test]
#[ignore = "This test should fail with UB"]
fn test_16_use_after_free() {
    let ptr = {
        let x = Box::new(42);
        &*x as *const i32
    };
    
    unsafe {
        // 这是 UB！不要这样做！
        println!("{}", *ptr);
    }
}

/// 测试 17: 数据竞争（应该 UB）
#[test]
#[ignore = "This test should fail with data race"]
fn test_17_data_race() {
    use std::thread;
    
    let mut x = 0;
    let ptr = &mut x as *mut i32;
    
    unsafe {
        let handle = thread::spawn(move || {
            *ptr = 1;
        });
        
        *ptr = 2;  // 数据竞争！
        
        handle.join().unwrap();
    }
}

// ==================== 辅助函数 ====================

#[cfg(test)]
mod benchmarks {
    use super::*;
    
    /// 基准测试：重新借用链性能
    #[test]
    fn bench_reborrow_chain() {
        let mut x = 0;
        
        for _ in 0..1000 {
            let a = &mut x;
            let b = &mut *a;
            let c = &mut *b;
            let d = &mut *c;
            *d += 1;
        }
        
        assert_eq!(x, 1000);
    }
    
    /// 基准测试：切片操作
    #[test]
    fn bench_slice_operations() {
        let mut data = [0; 1000];
        
        for i in 0..data.len() - 1 {
            let (left, right) = data.split_at_mut(i + 1);
            left[i] = i as i32;
            if !right.is_empty() {
                right[0] = -(i as i32);
            }
        }
    }
}
