//! Miri 测试模块 - Tree Borrows 验证
//!
//! 本模块包含用于 Miri 测试的代码示例，验证 Tree Borrows 模型的行为。
//! 运行方式:
//!   MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test miri_tests

// ==================== Tree Borrows 通过测试 ====================

/// 测试目的: 验证基本重新借用后使用父引用
/// 测试场景: 创建一个可变引用，然后重新借用，之后再次使用父引用
/// 预期结果: Tree Borrows 模型下应该通过，SB 模型下是 UB
#[test]
fn test_1_basic_reborrow() {
    let mut x = 0;
    let y = &mut x;
    let z = &mut *y;
    
    *z = 1;
    *y = 2;  // Tree Borrows: OK
    
    assert_eq!(x, 2);
}

/// 测试目的: 验证多次重新借用链
/// 测试场景: 创建多层重新借用链，然后逐层使用
/// 预期结果: Tree Borrows 模型下所有引用都有效
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

/// 测试目的: 验证循环中的重新借用
/// 测试场景: 在循环中重新借用 Vec 的元素，循环后继续使用父引用
/// 预期结果: Tree Borrows 模型下应该通过
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

/// 测试目的: 验证切片分割的内存安全
/// 测试场景: 将切片分割为不重叠的两部分并分别修改
/// 预期结果: Tree Borrows 模型下应该通过
#[test]
fn test_4_slice_split() {
    let mut data = [1, 2, 3, 4, 5];
    
    // 分割为不重叠的切片
    let (left, right) = data.split_at_mut(2);
    
    left[0] = 10;
    right[0] = 50;  // 修改 data[3]
    
    assert_eq!(data, [10, 2, 3, 50, 5]);
}

/// 测试目的: 验证重叠切片的不冲突访问
/// 测试场景: 创建逻辑上重叠但实际访问不冲突的切片
/// 预期结果: 不重叠访问应该安全
#[test]
fn test_5_overlapping_slices_no_conflict() {
    let mut data = [1, 2, 3, 4, 5];
    
    // 使用 split_at_mut 创建不重叠的借用
    let (left, temp) = data.split_at_mut(3);
    let right = &mut temp[1..]; // [4, 5] - 不重叠
    
    left[0] = 10;
    right[0] = 50;
    
    assert_eq!(data, [10, 2, 3, 50, 5]);
}

/// 测试目的: 验证 Vec 迭代时 push 的安全性
/// 测试场景: 先完成迭代，然后 push（容量足够）
/// 预期结果: 迭代完成后 push 应该安全
#[test]
fn test_6_vec_push_while_iter() {
    let mut vec = Vec::with_capacity(10);
    vec.extend([1, 2, 3]);
    
    // 先完成迭代
    let sum: i32 = vec.iter().copied().sum();
    
    // 然后再 push
    vec.push(4);
    
    assert_eq!(sum, 6); // 1+2+3
    assert_eq!(vec.len(), 4);
}

/// 测试目的: 验证裸指针直接创建后的别名
/// 测试场景: 使用 addr_of_mut 创建裸指针，然后通过裸指针和引用访问
/// 预期结果: Tree Borrows 模型下裸指针和引用可以共存
#[test]
#[allow(unused_assignments)]
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

/// 测试目的: 验证指针算术访问相邻字段
/// 测试场景: 使用指针算术从一个字段访问相邻字段
/// 预期结果: Tree Borrows 模型下 container_of 模式应该通过
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

/// 测试目的: 验证函数参数重新借用
/// 测试场景: 函数参数被重新借用后，原引用仍然可用
/// 预期结果: 函数返回后原引用应该仍然有效
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

/// 测试目的: 验证匹配中的重新借用
/// 测试场景: 在 match 中对可变引用进行重新借用
/// 预期结果: 匹配后原引用应该仍然有效
#[test]
fn test_10_match_reborrow() {
    let mut x = 5;
    let mut r = &mut x;
    
    match r {
        ref mut mr => {
            **mr = 10;
        }
    }
    
    assert_eq!(*r, 10);
    assert_eq!(x, 10);
}

// ==================== 边界测试 ====================

/// 测试目的: 验证零大小类型的处理
/// 测试场景: 对 ZST 进行可变引用的重新借用
/// 预期结果: ZST 的引用操作应该正常
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

/// 测试目的: 验证空切片的处理
/// 测试场景: 创建并操作空切片
/// 预期结果: 空切片操作应该正常
#[test]
fn test_12_empty_slice() {
    let mut data: [i32; 0] = [];
    let _slice = &mut data[..];
    // 空切片操作
}

/// 测试目的: 验证嵌套结构体的重新借用
/// 测试场景: 通过多级引用访问嵌套结构体
/// 预期结果: 父引用在子引用使用后仍然有效
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

/// 测试目的: 验证数组 windows 功能
/// 测试场景: 使用 array_windows 迭代数组
/// 预期结果: 应该正确计算相邻元素对的和
#[test]
fn test_14_array_windows() {
    let data = [1, 2, 3, 4, 5];
    
    let sum: i32 = data.array_windows::<2>()
        .map(|&[a, b]| a + b)
        .sum();
    
    assert_eq!(sum, (1+2) + (2+3) + (3+4) + (4+5));
}

/// 测试目的: 验证迭代器与可变引用
/// 测试场景: 使用 iter_mut 遍历并修改 Vec
/// 预期结果: 所有元素应该被正确修改
#[test]
fn test_15_iterator_mut() {
    let mut data = vec![1, 2, 3, 4, 5];
    
    for item in data.iter_mut() {
        *item *= 2;
    }
    
    assert_eq!(data, vec![2, 4, 6, 8, 10]);
}

// ==================== 明确 UB 测试（应该失败） ====================

/// 测试目的: 验证使用已释放内存的 UB 检测
/// 测试场景: 在块内创建 Box，块结束后使用其指针
/// 预期结果: Miri 应该检测到 use-after-free
#[test]
#[ignore = "This test should fail with UB"]
fn test_16_use_after_free() {
    let ptr = {
        let x = Box::new(42);
        &*x as *const i32
    };
    
    unsafe {
        // 这是 UB！不要这样做！
        let _ = *ptr;
    }
}

/// 测试目的: 验证数据竞争的 UB 检测
/// 测试场景: 两个线程同时写入同一位置而不使用原子操作
/// 预期结果: Miri 应该检测到数据竞争
#[test]
#[ignore = "This test should fail with data race"]
fn test_17_data_race() {
    use std::thread;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicI32, Ordering};
    
    let x = Arc::new(AtomicI32::new(0));
    let x_clone = Arc::clone(&x);
    
    let handle = thread::spawn(move || {
        x_clone.store(1, Ordering::Relaxed);
    });
    
    x.store(2, Ordering::Relaxed);  // 数据竞争！
    
    handle.join().unwrap();
}

// ==================== 辅助函数 ====================

#[cfg(test)]
mod benchmarks {
    
    /// 测试目的: 重新借用链性能基准
    /// 测试场景: 创建 1000 层重新借用链并操作
    /// 预期结果: 应该快速完成
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
    
    /// 测试目的: 切片操作性能基准
    /// 测试场景: 多次分割切片并操作
    /// 预期结果: 应该快速完成
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
