//! 集成测试套件
//!
//! 测试所有权与可判定性示例代码库的各种模式

use rust_ownership_exercises::*;
use rust_ownership_exercises::typestate::ConfigBuilder;

// ============================================
// 基础所有权测试
// ============================================

#[test]
fn test_ownership_transfer() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权转移
    // s1 不再有效
    assert_eq!(s2, "hello");
}

#[test]
fn test_copy_trait() {
    let x = 5i32;
    let y = x;  // Copy，不是Move
    assert_eq!(x, 5);  // x仍然有效
    assert_eq!(y, 5);
}

#[test]
fn test_borrowing_rules() {
    let mut data = vec![1, 2, 3];
    
    // 多个不可变借用
    let r1 = &data;
    let r2 = &data;
    assert_eq!(r1[0], r2[0]);
    
    // r1, r2 生命周期结束
    drop(r1);
    drop(r2);
    
    // 现在可以可变借用
    let r3 = &mut data;
    r3.push(4);
    assert_eq!(data.len(), 4);
}

// ============================================
// 生命周期测试
// ============================================

#[test]
fn test_lifetime_elision() {
    fn first_word(s: &str) -> &str {
        let bytes = s.as_bytes();
        for (i, &item) in bytes.iter().enumerate() {
            if item == b' ' {
                return &s[0..i];
            }
        }
        &s[..]
    }
    
    let s = String::from("hello world");
    let word = first_word(&s);
    assert_eq!(word, "hello");
}

#[test]
fn test_explicit_lifetime() {
    fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
        if x.len() > y.len() { x } else { y }
    }
    
    let s1 = String::from("long");
    let s2 = "short";
    let result = longest(&s1, s2);
    assert_eq!(result, "long");
}

// ============================================
// 智能指针测试
// ============================================

#[test]
fn test_box_basic() {
    let b = Box::new(5);
    assert_eq!(*b, 5);
}

#[test]
fn test_rc_counting() {
    use std::rc::Rc;
    
    let data = Rc::new(42);
    assert_eq!(Rc::strong_count(&data), 1);
    
    let data2 = Rc::clone(&data);
    assert_eq!(Rc::strong_count(&data), 2);
    assert_eq!(Rc::strong_count(&data2), 2);
    
    drop(data2);
    assert_eq!(Rc::strong_count(&data), 1);
}

#[test]
fn test_refcell_interior_mutability() {
    use std::cell::RefCell;
    
    let cell = RefCell::new(5);
    
    {
        let mut borrow = cell.borrow_mut();
        *borrow += 1;
    }
    
    assert_eq!(*cell.borrow(), 6);
}

// ============================================
// 并发测试
// ============================================

#[test]
fn test_arc_thread_safety() {
    use std::sync::Arc;
    use std::thread;
    
    let data = Arc::new(vec![1, 2, 3]);
    let mut handles = vec![];
    
    for _ in 0..5 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            assert_eq!(data.len(), 3);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}

#[test]
fn test_mutex_protection() {
    use std::sync::{Arc, Mutex};
    use std::thread;
    
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    assert_eq!(*counter.lock().unwrap(), 10);
}

// ============================================
// 模式测试
// ============================================

#[test]
fn test_typestate_pattern() {
    use rust_ownership_exercises::advanced_patterns::*;
    
    let req = Request::<Unverified>::new("https://example.com".to_string());
    let verified = req.verify();
    assert!(verified.is_ok());
    
    let req2 = Request::<Unverified>::new("http://insecure.com".to_string());
    let verified2 = req2.verify();
    assert!(verified2.is_err());
}

#[test]
fn test_zero_cost_abstraction() {
    use rust_ownership_exercises::advanced_patterns::*;
    
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let result = zero_cost_iterator_chain(&data);
    // 偶数: 2,4,6,8,10 -> 平方: 4,16,36,64,100 -> 和: 220
    assert_eq!(result, 220);
}

// ============================================
// 设计模式测试
// ============================================

#[test]
fn test_builder_pattern() {
    let config = ConfigBuilder::new()
        .host("localhost".to_string())
        .port(8080)
        .build()
        .unwrap();
    
    assert_eq!(config.host(), "localhost");
    assert_eq!(config.port(), 8080);
}

// ============================================
// FFI 安全测试
// ============================================

#[test]
fn test_ffi_c_string() {
    use rust_ownership_exercises::ffi_patterns::*;
    
    let original = "Hello, FFI!".to_string();
    let c_str = rust_to_c_string(original.clone()).unwrap();
    let roundtrip = unsafe { c_to_rust_str(c_str.as_ptr()) }.unwrap();
    assert_eq!(original, roundtrip);
}

// ============================================
// 错误处理测试
// ============================================

#[test]
fn test_result_type() {
    fn may_fail(input: i32) -> Result<i32, String> {
        if input >= 0 {
            Ok(input * 2)
        } else {
            Err("Negative input".to_string())
        }
    }
    
    assert_eq!(may_fail(5).unwrap(), 10);
    assert!(may_fail(-1).is_err());
}

#[test]
fn test_option_type() {
    fn find_index(arr: &[i32], target: i32) -> Option<usize> {
        arr.iter().position(|&x| x == target)
    }
    
    let arr = vec![1, 2, 3, 4, 5];
    assert_eq!(find_index(&arr, 3), Some(2));
    assert_eq!(find_index(&arr, 10), None);
}

// ============================================
// 切片与字符串测试
// ============================================

#[test]
fn test_slice_patterns() {
    let arr = [1, 2, 3, 4, 5];
    let slice = &arr[1..4];
    assert_eq!(slice, &[2, 3, 4]);
    
    // 可变切片
    let mut arr2 = [1, 2, 3, 4, 5];
    let slice2 = &mut arr2[..];
    slice2[0] = 10;
    assert_eq!(arr2[0], 10);
}

#[test]
fn test_string_vs_str() {
    let s = String::from("hello");
    let slice: &str = &s;  // &String -> &str
    assert_eq!(slice, "hello");
}
