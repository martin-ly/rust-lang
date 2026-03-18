//! 所有权系统专项测试
//!
//! 测试Rust所有权系统的各种边界情况

// ============================================
// 所有权转移测试
// ============================================

#[test]
fn test_move_semantics() {
    struct NonCopy {
        data: String,
    }
    
    let x = NonCopy { data: String::from("hello") };
    let y = x;  // Move
    // x.data 不能再访问
    assert_eq!(y.data, "hello");
}

#[test]
fn test_clone_explicit() {
    #[derive(Clone)]
    struct Cloneable {
        data: String,
    }
    
    let x = Cloneable { data: String::from("hello") };
    let y = x.clone();  // 显式克隆
    assert_eq!(x.data, "hello");  // x仍然有效
    assert_eq!(y.data, "hello");
}

// ============================================
// 借用生命周期测试
// ============================================

#[test]
fn test_non_lexical_lifetimes() {
    let mut x = 5;
    
    let y = &mut x;
    *y += 1;
    // y 的生命周期在这里结束（NLL）
    
    let z = &mut x;  // 可以再次借用
    *z += 1;
    
    assert_eq!(x, 7);
}

#[test]
fn test_borrow_scope_isolation() {
    let mut data = vec![1, 2, 3];
    
    {
        let borrow = &mut data;
        borrow.push(4);
    }  // 借用在这里结束
    
    // 可以新的借用
    let borrow2 = &data;
    assert_eq!(borrow2.len(), 4);
}

// ============================================
// 重新借用测试
// ============================================

#[test]
fn test_reborrowing() {
    fn process(data: &mut Vec<i32>) {
        data.push(100);
    }
    
    let mut vec = vec![1, 2, 3];
    process(&mut vec);  // 重新借用
    assert_eq!(vec.len(), 4);
    
    // vec 仍然可用
    vec.push(200);
    assert_eq!(vec.len(), 5);
}

// ============================================
// Drop顺序测试
// ============================================

#[test]
fn test_drop_order() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
    
    struct DropCounter;
    impl Drop for DropCounter {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(1, Ordering::SeqCst);
        }
    }
    
    {
        let _a = DropCounter;
        let _b = DropCounter;
        let _c = DropCounter;
    }  // 按c, b, a的顺序drop
    
    assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
}

// ============================================
// 所有权与模式匹配
// ============================================

#[test]
fn test_pattern_matching_ownership() {
    enum Message {
        Text(String),
        Number(i32),
    }
    
    let msg = Message::Text(String::from("hello"));
    
    match msg {
        Message::Text(s) => {
            assert_eq!(s, "hello");  // s拥有String
        }
        Message::Number(n) => {
            assert_eq!(n, 0);
        }
    }
    // msg 不能再使用（所有权已转移）
}

#[test]
fn test_ref_pattern() {
    let s = String::from("hello");
    
    match &s {
        ref text => {
            assert_eq!(text, &"hello");
        }
    }
    
    // s 仍然有效（借用）
    assert_eq!(s, "hello");
}

// ============================================
// 函数返回值所有权
// ============================================

#[test]
fn test_return_ownership() {
    fn take_and_return(s: String) -> String {
        s  // 返回所有权
    }
    
    let s = String::from("hello");
    let s = take_and_return(s);
    assert_eq!(s, "hello");
}

#[test]
fn test_return_borrow() {
    fn get_first(s: &str) -> &str {
        &s[0..1]
    }
    
    let s = String::from("hello");
    let first = get_first(&s);
    assert_eq!(first, "h");
    // s 仍然有效
    assert_eq!(s, "hello");
}

// ============================================
// 集合所有权测试
// ============================================

#[test]
fn test_vec_ownership() {
    let mut vec = vec![
        String::from("a"),
        String::from("b"),
    ];
    
    // 通过索引获取所有权
    let first = std::mem::replace(&mut vec[0], String::from("x"));
    assert_eq!(first, "a");
    assert_eq!(vec[0], "x");
    
    // pop 转移所有权
    let last = vec.pop().unwrap();
    assert_eq!(last, "b");
}

#[test]
fn test_hashmap_ownership() {
    use std::collections::HashMap;
    
    let mut map = HashMap::new();
    map.insert("key", String::from("value"));
    
    // get 返回借用
    if let Some(v) = map.get("key") {
        assert_eq!(v, "value");
    }
    
    // remove 转移所有权
    let removed = map.remove("key").unwrap();
    assert_eq!(removed, "value");
}

// ============================================
// 闭包与所有权
// ============================================

#[test]
fn test_closure_move() {
    let s = String::from("hello");
    
    let f = move || {
        println!("{}", s);
        s  // 返回所有权
    };
    
    let s = f();  // 重新获得所有权
    assert_eq!(s, "hello");
}

#[test]
fn test_closure_borrow() {
    let s = String::from("hello");
    
    let f = || {
        println!("{}", s);  // 借用
    };
    
    f();
    f();  // 可以多次调用
    assert_eq!(s, "hello");  // s 仍然有效
}

// ============================================
// 静态生命周期
// ============================================

#[test]
fn test_static_lifetime() {
    fn get_static() -> &'static str {
        "I am static"
    }
    
    let s = get_static();
    assert_eq!(s, "I am static");
}

#[test]
fn test_static_storage() {
    use std::sync::Mutex;
    
    static COUNTER: Mutex<i32> = Mutex::new(0);
    
    {
        let mut count = COUNTER.lock().unwrap();
        *count += 1;
    }
    
    {
        let count = COUNTER.lock().unwrap();
        assert_eq!(*count, 1);
    }
}
