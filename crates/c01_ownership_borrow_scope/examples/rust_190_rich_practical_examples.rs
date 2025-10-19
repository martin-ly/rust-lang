//! Rust 1.90 丰富实战示例集
//! 
//! 本文件包含所有可运行的实战代码示例
//! 对应文档：RUST_190_RICH_EXAMPLES_INTEGRATION.md

use std::rc::Rc;
use std::sync::{Arc, Mutex, RwLock};
use std::thread;
use std::time::Duration;
use std::cell::RefCell;

// ============================================================================
// 第一部分：基础层示例
// ============================================================================

/// 示例1: 栈和堆内存对比
#[allow(dead_code)]
fn memory_layout_example() {
    #[derive(Debug, Clone, Copy)]
    struct SmallData {
        x: i32,
        y: i32,
    }

    #[derive(Debug)]
    struct LargeData {
        data: [i32; 1000],
        metadata: String,
    }

    // 栈分配
    let stack_data = SmallData { x: 10, y: 20 };
    println!("栈数据: {:?}", stack_data);
    
    // 可以Copy
    let stack_copy = stack_data;
    println!("复制后原数据仍可用: {:?}", stack_data);
    println!("复制的数据: {:?}", stack_copy);

    // 堆分配
    let heap_data = Box::new(LargeData {
        data: [0; 1000],
        metadata: String::from("堆数据"),
    });
    println!("堆数据元信息: {}", heap_data.metadata);
    
    // Move语义
    let heap_moved = heap_data;
    println!("移动后的数据: {}", heap_moved.metadata);
}

/// 示例2: Copy vs Move 类型系统
#[allow(dead_code)]
fn copy_vs_move_example() {
    // Copy类型
    #[derive(Debug, Clone, Copy)]
    struct Point {
        x: i32,
        y: i32,
    }

    let p1 = Point { x: 5, y: 10 };
    let p2 = p1; // 自动Copy
    println!("p1: {:?}, p2: {:?}", p1, p2); // 两者都有效

    // Move类型
    #[derive(Debug)]
    struct Person {
        name: String,
        age: u32,
    }

    let person1 = Person {
        name: String::from("Alice"),
        age: 30,
    };
    
    let person2 = person1; // Move
    println!("person2: {:?}", person2);
    // println!("person1: {:?}", person1); // ❌ 编译错误
}

// ============================================================================
// 第二部分：核心层示例 - 所有权
// ============================================================================

/// 示例3: 所有权三大规则
#[allow(dead_code)]
fn ownership_rules_example() {
    #[derive(Debug)]
    struct Resource {
        id: u32,
    }

    impl Drop for Resource {
        fn drop(&mut self) {
            println!("释放资源: {}", self.id);
        }
    }

    // 规则1: 每个值有唯一所有者
    let r1 = Resource { id: 1 };
    
    // 规则2: 所有权可以转移
    let r2 = r1;
    // println!("{:?}", r1); // ❌ r1已失效
    
    println!("r2: {:?}", r2);
    
    // 规则3: 离开作用域自动释放
} // r2在这里被drop

/// 示例4: 所有权转移的各种场景
#[allow(dead_code)]
fn ownership_transfer_scenarios() {
    let s1 = String::from("hello");
    
    // 场景1: 赋值转移
    let s2 = s1;
    println!("s2: {}", s2);
    
    // 场景2: 函数参数转移
    fn takes_ownership(s: String) {
        println!("拥有: {}", s);
    }
    
    takes_ownership(s2);
    // println!("{}", s2); // ❌ 已被移动
    
    // 场景3: 函数返回转移
    fn gives_ownership() -> String {
        String::from("returned")
    }
    
    let s3 = gives_ownership();
    println!("s3: {}", s3);
    
    // 场景4: 先取后返
    fn takes_and_gives_back(s: String) -> String {
        s
    }
    
    let s4 = String::from("hello");
    let s5 = takes_and_gives_back(s4);
    println!("s5: {}", s5);
}

/// 示例5: Rust 1.90 改进的部分移动
#[allow(dead_code)]
fn partial_move_example() {
    #[derive(Debug)]
    struct Data {
        s: String,
        num: i32,
    }

    let data = Data {
        s: String::from("hello"),
        num: 42,
    };

    let s = data.s; // 部分移动String
    let num = data.num; // Copy i32
    
    println!("s: {}, num: {}", s, num);
    // println!("{:?}", data); // ❌ data部分失效
}

// ============================================================================
// 第三部分：核心层示例 - 借用
// ============================================================================

/// 示例6: 不可变借用
#[allow(dead_code)]
fn immutable_borrowing_example() {
    let s = String::from("hello world");
    
    // 多个不可变借用可以共存
    let r1 = &s;
    let r2 = &s;
    let r3 = &s;
    
    println!("r1: {}, r2: {}, r3: {}", r1, r2, r3);
    
    // 原始所有者仍有效
    println!("s: {}", s);
    
    // 函数借用
    fn calculate_length(s: &String) -> usize {
        s.len()
    }
    
    let len = calculate_length(&s);
    println!("长度: {}, 字符串: {}", len, s);
}

/// 示例7: 可变借用
#[allow(dead_code)]
fn mutable_borrowing_example() {
    let mut s = String::from("hello");
    
    // 可变借用
    {
        let r1 = &mut s;
        r1.push_str(" world");
        println!("r1: {}", r1);
    } // r1离开作用域
    
    // 现在可以创建新的可变借用
    let r2 = &mut s;
    r2.push_str("!");
    println!("r2: {}", r2);
    
    println!("最终: {}", s);
}

/// 示例8: Rust 1.90 NLL (Non-Lexical Lifetimes) 优化
#[allow(dead_code)]
fn nll_optimization_example() {
    let mut s = String::from("hello");
    
    // 在旧版本中，这可能会报错
    let r1 = &s;
    println!("r1: {}", r1);
    // r1的作用域在这里就结束了（NLL优化）
    
    // 现在可以创建可变借用
    let r2 = &mut s;
    r2.push_str(" world");
    println!("r2: {}", r2);
}

/// 示例9: 借用规则完整演示
#[allow(dead_code)]
fn borrowing_rules_complete_example() {
    let mut s = String::from("hello");
    
    // 规则1: 多个不可变借用
    {
        let r1 = &s;
        let r2 = &s;
        println!("多个不可变借用: {}, {}", r1, r2);
    }
    
    // 规则2: 单个可变借用
    {
        let r1 = &mut s;
        r1.push_str(" world");
        println!("单个可变借用: {}", r1);
    }
    
    // 规则3: 不可变和可变互斥
    let r1 = &s;
    println!("不可变: {}", r1);
    // r1最后使用
    
    let r2 = &mut s;
    r2.push_str("!");
    println!("可变: {}", r2);
}

/// 示例10: 分割借用
#[allow(dead_code)]
fn split_borrowing_example() {
    let mut arr = [1, 2, 3, 4, 5];
    
    // 分割为两个可变借用
    let (left, right) = arr.split_at_mut(2);
    
    left[0] = 10;
    right[0] = 30;
    
    println!("修改后: {:?}", arr);
}

// ============================================================================
// 第四部分：核心层示例 - 生命周期
// ============================================================================

/// 示例11: 基础生命周期
#[allow(dead_code)]
fn basic_lifetime_example() {
    fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
        if x.len() > y.len() {
            x
        } else {
            y
        }
    }
    
    let s1 = String::from("hello");
    let s2 = String::from("world!");
    
    let result = longest(&s1, &s2);
    println!("最长: {}", result);
}

/// 示例12: 结构体生命周期
#[allow(dead_code)]
fn struct_lifetime_example() {
    struct Book<'a> {
        title: &'a str,
        author: &'a str,
    }
    
    impl<'a> Book<'a> {
        fn new(title: &'a str, author: &'a str) -> Self {
            Book { title, author }
        }
        
        fn get_title(&self) -> &str {
            self.title
        }
    }
    
    let title = String::from("Rust编程");
    let author = String::from("张汉东");
    
    let book = Book::new(&title, &author);
    println!("书名: {}, 作者: {}", book.get_title(), book.author);
}

/// 示例13: 生命周期省略规则
#[allow(dead_code)]
fn lifetime_elision_example() {
    // 规则1: 每个引用参数都有独立的生命周期
    fn first_word(s: &str) -> &str {
        s.split_whitespace().next().unwrap_or("")
    }
    
    let text = String::from("hello world");
    let word = first_word(&text);
    println!("第一个单词: {}", word);
    
    // 规则2: 方法中self的生命周期赋予输出
    struct Data {
        value: String,
    }
    
    impl Data {
        fn get_value(&self) -> &str {
            &self.value
        }
    }
    
    let data = Data {
        value: String::from("data"),
    };
    println!("值: {}", data.get_value());
}

// ============================================================================
// 第五部分：应用层示例 - 智能指针
// ============================================================================

/// 示例14: Box<T> 堆分配
#[allow(dead_code)]
fn box_example() {
    // 基础Box
    let b = Box::new(5);
    println!("Box值: {}", b);
    
    // 递归类型
    #[derive(Debug)]
    enum List {
        Cons(i32, Box<List>),
        Nil,
    }
    
    let list = List::Cons(1,
        Box::new(List::Cons(2,
            Box::new(List::Cons(3,
                Box::new(List::Nil))))));
    
    println!("链表: {:?}", list);
}

/// 示例15: Rc<T> 引用计数
#[allow(dead_code)]
fn rc_example() {
    let data = Rc::new(String::from("shared data"));
    println!("初始计数: {}", Rc::strong_count(&data));
    
    let _data2 = Rc::clone(&data);
    println!("克隆后计数: {}", Rc::strong_count(&data));
    
    {
        let _data3 = Rc::clone(&data);
        println!("作用域内计数: {}", Rc::strong_count(&data));
    }
    
    println!("作用域外计数: {}", Rc::strong_count(&data));
}

/// 示例16: RefCell<T> 内部可变性
#[allow(dead_code)]
fn refcell_example() {
    let data = RefCell::new(vec![1, 2, 3]);
    
    // 不可变借用
    {
        let borrowed = data.borrow();
        println!("借用: {:?}", *borrowed);
    }
    
    // 可变借用
    {
        let mut borrowed_mut = data.borrow_mut();
        borrowed_mut.push(4);
        println!("可变借用: {:?}", *borrowed_mut);
    }
    
    println!("最终: {:?}", data.borrow());
}

/// 示例17: Rc<RefCell<T>> 组合
#[allow(dead_code)]
fn rc_refcell_example() {
    #[derive(Debug)]
    struct SharedState {
        value: Rc<RefCell<i32>>,
    }
    
    impl SharedState {
        fn new(initial: i32) -> Self {
            SharedState {
                value: Rc::new(RefCell::new(initial)),
            }
        }
        
        fn increment(&self) {
            *self.value.borrow_mut() += 1;
        }
        
        fn get_value(&self) -> i32 {
            *self.value.borrow()
        }
    }
    
    let state1 = SharedState::new(0);
    let state2 = SharedState {
        value: Rc::clone(&state1.value),
    };
    
    state1.increment();
    state2.increment();
    state1.increment();
    
    println!("state1: {}", state1.get_value());
    println!("state2: {}", state2.get_value());
}

// ============================================================================
// 第六部分：高级层示例 - 并发
// ============================================================================

/// 示例18: Arc<T> 多线程共享
#[allow(dead_code)]
fn arc_threading_example() {
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    let mut handles = vec![];
    
    for i in 0..3 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let sum: i32 = data_clone.iter().sum();
            println!("线程 {} 计算: {}", i, sum);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("原始数据: {:?}", data);
}

/// 示例19: Arc<Mutex<T>> 共享可变状态
#[allow(dead_code)]
fn arc_mutex_example() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for i in 0..10 {
        let counter_clone = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter_clone.lock().unwrap();
            *num += 1;
            println!("线程 {} 增加计数", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("最终计数: {}", *counter.lock().unwrap());
}

/// 示例20: RwLock 读写锁
#[allow(dead_code)]
fn rwlock_example() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    // 多个读线程
    for i in 0..3 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let read_guard = data_clone.read().unwrap();
            println!("读线程 {}: {:?}", i, *read_guard);
            thread::sleep(Duration::from_millis(10));
        });
        handles.push(handle);
    }
    
    // 一个写线程
    let data_clone = Arc::clone(&data);
    let handle = thread::spawn(move || {
        thread::sleep(Duration::from_millis(15));
        let mut write_guard = data_clone.write().unwrap();
        write_guard.push(4);
        println!("写线程: 添加元素");
    });
    handles.push(handle);
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("最终: {:?}", *data.read().unwrap());
}

/// 示例21: 消息传递
#[allow(dead_code)]
fn message_passing_example() {
    use std::sync::mpsc;
    
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        for i in 1..=5 {
            tx.send(format!("消息 {}", i)).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    for received in rx {
        println!("收到: {}", received);
    }
}

// ============================================================================
// 第七部分：综合项目示例
// ============================================================================

/// 示例22: 线程安全的缓存
#[allow(dead_code)]
fn thread_safe_cache_example() {
    use std::collections::HashMap;
    use std::hash::Hash;
    
    struct Cache<K, V> {
        map: Arc<RwLock<HashMap<K, V>>>,
    }
    
    impl<K, V> Cache<K, V>
    where
        K: Eq + Hash + Clone,
        V: Clone,
    {
        fn new() -> Self {
            Cache {
                map: Arc::new(RwLock::new(HashMap::new())),
            }
        }
        
        fn get(&self, key: &K) -> Option<V> {
            self.map.read().unwrap().get(key).cloned()
        }
        
        fn insert(&self, key: K, value: V) {
            self.map.write().unwrap().insert(key, value);
        }
        
        fn size(&self) -> usize {
            self.map.read().unwrap().len()
        }
    }
    
    let cache: Cache<String, i32> = Cache::new();
    
    cache.insert(String::from("a"), 1);
    cache.insert(String::from("b"), 2);
    cache.insert(String::from("c"), 3);
    
    println!("缓存大小: {}", cache.size());
    
    if let Some(value) = cache.get(&String::from("a")) {
        println!("获取 'a': {}", value);
    }
}

/// 示例23: 实用工具 - 数据共享方式对比
#[allow(dead_code)]
fn data_sharing_comparison_example() {
    let data = vec![1, 2, 3, 4, 5];
    
    // 方式1: 借用
    fn use_by_ref(d: &Vec<i32>) {
        println!("借用: {:?}", d);
    }
    use_by_ref(&data);
    
    // 方式2: 克隆
    fn use_by_clone(d: Vec<i32>) {
        println!("克隆: {:?}", d);
    }
    use_by_clone(data.clone());
    
    // 方式3: Rc
    let rc_data = Rc::new(data.clone());
    let rc_data2 = Rc::clone(&rc_data);
    println!("Rc1: {:?}", rc_data);
    println!("Rc2: {:?}", rc_data2);
    
    // 方式4: Arc
    let arc_data = Arc::new(data.clone());
    let arc_data2 = Arc::clone(&arc_data);
    println!("Arc1: {:?}", arc_data);
    println!("Arc2: {:?}", arc_data2);
    
    println!("原始数据: {:?}", data);
}

// ============================================================================
// 主函数和测试
// ============================================================================

fn main() {
    println!("=== Rust 1.90 丰富实战示例集 ===\n");
    println!("运行 cargo test --example rust_190_rich_practical_examples 查看所有测试\n");
    
    // 可以在这里调用任何示例函数
    memory_layout_example();
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_memory_layout() {
        memory_layout_example();
    }
    
    #[test]
    fn test_copy_vs_move() {
        copy_vs_move_example();
    }
    
    #[test]
    fn test_ownership_rules() {
        ownership_rules_example();
    }
    
    #[test]
    fn test_ownership_transfer() {
        ownership_transfer_scenarios();
    }
    
    #[test]
    fn test_partial_move() {
        partial_move_example();
    }
    
    #[test]
    fn test_immutable_borrowing() {
        immutable_borrowing_example();
    }
    
    #[test]
    fn test_mutable_borrowing() {
        mutable_borrowing_example();
    }
    
    #[test]
    fn test_nll_optimization() {
        nll_optimization_example();
    }
    
    #[test]
    fn test_borrowing_rules_complete() {
        borrowing_rules_complete_example();
    }
    
    #[test]
    fn test_split_borrowing() {
        split_borrowing_example();
    }
    
    #[test]
    fn test_basic_lifetime() {
        basic_lifetime_example();
    }
    
    #[test]
    fn test_struct_lifetime() {
        struct_lifetime_example();
    }
    
    #[test]
    fn test_lifetime_elision() {
        lifetime_elision_example();
    }
    
    #[test]
    fn test_box() {
        box_example();
    }
    
    #[test]
    fn test_rc() {
        rc_example();
    }
    
    #[test]
    fn test_refcell() {
        refcell_example();
    }
    
    #[test]
    fn test_rc_refcell() {
        rc_refcell_example();
    }
    
    #[test]
    fn test_arc_threading() {
        arc_threading_example();
    }
    
    #[test]
    fn test_arc_mutex() {
        arc_mutex_example();
    }
    
    #[test]
    fn test_rwlock() {
        rwlock_example();
    }
    
    #[test]
    fn test_message_passing() {
        message_passing_example();
    }
    
    #[test]
    fn test_thread_safe_cache() {
        thread_safe_cache_example();
    }
    
    #[test]
    fn test_data_sharing_comparison() {
        data_sharing_comparison_example();
    }
}

