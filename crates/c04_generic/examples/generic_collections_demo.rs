//! 泛型集合操作示例
//!
//! 本示例展示如何使用泛型实现各种集合操作，包括：
//! - 泛型栈和队列
//! - 泛型映射和集合
//! - 泛型迭代器适配器
//! - 泛型算法实现

use std::collections::{HashMap, HashSet};

/// 泛型栈实现
pub struct Stack<T> {
    items: Vec<T>,
}

impl<T> Stack<T> {
    /// 创建新的空栈
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    /// 推入元素
    pub fn push(&mut self, item: T) {
        self.items.push(item);
    }

    /// 弹出元素
    pub fn pop(&mut self) -> Option<T> {
        self.items.pop()
    }

    /// 查看栈顶元素
    pub fn peek(&self) -> Option<&T> {
        self.items.last()
    }

    /// 检查栈是否为空
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// 获取栈的大小
    pub fn len(&self) -> usize {
        self.items.len()
    }
}

impl<T> Default for Stack<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 泛型队列实现
pub struct Queue<T> {
    items: Vec<T>,
}

impl<T> Queue<T> {
    /// 创建新的空队列
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    /// 入队
    pub fn enqueue(&mut self, item: T) {
        self.items.push(item);
    }

    /// 出队
    pub fn dequeue(&mut self) -> Option<T> {
        if self.items.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }
    }

    /// 查看队首元素
    pub fn front(&self) -> Option<&T> {
        self.items.first()
    }

    /// 检查队列是否为空
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// 获取队列的大小
    pub fn len(&self) -> usize {
        self.items.len()
    }
}

impl<T> Default for Queue<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 泛型映射操作示例
pub fn demonstrate_generic_map() {
    println!("=== 泛型映射操作示例 ===");

    // 创建泛型 HashMap
    let mut map: HashMap<String, i32> = HashMap::new();
    map.insert("Alice".to_string(), 25);
    map.insert("Bob".to_string(), 30);
    map.insert("Charlie".to_string(), 35);

    println!("映射内容:");
    for (name, age) in &map {
        println!("  {}: {}", name, age);
    }

    // 泛型查找操作
    if let Some(age) = map.get("Alice") {
        println!("\nAlice 的年龄: {}", age);
    }

    // 泛型更新操作
    map.entry("Alice".to_string())
        .and_modify(|e| *e += 1)
        .or_insert(20);
    println!("更新后 Alice 的年龄: {}", map["Alice"]);
}

/// 泛型集合操作示例
pub fn demonstrate_generic_set() {
    println!("\n=== 泛型集合操作示例 ===");

    let mut set1: HashSet<i32> = HashSet::new();
    set1.insert(1);
    set1.insert(2);
    set1.insert(3);

    let mut set2: HashSet<i32> = HashSet::new();
    set2.insert(3);
    set2.insert(4);
    set2.insert(5);

    println!("集合1: {:?}", set1);
    println!("集合2: {:?}", set2);

    // 并集
    let union: HashSet<_> = set1.union(&set2).copied().collect();
    println!("并集: {:?}", union);

    // 交集
    let intersection: HashSet<_> = set1.intersection(&set2).copied().collect();
    println!("交集: {:?}", intersection);

    // 差集
    let difference: HashSet<_> = set1.difference(&set2).copied().collect();
    println!("差集: {:?}", difference);
}

/// 泛型算法示例
pub fn demonstrate_generic_algorithms<T: PartialOrd + Clone>(items: &mut [T]) -> Vec<T> {
    // 简单的冒泡排序（泛型版本）
    let n = items.len();
    for i in 0..n {
        for j in 0..n - i - 1 {
            if items[j] > items[j + 1] {
                items.swap(j, j + 1);
            }
        }
    }
    items.to_vec()
}

/// 泛型查找函数
pub fn find_item<T: PartialEq>(items: &[T], target: &T) -> Option<usize> {
    items.iter().position(|x| x == target)
}

fn main() {
    println!("🚀 泛型集合操作演示程序\n");

    // 1. 栈操作示例
    println!("=== 1. 泛型栈操作 ===");
    let mut stack: Stack<i32> = Stack::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);
    println!("栈大小: {}", stack.len());
    println!("栈顶元素: {:?}", stack.peek());
    while let Some(item) = stack.pop() {
        println!("弹出: {}", item);
    }

    // 2. 队列操作示例
    println!("\n=== 2. 泛型队列操作 ===");
    let mut queue: Queue<&str> = Queue::new();
    queue.enqueue("first");
    queue.enqueue("second");
    queue.enqueue("third");
    println!("队列大小: {}", queue.len());
    while let Some(item) = queue.dequeue() {
        println!("出队: {}", item);
    }

    // 3. 映射操作示例
    demonstrate_generic_map();

    // 4. 集合操作示例
    demonstrate_generic_set();

    // 5. 泛型算法示例
    println!("\n=== 5. 泛型算法示例 ===");
    let mut numbers = vec![64, 34, 25, 12, 22, 11, 90];
    println!("排序前: {:?}", numbers);
    let sorted = demonstrate_generic_algorithms(&mut numbers);
    println!("排序后: {:?}", sorted);

    // 6. 泛型查找示例
    println!("\n=== 6. 泛型查找示例 ===");
    let items = vec!["apple", "banana", "cherry", "date"];
    if let Some(index) = find_item(&items, &"banana") {
        println!("找到 'banana' 在索引: {}", index);
    }

    println!("\n✅ 所有演示完成！");
}
