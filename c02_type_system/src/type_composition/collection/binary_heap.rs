/*
BinaryHeap<T> 是 Rust 标准库中提供的一种优先级队列实现，基于二叉堆（最大堆）数据结构。
它允许高效地插入元素和删除最大元素。
BinaryHeap 是无序的，但可以快速访问最大元素。
定义
    BinaryHeap<T> 是一个泛型类型，其中 T 是堆中元素的类型，
    必须实现 Ord trait，以便能够进行比较。
    默认情况下，BinaryHeap 是一个最大堆，意味着最大的元素总是位于堆的顶部。

主要特性
    插入和删除: 插入元素的时间复杂度为 O(log n)，删除最大元素的时间复杂度也是 O(log n)。
    动态大小: BinaryHeap 可以根据需要动态调整大小。
    优先级队列: 适用于需要按优先级处理元素的场景。
*/

use std::collections::BinaryHeap;
use std::cmp::Ordering;

#[allow(unused)]
pub fn binary_heap_demo01() {
    println!("binary_heap_demo01");
    // 创建一个新的 BinaryHeap
    let mut heap = BinaryHeap::new();

    // 插入元素
    heap.push(3);
    heap.push(1);
    heap.push(4);
    heap.push(2);

    // 打印 BinaryHeap 中的元素（按优先级顺序）
    println!("BinaryHeap 中的元素（按优先级顺序）:");
    while let Some(value) = heap.pop() {
        println!("{}", value);
    }
}

#[allow(unused)]
pub fn binary_heap_demo02() {
    println!("binary_heap_demo02");

    #[derive(Debug, Eq, PartialEq)]
    struct Person {
        name: String,
        age: u32,
    }

    impl Ord for Person {
        fn cmp(&self, other: &Self) -> Ordering {
            // 按年龄降序排序
            other.age.cmp(&self.age)
        }
    }

    impl PartialOrd for Person {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    let mut heap = BinaryHeap::new();

    heap.push(Person { name: "Alice".to_string(), age: 30 });
    heap.push(Person { name: "Bob".to_string(), age: 25 });
    heap.push(Person { name: "Charlie".to_string(), age: 35 });

    println!("BinaryHeap 中的人员（按年龄优先级顺序）:");
    while let Some(person) = heap.pop() {
        println!("{:?}", person);
    }

}

#[allow(unused)]
pub fn binary_heap_demo03() {
    println!("binary_heap_demo03");
    #[derive(Debug, Eq, PartialEq)]
    struct Task {
        priority: u32,
        description: String,
    }
    
    impl Ord for Task {
        fn cmp(&self, other: &Self) -> Ordering {
            // 按优先级降序排序
            other.priority.cmp(&self.priority)
        }
    }
    
    impl PartialOrd for Task {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    
    
    let mut task_queue = BinaryHeap::new();

    task_queue.push(Task { priority: 2, description: "Do laundry".to_string() });
    task_queue.push(Task { priority: 1, description: "Write report".to_string() });
    task_queue.push(Task { priority: 3, description: "Prepare presentation".to_string() });

    println!("任务调度队列（按优先级顺序）:");
    while let Some(task) = task_queue.pop() {
        println!("优先级 {}: {}", task.priority, task.description);
    }
    
}

#[allow(unused)]
pub fn binary_heap_demo04() {
    println!("binary_heap_demo04");
    let mut heap = BinaryHeap::new();
    heap.push(5);
    heap.push(1);
    heap.push(3);

    // 查看最大元素
    if let Some(&max) = heap.peek() {
        println!("当前最大元素: {}", max);
    }

    // 删除最大元素
    heap.pop();

    // 再次查看最大元素
    if let Some(&max) = heap.peek() {
        println!("删除后新的最大元素: {}", max);
    }
}
