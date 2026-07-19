/*
在 Rust 中，LinkedList 是一个双向链表的数据结构，提供了在列表的两端高效的插入和删除操作。
与数组或向量不同，LinkedList 允许在任意位置进行高效的插入和删除，但在随机访问元素时效率较低。
定义
    LinkedList<T> 的定义如下：
    T 是链表中元素的类型，可以是任何类型。

*/
use std::collections::{HashMap, LinkedList};
use std::time::Instant;

#[allow(unused)]
pub fn linked_list_demo01() {
    println!("linked_list_demo01");
    // 创建一个新的 LinkedList
    let mut list = LinkedList::new();

    // 在链表的尾部插入元素
    list.push_back(1);
    list.push_back(2);
    list.push_back(3);

    // 在链表的头部插入元素
    list.push_front(0);

    // 打印链表中的所有元素
    println!("链表中的元素:");
    for value in &list {
        println!("{}", value);
    }

    // 删除链表的头部元素
    list.pop_front();
    println!("删除头部元素后的链表:");
    for value in &list {
        println!("{}", value);
    }

    // 删除链表的尾部元素
    list.pop_back();
    println!("删除尾部元素后的链表:");
    for value in &list {
        println!("{}", value);
    }
}

#[allow(unused)]
pub fn linked_list_demo02() {
    println!("linked_list_demo02");
    let mut list = LinkedList::new();
    list.push_back(1);
    list.push_back(2);
    list.push_back(3);

    // 在链表的第二个位置插入元素
    let mut new_list = LinkedList::new();
    new_list.push_back(1); // 添加第一个元素
    new_list.push_back(4); // 在第二个位置插入 4
    new_list.push_back(2); // 添加原链表的第二个元素
    new_list.push_back(3); // 添加原链表的第三个元素

    // 更新原链表为新链表
    list = new_list;

    // 打印链表中的所有元素
    println!("插入元素后的链表:");
    for value in &list {
        println!("{}", value);
    }

    // 删除第二个位置的元素
    let mut new_list = LinkedList::new();
    let mut iter = list.iter();
    let first = iter.next(); // 获取第一个元素
    let second = iter.next(); // 获取第二个元素

    // 添加第一个元素到新链表
    if let Some(&first_value) = first {
        new_list.push_back(first_value);
    }

    // 只添加第二个元素之后的元素
    for value in iter {
        new_list.push_back(*value);
    }

    // 更新原链表为新链表，跳过第二个元素
    list = new_list;

    // 打印删除后的链表
    println!("删除元素后的链表:");
    for value in &list {
        println!("{}", value);
    }
}

#[allow(unused)]
pub fn linked_list_demo03() {
    println!("linked_list_demo03");
    struct Queue<T> {
        list: LinkedList<T>,
    }

    impl<T> Queue<T> {
        fn new() -> Self {
            Queue {
                list: LinkedList::new(),
            }
        }

        fn enqueue(&mut self, item: T) {
            self.list.push_back(item);
        }

        fn dequeue(&mut self) -> Option<T> {
            self.list.pop_front()
        }

        fn is_empty(&self) -> bool {
            self.list.is_empty()
        }
    }

    let mut queue = Queue::new();
    queue.enqueue(1);
    queue.enqueue(2);
    queue.enqueue(3);

    println!("队列中的元素:");
    while !queue.is_empty() {
        if let Some(value) = queue.dequeue() {
            println!("{}", value);
        }
    }
}

#[allow(unused)]
pub fn linked_list_demo04() {
    println!("linked_list_demo04");
    let mut vec = Vec::new();
    let mut linked_list = LinkedList::new();

    let data: Vec<i32> = (1..=1_000_000).collect();

    // 测试 Vec 的插入性能
    let start = Instant::now();
    for &value in &data {
        vec.push(value);
    }
    let duration = start.elapsed();
    println!("Vec 插入时间: {:?}", duration);

    // 测试 LinkedList 的插入性能
    let start = Instant::now();
    for &value in &data {
        linked_list.push_back(value);
    }
    let duration = start.elapsed();
    println!("LinkedList 插入时间: {:?}", duration);

    // 测试 Vec 的删除性能
    let start = Instant::now();
    vec.pop();
    let duration = start.elapsed();
    println!("Vec 删除时间: {:?}", duration);

    // 测试 LinkedList 的删除性能
    let start = Instant::now();
    linked_list.pop_back();
    let duration = start.elapsed();
    println!("LinkedList 删除时间: {:?}", duration);
}

#[allow(unused)]
pub fn linked_list_demo05() {
    println!("linked_list_demo04");
    struct Graph {
        edges: HashMap<String, LinkedList<String>>,
    }

    impl Graph {
        fn new() -> Self {
            Graph {
                edges: HashMap::new(),
            }
        }

        fn add_edge(&mut self, from: String, to: String) {
            self.edges
                .entry(from)
                .or_insert_with(LinkedList::new)
                .push_back(to);
        }

        fn display(&self) {
            for (node, neighbors) in &self.edges {
                println!("{} -> {:?}", node, neighbors);
            }
        }
    }

    let mut graph = Graph::new();
    graph.add_edge("A".to_string(), "B".to_string());
    graph.add_edge("A".to_string(), "C".to_string());
    graph.add_edge("B".to_string(), "D".to_string());

    // 打印图的结构
    graph.display();
}

#[allow(unused)]
pub fn linked_list_demo06() {
    println!("linked_list_demo06");
    struct Queue<T> {
        list: LinkedList<T>,
    }

    impl<T> Queue<T> {
        fn new() -> Self {
            Queue {
                list: LinkedList::new(),
            }
        }

        fn enqueue(&mut self, item: T) {
            self.list.push_back(item);
        }

        fn dequeue(&mut self) -> Option<T> {
            self.list.pop_front()
        }

        fn is_empty(&self) -> bool {
            self.list.is_empty()
        }
    }

    let mut queue = Queue::new();
    queue.enqueue(1);
    queue.enqueue(2);
    queue.enqueue(3);

    println!("队列中的元素:");
    while !queue.is_empty() {
        if let Some(value) = queue.dequeue() {
            println!("{}", value);
        }
    }
}
