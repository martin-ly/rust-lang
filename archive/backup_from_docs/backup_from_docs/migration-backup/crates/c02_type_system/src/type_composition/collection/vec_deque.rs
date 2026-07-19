/*
VecDeque<T> 是 Rust 标准库中提供的一种双端队列（double-ended queue）实现，
允许在两端高效地插入和删除元素。
与 Vec 不同，VecDeque 在两端的操作性能更好，适合需要频繁在队列两端进行插入和删除的场景。
定义
    VecDeque<T> 是一个泛型类型，其中 T 是队列中元素的类型。
    它提供了 O(1) 的时间复杂度来在队列的前端和后端进行插入和删除操作。
主要特性
    双端操作: 可以在队列的两端进行高效的插入和删除。
    动态大小: VecDeque 可以根据需要动态调整大小。
    随机访问: 支持通过索引访问元素，但效率不如 Vec。
*/

use std::collections::VecDeque;

#[allow(unused)]
pub fn vec_deque_demo01() {
    println!("vec_deque_demo01");
    // 创建一个新的 VecDeque
    let mut deque = VecDeque::new();

    // 在队列的尾部插入元素
    deque.push_back(1);
    deque.push_back(2);
    deque.push_back(3);

    // 在队列的头部插入元素
    deque.push_front(0);

    // 打印队列中的所有元素
    println!("VecDeque 中的元素:");
    for value in &deque {
        println!("{}", value);
    }

    // 删除队列的头部元素
    deque.pop_front();
    println!("删除头部元素后的 VecDeque:");
    for value in &deque {
        println!("{}", value);
    }

    // 删除队列的尾部元素
    deque.pop_back();
    println!("删除尾部元素后的 VecDeque:");
    for value in &deque {
        println!("{}", value);
    }
}

#[allow(unused)]
pub fn vec_deque_demo02() {
    println!("vec_deque_demo02");
    let mut deque = VecDeque::new();
    deque.push_back(1);
    deque.push_back(2);
    deque.push_back(3);

    // 在第二个位置插入元素
    let index = 1; // 插入位置
    let value_to_insert = 4;

    // 创建一个新的 VecDeque 来存储结果
    let mut new_deque = VecDeque::new();

    for (i, &value) in deque.iter().enumerate() {
        if i == index {
            new_deque.push_back(value_to_insert); // 插入新元素
        }
        new_deque.push_back(value); // 添加原有元素
    }

    // 如果插入位置在最后，直接添加
    if index >= deque.len() {
        new_deque.push_back(value_to_insert);
    }

    // 更新原 deque
    deque = new_deque;

    // 打印更新后的 VecDeque
    println!("更新后的 VecDeque:");
    for value in &deque {
        println!("{}", value);
    }

    // 删除第二个位置的元素
    let index_to_remove = 1; // 删除位置
    let mut new_deque = VecDeque::new();

    for (i, &value) in deque.iter().enumerate() {
        if i != index_to_remove {
            new_deque.push_back(value); // 只添加不等于要删除的元素
        }
    }

    // 更新原 deque
    deque = new_deque;

    // 打印删除后的 VecDeque
    println!("删除后的 VecDeque:");
    for value in &deque {
        println!("{}", value);
    }
}

#[allow(unused)]
pub fn vec_deque_demo03() {
    println!("vec_deque_demo03");
    struct Cache {
        capacity: usize,
        data: VecDeque<i32>,
    }

    impl Cache {
        fn new(capacity: usize) -> Self {
            Cache {
                capacity,
                data: VecDeque::new(),
            }
        }

        fn insert(&mut self, value: i32) {
            if self.data.len() == self.capacity {
                self.data.pop_front(); // 移除最旧的元素
            }
            self.data.push_back(value); // 添加新元素
        }

        fn display(&self) {
            println!("缓存中的元素:");
            for value in &self.data {
                println!("{}", value);
            }
        }
    }

    let mut cache = Cache::new(3);
    cache.insert(1);
    cache.insert(2);
    cache.insert(3);
    cache.display();

    cache.insert(4); // 这将移除 1
    cache.display();
}

#[allow(unused)]
pub fn vec_deque_demo04() {
    println!("vec_deque_demo04");
    let mut deque = VecDeque::new();
    deque.push_back(1);
    deque.push_back(2);
    deque.push_back(3);

    // 使用迭代器遍历元素
    println!("使用迭代器遍历 VecDeque:");
    for value in deque.iter() {
        println!("{}", value);
    }

    // 使用迭代器进行过滤
    let filtered: Vec<_> = deque.iter().filter(|&&x| x > 1).collect();
    println!("过滤后的元素（大于 1）:");
    for value in filtered {
        println!("{}", value);
    }
}
