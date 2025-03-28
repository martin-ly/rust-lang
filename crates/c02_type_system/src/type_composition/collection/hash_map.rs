/*
在 Rust 中，HashMap 是一个基于哈希表的数据结构，提供了键值对的无序集合。
它的主要特点是能够在平均常数时间内进行插入、删除和查找操作。
HashMap 是 Rust 标准库中 std::collections 模块的一部分。
定义
    HashMap<K, V> 的定义如下：
        K 是键的类型，必须实现 Hash 和 Eq trait，以便能够进行哈希和相等比较。
        V 是值的类型，可以是任何类型。
*/

use std::collections::{HashMap, BTreeMap, HashSet};
use std::hash::Hash;
use std::time::Instant;


#[allow(unused)]
pub fn hash_map_demo01() {
    println!("hash_map_demo01");
    // 创建一个新的 HashMap
    let mut map = HashMap::new();

    // 插入键值对
    map.insert("apple", 3);
    map.insert("banana", 2);
    map.insert("orange", 5);

    // 打印所有键值对
    println!("HashMap 中的键值对:");
    for (key, value) in &map {
        println!("{}: {}", key, value);
    }

    // 查找一个键的值
    if let Some(&value) = map.get("banana") {
        println!("香蕉的数量: {}", value);
    } else {
        println!("香蕉不在 HashMap 中");
    }

    // 删除一个键值对
    map.remove("apple");
    println!("删除苹果后的 HashMap:");
    for (key, value) in &map {
        println!("{}: {}", key, value);
    }
}


#[allow(unused)]
pub fn hash_map_demo02() {
    println!("hash_map_demo02");
    let mut map = HashMap::new();
    let text = "hello world hello rust rust rust";

    // 统计单词出现次数
    for word in text.split_whitespace() {
        *map.entry(word).or_insert(0) += 1;
    }

    // 打印单词计数
    println!("单词计数:");
    for (word, count) in &map {
        println!("{}: {}", word, count);
    }
}


#[allow(unused)]
pub fn hash_map_demo03() {
    println!("hash_map_demo03");
    #[derive(Debug, Eq, PartialEq, Hash)]
    struct Person {
        name: String,
        age: u32,
    }

    let mut people = HashMap::new();
    people.insert(Person { name: "Alice".to_string(), age: 30 }, "Engineer");
    people.insert(Person { name: "Bob".to_string(), age: 25 }, "Designer");

    // 打印所有人及其职业
    println!("HashMap 中的人及其职业:");
    for (person, job) in &people {
        println!("{:?}: {}", person, job);
    }
    
}


#[allow(unused)]
pub fn hash_map_demo04() {
    println!("hash_map_demo04");
    let data = vec![5, 3, 1, 2, 4, 3, 2, 1];
    let mut counts: HashMap<i32, usize> = HashMap::new();

    for &value in &data {
        *counts.entry(value).or_insert(0) += 1;
    }

    // 打印元素计数
    println!("元素计数:");
    for (value, count) in &counts {
        println!("{}: {}", value, count);
    }
}

#[allow(unused)]
pub fn hash_map_demo05() {
    println!("hash_map_demo05");
    let mut hash_map = HashMap::new();
    let mut btree_map = BTreeMap::new();
    
    let data: Vec<i32> = (1..=1_000_000).collect();

    // 测试 HashMap 的插入性能
    let start = Instant::now();
    for &value in &data {
        hash_map.insert(value, value);
    }
    let duration = start.elapsed();
    println!("HashMap 插入时间: {:?}", duration);

    // 测试 BTreeMap 的插入性能
    let start = Instant::now();
    for &value in &data {
        btree_map.insert(value, value);
    }
    let duration = start.elapsed();
    println!("BTreeMap 插入时间: {:?}", duration);

    // 测试 HashMap 的查找性能
    let start = Instant::now();
    for &value in &data {
        hash_map.get(&value);
    }
    let duration = start.elapsed();
    println!("HashMap 查找时间: {:?}", duration);

    // 测试 BTreeMap 的查找性能
    let start = Instant::now();
    for &value in &data {
        btree_map.get(&value);
    }
    let duration = start.elapsed();
    println!("BTreeMap 查找时间: {:?}", duration); 
}


#[allow(unused)]
pub fn hash_map_demo06() {
    struct Graph {
        edges: HashMap<String, HashSet<String>>,
    }
    
    impl Graph {
        fn new() -> Self {
            Graph {
                edges: HashMap::new(),
            }
        }
    
        fn add_edge(&mut self, from: String, to: String) {
            self.edges.entry(from).or_insert_with(HashSet::new).insert(to);
        }
    
        fn display(&self) {
            for (node, neighbors) in &self.edges {
                println!("{} -> {:?}", node, neighbors);
            }
        }
    }
    
    println!("hash_map_demo06");
    let mut graph = Graph::new();
    graph.add_edge("A".to_string(), "B".to_string());
    graph.add_edge("A".to_string(), "C".to_string());
    graph.add_edge("B".to_string(), "D".to_string());

    // 打印图的结构
    graph.display();
    
}


