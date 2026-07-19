/*
在 Rust 中，BTreeMap 是一个基于 B 树的数据结构，提供了有序的键值对存储。
它的主要特点是能够在对数时间内进行插入、删除和查找操作。
BTreeMap 是 Rust 标准库中 std::collections 模块的一部分。

定义
    BTreeMap<K, V> 的定义如下：
    1. K 是键的类型，必须实现 Ord trait，以便能够进行排序。
    2. V 是值的类型，可以是任何类型。
*/

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::thread;

#[allow(unused)]
pub fn btree_map_demo01() {
    println!("btree_map_demo01");
    // 创建一个新的 BTreeMap
    let mut map = BTreeMap::new();

    // 插入键值对
    map.insert("apple", 3);
    map.insert("banana", 2);
    map.insert("orange", 5);

    // 打印所有键值对
    for (key, value) in &map {
        println!("{}: {}", key, value);
    }

    // 查找一个键的值
    if let Some(&value) = map.get("banana") {
        println!("香蕉的数量: {}", value);
    }

    // 删除一个键值对
    map.remove("apple");

    // 打印删除后的 BTreeMap
    println!("删除苹果后的 BTreeMap:");
    for (key, value) in &map {
        println!("{}: {}", key, value);
    }
}

#[allow(unused)]
pub fn btree_map_demo02() {
    println!("btree_map_demo02");
    let mut map = BTreeMap::new();
    map.insert("apple", 3);
    map.insert("banana", 2);
    map.insert("orange", 5);
    map.insert("grape", 4);

    // 获取最小和最大键
    if let Some((key, value)) = map.first_key_value() {
        println!("最小键: {}，值: {}", key, value);
    }

    if let Some((key, value)) = map.last_key_value() {
        println!("最大键: {}，值: {}", key, value);
    }

    // 范围查询
    println!("范围查询 (banana 到 grape):");
    for (key, value) in map.range("banana".."grape") {
        println!("{}: {}", key, value);
    }

    // 清空 BTreeMap
    map.clear();
    println!("清空后的 BTreeMap: {:?}", map);
}

#[allow(unused)]
pub fn btree_map_demo03() {
    println!("btree_map_demo03");
    // 自定义排序：按字符串长度排序
    let mut map1 = BTreeMap::new();
    map1.insert("apple", 3);
    map1.insert("banana", 2);

    let mut map2 = BTreeMap::new();
    map2.insert("kiwi", 5);
    map2.insert("grape", 4);

    // 合并 map2 到 map1
    map1.extend(map2);

    // 打印合并后的 BTreeMap
    println!("合并后的 BTreeMap:");
    for (key, value) in &map1 {
        println!("{}: {}", key, value);
    }

    // 使用迭代器进行过滤
    let filtered: Vec<_> = map1
        .iter()
        .filter(|&(_, &v)| v > 3) // 只保留值大于 3 的项
        .collect();

    println!("过滤后的 BTreeMap (值大于 3):");
    for (key, value) in filtered {
        println!("{}: {}", key, value);
    }
}

#[allow(unused)]
pub fn btree_map_demo04() {
    println!("btree_map_demo04");
    let text = "hello world hello rust rust rust";
    let mut word_count: BTreeMap<String, i32> = BTreeMap::new();

    // 统计单词出现次数
    for word in text.split_whitespace() {
        *word_count.entry(word.to_string()).or_insert(0) += 1;
    }

    // 打印单词计数
    println!("单词计数:");
    for (word, count) in &word_count {
        println!("{}: {}", word, count);
    }
}

#[allow(unused)]
pub fn btree_map_demo05() {
    println!("btree_map_demo05");
    // 创建一个嵌套的 BTreeMap
    let mut categories: BTreeMap<String, BTreeMap<String, i32>> = BTreeMap::new();

    // 添加类别和项目
    categories.insert("水果".to_string(), {
        let mut fruits = BTreeMap::new();
        fruits.insert("苹果".to_string(), 3);
        fruits.insert("香蕉".to_string(), 2);
        fruits
    });

    categories.insert("蔬菜".to_string(), {
        let mut vegetables = BTreeMap::new();
        vegetables.insert("胡萝卜".to_string(), 5);
        vegetables.insert("西红柿".to_string(), 4);
        vegetables
    });

    // 打印嵌套的 BTreeMap
    for (category, items) in &categories {
        println!("类别: {}", category);
        for (item, count) in items {
            println!("  {}: {}", item, count);
        }
    }
}

#[allow(unused)]
pub fn btree_map_demo06() {
    println!("btree_map_demo06");
    let mut map = BTreeMap::new();
    map.insert("apple", 3);
    map.insert("banana", 2);
    map.insert("orange", 5);
    map.insert("grape", 4);

    // 按值排序
    let mut sorted_by_value: Vec<_> = map.iter().collect();
    sorted_by_value.sort_by(|a, b| a.1.cmp(b.1));

    // 打印按值排序的结果
    println!("按值排序的 BTreeMap:");
    for (key, value) in sorted_by_value {
        println!("{}: {}", key, value);
    }
}

#[allow(unused)]
pub fn btree_map_demo07() {
    println!("btree_map_demo07");
    // 创建一个图
    struct Graph {
        edges: BTreeMap<String, Vec<String>>,
    }

    impl Graph {
        fn new() -> Self {
            Graph {
                edges: BTreeMap::new(),
            }
        }

        fn add_edge(&mut self, from: String, to: String) {
            self.edges.entry(from).or_insert_with(Vec::new).push(to);
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
pub fn btree_map_demo08() {
    println!("btree_map_demo08");
    let map = Arc::new(Mutex::new(BTreeMap::new()));

    let mut handles = vec![];

    for i in 0..5 {
        let map_clone = Arc::clone(&map);
        let handle = thread::spawn(move || {
            let mut map = map_clone.lock().unwrap();
            map.insert(format!("key{}", i), i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 打印最终的 BTreeMap
    let map = map.lock().unwrap();
    println!("最终的 BTreeMap:");
    for (key, value) in map.iter() {
        println!("{}: {}", key, value);
    }
}
