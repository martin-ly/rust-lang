/* 

在 Rust 中，HashSet 是一个基于哈希表的数据结构，提供了无序的唯一元素集合。
它的主要特点是能够在平均常数时间内进行插入、删除和查找操作。
HashSet 是 Rust 标准库中 std::collections 模块的一部分。

HashSet<T> 的定义如下：
    T 是集合中元素的类型，必须实现 Hash 和 Eq trait，以便能够进行哈希和相等比较。

*/

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

#[allow(unused)]
pub fn hash_set_demo01() {
    println!("hash_set_demo01");
    // 创建一个新的 HashSet
    let mut set = HashSet::new();

    // 插入元素
    set.insert(1);
    set.insert(2);
    set.insert(3);
    set.insert(2); // 重复的元素不会被插入

    // 打印所有元素
    println!("HashSet 中的元素:");
    for value in &set {
        println!("{}", value);
    }

    // 查找一个元素
    if set.contains(&2) {
        println!("集合中包含元素 2");
    } else {
        println!("集合中不包含元素 2");
    }

    // 删除一个元素
    set.remove(&3);
    println!("删除元素 3 后的 HashSet:");
    for value in &set {
        println!("{}", value);
    }

}

#[allow(unused)]
pub fn hash_set_demo02() {
    println!("hash_set_demo02");
    let mut set1: HashSet<i32> = HashSet::new();
    set1.insert(1);
    set1.insert(2);
    set1.insert(3);

    let mut set2: HashSet<i32> = HashSet::new();
    set2.insert(2);
    set2.insert(3);
    set2.insert(4);

    // 并集
    let union: HashSet<_> = set1.union(&set2).cloned().collect();
    println!("并集: {:?}", union);

    // 交集
    let intersection: HashSet<_> = set1.intersection(&set2).cloned().collect();
    println!("交集: {:?}", intersection);

    // 差集
    let difference: HashSet<_> = set1.difference(&set2).cloned().collect();
    println!("差集: {:?}", difference);
}

#[allow(unused)]
pub fn hash_set_demo03() {
    println!("hash_set_demo03");
    #[derive(Debug, Eq)]
    struct Person {
        name: String,
        age: u32,
    }
    
    impl Hash for Person {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.name.hash(state);
            self.age.hash(state);
        }
    }
    
    impl PartialEq for Person {
        fn eq(&self, other: &Self) -> bool {
            self.name == other.name && self.age == other.age
        }
    }
    
    let mut people = HashSet::new();
    people.insert(Person { name: "Alice".to_string(), age: 30 });
    people.insert(Person { name: "Bob".to_string(), age: 25 });
    people.insert(Person { name: "Alice".to_string(), age: 30 }); // 重复的元素不会被插入

    // 打印所有人
    println!("HashSet 中的人:");
    for person in &people {
        println!("{:?}", person);
    }

}

#[allow(unused)]
pub fn hash_set_demo04() {
    println!("hash_set_demo04");
    let data = vec![5, 3, 1, 2, 4, 3, 2, 1];
    let unique_set: HashSet<_> = data.into_iter().collect();

    // 打印去重后的集合
    println!("去重后的 HashSet: {:?}", unique_set);
}

#[allow(unused)]
pub fn hash_set_demo05() {
    println!("hash_set_demo05");
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
    
    let mut graph = Graph::new();
    graph.add_edge("A".to_string(), "B".to_string());
    graph.add_edge("A".to_string(), "C".to_string());
    graph.add_edge("B".to_string(), "D".to_string());

    // 打印图的结构
    graph.display();

}

#[allow(unused)]
pub fn hash_set_demo06() {
    println!("hash_set_demo06");
    let data = vec![5, 3, 1, 2, 4, 3, 2, 1];
    let mut counts: HashMap<i32, usize> = HashMap::new();
    let unique_elements: HashSet<i32> = data.iter().cloned().collect();

    for &value in &data {
        *counts.entry(value).or_insert(0) += 1;
    }

    // 打印唯一元素和计数
    println!("唯一元素: {:?}", unique_elements);
    println!("元素计数: {:?}", counts);
}
