/*
在 Rust 中，BTreeSet 是一个基于 B 树的数据结构，提供了有序的唯一元素集合。
它的主要特点是能够在对数时间内进行插入、删除和查找操作。
BTreeSet 是 Rust 标准库中 std::collections 模块的一部分。
定义
    BTreeSet<T> 的定义如下：
      T 是集合中元素的类型，必须实现 Ord trait，以便能够进行排序。
*/

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};
use std::thread;

#[allow(unused)]
pub fn btree_set_demo01() {
    println!("btree_set_demo01");
    // 创建一个新的 BTreeSet
    let mut set = BTreeSet::new();

    // 插入元素
    set.insert(3);
    set.insert(1);
    set.insert(2);
    set.insert(4);
    set.insert(2); // 重复的元素不会被插入

    // 打印所有元素
    println!("BTreeSet 中的元素:");
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
    println!("删除元素 3 后的 BTreeSet:");
    for value in &set {
        println!("{}", value);
    }
}

#[allow(unused)]
pub fn btree_set_demo02() {
    println!("btree_set_demo02");
    let mut set1: BTreeSet<i32> = BTreeSet::new();
    set1.insert(1);
    set1.insert(2);
    set1.insert(3);

    let mut set2: BTreeSet<i32> = BTreeSet::new();
    set2.insert(2);
    set2.insert(3);
    set2.insert(4);

    // 并集
    let union: BTreeSet<_> = set1.union(&set2).cloned().collect();
    println!("并集: {:?}", union);

    // 交集
    let intersection: BTreeSet<_> = set1.intersection(&set2).cloned().collect();
    println!("交集: {:?}", intersection);

    // 差集
    let difference: BTreeSet<_> = set1.difference(&set2).cloned().collect();
    println!("差集: {:?}", difference);
}

#[allow(unused)]
pub fn btree_set_demo03() {
    println!("btree_set_demo03");
    let set = Arc::new(Mutex::new(BTreeSet::new()));

    let mut handles = vec![];

    for i in 0..5 {
        let set_clone = Arc::clone(&set);
        let handle = thread::spawn(move || {
            let mut set = set_clone.lock().unwrap();
            set.insert(i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 打印最终的 BTreeSet
    let set = set.lock().unwrap();
    println!("最终的 BTreeSet:");
    for value in set.iter() {
        println!("{}", value);
    }
}

#[allow(unused)]
pub fn btree_set_demo04() {
    println!("btree_set_demo04");
    #[derive(Debug, Eq, PartialEq)]
    struct Person {
        name: String,
        age: u32,
    }

    impl Ord for Person {
        fn cmp(&self, other: &Self) -> Ordering {
            self.age
                .cmp(&other.age)
                .then_with(|| self.name.cmp(&other.name))
        }
    }

    impl PartialOrd for Person {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    let mut people = BTreeSet::new();
    people.insert(Person {
        name: "Alice".to_string(),
        age: 30,
    });
    people.insert(Person {
        name: "Bob".to_string(),
        age: 25,
    });
    people.insert(Person {
        name: "Charlie".to_string(),
        age: 30,
    });

    // 打印所有人
    println!("BTreeSet 中的人:");
    for person in &people {
        println!("{:?}", person);
    }
}

#[allow(unused)]
pub fn btree_set_demo05() {
    println!("btree_set_demo05");
    let data = vec![5, 3, 1, 2, 4, 3, 2, 1];
    let unique_sorted: BTreeSet<_> = data.into_iter().collect();

    // 打印去重后的有序集合
    println!("去重后的有序集合: {:?}", unique_sorted);
}

#[allow(unused)]
pub fn btree_set_demo06() {
    println!("btree_set_demo06");
    struct Graph {
        edges: BTreeMap<String, BTreeSet<String>>,
    }

    impl Graph {
        fn new() -> Self {
            Graph {
                edges: BTreeMap::new(),
            }
        }

        fn add_edge(&mut self, from: String, to: String) {
            self.edges
                .entry(from)
                .or_insert_with(BTreeSet::new)
                .insert(to);
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
pub fn btree_set_demo07() {
    println!("btree_set_demo07");
    #[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
    struct Event {
        time: u32,
        description: String,
    }

    let mut events = BTreeSet::new();

    events.insert(Event {
        time: 10,
        description: "Event 1".to_string(),
    });
    events.insert(Event {
        time: 5,
        description: "Event 2".to_string(),
    });
    events.insert(Event {
        time: 15,
        description: "Event 3".to_string(),
    });

    // 打印按时间排序的事件
    println!("按时间排序的事件:");
    for event in &events {
        println!("{:?}", event);
    }
}
