//! Treap（树堆）与跳表（Skip List）高级数据结构示例。
//!
//! 运行: `cargo run -p c08_algorithms --example treap_skip_list_demo`

use c08_algorithms::data_structure::{SkipList, Treap};

fn main() {
    demo_treap();
    demo_skip_list();
}

fn demo_treap() {
    println!("=== Treap（树堆）===");
    let mut treap = Treap::new();
    let keys = [50, 30, 70, 20, 40, 60, 80];
    for (i, key) in keys.iter().enumerate() {
        // 使用递增优先级便于演示；实际应使用随机值。
        treap.insert(*key, (i + 1) as u64);
    }
    println!("中序遍历: {:?}", treap.sorted());
    println!("包含 40? {}", treap.contains(40));
    println!("查找 40: {:?}", treap.find(40));
    println!("查找 99: {:?}", treap.find(99));
    println!("第 3 小: {:?}", treap.kth(3));
    println!("40 的排名: {}", treap.rank(40));
    treap.delete(40);
    println!("删除 40 后: {:?}", treap.sorted());
    println!();
}

fn demo_skip_list() {
    println!("=== Skip List（跳表）===");
    let mut list = SkipList::new();
    for v in [3, 1, 4, 1, 5, 9, 2, 6] {
        list.insert(v);
    }
    println!("升序列表: {:?}", list.to_vec());
    println!("包含 5? {}", list.contains(&5));
    println!("包含 7? {}", list.contains(&7));
    println!("范围 [2, 5]: {:?}", list.range(Some(&2), Some(&5)));
    println!("范围 (-∞, 2]: {:?}", list.range(None, Some(&2)));
    println!("范围 [6, +∞): {:?}", list.range(Some(&6), None::<&i32>));
    list.delete(&5);
    println!("删除 5 后: {:?}", list.to_vec());
    println!();
}
