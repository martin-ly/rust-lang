//! 高级数据结构使用示例。
//!
//! 运行: `cargo run -p c08_algorithms --example advanced_data_structures_demo`

use c08_algorithms::data_structure::{PersistentSegmentTree, RedBlackTree, SkipList, Treap};

fn main() {
    demo_treap();
    demo_skip_list();
    demo_red_black_tree();
    demo_persistent_segment_tree();
}

fn demo_treap() {
    println!("=== Treap（树堆） ===");
    let mut treap = Treap::new();
    let keys = [50, 30, 70, 20, 40, 60, 80];
    for (i, key) in keys.iter().enumerate() {
        // 使用递增优先级便于演示；实际应使用随机值。
        treap.insert(*key, (i + 1) as u64);
    }
    println!("中序遍历: {:?}", treap.sorted());
    println!("包含 40? {}", treap.contains(40));
    println!("第 3 小: {:?}", treap.kth(3));
    println!("40 的排名: {}", treap.rank(40));
    treap.delete(40);
    println!("删除 40 后: {:?}", treap.sorted());
    println!();
}

fn demo_skip_list() {
    println!("=== Skip List（跳表） ===");
    let mut list = SkipList::new();
    for v in [3, 1, 4, 1, 5, 9, 2, 6] {
        list.insert(v);
    }
    println!("升序列表: {:?}", list.to_vec());
    println!("包含 5? {}", list.contains(&5));
    println!("包含 7? {}", list.contains(&7));
    list.delete(&5);
    println!("删除 5 后: {:?}", list.to_vec());
    println!();
}

fn demo_red_black_tree() {
    println!("=== Red-Black Tree（红黑树） ===");
    let mut tree = RedBlackTree::new();
    for v in [10, 5, 15, 3, 7, 12, 20] {
        tree.insert(v);
    }
    println!("中序遍历: {:?}", tree.sorted());
    println!("包含 12? {}", tree.contains(12));
    tree.delete(10);
    println!("删除 10 后: {:?}", tree.sorted());
    println!();
}

fn demo_persistent_segment_tree() {
    println!("=== Persistent Segment Tree（可持久化线段树） ===");
    let arr = vec![1, 2, 3, 4, 5];
    let (mut pst, root0) = PersistentSegmentTree::from_slice(&arr);
    println!("版本 0 区间和 [0,4]: {}", pst.query(root0, 0, 4));

    let root1 = pst.update(root0, 2, 10);
    println!("版本 1 区间和 [0,4]: {}", pst.query(root1, 0, 4));
    println!("版本 0 仍不变: {}", pst.query(root0, 0, 4));

    let root2 = pst.update(root1, 4, 100);
    println!("版本 2 区间和 [0,4]: {}", pst.query(root2, 0, 4));
    println!("版本 1 仍不变: {}", pst.query(root1, 0, 4));
    println!();
}
