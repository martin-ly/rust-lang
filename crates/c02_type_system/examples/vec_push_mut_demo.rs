//! Rust 1.95.0 `Vec::push_mut` / `insert_mut` 专题示例
//!
//! Rust 1.95.0 为 `Vec` 新增了 `push_mut` 和 `insert_mut` 方法，
//! 允许在插入元素的同时获取其可变引用，避免二次查找。
//!
//! 权威来源: https://releases.rs/docs/1.95.0/
//!
//! 运行方式:
//! ```bash
//! cargo run --example vec_push_mut_demo -p c02_type_system
//! ```

// ==================== 示例 1: Vec::push_mut 基础 ====================

/// `push_mut` 在尾部插入元素并返回 `&mut T`
fn demo_push_mut_basic() {
    println!("--- Vec::push_mut 基础 ---");

    let mut vec = vec![1, 2, 3];

    // push_mut: 插入 42 并立即获取可变引用
    let elem: &mut i32 = vec.push_mut(42);
    println!("  新元素地址: {:p}, 值: {}", elem as *mut i32, *elem);

    // 直接通过返回的引用修改
    *elem += 8;
    println!("  修改后: {:?}", vec);

    assert_eq!(vec, [1, 2, 3, 50]);
}

// ==================== 示例 2: Vec::push_mut 与复杂类型 ====================

/// `push_mut` 用于需要立即初始化的结构体
fn demo_push_mut_struct() {
    println!("\n--- Vec::push_mut 与结构体 ---");

    #[derive(Debug, PartialEq)]
    struct Config {
        name: String,
        enabled: bool,
    }

    let mut configs: Vec<Config> = Vec::new();

    // 插入并立即完成初始化
    let cfg = configs.push_mut(Config {
        name: String::new(),
        enabled: false,
    });
    cfg.name.push_str("database");
    cfg.enabled = true;

    println!("  configs: {:?}", configs);
    assert_eq!(configs[0].name, "database");
    assert!(configs[0].enabled);
}

// ==================== 示例 3: Vec::insert_mut 基础 ====================

/// `insert_mut` 在指定位置插入并返回 `&mut T`
fn demo_insert_mut_basic() {
    println!("\n--- Vec::insert_mut 基础 ---");

    let mut vec = vec!['a', 'c', 'd'];

    // 在索引 1 处插入 'b' 并获取可变引用
    let elem: &mut char = vec.insert_mut(1, 'x');

    // 修正为正确值
    *elem = 'b';
    println!("  修正后: {:?}", vec);

    assert_eq!(vec, ['a', 'b', 'c', 'd']);
}

// ==================== 示例 4: 对比旧写法 vs 新写法 ====================

/// 展示 `push_mut` 如何消除冗余索引
fn demo_comparison_old_vs_new() {
    println!("\n--- 旧写法 vs 新写法对比 ---");

    // 旧写法: push 后再通过索引/last_mut 获取引用
    let mut vec_old = vec![10, 20];
    vec_old.push(30);
    if let Some(last) = vec_old.last_mut() {
        *last *= 2; // 需要额外的 Option 解包
    }
    println!("  旧写法结果: {:?}", vec_old);

    // 新写法: push_mut 直接返回 &mut T，无 Option 开销
    let mut vec_new = vec![10, 20];
    let last = vec_new.push_mut(30);
    *last *= 2; // 直接操作，无 Option
    println!("  新写法结果: {:?}", vec_new);

    assert_eq!(vec_old, vec_new);
}

// ==================== 示例 5: 批量构建并初始化 ====================

/// 使用 `push_mut` 批量构建预分配向量
fn demo_batch_build() {
    println!("\n--- 批量构建与初始化 ---");

    let mut buffers: Vec<Vec<u8>> = Vec::with_capacity(3);

    for size in [1024, 2048, 4096] {
        let buf = buffers.push_mut(Vec::with_capacity(size));
        buf.extend_from_slice(&[0u8; 4]); // 写入头部标记
        buf.push(0xFF); // 尾部标记
    }

    println!("  创建了 {} 个缓冲区", buffers.len());
    for (i, buf) in buffers.iter().enumerate() {
        println!(
            "    缓冲区 {}: 容量={}, 长度={}, 内容={:?}",
            i,
            buf.capacity(),
            buf.len(),
            buf
        );
    }

    assert_eq!(buffers.len(), 3);
}

// ==================== 示例 6: insert_mut 在有序列表中的应用 ====================

/// 在有序 Vec 中插入并调整邻居
fn demo_insert_mut_sorted() {
    println!("\n--- insert_mut 在有序列表中的应用 ---");

    let mut scores = vec![85, 90, 95];

    // 在索引 1 插入新分数
    let new_score = scores.insert_mut(1, 0);
    *new_score = 88;

    // 验证顺序
    println!("  分数列表: {:?}", scores);
    assert!(scores.windows(2).all(|w| w[0] <= w[1]));
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 `Vec::push_mut` / `Vec::insert_mut` 专题演示\n");

    demo_push_mut_basic();
    demo_push_mut_struct();
    demo_insert_mut_basic();
    demo_comparison_old_vs_new();
    demo_batch_build();
    demo_insert_mut_sorted();

    println!("\n✅ `Vec::push_mut` / `insert_mut` 演示完成！");
    println!("   关键要点:");
    println!("   - push_mut(value) -> &mut T: 尾部插入并直接获取可变引用");
    println!("   - insert_mut(index, value) -> &mut T: 指定位置插入并获取可变引用");
    println!("   - 避免 push + last_mut() 的 Option 解包开销和冗余查找");
    println!("   - 适用于需要立即初始化或修改新插入元素的场景");
}
