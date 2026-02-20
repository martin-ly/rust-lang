# 内存安全语义

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [borrow_checker_proof.md](../../../research_notes/formal_methods/borrow_checker_proof.md)

[返回理论基础](../README.md) | [返回主索引](../../00_master_index.md)

---

## 内存安全的核心保证

Rust 通过所有权和借用系统在编译时保证内存安全：

```rust
// 保证 1：无空指针解引用
fn no_null_deref() {
    let opt: Option<&i32> = None;
    // opt.unwrap();  // panic，但不会是未定义行为

    // 安全解包
    if let Some(val) = opt {
        println!("{}", val);
    }
}

// 保证 2：无悬垂指针
fn no_dangling_ptr() {
    let ptr: *const i32;
    {
        let x = 5;
        // ptr = &x;  // 错误：x 的生命周期不够长
    }  // x 在这里被释放
    // 使用 ptr 将是未定义行为
}

// 保证 3：无数据竞争
fn no_data_race() {
    use std::sync::Arc;
    use std::sync::Mutex;
    use std::thread;

    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += 1;  // 互斥访问保证无数据竞争
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}

// 保证 4：无 use-after-free
fn no_use_after_free() {
    let s = String::from("hello");
    let r = &s;
    drop(s);  // 错误：不能在有引用时丢弃所有者
    // println!("{}", r);
}
```

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 借用检查器证明 | 借用检查器的形式化正确性证明 | [../../../research_notes/formal_methods/borrow_checker_proof.md](../../../research_notes/formal_methods/borrow_checker_proof.md) |
| 所有权模型 | 所有权系统的形式化模型 | [../../../research_notes/formal_methods/ownership_model.md](../../../research_notes/formal_methods/ownership_model.md) |
| 安全/非安全分析 | unsafe Rust 的边界分析 | [../../../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md](../../../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) |
