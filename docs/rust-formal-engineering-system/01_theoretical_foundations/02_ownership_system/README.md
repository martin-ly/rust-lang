# 所有权系统理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至： [ownership_model.md](../../../research_notes/formal_methods/ownership_model.md)

[返回理论基础](../README.md) | [返回主索引](../../00_master_index.md)

---

## 所有权的核心规则

```rust
// 规则 1：每个值都有一个所有者
fn rule1() {
    let s = String::from("hello");  // s 是所有者
    // String 数据存储在堆上，s 负责管理它
}
// s 离开作用域，内存自动释放

// 规则 2：同一时间只能有一个所有者
fn rule2() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权从 s1 转移到 s2
    // println!("{}", s1);  // 错误：s1 不再拥有该值
    println!("{}", s2);   // OK
}

// 规则 3：当所有者离开作用域，值被丢弃
fn rule3() {
    {
        let s = String::from("hello");
        // s 在这里有效
    }  // s 离开作用域，drop(s) 被自动调用
    // s 不再有效
}
```

## 所有权与函数

```rust
fn take_ownership(s: String) {
    // s 获得所有权
    println!("{}", s);
}  // s 在这里被丢弃

fn give_ownership() -> String {
    String::from("hello")  // 所有权返回给调用者
}

fn borrow(s: &String) {
    // s 借用，不获得所有权
    println!("{}", s);
}  // s 只是借用，不会被丢弃

fn demo() {
    let s1 = String::from("hello");
    take_ownership(s1);
    // s1 在这里不再有效

    let s2 = give_ownership();
    // s2 获得所有权

    borrow(&s2);
    // s2 仍然有效，因为只是借用
}
```

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 所有权模型 | 所有权系统的完整形式化模型 | [../../../research_notes/formal_methods/ownership_model.md](../../../research_notes/formal_methods/ownership_model.md) |
| 借用检查器 | 借用检查的形式化证明 | [../../../research_notes/formal_methods/borrow_checker_proof.md](../../../research_notes/formal_methods/borrow_checker_proof.md) |


## 更多代码示例

### Copy 与 Clone 语义

```rust
// Copy 类型：隐式按位复制，原值仍然有效
fn copy_semantics() {
    let x: i32 = 42;
    let y = x;  // x 被复制，仍然可用
    println!("x = {}, y = {}", x, y);  // 两者都有效

    // 其他 Copy 类型
    let a: bool = true;
    let b = a;  // 复制

    let arr: [i32; 3] = [1, 2, 3];
    let arr2 = arr;  // 数组是 Copy

    let tup: (i32, f64) = (1, 2.0);
    let tup2 = tup;  // 元组是 Copy（如果所有元素都是 Copy）

    println!("{:?} {:?} {:?} {:?}", a, arr, arr2, tup);
}

// Clone 类型：显式深拷贝
fn clone_semantics() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 显式克隆
    println!("s1 = {}, s2 = {}", s1, s2);  // 两者都有效

    let v1 = vec![1, 2, 3];
    let v2 = v1.clone();
    println!("v1 = {:?}, v2 = {:?}", v1, v2);
}

// 自定义 Copy/Clone
#[derive(Clone, Copy, Debug)]
struct Point {
    x: f64,
    y: f64,
}

fn custom_copy() {
    let p1 = Point { x: 1.0, y: 2.0 };
    let p2 = p1;  // 复制，不是移动
    println!("p1 = {:?}, p2 = {:?}", p1, p2);  // 两者都有效
}
```

### Drop 与资源管理

```rust
// Drop trait：资源清理的自定义行为
struct DatabaseConnection {
    id: u32,
}

impl Drop for DatabaseConnection {
    fn drop(&mut self) {
        println!("DatabaseConnection {} is being closed", self.id);
        // 执行清理操作
    }
}

fn drop_demo() {
    {
        let conn = DatabaseConnection { id: 1 };
        // 使用 conn
        println!("Using connection {}", conn.id);
    }  // conn 在这里自动 drop

    // 提前手动 drop
    let conn2 = DatabaseConnection { id: 2 };
    drop(conn2);  // 显式调用 drop
    // conn2 在这里不再有效
}

// RAII 模式：资源获取即初始化
fn raii_pattern() {
    // 文件句柄
    {
        let file = std::fs::File::open("README.md").unwrap();
        // 使用 file
        let _metadata = file.metadata().unwrap();
    }  // file 在这里自动关闭

    // 锁守卫
    use std::sync::Mutex;
    let data = Mutex::new(0);
    {
        let mut guard = data.lock().unwrap();
        *guard += 1;
    }  // 锁在这里自动释放
}
```

### 所有权与闭包

```rust
// 闭包捕获所有权的方式
fn closure_ownership() {
    let s = String::from("hello");

    // 不可变借用捕获
    let closure_ref = || println!("{}", s);
    closure_ref();
    println!("s still available: {}", s);  // s 仍然可用

    // 可变借用捕获
    let mut s2 = String::from("world");
    let mut closure_mut = || s2.push_str("!");
    closure_mut();
    println!("s2 modified: {}", s2);  // s2 仍然可用

    // 移动捕获（move 关键字）
    let s3 = String::from("moved");
    let closure_move = move || println!("{}", s3);
    // s3 在这里不再可用，所有权转移给闭包
    closure_move();
}

// Fn、FnMut、FnOnce trait
fn closure_traits() {
    // Fn：不可变借用捕获
    let s = String::from("hello");
    let print_s = || println!("{}", s);
    call_fn(print_s);
    call_fn(print_s);  // 可以多次调用

    // FnMut：可变借用捕获
    let mut count = 0;
    let mut increment = || { count += 1; count };
    call_fn_mut(&mut increment);
    call_fn_mut(&mut increment);
    println!("final count: {}", count);

    // FnOnce：移动捕获，只能调用一次
    let s = String::from("consumed");
    let consume = || s;  // 返回 s，移动所有权
    call_fn_once(consume);
    // consume();  // 错误：不能再次调用
}

fn call_fn<F: Fn()>(f: F) { f(); }
fn call_fn_mut<F: FnMut()>(f: &mut F) { f(); }
fn call_fn_once<F: FnOnce()>(f: F) { f(); }
```

---

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 所有权模型 | 所有权系统的完整形式化模型 | [../../../research_notes/formal_methods/ownership_model.md](../../../research_notes/formal_methods/ownership_model.md) |
| 借用检查器 | 借用检查的形式化证明 | [../../../research_notes/formal_methods/borrow_checker_proof.md](../../../research_notes/formal_methods/borrow_checker_proof.md) |
| 证明索引 | 所有权相关证明 | [../../../research_notes/PROOF_INDEX.md](../../../research_notes/PROOF_INDEX.md) |
| 工具指南 | 形式化验证工具 | [../../../research_notes/TOOLS_GUIDE.md](../../../research_notes/TOOLS_GUIDE.md) |
