# 所有权与借用理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至： [formal_methods/](../../../research_notes/formal_methods/)

- [所有权模型](../../../research_notes/formal_methods/ownership_model.md)
- [借用检查器证明](../../../research_notes/formal_methods/borrow_checker_proof.md)
- [生命周期形式化](../../../research_notes/formal_methods/lifetime_formalization.md)

[返回主索引](../../00_master_index.md)

---

## 形式化链接

| 文档 | 路径 | 内容 |
| :--- | :--- | :--- |
| **所有权模型** | [../../../research_notes/formal_methods/ownership_model.md](../../../research_notes/formal_methods/ownership_model.md) | 所有权系统的形式化定义 |
| **借用检查器证明** | [../../../research_notes/formal_methods/borrow_checker_proof.md](../../../research_notes/formal_methods/borrow_checker_proof.md) | 借用规则的形式化证明 |
| **生命周期形式化** | [../../../research_notes/formal_methods/lifetime_formalization.md](../../../research_notes/formal_methods/lifetime_formalization.md) | 生命周期与区域理论 |
| **证明索引** | [../../../research_notes/PROOF_INDEX.md](../../../research_notes/PROOF_INDEX.md) | 所有权/借用相关证明 |
| **工具指南** | [../../../research_notes/TOOLS_GUIDE.md](../../../research_notes/TOOLS_GUIDE.md) | 借用检查验证工具 |

---

## 所有权系统的形式化理解

### 资源管理代数

Rust 的所有权系统可以形式化为线性逻辑的资源管理：

```rust
// 线性类型：每个资源必须且只能使用一次
// Γ ⊢ e : τ （在上下文 Γ 下，表达式 e 具有类型 τ）

// 所有权转移（Move）
fn linear_logic() {
    let resource = Box::new(vec![1, 2, 3]);
    // resource : Vec<i32> （拥有资源）

    let moved = resource;
    // resource : ⊥ （资源已耗尽，不可再用）
    // moved : Vec<i32> （资源转移）

    drop(moved);
    // moved : ⊥ （资源被消耗）
}

// 借用作为资源的部分使用
fn partial_use() {
    let mut resource = vec![1, 2, 3];

    // 借用：暂时共享资源而不转移所有权
    let borrow = &resource;  // &Vec<i32>
    // 资源仍由 resource 拥有，但暂时可读

    println!("{:?}", borrow);
    // 借用结束，资源恢复完全所有权

    resource.push(4);  // 现在可以修改
}
```

### 借用检查器的形式化规则

```rust
// 借用检查器确保以下不变式：
// 1. 唯一可变引用：∀l∈Location, ∀t∈Time: count_mut_refs(l, t) ≤ 1
// 2. 读写互斥：∀l∈Location, ∀t∈Time: has_mut_ref(l, t) → count_imm_refs(l, t) = 0
// 3. 生命周期包含：∀r∈Reference: lifetime(r) ⊆ lifetime(pointee(r))

fn borrow_rules() {
    let mut x = 5;

    // 规则 1：唯一可变引用
    let r1 = &mut x;
    // let r2 = &mut x;  // 错误：只能有一个可变引用
    *r1 += 1;
    drop(r1);  // r1 结束生命周期

    // 规则 2：读写互斥
    let r3 = &x;  // 不可变借用
    let r4 = &x;  // 多个不可变借用允许
    // let r5 = &mut x;  // 错误：不可变借用期间不能有可变借用
    println!("{} {}", r3, r4);
    drop(r3);
    drop(r4);  // 所有不可变借用结束

    // 现在可以可变借用
    let r6 = &mut x;
    *r6 += 1;

    // 规则 3：生命周期包含
    let r7: &i32;
    {
        let y = 10;
        // r7 = &y;  // 错误：y 的生命周期不足以支持 r7
    }  // y 在这里被丢弃
    // println!("{}", r7);  // r7 将引用已释放的内存
}
```

### 非词法生命周期（NLL）

```rust
// Rust 2018+ 的非词法生命周期允许更早释放借用
fn non_lexical_lifetime() {
    let mut data = vec![1, 2, 3];

    // 借用只持续到它最后一次使用
    let x = &data[0];  // 借用开始
    println!("{}", x);  // 借用在 println! 后结束

    // 现在可以修改 data，因为 x 的借用已经结束
    data.push(4);  // 在 Rust 2015 中这是错误，2018+ 允许
}

// NLL 在复杂控制流中的效果
fn nll_control_flow() {
    let mut data = vec![1, 2, 3];

    if true {
        let x = &data[0];
        println!("{}", x);
    }  // x 在这里结束，即使没有显式 drop

    data.push(4);  // ✅ 允许
}
```

### 内部可变性模式

```rust
use std::cell::RefCell;
use std::sync::{Arc, Mutex};

// Cell<T>：无内部引用的内部可变性
use std::cell::Cell;

fn cell_demo() {
    let cell = Cell::new(5);

    // get/set 不需要 &mut
    let val = cell.get();  // 复制值
    cell.set(val + 1);     // 修改内部值

    // 适用于 Copy 类型
}

// RefCell<T>：运行期借用检查
fn refcell_demo() {
    let data = RefCell::new(vec![1, 2, 3]);

    {
        let mut borrow = data.borrow_mut();  // 运行时检查
        borrow.push(4);
    }  // 可变借用结束

    let borrow = data.borrow();
    println!("{:?}", *borrow);

    // 运行时 panic：违反借用规则
    // let _b1 = data.borrow_mut();
    // let _b2 = data.borrow();  // panic!
}

// Arc<Mutex<T>>：跨线程共享可变状态
fn arc_mutex_demo() {
    let data = Arc::new(Mutex::new(0));

    let handles: Vec<_> = (0..10)
        .map(|_| {
            let data = Arc::clone(&data);
            std::thread::spawn(move || {
                let mut guard = data.lock().unwrap();
                *guard += 1;
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Result: {}", *data.lock().unwrap());  // 10
}
```

### 所有权与并发的形式化

```rust
// Send 和 Sync 的形式化定义
// Send: 可以安全地在线程间转移所有权
// Sync: 可以安全地在线程间共享引用（&T 是 Send）

// Send 示例
fn send_demo() {
    let data = vec![1, 2, 3];

    std::thread::spawn(move || {
        // data 的所有权转移到新线程
        println!("{:?}", data);
    }).join().unwrap();

    // data 在这里不可用
}

// Sync 示例
fn sync_demo() {
    let data = Arc::new(vec![1, 2, 3]);
    let data2 = Arc::clone(&data);

    std::thread::spawn(move || {
        // 共享引用 &Vec<i32> 被发送到新线程
        println!("{:?}", data2);
    }).join().unwrap();

    println!("{:?}", data);
}

// 非 Send/Sync 类型
use std::rc::Rc;

fn non_send_sync() {
    let data = Rc::new(vec![1, 2, 3]);

    // 错误：Rc 不是 Send
    // std::thread::spawn(move || {
    //     println!("{:?}", data);
    // });

    // 必须使用 Arc 代替
}
```
