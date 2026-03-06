# 所有权系统 - 反例与逻辑论证

> **通过错误示例理解所有权边界**

---

## 1. 所有权规则反例

### 1.1 规则2反例: Move后使用

```rust
// 反例: Move后继续使用原变量
fn use_after_move() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权从s1转移到s2

    // 错误! s1已被move，不能再使用
    println!("{}", s1);  // 编译错误: borrow of moved value: `s1`
}

// 逻辑论证:
// 前提: s1拥有String("hello")
// 操作: let s2 = s1; (Move语义)
// 结果: 所有权转移到s2，s1无效
// 后续使用s1: 违反唯一所有者原则
```

#### 形式化证明错误

```text
定义 MOVE-INVALIDATION:
    设 Γ 为类型环境
    设 x: T 且 own(x, v)

    操作: let y = x;
    在Rust语义中，如果T: !Copy:
        - 所有权从x转移到y
        - x从环境中移除

    后续使用x:
        Γ' ⊢ x: T
        但 x ∉ dom(Γ')  (因为已被move)
        ∴ 类型错误

编译错误:
    error[E0382]: borrow of moved value: `s1`
    --> src/main.rs:5:20
     |
     |     let s2 = s1;
     |              --- value moved here
     |     println!("{}", s1);
     |                    ^^ value borrowed here after move
```

#### 修复方案

```rust
// 方案1: 使用Clone
fn use_after_move_fixed_clone() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 显式克隆
    println!("{}", s1);   // OK: s1仍然有效
    println!("{}", s2);   // OK: s2拥有副本
}

// 方案2: 借用而非Move
fn use_after_move_fixed_borrow() {
    let s1 = String::from("hello");
    let s2 = &s1;  // 借用，不转移所有权
    println!("{}", s1);   // OK
    println!("{}", s2);   // OK
}
```

---

### 1.2 规则3反例: 作用域与Drop

```rust
// 反例: 误以为可以手动控制Drop时机
fn wrong_drop_assumption() {
    let s = String::from("data");
    // s在此作用域结束，自动Drop
} // s在这里被drop

// 错误尝试: 提前"释放"
fn wrong_early_release() {
    let s = String::from("data");
    // 没有safe方法可以手动drop s
    // std::mem::drop(s);  // 这是可以的，但会move s
    // s;  // 错误: s已被move
}
```

#### 逻辑论证: RAII的强制性

```text
定义 RAII-ENFORCEMENT:
    设 x: T 其中 T: Drop
    设 scope(x) = [l_x, r_x] (x的生命周期)

    Rust保证:
        ∀x. at r_x, Drop::drop(&mut x) 被自动调用

    这意味着:
        1. 程序员不能忘记drop (编译器强制)
        2. 程序员不能double drop (所有权系统防止)
        3. 程序员不能在drop后使用 (所有权系统防止)

    反例尝试:
        尝试在scope结束前手动管理内存
        → 与所有权系统冲突
        → 需要unsafe
```

---

## 2. 借用规则反例

### 2.1 XOR原则反例: 可变+共享借用共存

```rust
// 反例: 同时存在可变和共享借用
fn mutable_and_shared_borrow() {
    let mut data = vec![1, 2, 3];

    let ref1 = &data;        // 共享借用开始
    let ref2 = &mut data;    // 可变借用开始 ❌

    println!("{}", ref1[0]); // 使用共享借用
    ref2.push(4);            // 使用可变借用
}

// 编译错误:
// error[E0502]: cannot borrow `data` as mutable
// because it is also borrowed as immutable
```

#### 形式化证明错误

```text
定义 BORROW-XOR-VIOLATION:
    设 γ 为借用环境

    操作1: let ref1 = &data;
        γ' = γ ∪ { &data }

    操作2: let ref2 = &mut data;
        检查: ∃r ∈ γ'. r 是 &data
        结果: 冲突! 不能同时拥有 &data 和 &mut data

    借用检查规则:
        ∀t. ∀v. at time t,
            (count(&v) > 0 → count(&mut v) = 0) ∧
            (count(&mut v) > 0 → count(&v) = 0 ∧ count(&mut v) = 1)

    反例违反:
        t1: count(&data) = 1
        t2: count(&data) = 1 ∧ count(&mut data) = 1  // 违反!
```

#### 修复方案

```rust
// 方案1: 缩小借用作用域
fn fixed_borrow_scope() {
    let mut data = vec![1, 2, 3];

    {
        let ref1 = &data;
        println!("{}", ref1[0]);
    } // ref1在这里结束

    let ref2 = &mut data;  // OK: 没有活跃的借用
    ref2.push(4);
}

// 方案2: 复制需要的值
fn fixed_copy_value() {
    let mut data = vec![1, 2, 3];

    let first = data[0];  // 复制值，不是借用
    let ref2 = &mut data; // OK

    println!("{}", first);
    ref2.push(4);
}
```

---

### 2.2 多个可变借用反例

```rust
// 反例: 多个可变借用
fn multiple_mutable_borrows() {
    let mut data = vec![1, 2, 3];

    let ref1 = &mut data;
    let ref2 = &mut data;  // ❌ 编译错误

    ref1.push(4);
    ref2.push(5);
}

// 编译错误:
// error[E0499]: cannot borrow `data` as mutable more than once at a time
```

#### 逻辑论证: 别名与数据竞争

```text
定义 ALIASING-AND-SAFETY:
    假设允许多个 &mut T:
        let ref1 = &mut data;
        let ref2 = &mut data;

    可能的问题:
        1. ref1.push(4) 可能导致reallocation
        2. ref2仍然指向旧缓冲区
        3. ref2.push(5) 写入已释放内存

    这就是C/C++中的use-after-free!

    Rust通过限制:
        任意时刻只有一个 &mut T
    来保证:
        修改者拥有独占访问
        没有其他引用可以观察到中间状态
```

---

## 3. 生命周期反例

### 3.1 生命周期不足反例

```rust
// 反例: 返回悬垂引用
fn dangling_reference() -> &String {
    let s = String::from("hello");
    &s  // ❌ 编译错误
} // s在这里被drop，返回的引用指向已释放内存

// 编译错误:
// error[E0106]: missing lifetime specifier
// error[E0515]: cannot return reference to local variable `s`
```

#### 形式化证明错误

```text
定义 LIFETIME-INSUFFICIENCY:
    设函数 f() -> &T
    设局部变量 s: T

    操作: &s
        lifetime(&s) ⊆ lifetime(s)
        lifetime(s) = 函数作用域

    返回 &s:
        返回类型需要 'static 或更长的生命周期
        但 &s 的生命周期 < 函数作用域

    类型错误:
        expected: &'a T where 'a: 'caller
        actual: &'s T where 's = 函数作用域
        's 不包含 'caller
        ∴ 编译错误
```

#### 修复方案

```rust
// 方案1: 返回所有权
fn return_ownership() -> String {
    let s = String::from("hello");
    s  // OK: 转移所有权
}

// 方案2: 接受引用参数
fn borrow_from_caller(input: &String) -> &str {
    &input[0..2]  // OK: 返回的生命周期与input相同
}

// 方案3: 使用生命周期参数
fn borrow_with_lifetime<'a>(input: &'a String) -> &'a str {
    &input[0..2]
}
```

---

### 3.2 生命周期不匹配反例

```rust
// 反例: 生命周期不匹配
struct Parser {
    text: String,
    current: &str,  // 引用text的内容
}

impl Parser {
    fn new(text: String) -> Parser {
        Parser {
            text,
            current: &text[0..],  // ❌ 编译错误
        }
    }
}

// 编译错误:
// error[E0106]: missing lifetime specifier
```

#### 修复: 自引用结构

```rust
// 方案: 使用索引而非引用
struct Parser {
    text: String,
    pos: usize,  // 使用索引而非引用
}

impl Parser {
    fn new(text: String) -> Self {
        Self { text, pos: 0 }
    }

    fn current(&self) -> &str {
        &self.text[self.pos..]
    }
}

// 或使用Pin (高级)
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    text: String,
    current: *const str,
    _pin: PhantomPinned,
}
```

---

## 4. Send/Sync反例

### 4.1 Rc跨线程反例

```rust
use std::rc::Rc;
use std::thread;

// 反例: 尝试将Rc发送到其他线程
fn rc_across_threads() {
    let data = Rc::new(String::from("hello"));

    let data2 = data.clone();
    thread::spawn(move || {
        println!("{}", data2);  // ❌ 编译错误
    });
}

// 编译错误:
// error[E0277]: `Rc<String>` cannot be sent between threads safely
```

#### 逻辑论证

```text
定义 RC-THREAD-UNSAFETY:
    Rc使用非原子引用计数

    如果允许Rc跨线程:
        Thread A: Rc::clone() → increment ref_count
        Thread B: Rc::clone() → increment ref_count

        非原子的increment:
            A读: count = 1
            B读: count = 1
            A写: count = 2
            B写: count = 2  // 应该是3!

        结果: 内存泄漏或use-after-free

    Rust阻止:
        Rc<T>: !Send + !Sync
        编译时阻止跨线程传递
```

#### 修复方案

```rust
use std::sync::Arc;
use std::thread;

// 使用Arc替代Rc
fn arc_across_threads() {
    let data = Arc::new(String::from("hello"));

    let data2 = data.clone();
    thread::spawn(move || {
        println!("{}", data2);  // OK
    });
}
```

---

## 5. 常见逻辑谬误

### 5.1 "Clone是免费的"

```rust
// 谬误: 频繁Clone没有成本
fn expensive_clones() {
    let data = vec![0; 1_000_000];  // 大向量

    for i in 0..1000 {
        process(data.clone());  // 每次Clone都分配内存并复制!
    }
}

// 正确: 使用引用
fn efficient_borrow() {
    let data = vec![0; 1_000_000];

    for i in 0..1000 {
        process(&data);  // 只是借用，无复制
    }
}
```

### 5.2 "RefCell可以替代所有借用"

```rust
// 谬误: 用RefCell避免所有借用规则
fn overusing_refcell() {
    let data = RefCell::new(vec![1, 2, 3]);

    let borrow1 = data.borrow();
    let borrow2 = data.borrow();
    // 运行时才能发现double borrow
    // 代码可编译，但可能panic
}

// 正确: 尽可能使用编译时检查
fn prefer_compile_time() {
    let data = vec![1, 2, 3];
    let ref1 = &data;
    let ref2 = &data;  // OK: 编译时检查
}
```

---

## 6. 反例总结表

| 反例 | 违反规则 | 错误类型 | 修复方案 |
|:---|:---|:---:|:---|
| use-after-move | 唯一所有者 | 编译错误 | Clone / 借用 |
| mutable + shared | XOR原则 | 编译错误 | 缩小作用域 |
| 多个&mut | 唯一可变 | 编译错误 | 串行化访问 |
| 悬垂引用 | 生命周期 | 编译错误 | 返回所有权 |
| Rc跨线程 | Send/Sync | 编译错误 | 使用Arc |
| RefCell panic | 借用规则 | 运行时panic | 编译时借用 |

---

**维护er**: Rust Counterexamples Team
**更新日期**: 2026-03-06
**对齐版本**: Rust 1.94.0
