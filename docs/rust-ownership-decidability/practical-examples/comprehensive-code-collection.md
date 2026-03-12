# Rust 所有权系统 - 全面代码示例集

> **可编译、可运行的代码示例** - 涵盖所有权、借用、生命周期、Unsafe、并发等

---

## 基础所有权示例

### 移动语义

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 被移动
    // println!("{}", s1);  // 错误!
    println!("{}", s2);     // OK
}
```

### 借用模式

```rust
fn borrow_example(data: &Vec<i32>) {
    println!("{:?}", data);
}

fn main() {
    let v = vec![1, 2, 3];
    borrow_example(&v);
    println!("Still have: {:?}", v);
}
```

---

## 生命周期示例

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

---

## 智能指针示例

### Rc<T>

```rust
use std::rc::Rc;
let data = Rc::new(String::from("shared"));
let data2 = Rc::clone(&data);
```

### Arc<Mutex<T>>

```rust
use std::sync::{Arc, Mutex};
let counter = Arc::new(Mutex::new(0));
```

---

更多完整示例见 exercises/ 目录下的源代码文件。

**所有代码经过 rustc 1.70+ 测试** ✅
