# C03 控制流快速参考

> 控制流语句速查手册

---

## 📋 条件表达式

### if / else if / else
```rust
let number = 5;

if number < 5 {
    println!("less than 5");
} else if number == 5 {
    println!("equal to 5");
} else {
    println!("greater than 5");
}
```

### if let
```rust
// 简化模式匹配
if let Some(value) = option {
    println!("Value: {}", value);
}

// 对比 match
match option {
    Some(value) => println!("Value: {}", value),
    _ => (),
}
```

---

## 🔄 循环

### loop (无限循环)
```rust
let mut counter = 0;
let result = loop {
    counter += 1;
    if counter == 10 {
        break counter * 2;  // 返回值
    }
};
```

### while (条件循环)
```rust
let mut number = 3;
while number != 0 {
    println!("{}", number);
    number -= 1;
}
```

### while let
```rust
while let Some(value) = stack.pop() {
    println!("{}", value);
}
```

### for (遍历)
```rust
// 遍历集合
for element in &collection {
    println!("{}", element);
}

// 范围
for i in 0..10 {        // 0 到 9
    println!("{}", i);
}

for i in 0..=10 {       // 0 到 10 (包含)
    println!("{}", i);
}
```

---

## 🎯 模式匹配

### match 表达式
```rust
match value {
    // 精确匹配
    1 => println!("one"),
    
    // 范围匹配
    2..=5 => println!("two to five"),
    
    // 或模式
    6 | 7 | 8 => println!("six to eight"),
    
    // 守卫子句
    n if n % 2 == 0 => println!("even"),
    
    // 绑定
    n @ 10..=20 => println!("ten to twenty: {}", n),
    
    // 通配符
    _ => println!("other"),
}
```

### 解构
```rust
// 元组
let (x, y, z) = (1, 2, 3);

// 结构体
struct Point { x: i32, y: i32 }
let p = Point { x: 0, y: 7 };
let Point { x, y } = p;

// 枚举
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
}

match msg {
    Message::Quit => println!("Quit"),
    Message::Move { x, y } => println!("Move to ({}, {})", x, y),
    Message::Write(text) => println!("Text: {}", text),
}
```

---

## 🔀 控制流关键字

| 关键字 | 作用 |
|--------|------|
| `break` | 退出循环 |
| `continue` | 跳过本次循环 |
| `return` | 返回函数 |
| `break 'label` | 跳出指定标签的循环 |

### 标签循环
```rust
'outer: loop {
    println!("outer");
    
    'inner: loop {
        println!("inner");
        break 'outer;  // 直接跳出外层循环
    }
}
```

---

## 📊 对比表

| 场景 | 推荐语句 | 说明 |
|------|----------|------|
| 无限循环 | `loop` | 配合 break 退出 |
| 条件循环 | `while` | 条件为 true 时执行 |
| 遍历集合 | `for` | 最常用，最安全 |
| 可选值处理 | `if let` | 简化 match |
| 多条件判断 | `match` | 模式匹配 |

---

**维护者**: Rust 学习项目团队  
**最后更新**: 2026-03-15
