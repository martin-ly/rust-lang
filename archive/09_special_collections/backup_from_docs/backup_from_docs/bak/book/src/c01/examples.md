# 代码示例

本章提供 C01 模块的交互式代码示例。所有示例都可以在浏览器中运行。

---

## 🎯 示例概览

本页包含以下主题的代码示例：

1. [所有权基础](#所有权基础)
2. [借用和引用](#借用和引用)
3. [生命周期](#生命周期)
4. [实战案例](#实战案例)

---

## 所有权基础

### 示例 1: 移动语义

理解 Rust 的移动语义：

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的所有权转移给 s2
    
    // println!("{}", s1);  // 编译错误！取消注释试试
    println!("{}", s2);  // 正确
}
```

**练习**: 尝试取消注释第 5 行，观察编译器的错误信息。

### 示例 2: 克隆 vs 移动

对比克隆和移动的区别：

```rust
fn main() {
    // 移动
    let s1 = String::from("hello");
    let s2 = s1;
    // s1 不再可用
    
    // 克隆
    let s3 = String::from("world");
    let s4 = s3.clone();
    println!("s3 = {}, s4 = {}", s3, s4);  // 都可用
    
    // Copy 类型
    let x = 5;
    let y = x;
    println!("x = {}, y = {}", x, y);  // 都可用
}
```

### 示例 3: 函数所有权

函数如何影响所有权：

```rust
fn main() {
    let s = String::from("hello");
    
    takes_ownership(s);
    // s 不再有效
    
    let x = 5;
    makes_copy(x);
    println!("x = {}", x);  // x 仍然有效（Copy 类型）
}

fn takes_ownership(some_string: String) {
    println!("{}", some_string);
}  // some_string 在这里被 drop

fn makes_copy(some_integer: i32) {
    println!("{}", some_integer);
}
```

---

## 借用和引用

### 示例 4: 不可变借用

多个不可变引用：

```rust
fn main() {
    let s = String::from("hello");
    
    let r1 = &s;  // 第一个不可变引用
    let r2 = &s;  // 第二个不可变引用
    
    println!("r1: {}, r2: {}", r1, r2);
    // r1 和 r2 都可以使用
}
```

### 示例 5: 可变借用

只能有一个可变引用：

```rust
fn main() {
    let mut s = String::from("hello");
    
    let r1 = &mut s;  // 可变引用
    r1.push_str(", world");
    
    println!("{}", r1);
    
    // let r2 = &mut s;  // 编译错误！不能同时有两个可变引用
}
```

### 示例 6: 借用规则

理解借用规则：

```rust
fn main() {
    let mut s = String::from("hello");
    
    {
        let r1 = &mut s;
        r1.push_str(", world");
    }  // r1 在这里离开作用域
    
    let r2 = &mut s;  // 现在可以创建新的可变引用
    r2.push_str("!");
    
    println!("{}", r2);
}
```

---

## 生命周期

### 示例 7: 基本生命周期

函数中的生命周期标注：

```rust
fn main() {
    let string1 = String::from("abcd");
    let string2 = "xyz";
    
    let result = longest(string1.as_str(), string2);
    println!("最长的字符串是: {}", result);
}

fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

### 示例 8: 结构体生命周期

结构体中的生命周期：

```rust
fn main() {
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().unwrap();
    
    let excerpt = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("摘录: {}", excerpt.part);
}

struct ImportantExcerpt<'a> {
    part: &'a str,
}
```

---

## 实战案例

### 示例 9: 字符串所有权管理

实际场景中的所有权：

```rust
fn main() {
    let mut text = String::from("Hello");
    
    // 场景1: 修改字符串
    append_world(&mut text);
    println!("修改后: {}", text);
    
    // 场景2: 计算长度（不需要所有权）
    let len = calculate_length(&text);
    println!("长度: {}", len);
    
    // 场景3: 获取第一个单词
    let first = first_word(&text);
    println!("第一个单词: {}", first);
}

fn append_world(s: &mut String) {
    s.push_str(", World!");
}

fn calculate_length(s: &String) -> usize {
    s.len()
}

fn first_word(s: &str) -> &str {
    let bytes = s.as_bytes();
    
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    
    &s[..]
}
```

### 示例 10: 综合练习

综合运用所有权概念：

```rust
fn main() {
    // 创建数据
    let mut data = vec![1, 2, 3, 4, 5];
    
    // 只读访问
    let sum = calculate_sum(&data);
    println!("总和: {}", sum);
    
    // 修改数据
    double_values(&mut data);
    println!("翻倍后: {:?}", data);
    
    // 移动数据
    let new_data = data;
    println!("新数据: {:?}", new_data);
    
    // data 不再可用
    // println!("{:?}", data);  // 编译错误
}

fn calculate_sum(v: &Vec<i32>) -> i32 {
    v.iter().sum()
}

fn double_values(v: &mut Vec<i32>) {
    for item in v.iter_mut() {
        *item *= 2;
    }
}
```

---

## 💡 学习建议

### 如何使用这些示例

1. **阅读代码**: 先理解代码的目的
2. **运行示例**: 点击 "Run" 按钮运行代码
3. **修改实验**: 尝试修改代码，观察结果
4. **理解错误**: 故意引入错误，学习编译器提示

### 练习建议

- **示例 1-3**: 理解所有权转移
- **示例 4-6**: 掌握借用规则
- **示例 7-8**: 学习生命周期标注
- **示例 9-10**: 应用到实际场景

### 常见陷阱

⚠️ **同时存在可变和不可变引用**

```rust
let mut s = String::from("hello");
let r1 = &s;  // 不可变引用
let r2 = &mut s;  // 编译错误！
```

⚠️ **悬垂引用**

```rust
fn dangle() -> &String {  // 编译错误！
    let s = String::from("hello");
    &s
}  // s 在这里被释放
```

---

## 🔗 更多资源

- [完整代码示例集合](../../crates/c01_ownership_borrow_scope/docs/tier_02_guides/06_代码示例集合.md)
- [返回指南页面](./guides.md)
- [返回模块首页](./README.md)
- [交互式示例使用指南](../tools/interactive-examples.md)

---

**记住**: 所有权是 Rust 最重要的特性，多练习才能真正掌握！🚀
