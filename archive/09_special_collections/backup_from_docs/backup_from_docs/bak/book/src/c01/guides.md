# 实践指南

本页提供所有权、借用与作用域的实用技巧和最佳实践。

---

## 💡 常见模式

### 1. 何时使用借用 vs 移动？

**使用借用** (`&T` 或 `&mut T`) 当：
- ✅ 只需要读取数据
- ✅ 需要临时修改数据
- ✅ 调用者还需要使用该值

**使用移动** (获取所有权) 当：
- ✅ 需要完全拥有数据
- ✅ 数据不再需要被调用者使用
- ✅ 需要返回修改后的数据

### 示例对比

```rust
// 方案1: 使用借用（推荐）
fn calculate_length(s: &String) -> usize {
    s.len()
}

// 方案2: 获取所有权（不推荐，除非必要）
fn calculate_length_owned(s: String) -> (String, usize) {
    let length = s.len();
    (s, length)  // 必须返回所有权
}

fn main() {
    let s = String::from("hello");
    
    // 使用借用
    let len = calculate_length(&s);
    println!("长度: {}, 字符串: {}", len, s);  // s 仍然有效
}
```

---

## 🎯 最佳实践

### 1. 优先使用不可变引用

```rust
// 好的做法
fn process(data: &Vec<i32>) -> i32 {
    data.iter().sum()
}

// 只在必要时使用可变引用
fn modify(data: &mut Vec<i32>) {
    data.push(42);
}
```

### 2. 使用切片代替完整引用

```rust
// 更灵活：接受 Vec、数组、切片
fn first_word(s: &str) -> &str {
    // ...
    s
}

// 不够灵活：只接受 String
fn first_word_bad(s: &String) -> &str {
    // ...
    s
}
```

### 3. 避免不必要的克隆

```rust
// 不好：不必要的克隆
fn bad_example() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 开销大
    println!("{}", s1);
    println!("{}", s2);
}

// 好：使用引用
fn good_example() {
    let s = String::from("hello");
    let r1 = &s;
    let r2 = &s;
    println!("{}", r1);
    println!("{}", r2);
}
```

---

## 🐛 常见错误及修复

### 错误 1: 使用已移动的值

```rust
// ❌ 错误
fn error_example() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 移动到 s2
    println!("{}", s1);  // 编译错误！
}

// ✅ 修复方案1: 使用克隆
fn fix1() {
    let s1 = String::from("hello");
    let s2 = s1.clone();
    println!("{} {}", s1, s2);
}

// ✅ 修复方案2: 使用引用
fn fix2() {
    let s1 = String::from("hello");
    let s2 = &s1;
    println!("{} {}", s1, s2);
}
```

### 错误 2: 可变和不可变引用同时存在

```rust
// ❌ 错误
fn error_example() {
    let mut s = String::from("hello");
    let r1 = &s;  // 不可变引用
    let r2 = &mut s;  // 编译错误！
    println!("{} {}", r1, r2);
}

// ✅ 修复: 分离作用域
fn fix() {
    let mut s = String::from("hello");
    
    {
        let r1 = &s;
        println!("{}", r1);
    }  // r1 离开作用域
    
    let r2 = &mut s;
    println!("{}", r2);
}
```

### 错误 3: 返回局部变量的引用

```rust
// ❌ 错误
fn error_example() -> &String {
    let s = String::from("hello");
    &s  // 编译错误！s 将被释放
}

// ✅ 修复: 返回所有权
fn fix() -> String {
    let s = String::from("hello");
    s  // 转移所有权
}
```

---

## 📚 高级技巧

### 1. 智能使用生命周期省略

Rust 可以自动推断简单情况下的生命周期：

```rust
// 编译器自动推断生命周期
fn first_word(s: &str) -> &str {
    // 返回值的生命周期与参数相同
    &s[..1]
}

// 等价于（显式标注）
fn first_word_explicit<'a>(s: &'a str) -> &'a str {
    &s[..1]
}
```

### 2. 结构体中的引用

```rust
struct User<'a> {
    name: &'a str,
    email: &'a str,
}

impl<'a> User<'a> {
    fn get_domain(&self) -> &str {
        let at = self.email.find('@').unwrap();
        &self.email[at + 1..]
    }
}

fn main() {
    let name = String::from("Alice");
    let email = String::from("alice@example.com");
    
    let user = User {
        name: &name,
        email: &email,
    };
    
    println!("域名: {}", user.get_domain());
}
```

### 3. 静态生命周期

```rust
// 'static 表示整个程序运行期间有效
const MESSAGE: &'static str = "Hello, World!";

fn get_message() -> &'static str {
    MESSAGE
}
```

---

## 🔧 实用工具函数

### 安全的字符串拼接

```rust
fn concat_strings(s1: &str, s2: &str) -> String {
    format!("{}{}", s1, s2)
}

// 使用
fn main() {
    let a = "Hello, ";
    let b = "World!";
    let result = concat_strings(a, b);
    println!("{}", result);
}
```

### 安全的向量处理

```rust
fn process_vec(v: &[i32]) -> Vec<i32> {
    v.iter()
        .filter(|&&x| x > 0)
        .map(|&x| x * 2)
        .collect()
}

// 使用
fn main() {
    let numbers = vec![-1, 2, -3, 4];
    let positive_doubled = process_vec(&numbers);
    println!("{:?}", positive_doubled);  // [4, 8]
}
```

---

## 🎓 学习检查清单

在继续学习之前，确保你理解了：

- [ ] 所有权三规则
- [ ] 移动语义和 Copy trait
- [ ] 借用的两种规则
- [ ] 生命周期的基本概念
- [ ] 如何修复常见的所有权错误
- [ ] 何时使用借用 vs 移动
- [ ] 如何在函数中使用引用
- [ ] 结构体中如何使用引用

---

## 🔗 相关资源

- **[基础概念](./foundations.md)** - 理论基础
- **[代码示例](./examples.md)** - 交互式示例 ⭐
- **[返回模块首页](./README.md)**

### 外部学习资源

- [Rust Book - 所有权](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Rustonomicon - 高级主题](https://doc.rust-lang.org/nomicon/)
- [Rust By Example](https://doc.rust-lang.org/rust-by-example/)

---

**记住**: 实践是掌握所有权最好的方式！多写代码，多运行示例 🚀
