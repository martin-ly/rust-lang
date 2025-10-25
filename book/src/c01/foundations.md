# 基础概念

本页介绍所有权、借用与作用域的核心理论。

---

## 📚 目录

1. [所有权基础](#所有权基础)
2. [借用规则](#借用规则)
3. [生命周期](#生命周期)
4. [实践应用](#实践应用)

---

## 所有权基础

### 什么是所有权？

**所有权 (Ownership)** 是 Rust 最独特的特性，使得 Rust 无需垃圾回收器就能保证内存安全。

### 所有权规则

Rust 的所有权有三条基本规则：

1. **每个值都有一个所有者 (owner)**
2. **值在任一时刻只能有一个所有者**
3. **当所有者离开作用域时，值被释放**

### 示例

```rust
fn main() {
    {
        let s = String::from("hello");  // s 开始有效
        // 使用 s
    }  // s 离开作用域，被释放
}
```

---

## 移动语义

当一个值被赋值给另一个变量时，所有权会转移（移动）：

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的值移动到 s2
    
    // println!("{}", s1);  // 编译错误！s1 不再有效
    println!("{}", s2);  // 正确
}
```

### 为什么需要移动？

移动语义防止了**双重释放 (double free)** 错误：

- 如果 `s1` 和 `s2` 都拥有相同的数据
- 当它们离开作用域时，都会尝试释放内存
- 这会导致二次释放，引发崩溃

通过移动，Rust 确保只有一个变量负责释放内存。

---

## 克隆

如果你真的需要深拷贝数据，可以使用 `clone()`：

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 深拷贝
    
    println!("s1 = {}, s2 = {}", s1, s2);  // 都有效
}
```

⚠️ **性能提示**: `clone()` 可能开销很大，使用时要谨慎。

---

## Copy 类型

某些类型（如整数）实现了 `Copy` trait，赋值时会自动复制：

```rust
fn main() {
    let x = 5;
    let y = x;  // x 被复制，不是移动
    
    println!("x = {}, y = {}", x, y);  // 都有效
}
```

### 哪些类型是 Copy？

- ✅ 所有整数类型
- ✅ 布尔类型
- ✅ 浮点类型
- ✅ 字符类型
- ✅ 元组（如果所有元素都是 Copy）

❌ 不是 Copy:
- ❌ `String`
- ❌ `Vec<T>`
- ❌ 任何实现了 `Drop` 的类型

---

## 借用规则

### 不可变借用

可以同时存在多个不可变引用：

```rust
fn main() {
    let s = String::from("hello");
    
    let r1 = &s;  // 不可变引用
    let r2 = &s;  // 另一个不可变引用
    
    println!("{} and {}", r1, r2);  // 正确
}
```

### 可变借用

只能有一个可变引用：

```rust
fn main() {
    let mut s = String::from("hello");
    
    let r1 = &mut s;  // 可变引用
    // let r2 = &mut s;  // 编译错误！
    
    r1.push_str(", world");
    println!("{}", r1);
}
```

### 借用规则总结

在任意给定时间，要么只能有一个可变引用，要么只能有多个不可变引用：

- **规则 1**: 可以有任意数量的不可变引用
- **规则 2**: 只能有一个可变引用
- **规则 3**: 不能同时存在可变和不可变引用

---

## 生命周期

### 什么是生命周期？

**生命周期 (Lifetime)** 是引用有效的作用域。

### 为什么需要生命周期？

防止**悬垂引用 (dangling reference)**：

```rust
// 这段代码不能编译！
fn main() {
    let r;
    {
        let x = 5;
        r = &x;  // x 的生命周期太短
    }  // x 在这里被释放
    
    // println!("{}", r);  // r 引用的数据已被释放
}
```

### 生命周期标注

函数签名中的生命周期标注：

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

`'a` 表示返回值的生命周期与参数的生命周期相关联。

---

## 实践应用

### 函数参数

传递所有权 vs 借用：

```rust
// 获取所有权
fn take_ownership(s: String) {
    println!("{}", s);
}  // s 在这里被释放

// 借用
fn borrow(s: &String) {
    println!("{}", s);
}  // s 不被释放

fn main() {
    let s = String::from("hello");
    borrow(&s);  // 借用
    println!("{}", s);  // s 仍然有效
    
    take_ownership(s);  // 移动
    // println!("{}", s);  // 编译错误！s 已被移动
}
```

### 返回值

返回所有权：

```rust
fn create_string() -> String {
    let s = String::from("hello");
    s  // 所有权转移给调用者
}

fn main() {
    let my_string = create_string();
    println!("{}", my_string);
}
```

---

## 💡 关键要点

### 记住这些原则

1. **所有权**: 每个值都有唯一的所有者
2. **移动**: 赋值转移所有权（除非是 Copy 类型）
3. **借用**: 使用 `&` 创建引用，不获取所有权
4. **规则**: 多个不可变引用或一个可变引用
5. **生命周期**: 所有引用都必须有效

### 常见模式

**返回多个值**:

```rust
fn calculate(s: String) -> (String, usize) {
    let length = s.len();
    (s, length)  // 返回所有权和计算结果
}
```

**使用引用避免移动**:

```rust
fn calculate(s: &String) -> usize {
    s.len()  // 只返回长度，不需要所有权
}
```

---

## 🔗 下一步

- **[实践指南](./guides.md)** - 实用技巧和最佳实践
- **[代码示例](./examples.md)** - 交互式代码示例 ⭐
- **[返回模块首页](./README.md)**

---

**记住**: 所有权系统一开始可能难以理解，但它是 Rust 最强大的特性！多练习就能掌握 🚀
