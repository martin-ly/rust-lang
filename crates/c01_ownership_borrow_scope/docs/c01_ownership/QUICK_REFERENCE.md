# C01 所有权快速参考

> 所有权系统的核心概念速查

---

## 📋 所有权三规则

1. **每个值都有一个所有者**
2. **同一时间只有一个所有者**
3. **所有者离开作用域，值被释放**

---

## 🔑 借用规则

| 类型 | 语法 | 数量 | 可变性 |
|------|------|------|--------|
| 不可变借用 | `&T` | 多个 | 不可变 |
| 可变借用 | `&mut T` | 一个 | 可变 |

**规则**: 不可变借用和可变借用不能同时存在

---

## 💡 常见模式

### 1. 所有权转移

```rust
let s1 = String::from("hello");
let s2 = s1;  // 所有权转移
// s1 不能再使用
```

### 2. 克隆

```rust
let s1 = String::from("hello");
let s2 = s1.clone();  // 深拷贝
```

### 3. 借用

```rust
fn calculate_length(s: &String) -> usize {
    s.len()
}
```

### 4. 可变借用

```rust
fn change(s: &mut String) {
    s.push_str(" world");
}
```

---

## 📝 生命周期标注

```rust
// 函数
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 结构体
struct ImportantExcerpt<'a> {
    part: &'a str,
}
```

---

## 🎯 智能指针选择

| 场景 | 推荐类型 | 说明 |
|------|----------|------|
| 堆分配 | `Box<T>` | 唯一所有权 |
| 共享只读 | `Rc<T>` | 引用计数 |
| 共享可变 | `Rc<RefCell<T>>` | 运行时借用检查 |
| 线程共享 | `Arc<T>` | 原子引用计数 |
| 延迟初始化 | `LazyLock<T>` | 线程安全延迟初始化 |

---

## ⚠️ 常见错误

| 错误 | 原因 | 解决 |
|------|------|------|
| use of moved value | 所有权已转移 | 使用借用或克隆 |
| cannot borrow as mutable | 已有不可变借用 | 调整借用范围 |
| cannot borrow as immutable | 已有可变借用 | 调整借用范围 |
| lifetime mismatch | 生命周期不匹配 | 添加生命周期标注 |

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
