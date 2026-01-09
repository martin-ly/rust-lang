# Tier 3: Drop 与 RAII 参考

> **文档类型**: 技术参考
> **适用版本**: Rust 1.92.0+

---

## 📊 目录

- [Tier 3: Drop 与 RAII 参考](#tier-3-drop-与-raii-参考)
  - [📊 目录](#-目录)
  - [📐 知识结构](#-知识结构)
  - [Drop trait](#drop-trait)
    - [基本使用](#基本使用)
  - [RAII 模式](#raii-模式)
    - [文件 RAII](#文件-raii)
    - [锁 RAII](#锁-raii)
  - [Drop 顺序](#drop-顺序)

## Drop trait

```rust
pub trait Drop {
    fn drop(&mut self);
}
```

### 基本使用

```rust
struct CustomSmartPointer {
    data: String,
}

impl Drop for CustomSmartPointer {
    fn drop(&mut self) {
        println!("Dropping CustomSmartPointer with data `{}`!", self.data);
    }
}

fn main() {
    let c = CustomSmartPointer {
        data: String::from("my stuff"),
    };
    let d = CustomSmartPointer {
        data: String::from("other stuff"),
    };
    println!("CustomSmartPointers created.");
} // d 和 c 自动调用 drop
```

---

## RAII 模式

**Resource Acquisition Is Initialization** - 资源获取即初始化

从引用一致性视角看，RAII 模式是**资源管理的编译期证明机制**。资源的获取和释放由编译期证明的资源生命周期决定，而非运行时检查。Drop trait 的自动调用是**编译期证明的确定性析构**。

### 文件 RAII

```rust
use std::fs::File;
use std::io::Write;

fn write_file() -> std::io::Result<()> {
    let mut file = File::create("output.txt")?; // 获取资源
    file.write_all(b"Hello")?;
    Ok(())
} // file 自动关闭（Drop）
```

### 锁 RAII

```rust
use std::sync::Mutex;

let data = Mutex::new(0);
{
    let mut num = data.lock().unwrap(); // 获取锁
    *num += 1;
} // 锁自动释放（Drop）
```

---

## Drop 顺序

1. 变量按声明的**相反顺序** drop
2. 结构体字段按**声明顺序** drop
3. 元组元素按**顺序** drop

```rust
struct Inner;
struct Outer(Inner);

impl Drop for Inner {
    fn drop(&mut self) { println!("Dropping Inner!"); }
}

impl Drop for Outer {
    fn drop(&mut self) { println!("Dropping Outer!"); }
}

fn main() {
    let _outer = Outer(Inner);
}
// 输出:
// Dropping Outer!
// Dropping Inner!
```

---

**相关文档**:

- [Tier 2: 04_作用域管理实践](../tier_02_guides/04_作用域管理实践.md)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-22
**最后更新**: 2025-12-11
