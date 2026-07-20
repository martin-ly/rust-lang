# 所有权系统思维导图

> **文档类型**: 🧠 思维导图 | 🗺️ 知识可视化  
> **创建日期**: 2025-10-19  
> **Rust 版本**: 1.90+

---

## 目录

- [所有权系统思维导图](#所有权系统思维导图)
  - [目录](#目录)
  - [📋 思维导图概览](#-思维导图概览)
    - [核心分支](#核心分支)
  - [🗺️ 所有权系统全景图](#️-所有权系统全景图)
  - [核心概念速查](#核心概念速查)
    - [所有权规则](#所有权规则)
    - [借用系统](#借用系统)
    - [智能指针](#智能指针)
    - [内部可变性](#内部可变性)
    - [RAII 模式](#raii-模式)
  - [学习路径](#学习路径)
  - [🔗 相关文档](#-相关文档)

## 📋 思维导图概览

本思维导图以 **Rust 所有权系统** 为中心，展开为10个主要分支，涵盖所有权、借用、智能指针、内部可变性等核心概念。

### 核心分支

1. **所有权规则**: 三大规则、RAII、作用域
2. **移动语义**: 默认移动、浅拷贝、值失效
3. **复制语义**: Copy特征、按位复制
4. **克隆语义**: Clone特征、深拷贝
5. **借用系统**: 不可变借用、可变借用
6. **借用检查器**: 规则、NLL、错误
7. **智能指针**: Box/Rc/Arc
8. **内部可变性**: Cell/RefCell/Mutex
9. **内存安全**: 防护机制、保证
10. **实战模式**: RAII、构建器、零拷贝

---

## 🗺️ 所有权系统全景图

```mermaid
mindmap
  root((所有权系统))
    所有权规则
      规则1
        每个值有唯一所有者
      规则2
        离开作用域自动释放
        RAII模式
      规则3
        赋值/传参默认移动
        移动语义
    
    移动语义
      默认行为
        非Copy类型移动
        原值失效
      浅拷贝
        栈数据复制
        堆数据指针转移
      防止双重释放
        编译时检查
        所有权转移
    
    复制语义
      Copy特征
        按位复制
        隐式复制
      要求
        所有字段都Copy
        无Drop实现
      常见类型
        基本类型 i32 bool
        元组 数组(元素Copy)
        引用 &T
    
    克隆语义
      Clone特征
        显式深拷贝
        clone()方法
      实现
        派生#[derive(Clone)]
        手动实现
      vs Copy
        Clone显式 可能昂贵
        Copy隐式 廉价
    
    借用系统
      不可变借用
        &T
        共享引用
        多个同时存在
        只读访问
      可变借用
        &mut T
        独占引用
        同时只能一个
        可写访问
      借用规则
        互斥：&T多个 或 &mut T一个
        引用必须有效
    
    借用检查器
      编译时检查
        生命周期分析
        借用冲突检测
      NLL
        Rust 2018
        非词法生命周期
        更精确
      错误类型
        移动后使用
        借用冲突
        悬垂引用
    
    智能指针
      Box<T>
        堆分配
        独占所有权
        解引用
      Rc<T>
        引用计数
        共享所有权
        单线程
      Arc<T>
        原子引用计数
        线程安全
        多线程
    
    内部可变性
      Cell<T>
        Copy类型
        内部可变
        单线程
      RefCell<T>
        运行时借用检查
        panic可能
        单线程
      Mutex<T>
        互斥锁
        线程安全
        运行时开销
    
    内存安全
      防悬垂指针
        生命周期检查
        编译时保证
      防数据竞争
        借用规则
        Send/Sync
      防迭代器失效
        借用冲突检测
    
    实战模式
      RAII
        资源获取即初始化
        Drop自动清理
      构建器
        Builder模式
        类型状态
      零拷贝
        借用而非克隆
        切片视图
        Cow<T>
```

---

## 核心概念速查

### 所有权规则

```rust
fn ownership_rules() {
    let s1 = String::from("hello"); // s1 拥有
    let s2 = s1; // 移动到 s2
    // println!("{}", s1); // ❌ s1 已失效
    println!("{}", s2); // ✅
} // s2 离开作用域，自动释放
```

### 借用系统

```rust
fn borrowing() {
    let mut s = String::from("hello");
    
    // 不可变借用
    let r1 = &s;
    let r2 = &s;
    println!("{}, {}", r1, r2);
    
    // 可变借用
    let r3 = &mut s;
    r3.push_str(" world");
    println!("{}", r3);
}
```

### 智能指针

```rust
use std::rc::Rc;
use std::sync::Arc;

fn smart_pointers() {
    // Box: 堆分配
    let b = Box::new(5);
    
    // Rc: 引用计数
    let rc1 = Rc::new(String::from("hello"));
    let rc2 = Rc::clone(&rc1);
    
    // Arc: 线程安全引用计数
    let arc1 = Arc::new(42);
    let arc2 = Arc::clone(&arc1);
}
```

### 内部可变性

```rust
use std::cell::{Cell, RefCell};

fn interior_mutability() {
    // Cell: Copy类型
    let cell = Cell::new(5);
    cell.set(10);
    
    // RefCell: 运行时检查
    let refcell = RefCell::new(String::from("hello"));
    refcell.borrow_mut().push_str(" world");
    
    println!("{}", refcell.borrow());
}
```

### RAII 模式

```rust
struct File {
    name: String,
}

impl File {
    fn open(name: String) -> Self {
        println!("Opening: {}", name);
        File { name }
    }
}

impl Drop for File {
    fn drop(&mut self) {
        println!("Closing: {}", self.name);
    }
}

fn raii_example() {
    let _file = File::open("data.txt".to_string());
    // 自动调用 drop
}
```

---

## 学习路径

```mermaid
graph LR
    A[所有权规则] --> B[移动语义]
    B --> C[借用系统]
    C --> D[借用检查器]
    D --> E[智能指针]
    E --> F[内部可变性]
    F --> G[实战模式]
    
    style A fill:#e1f5e1
    style G fill:#ffe1e1
```

---

## 🔗 相关文档

- [01_concept_ontology.md](01_concept_ontology.md) - 所有权概念定义
- [14_ownership_borrowing_matrix.md](14_ownership_borrowing_matrix.md) - 所有权借用对比
- [23_lifetime_system_mindmap.md](23_lifetime_system_mindmap.md) - 生命周期系统
- [Rust Book - Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)

---

**文档状态**: ✅ 已完成  
**最后更新**: 2025-10-19  
**贡献者**: Rust Type System Knowledge Engineering Team
