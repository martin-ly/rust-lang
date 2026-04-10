# C01: 所有权、借用与作用域

> **Rust 基础核心** | **必须掌握** | ⭐⭐⭐⭐⭐ 重要性

## 模块职责

本 crate 是 Rust 学习路径的第一站，涵盖 Rust 最核心的内存安全机制：

- **所有权系统**: 理解值的所有权转移和唯一性
- **借用规则**: 掌握不可变借用与可变借用的约束
- **生命周期**: 学习编译器如何验证引用有效性
- **智能指针**: Box, Rc, Arc, RefCell 等的使用场景

## 目录结构

```
src/
├── lib.rs              # 模块入口，公开 API
├── bin/
│   └── main.rs         # CLI 可执行文件
├── ownership/          # 所有权基础
├── borrow/             # 借用机制
├── lifetime/           # 生命周期
├── smart_pointers/     # 智能指针
└── threads/            # 多线程与所有权
```

## 主要类型和 Trait

### 核心类型

| 类型 | 描述 | 使用场景 |
|------|------|----------|
| `Box<T>` | 堆分配智能指针 | 递归类型、大数据 |
| `Rc<T>` | 单线程引用计数 | 共享所有权 |
| `Arc<T>` | 原子引用计数 | 跨线程共享 |
| `RefCell<T>` | 运行时借用检查 | 内部可变性 |
| `Cow<T>` | 写时克隆 | 避免不必要的拷贝 |

### 关键 Trait

| Trait | 功能 | 示例 |
|-------|------|------|
| `Drop` | 析构时自定义清理 | 资源释放 |
| `Clone` | 显式深拷贝 | 值复制 |
| `Copy` | 隐式按位复制 | 基本类型 |
| `Deref` | 智能指针解引用 | 自定义指针 |

## 使用示例

### 所有权转移

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权转移
    // println!("{}", s1); // 错误！s1 已失效
    println!("{}", s2);   // 正确
}
```

### 借用规则

```rust
fn main() {
    let mut s = String::from("hello");
    
    let r1 = &s;      // 不可变借用
    let r2 = &s;      // 多个不可变借用 OK
    // let r3 = &mut s; // 错误！不能同时拥有可变和不可变借用
    
    println!("{} {}", r1, r2);
    
    let r3 = &mut s;  // 正确，r1, r2 已不再使用
    r3.push_str(" world");
}
```

### 智能指针使用

```rust
use std::rc::Rc;
use std::cell::RefCell;

fn main() {
    // Rc 用于共享所有权
    let data = Rc::new(RefCell::new(5));
    
    let data2 = Rc::clone(&data);
    *data2.borrow_mut() += 10;
    
    println!("{}", data.borrow()); // 输出: 15
}
```

## 依赖关系

### 上游依赖
- `common`: 共享错误处理工具

### 下游依赖
- `c02_type_system`: 基于所有权构建类型系统
- `c05_threads`: Arc 用于跨线程共享

### 外部依赖
```toml
[dependencies]
tokio = { workspace = true }
serde = { workspace = true }
serde_json = { workspace = true }
```

## 运行方式

```bash
# 运行库测试
cargo test -p c01_ownership_borrow_scope

# 运行 CLI
cargo run -p c01_ownership_borrow_scope --bin obs

# 运行基准测试
cargo bench -p c01_ownership_borrow_scope
```

## 学习路径建议

1. 首先阅读 `src/ownership/mod.rs` 理解所有权三规则
2. 练习 `examples/` 中的示例代码
3. 完成 `exercises/` 中的练习
4. 运行 Miri 检查验证内存安全

## 相关文档

- [Rust Book - Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Rustnomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)
- [docs/01_learning/ownership_guide.md](../../docs/01_learning/)
