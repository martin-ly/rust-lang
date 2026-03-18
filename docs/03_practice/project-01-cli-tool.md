# 实践项目 01: 命令行工具

> **难度**: ⭐ 入门级
> **所需知识**: c01-c03 (所有权、类型系统、控制流)
> **预计时间**: 2-3小时

---

## 项目目标

创建一个命令行待办事项管理工具 (Todo CLI)，学习Rust基础编程。

---

## 功能需求

### 基本功能

- [ ] 添加待办事项: `todo add "买牛奶"`
- [ ] 列出待办事项: `todo list`
- [ ] 标记完成: `todo done 1`
- [ ] 删除待办: `todo delete 1`
- [ ] 数据持久化到文件

### 扩展功能

- [ ] 设置优先级
- [ ] 截止日期提醒
- [ ] 分类标签

---

## 学习要点

### 1. 所有权和借用

```rust
// 学习如何管理字符串所有权
fn add_todo(todos: &mut Vec<String>, item: String) {
    todos.push(item);  // 所有权转移
}
```

### 2. 错误处理

```rust
// 学习 Result 类型
fn load_todos() -> Result<Vec<String>, std::io::Error> {
    std::fs::read_to_string("todos.txt")
        .map(|content| content.lines().map(String::from).collect())
}
```

### 3. 文件IO

```rust
// 学习文件读写
use std::fs::File;
use std::io::{Write, BufRead, BufReader};

fn save_todos(todos: &[String]) -> std::io::Result<()> {
    let mut file = File::create("todos.txt")?;
    for todo in todos {
        writeln!(file, "{}", todo)?;
    }
    Ok(())
}
```

---

## 项目结构

```
todo-cli/
├── Cargo.toml
└── src/
    ├── main.rs
    ├── commands.rs    # 命令处理
    ├── storage.rs     # 文件存储
    └── models.rs      # 数据结构
```

---

## 实现步骤

### 步骤 1: 创建项目

```bash
cargo new todo-cli
cd todo-cli
```

### 步骤 2: 定义数据结构

```rust
// src/models.rs
#[derive(Debug)]
struct Todo {
    id: usize,
    content: String,
    completed: bool,
}
```

### 步骤 3: 实现存储

```rust
// src/storage.rs
use std::fs;

pub struct TodoStorage {
    filename: String,
}

impl TodoStorage {
    pub fn new(filename: &str) -> Self {
        Self {
            filename: filename.to_string(),
        }
    }

    pub fn load(&self) -> Vec<String> {
        fs::read_to_string(&self.filename)
            .unwrap_or_default()
            .lines()
            .map(String::from)
            .collect()
    }

    pub fn save(&self, todos: &[String]) -> Result<(), std::io::Error> {
        fs::write(&self.filename, todos.join("\n"))
    }
}
```

### 步骤 4: 实现命令处理

```rust
// src/commands.rs
use crate::storage::TodoStorage;

pub fn add(storage: &TodoStorage, content: &str) {
    let mut todos = storage.load();
    todos.push(content.to_string());
    storage.save(&todos).expect("保存失败");
    println!("已添加: {}", content);
}

pub fn list(storage: &TodoStorage) {
    let todos = storage.load();
    for (i, todo) in todos.iter().enumerate() {
        println!("{}. {}", i + 1, todo);
    }
}
```

### 步骤 5: 主程序

```rust
// src/main.rs
use std::env;

mod commands;
mod models;
mod storage;

use storage::TodoStorage;

fn main() {
    let args: Vec<String> = env::args().collect();
    let storage = TodoStorage::new("todos.txt");

    if args.len() < 2 {
        println!("用法: todo <command> [args]");
        return;
    }

    match args[1].as_str() {
        "add" => {
            if args.len() < 3 {
                println!("请提供待办内容");
                return;
            }
            commands::add(&storage, &args[2]);
        }
        "list" => commands::list(&storage),
        _ => println!("未知命令"),
    }
}
```

---

## 测试验证

### 手动测试

```bash
# 编译
cargo build --release

# 添加待办
./target/release/todo-cli add "买牛奶"
./target/release/todo-cli add "写代码"

# 列出待办
./target/release/todo-cli list

# 预期输出:
# 1. 买牛奶
# 2. 写代码
```

---

## 参考实现

完整参考实现位于: `examples/todo-cli/`

---

## 下一步

完成此项目后，继续:

- [项目 02: 文件处理器](project-02-file-processor.md)
