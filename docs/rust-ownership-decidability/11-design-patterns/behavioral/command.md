# Command Pattern in Rust

> **设计模式**: 行为型模式
> **难度**: 🟡 中等
> **应用场景**: 撤销/重做、任务队列、宏录制

---

## 概念

命令模式将请求封装为对象，从而可用不同的请求、队列或日志来参数化客户端，同时支持可撤销的操作。

---

## 实现

### 基础命令模式

```rust
// 命令 trait
pub trait Command {
    fn execute(&self);
    fn undo(&self);
    fn description(&self) -> &str;
}

// 接收者
pub struct TextEditor {
    content: String,
    clipboard: String,
}

impl TextEditor {
    pub fn new() -> Self {
        Self {
            content: String::new(),
            clipboard: String::new(),
        }
    }

    pub fn insert(&mut self, text: &str, position: usize) {
        self.content.insert_str(position, text);
    }

    pub fn delete(&mut self, start: usize, length: usize) -> String {
        let removed = self.content[start..start+length].to_string();
        self.content.replace_range(start..start+length, "");
        removed
    }

    pub fn copy_to_clipboard(&mut self, text: &str) {
        self.clipboard = text.to_string();
    }

    pub fn paste_from_clipboard(&self) -> &str {
        &self.clipboard
    }

    pub fn content(&self) -> &str {
        &self.content
    }
}

// 具体命令: 插入
pub struct InsertCommand {
    editor: std::cell::RefCell<TextEditor>,
    text: String,
    position: usize,
}

impl InsertCommand {
    pub fn new(editor: std::cell::RefCell<TextEditor>, text: &str, position: usize) -> Self {
        Self {
            editor,
            text: text.to_string(),
            position,
        }
    }
}

impl Command for InsertCommand {
    fn execute(&self) {
        self.editor.borrow_mut().insert(&self.text, self.position);
    }

    fn undo(&self) {
        let len = self.text.len();
        self.editor.borrow_mut().delete(self.position, len);
    }

    fn description(&self) -> &str {
        "Insert text"
    }
}

// 调用者
pub struct CommandManager {
    history: Vec<Box<dyn Command>>,
    current: usize,
}

impl CommandManager {
    pub fn new() -> Self {
        Self {
            history: Vec::new(),
            current: 0,
        }
    }

    pub fn execute(&mut self, command: Box<dyn Command>) {
        // 如果在历史中间，丢弃后面的命令
        if self.current < self.history.len() {
            self.history.truncate(self.current);
        }

        command.execute();
        self.history.push(command);
        self.current += 1;
    }

    pub fn undo(&mut self) {
        if self.current > 0 {
            self.current -= 1;
            self.history[self.current].undo();
        }
    }

    pub fn redo(&mut self) {
        if self.current < self.history.len() {
            self.history[self.current].execute();
            self.current += 1;
        }
    }
}
```

### 闭包命令 (Rust 风格)

```rust
pub struct ClosureCommand {
    execute_fn: Box<dyn Fn()>,
    undo_fn: Box<dyn Fn()>,
    description: String,
}

impl ClosureCommand {
    pub fn new(
        execute: impl Fn() + 'static,
        undo: impl Fn() + 'static,
        description: &str,
    ) -> Self {
        Self {
            execute_fn: Box::new(execute),
            undo_fn: Box::new(undo),
            description: description.to_string(),
        }
    }
}

impl Command for ClosureCommand {
    fn execute(&self) {
        (self.execute_fn)();
    }

    fn undo(&self) {
        (self.undo_fn)();
    }

    fn description(&self) -> &str {
        &self.description
    }
}

// 使用
fn main() {
    let mut value = 0i32;
    let value_ref = std::cell::RefCell::new(&mut value);

    let cmd = ClosureCommand::new(
        || { *value_ref.borrow_mut() += 10; },
        || { *value_ref.borrow_mut() -= 10; },
        "Add 10",
    );

    cmd.execute();
    println!("Value: {}", value);
    cmd.undo();
    println!("Value: {}", value);
}
```

---

## 形式化定义

```
Command = (execute: () → (), undo: () → ())

历史管理:
  History = Command*
  undo: History × ℕ → History
  redo: History × ℕ → History

约束:
  execute(c); undo(c) = id (幂等)
```
