# RAII Guard Pattern in Rust

> **设计模式**: Rust 特有
> **难度**: 🟢 简单
> **应用场景**: 资源自动释放、锁管理、临时状态

---

## 概念

RAII (Resource Acquisition Is Initialization) Guard 是 Rust 的核心模式，利用所有权和 Drop trait 确保资源在作用域结束时自动释放。

---

## 标准库示例

### MutexGuard

```rust
use std::sync::Mutex;

let data = Mutex::new(0);

{
    let mut guard = data.lock().unwrap(); // 获取锁
    *guard += 1;                          // 修改数据
} // guard 在这里 drop，自动释放锁
```

### 自定义 Guard

```rust
pub struct FileGuard {
    path: String,
    was_modified: bool,
}

impl FileGuard {
    pub fn new(path: &str) -> Self {
        println!("Opening file: {}", path);
        Self {
            path: path.to_string(),
            was_modified: false,
        }
    }

    pub fn modify(&mut self) {
        self.was_modified = true;
    }
}

impl Drop for FileGuard {
    fn drop(&mut self) {
        if self.was_modified {
            println!("Saving changes to {}", self.path);
        }
        println!("Closing file: {}", self.path);
    }
}

// 使用
fn process_file() {
    let mut file = FileGuard::new("data.txt");
    file.modify();
} // 自动保存并关闭
```

---

## 形式化语义

```
Guard<T> = T + Drop

性质:
  acquire(resource) → Guard<resource>
  drop(Guard) ⟹ release(resource)

线性类型保证:
  如果 Guard 没有被 drop，则资源未释放 (类型错误)
```
