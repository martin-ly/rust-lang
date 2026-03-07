# Miri 深度解析

> **工具类型**: 运行时 UB 检测
> **难度**: 🟡 中等
> **应用场景**: 检测未定义行为、调试 Unsafe 代码

---

## 概念

Miri 是 Rust 的解释器，可以检测程序中的**未定义行为 (UB)**。它通过模拟 Rust 的内存模型来发现潜在问题。

---

## 安装与使用

### 安装

```bash
rustup component add miri
```

### 基本使用

```bash
# 运行 Miri
cargo miri run

# 运行测试
cargo miri test

# 检查特定文件
miri path/to/main.rs
```

---

## 检测能力

### 1. 使用未初始化内存

```rust
// 错误代码
fn main() {
    let x: i32;
    println!("{}", x);  // 使用未初始化变量 - UB!
}
```

```bash
$ cargo miri run
error: Undefined Behavior: memory access uses uninitialized data
```

**修复**:

```rust
fn main() {
    let x: i32 = 0;
    println!("{}", x);
}
```

### 2. 解引用悬垂指针

```rust
fn main() {
    let ptr: *const i32 = {
        let x = 5;
        &x
    };  // x 在这里释放

    unsafe { *ptr };  // UB!
}
```

```bash
$ cargo miri run
error: Undefined Behavior: pointer to alloc2733 was dereferenced after this allocation got freed
```

### 3. 数据竞争

```rust
use std::thread;

static mut X: i32 = 0;

fn main() {
    thread::spawn(|| unsafe { X = 1 });
    thread::spawn(|| unsafe { X = 2 });
}
```

```bash
$ cargo miri run
warning: thread XXX is trying to join thread YYY, but thread YYY tried to modify static mut X
which is also being accessed by the main thread
```

### 4. 违反 Stacked Borrows

```rust
fn main() {
    let mut x = 5;
    let ptr1 = &mut x as *mut i32;
    let ptr2 = &mut x as *mut i32;

    unsafe {
        *ptr1 = 10;
        *ptr2 = 20;  // 违反别名规则
    }
}
```

```bash
$ cargo miri run
error: Undefined Behavior: no item granting read access to tag <untagged>
```

---

## 高级配置

### 环境变量

```bash
# 禁用孤立检查 (FFI 测试)
MIRI_DISABLE_ISOLATION=1 cargo miri run

# 使用 Tree Borrows 代替 Stacked Borrows
MIRI_TREE_BORROWS=1 cargo miri test

# 回溯层数
MIRI_BACKTRACE=1 cargo miri run
```

### 与测试框架集成

```rust
#[cfg(test)]
mod tests {
    #[test]
    fn test_unsafe_code() {
        // 这个测试会在 Miri 中运行
        unsafe {
            // unsafe 代码
        }
    }
}
```

---

## 实战案例

### 实现 Vec 的 Miri 验证

```rust
pub struct MyVec<T> {
    ptr: *mut T,
    len: usize,
    cap: usize,
}

impl<T> MyVec<T> {
    pub fn push(&mut self, value: T) {
        if self.len == self.cap {
            self.grow();
        }

        unsafe {
            ptr::write(self.ptr.add(self.len), value);
            self.len += 1;
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }
        unsafe { Some(&*self.ptr.add(index)) }
    }
}

#[test]
fn test_my_vec() {
    let mut v = MyVec::new();
    v.push(1);
    v.push(2);
    assert_eq!(v.get(0), Some(&1));
    assert_eq!(v.get(1), Some(&2));
}
```

运行 `cargo miri test` 可以验证内存操作是否正确。

---

## 限制

1. **性能慢**: 解释执行，比原生慢 10-100x
2. **不支持所有平台**: 仅支持部分目标平台
3. **需要完整源代码**: 不能检查闭源代码
4. **非确定性**: 不检测所有可能的 UB

---

## 最佳实践

```markdown
1. 在 CI 中运行 Miri 测试
2. 所有 unsafe 代码都应有 Miri 测试
3. 配合其他工具使用 (ASan, TSan)
4. 定期运行 (每次发布前)
```

---

*文档版本: 1.0.0*
