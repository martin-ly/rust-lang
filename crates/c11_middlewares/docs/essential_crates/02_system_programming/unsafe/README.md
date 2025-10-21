# 不安全代码与底层操作

> **核心库**: std::ptr, std::mem, std::slice  
> **适用场景**: 底层内存操作、性能优化、FFI

---

## ⚠️ 不安全代码基础

### 原始指针操作

```rust
fn main() {
    let mut num = 5;
    
    // 创建原始指针
    let r1 = &num as *const i32;
    let r2 = &mut num as *mut i32;
    
    unsafe {
        println!("r1: {}", *r1);
        *r2 = 10;
        println!("r2: {}", *r2);
    }
}
```

### 内存操作

```rust
use std::mem;

fn main() {
    // 获取大小和对齐
    println!("Size: {}", mem::size_of::<i32>());
    println!("Align: {}", mem::align_of::<i32>());
    
    // 交换值
    let mut x = 5;
    let mut y = 10;
    mem::swap(&mut x, &mut y);
    
    // 替换值
    let old = mem::replace(&mut x, 100);
    println!("Old: {}, New: {}", old, x);
}
```

### 切片操作

```rust
use std::slice;

fn main() {
    let data = vec![1, 2, 3, 4, 5];
    let ptr = data.as_ptr();
    
    unsafe {
        let slice = slice::from_raw_parts(ptr, data.len());
        println!("{:?}", slice);
    }
}
```

---

## 💡 最佳实践

### ✅ 安全封装

```rust
pub struct SafeWrapper {
    ptr: *mut i32,
    len: usize,
}

impl SafeWrapper {
    pub fn new(data: Vec<i32>) -> Self {
        let len = data.len();
        let ptr = Box::into_raw(data.into_boxed_slice()) as *mut i32;
        Self { ptr, len }
    }
    
    pub fn get(&self, index: usize) -> Option<i32> {
        if index < self.len {
            unsafe { Some(*self.ptr.add(index)) }
        } else {
            None
        }
    }
}

impl Drop for SafeWrapper {
    fn drop(&mut self) {
        unsafe {
            Vec::from_raw_parts(self.ptr, self.len, self.len);
        }
    }
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20

