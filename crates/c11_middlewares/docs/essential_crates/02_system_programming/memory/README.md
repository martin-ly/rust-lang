# 内存管理

> **核心库**: bytes, bumpalo, typed-arena, slab  
> **适用场景**: 高性能内存管理、零拷贝、内存池、竞技场分配器

---

## 📋 核心库概览

| 库 | 用途 | 特点 | 推荐度 |
|-----|------|------|--------|
| **bytes** | 高效字节缓冲 | 零拷贝、引用计数 | ⭐⭐⭐⭐⭐ |
| **bumpalo** | 竞技场分配器 | 快速分配 | ⭐⭐⭐⭐⭐ |
| **slab** | 预分配内存池 | 固定大小对象 | ⭐⭐⭐⭐ |

---

## 📦 bytes - 高效字节缓冲

```rust
use bytes::{Bytes, BytesMut, Buf, BufMut};

fn main() {
    // 零拷贝共享
    let bytes = Bytes::from(&b"hello world"[..]);
    let slice1 = bytes.slice(0..5);
    let slice2 = bytes.slice(6..11);
    
    println!("{:?}", slice1); // b"hello"
    println!("{:?}", slice2); // b"world"
    
    // 可变缓冲区
    let mut buf = BytesMut::with_capacity(1024);
    buf.put(&b"hello "[..]);
    buf.put(&b"world"[..]);
    
    let bytes = buf.freeze(); // 转为不可变
    println!("{:?}", bytes);
}
```

---

## 🏟️ bumpalo - 竞技场分配器

```rust
use bumpalo::Bump;

fn main() {
    let bump = Bump::new();
    
    // 快速分配
    let x = bump.alloc(42);
    let y = bump.alloc_slice_fill_copy(10, 100);
    
    println!("x: {}", x);
    println!("y: {:?}", y);
    
    // 批量释放（作用域结束时）
}
```

---

## 🎰 slab - 内存池

```rust
use slab::Slab;

fn main() {
    let mut slab = Slab::new();
    
    // 插入并获取索引
    let key1 = slab.insert("hello");
    let key2 = slab.insert("world");
    
    // 通过索引访问
    println!("{}", slab[key1]);
    
    // 删除
    slab.remove(key1);
    
    // 迭代
    for (key, value) in &slab {
        println!("{}: {}", key, value);
    }
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20

