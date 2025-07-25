# 内存分配器

## 1. 分配器接口与全局分配器

- std::alloc::GlobalAlloc trait定义分配/释放接口
- 可自定义全局或局部分配器

## 2. 分配器正确性与安全性

- $\text{alloc}(n)$、$\text{dealloc}(p)$操作的正确性
- 分配器正确性定理：不会发生内存泄漏、重复释放

## 3. 工程案例

```rust
use std::alloc::{GlobalAlloc, Layout, System};
struct MyAlloc;
unsafe impl GlobalAlloc for MyAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        System.alloc(layout)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}
```

## 4. 批判性分析与未来展望

- 自定义分配器提升灵活性与性能，但安全性与兼容性需严格验证
- 未来可探索自动化分配器验证与性能分析工具
