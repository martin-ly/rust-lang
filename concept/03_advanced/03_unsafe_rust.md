
### 10.4 边界测试：自定义 allocator 的 `GlobalAlloc` 实现与安全契约（运行时 UB）

```rust,ignore
use std::alloc::{GlobalAlloc, Layout, System};

struct LoggingAlloc;

unsafe impl GlobalAlloc for LoggingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // ❌ 运行时 UB: 若 alloc 返回的指针未满足 layout 的对齐要求
        // 或分配大小小于 layout.size()
        System.alloc(layout)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // ❌ 运行时 UB: 若 dealloc 的 ptr 不是由对应 alloc 返回的
        // 或 layout 不匹配
        System.dealloc(ptr, layout);
    }
}

#[global_allocator]
static ALLOCATOR: LoggingAlloc = LoggingAlloc;

fn main() {}
```

> **修正**: **自定义分配器**的契约：1) `alloc(layout)` 返回的指针必须满足 `layout.align()` 对齐，且至少有 `layout.size()` 字节可用；2) `dealloc(ptr, layout)` 的 `ptr` 必须是同一 `layout` 的 `alloc` 返回值；3) `realloc` 保持数据不变。常见错误：1) 对齐不足（返回未对齐指针）；2) 重复释放（double free）；3) 释放非分配指针（use-after-free 的前置）。`#[global_allocator]` 替换全局分配器，影响所有堆分配（`Box`、`Vec`、`String`）。调试工具：1) `#[cfg(test)]` 使用检测分配器（如 `dhat`）；2) Miri 检测未定义行为；3) `loom` 检测并发分配器竞态。这与 C 的 `malloc`/`free`（无接口约束，全靠约定）或 C++ 的 `operator new`（可重载，但无 `GlobalAlloc` 的统一 trait）不同——Rust 的分配器接口是类型化的、有契约的。[来源: [GlobalAlloc](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html)] · [来源: [Rust Allocator Design](https://doc.rust-lang.org/std/alloc/index.html)]
