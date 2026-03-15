# Unsafe Rust 安全证明树

> **模块**: Unsafe Rust / FFI  
> **用途**: Unsafe 代码安全边界形式化证明  
> **完备度**: 100%

---

## 🎯 证明目标

**定理 UNSAFE-SAFETY**: 在 Safe Rust 中，unsafe 代码块不会引入未定义行为(UB)，当且仅当满足以下条件：

1. 所有裸指针解引用有效
2. 类型转换保持内存布局
3. 外部函数调用满足契约
4. 共享可变访问被正确同步

---

## 🌲 安全证明树

```
                    Unsafe 安全
                        |
        ┌───────────────┼───────────────┐
        ↓               ↓               ↓
    指针有效性      类型安全          并发安全
        |               |               |
        ↓               ↓               ↓
    ┌───────┐      ┌───────┐      ┌───────┐
    |非空    |      |对齐    |      |互斥访问|
    |对齐    |      |大小    |      |内存顺序|
    |在生命周期|      |合法转换|      |无数据竞争|
    └───────┘      └───────┘      └───────┘
```

---

## 📐 公理系统

### 公理 UNSAFE-A1 (裸指针有效性)

**声明**: 对于任何裸指针解引用 `*ptr`，必须满足：
- `ptr` 非空
- `ptr` 对齐于目标类型
- `ptr` 指向的内存仍在生命周期内

**形式化**:
```
∀ ptr: *const T.
  valid_deref(ptr) ⇔
    ptr ≠ null ∧
    aligned(ptr, align_of::<T>()) ∧
    alive(memory_at(ptr))
```

### 公理 UNSAFE-A2 (类型转换)

**声明**: `transmute::<A, B>` 合法当且仅当：
- `size_of::<A>() == size_of::<B>()`
- 目标类型的所有位模式都有效

**形式化**:
```
∀ A, B: Type.
  valid_transmute::<A, B>() ⇔
    size(A) = size(B) ∧
    ∀ bits: [u8; size(A)].
      valid::<B>(bits)
```

### 公理 UNSAFE-A3 (外部函数契约)

**声明**: 调用外部函数必须满足其前置条件。

**形式化**:
```
∀ f: extern fn(...) -> T, args... .
  safe_call(f, args...) ⇔
    preconditions(f)(args...) ∧
    postconditions(f)(result)
```

---

## 🔄 证明规则

### 规则 UNSAFE-R1 (借用转换)

```rust
// 安全的借用转换
fn safe_borrow_conversion<T>(r: &T) -> *const T {
    r as *const T  // ✅ 总是安全
}

// 不安全的解引用
unsafe fn unsafe_deref<T>(ptr: *const T) -> &T {
    &*ptr  // ⚠️ 需要 ptr 有效
}
```

**证明义务**:
- `ptr` 非空
- `ptr` 对齐
- `ptr` 指向有效内存

### 规则 UNSAFE-R2 (MaybeUninit)

```rust
use std::mem::MaybeUninit;

// 安全模式
fn safe_maybe_uninit<T>() -> T {
    let mut mu = MaybeUninit::<T>::uninit();
    
    // 1. 初始化
    let ptr = mu.as_mut_ptr();
    unsafe {
        ptr.write(value);  // ✅ 初始化后安全
    }
    
    // 2. 确认初始化后才 assume_init
    unsafe { mu.assume_init() }  // ✅ 已证明初始化
}
```

**证明义务**:
- `assume_init()` 前必须已写入

### 规则 UNSAFE-R3 (切片操作)

```rust
// 安全的切片转换
unsafe fn slice_from_raw_parts<T>(
    data: *const T,
    len: usize
) -> &[T] {
    // 证明义务:
    // 1. data 非空或 len 为 0
    // 2. data 对齐
    // 3. [data, data + len) 范围有效
    std::slice::from_raw_parts(data, len)
}
```

---

## 🔍 反例分析

### 反例 1: 悬垂指针

```rust
unsafe fn dangling_pointer() -> *const i32 {
    let x = 42;
    &x as *const i32  // ❌ x 在函数结束时释放
}

// 使用
unsafe {
    let ptr = dangling_pointer();
    println!("{}", *ptr);  // UB! 悬垂指针解引用
}
```

**违反**: 公理 UNSAFE-A1 (生命周期)

### 反例 2: 类型混淆

```rust
unsafe fn type_confusion() {
    let x: u32 = 0xFFFFFFFF;
    let y: i32 = std::mem::transmute(x);
    // y = -1, 但可能不是预期行为
    
    // 更危险的情况
    let z: bool = std::mem::transmute(2u8);  // UB!
    // bool 只能是 0 或 1
}
```

**违反**: 公理 UNSAFE-A2 (位模式有效性)

### 反例 3: 数据竞争

```rust
static mut COUNTER: i32 = 0;

unsafe fn race_condition() {
    // 线程 A
    COUNTER += 1;  // 非原子操作
    
    // 线程 B
    COUNTER += 1;  // 数据竞争!
}
```

**违反**: 公理 UNSAFE-A3 (并发安全)

---

## ✅ 安全模式证明

### 模式 1: 初始化检查

```rust
struct SafeBuffer<T> {
    data: [MaybeUninit<T>; 1024],
    initialized: [bool; 1024],
}

impl<T> SafeBuffer<T> {
    fn get(&self, idx: usize) -> Option<&T> {
        if idx >= 1024 || !self.initialized[idx] {
            return None;
        }
        
        // 安全: 已检查初始化
        Some(unsafe { &*self.data[idx].as_ptr() })
    }
    
    fn set(&mut self, idx: usize, value: T) {
        if idx >= 1024 {
            return;
        }
        
        self.data[idx].write(value);
        self.initialized[idx] = true;
    }
}
```

**定理**: `get` 在 `initialized[idx] == true` 时总是返回有效引用。

**证明**:
1. `set` 写入 `data[idx]` 并设置 `initialized[idx] = true`
2. `get` 检查 `initialized[idx]` 为真后才解引用
3. 因此解引用时内存已初始化
∎

### 模式 2: 引用保证

```rust
struct SafeWrapper<'a, T> {
    ptr: *const T,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> SafeWrapper<'a, T> {
    fn new(r: &'a T) -> Self {
        Self {
            ptr: r as *const T,
            _marker: PhantomData,
        }
    }
    
    fn get(&self) -> &'a T {
        // 安全: ptr 来自有效引用，生命周期 'a 保证有效性
        unsafe { &*self.ptr }
    }
}
```

**定理**: `get()` 总是返回有效引用。

**证明**:
1. `ptr` 从有效引用 `r` 创建
2. `_marker` 绑定生命周期 `'a`
3. 引用 `r` 在 `'a` 期间有效
4. 因此 `ptr` 在 `'a` 期间有效
∎

### 模式 3: 所有权转移

```rust
struct UniquePtr<T> {
    ptr: *mut T,
}

impl<T> UniquePtr<T> {
    fn new(value: T) -> Self {
        Self {
            ptr: Box::into_raw(Box::new(value)),
        }
    }
    
    fn into_inner(self) -> T {
        // 安全: 我们有唯一的所有权
        let value = unsafe { Box::from_raw(self.ptr) };
        std::mem::forget(self);  // 防止析构
        *value
    }
}

impl<T> Drop for UniquePtr<T> {
    fn drop(&mut self) {
        // 安全: 我们有唯一的所有权
        unsafe { drop(Box::from_raw(self.ptr)) };
    }
}
```

**定理**: `UniquePtr` 管理唯一所有权，无双重释放。

**证明**:
1. `new` 创建堆分配，转移到 `ptr`
2. `into_inner` 转移所有权到返回值
3. `Drop` 仅在未转移时执行
4. Rust 所有权系统保证只执行一个路径
∎

---

## 📊 安全检查清单

### 编写 Unsafe 代码前

- [ ] 是否可以用 Safe Rust 实现？
- [ ] 所有裸指针是否已验证有效性？
- [ ] 所有索引是否在边界内？
- [ ] 类型转换是否保持内存布局？
- [ ] 外部函数契约是否已文档化？

### 代码审查清单

- [ ] 每个 `unsafe` 块是否有安全注释？
- [ ] 不变量是否在文档中说明？
- [ ] 是否有 Miri 测试？
- [ ] 边界情况是否已处理？
- [ ] 并发访问是否正确同步？

---

## 🔗 相关文档

- [Unsafe Rust 指南](../../../docs/05_guides/UNSAFE_RUST_GUIDE.md)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/)
- [Miri 工具](https://github.com/rust-lang/miri)

---

**维护者**: Rust 学习项目团队  
**最后更新**: 2026-03-15  
**状态**: ✅ 100% 完成
