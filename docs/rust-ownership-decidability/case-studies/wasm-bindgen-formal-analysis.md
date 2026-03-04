# wasm-bindgen 形式化分析

> **主题**: Rust/WASM与JavaScript的安全互操作
>
> **形式化框架**: 边界类型转换 + 内存隔离
>
> **参考**: wasm-bindgen Documentation

---

## 目录

- [wasm-bindgen 形式化分析](#wasm-bindgen-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 绑定生成](#2-绑定生成)
    - [2.1 导出到JS](#21-导出到js)
    - [定理 2.1 (导出安全性)](#定理-21-导出安全性)
    - [2.2 从JS导入](#22-从js导入)
    - [定理 2.2 (导入类型安全)](#定理-22-导入类型安全)
  - [3. 内存管理](#3-内存管理)
    - [定理 3.1 (所有权转移)](#定理-31-所有权转移)
  - [4. 类型转换](#4-类型转换)
    - [定理 4.1 (可转换类型)](#定理-41-可转换类型)
  - [5. 异常处理](#5-异常处理)
    - [定理 5.1 (panic转异常)](#定理-51-panic转异常)
  - [6. 反例](#6-反例)
    - [反例 6.1 (生命周期陷阱)](#反例-61-生命周期陷阱)
    - [反例 6.2 (闭包泄漏)](#反例-62-闭包泄漏)

---

## 1. 引言

wasm-bindgen提供:

- Rust与JavaScript无缝互操作
- 自动绑定生成
- 类型安全的边界
- 内存管理桥接

---

## 2. 绑定生成

### 2.1 导出到JS

### 定理 2.1 (导出安全性)

> wasm-bindgen确保导出的Rust函数遵守WASM边界。

```rust
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

**生成**:

```javascript
export function add(a, b) {
    // 类型检查
    // WASM调用
    return wasm.add(a, b);
}
```

∎

### 2.2 从JS导入

### 定理 2.2 (导入类型安全)

> 导入的JS函数通过类型声明检查。

```rust
#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);  // 类型约束
}
```

**运行时检查**:

- 参数类型验证
- 返回值解包

∎

---

## 3. 内存管理

### 定理 3.1 (所有权转移)

> 跨边界传递数据时明确所有权。

```rust
#[wasm_bindgen]
pub struct MyData {
    data: Vec<u8>,
}

#[wasm_bindgen]
impl MyData {
    pub fn new() -> MyData { ... }
    // Rust管理内存，JS通过句柄访问
}
```

**形式化**:

$$
\text{JS侧}: \text{handle} \leftrightarrow \text{Rust侧}: \text{Box<T>}
$$

∎

---

## 4. 类型转换

### 定理 4.1 (可转换类型)

| Rust | JavaScript |
|------|------------|
| i32, i64, f32, f64 | number, bigint |
| String | string |
| `Vec<u8>` | Uint8Array |
| JsValue | any |

∎

---

## 5. 异常处理

### 定理 5.1 (panic转异常)

> Rust panic转换为JS异常。

```rust
#[wasm_bindgen]
pub fn may_panic() {
    panic!("error");  // 转换为JS Error
}
```

```javascript
try {
    may_panic();
} catch (e) {
    // e是WASM panic消息
}
```

∎

---

## 6. 反例

### 反例 6.1 (生命周期陷阱)

```rust
// 错误: 返回引用
#[wasm_bindgen]
pub fn get_slice(data: &[u8]) -> &[u8] {
    &data[0..10]  // 生命周期无法跨边界!
}

// 正确: 返回拥有数据
#[wasm_bindgen]
pub fn get_vec(data: &[u8]) -> Vec<u8> {
    data[0..10].to_vec()
}
```

### 反例 6.2 (闭包泄漏)

```rust
#[wasm_bindgen]
pub fn set_callback(f: &Closure<dyn FnMut()>) {
    // Closure可能需要在JS存活
    // 需手动管理内存
}
```

---

*文档版本: 1.0.0*
*定理数量: 7个*
