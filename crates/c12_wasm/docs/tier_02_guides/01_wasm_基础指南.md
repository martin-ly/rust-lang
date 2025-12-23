# C12 WASM - WASM 基础指南

> **文档类型**: Tier 2 - 实践层
> **文档定位**: WASM 核心概念和实践指南
> **项目状态**: ✅ 完整完成
> **相关文档**: [项目概览](../tier_01_foundations/01_项目概览.md) | [主索引导航](../tier_01_foundations/02_主索引导航.md)

**最后更新**: 2025-10-30
**适用版本**: Rust 1.92.0+ / Edition 2024, WASM 2.0 + WASI 0.2

---

## 📋 目录

- [C12 WASM - WASM 基础指南](#c12-wasm---wasm-基础指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🌐 WASM 核心概念](#-wasm-核心概念)
    - [什么是 WebAssembly](#什么是-webassembly)
    - [WASM 的设计目标](#wasm-的设计目标)
    - [WASM 的执行模型](#wasm-的执行模型)
  - [📦 WASM 模块结构](#-wasm-模块结构)
    - [模块组成](#模块组成)
    - [线性内存](#线性内存)
    - [函数](#函数)
    - [表](#表)
    - [全局变量](#全局变量)
  - [🔧 WASM 指令集](#-wasm-指令集)
    - [数值操作](#数值操作)
    - [控制流](#控制流)
    - [内存操作](#内存操作)
  - [📝 WAT 文本格式](#-wat-文本格式)
    - [WAT 语法](#wat-语法)
    - [示例](#示例)
  - [🚀 实践示例](#-实践示例)
    - [示例 1: 简单计算](#示例-1-简单计算)
    - [示例 2: 字符串处理](#示例-2-字符串处理)
    - [示例 3: 数组操作](#示例-3-数组操作)
    - [示例 4: 结构体和方法](#示例-4-结构体和方法)
    - [示例 5: 完整的 WAT 文本格式示例](#示例-5-完整的-wat-文本格式示例)
  - [📚 相关资源](#-相关资源)

---

## 🎯 概述

本指南介绍 WebAssembly 的核心概念，包括：

- WASM 的设计目标和优势
- 模块结构和执行模型
- 指令集和操作
- WAT 文本格式
- 实践示例

---

## 🌐 WASM 核心概念

### 什么是 WebAssembly

WebAssembly (WASM) 是一种低级的二进制指令格式，设计为可移植的编译目标。

**核心特性**:

- ✅ **二进制格式**: 紧凑、高效
- ✅ **执行速度快**: 接近原生代码性能
- ✅ **安全性高**: 沙箱执行环境
- ✅ **跨平台**: 一次编写，到处运行

### WASM 的设计目标

1. **性能**: 接近原生代码的执行速度
2. **安全性**: 沙箱执行，内存安全
3. **可移植性**: 跨平台运行
4. **可读性**: 支持文本格式（WAT）

### WASM 的执行模型

**栈式虚拟机**:

- 使用栈存储操作数
- 指令从栈顶弹出操作数
- 结果推回栈顶

**示例**:

```wat
;; 计算 2 + 3
i32.const 2  ;; 推送 2 到栈
i32.const 3  ;; 推送 3 到栈
i32.add      ;; 弹出两个值，相加，推送结果
```

---

## 📦 WASM 模块结构

### 模块组成

一个 WASM 模块包含：

1. **函数**: 定义和导入的函数
2. **内存**: 线性内存定义
3. **表**: 函数引用表
4. **全局变量**: 全局状态

### 线性内存

**定义**: 连续的内存空间，从 0 开始。

**特性**:

- 可以动态增长
- 大小限制为 4GB
- JavaScript 可以访问

**示例**:

```wat
(memory 1)  ;; 初始大小 1 页 (64KB)
```

### 函数

**定义**: 可执行的代码单元。

**类型**: 函数签名（参数类型、返回类型）

**示例**:

```wat
(func $add (param $a i32) (param $b i32) (result i32)
  local.get $a
  local.get $b
  i32.add
)
```

### 表

**定义**: 存储函数引用的表。

**用途**: 实现间接调用和动态链接。

### 全局变量

**定义**: 模块级别的全局状态。

**特性**: 可以是可变或不可变的。

---

## 🔧 WASM 指令集

### 数值操作

**算术运算**:

- `i32.add`, `i32.sub`, `i32.mul`, `i32.div`
- `f32.add`, `f32.sub`, `f32.mul`, `f32.div`

**比较操作**:

- `i32.eq`, `i32.ne`, `i32.lt`, `i32.gt`

### 控制流

**条件分支**:

```wat
block $label
  ;; 条件
  if
    ;; true 分支
  else
    ;; false 分支
  end
end
```

**循环**:

```wat
loop $label
  ;; 循环体
  br_if $label  ;; 条件分支回循环开始
end
```

### 内存操作

**加载**:

- `i32.load`: 从内存加载 32 位整数
- `i64.load`: 从内存加载 64 位整数

**存储**:

- `i32.store`: 存储 32 位整数到内存
- `i64.store`: 存储 64 位整数到内存

---

## 📝 WAT 文本格式

### WAT 语法

WAT (WebAssembly Text) 是 WASM 的文本表示格式。

**基本结构**:

```wat
(module
  ;; 函数定义
  (func $add (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.add
  )

  ;; 导出函数
  (export "add" (func $add))
)
```

### 示例

**完整示例**:

```wat
(module
  ;; 内存定义
  (memory 1)

  ;; 函数：计算斐波那契数
  (func $fib (param $n i32) (result i32)
    (if (result i32)
      (i32.le_s (local.get $n) (i32.const 1))
      (then (i32.const 1))
      (else
        (i32.add
          (call $fib (i32.sub (local.get $n) (i32.const 1)))
          (call $fib (i32.sub (local.get $n) (i32.const 2)))
        )
      )
    )
  )

  ;; 导出函数
  (export "fib" (func $fib))
)
```

---

## 🚀 实践示例

### 示例 1: 简单计算

```rust
use wasm_bindgen::prelude::*;

/// 加法函数
///
/// 这是一个简单的示例，展示如何将 Rust 函数暴露给 JavaScript
///
/// # 参数
/// - `a`: 第一个加数
/// - `b`: 第二个加数
///
/// # 返回值
/// 返回两个数的和
///
/// # JavaScript 使用示例
/// ```javascript
/// import { add } from './pkg/hello_wasm';
/// const result = add(2, 3); // 5
/// ```
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

**编译和使用**:

```bash
# 编译为 WASM
wasm-pack build --target web

# 在 JavaScript 中使用
import { add } from './pkg/hello_wasm.js';
console.log(add(2, 3)); // 输出: 5
```

### 示例 2: 字符串处理

```rust
use wasm_bindgen::prelude::*;

/// 问候函数
///
/// 展示如何处理字符串参数和返回值
///
/// # 参数
/// - `name`: 要问候的名字
///
/// # 返回值
/// 返回格式化的问候字符串
///
/// # 注意
/// Rust 的 `&str` 会自动转换为 JavaScript 的 `string` 类型
#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

/// 反转字符串
///
/// # 参数
/// - `s`: 要反转的字符串
///
/// # 返回值
/// 返回反转后的字符串
///
/// # 性能说明
/// 时间复杂度 O(n)，其中 n 是字符串长度
#[wasm_bindgen]
pub fn reverse_string(s: &str) -> String {
    s.chars().rev().collect()
}
```

### 示例 3: 数组操作

```rust
use wasm_bindgen::prelude::*;

/// 计算数组元素的和
///
/// # 参数
/// - `arr`: 整数数组切片
///
/// # 返回值
/// 返回数组中所有元素的和
///
/// # 注意
/// 在 JavaScript 中需要使用 TypedArray 传递数组：
/// ```javascript
/// const arr = new Int32Array([1, 2, 3, 4, 5]);
/// const sum = sum_array(arr); // 15
/// ```
#[wasm_bindgen]
pub fn sum_array(arr: &[i32]) -> i32 {
    arr.iter().sum()
}

/// 计算数组的平均值
///
/// # 参数
/// - `numbers`: 浮点数数组
///
/// # 返回值
/// 返回平均值，如果数组为空则返回 0.0
///
/// # 性能说明
/// 时间复杂度 O(n)，需要遍历整个数组一次
#[wasm_bindgen]
pub fn calculate_average(numbers: &[f64]) -> f64 {
    if numbers.is_empty() {
        return 0.0;
    }
    let sum: f64 = numbers.iter().sum();
    sum / (numbers.len() as f64)
}

/// 查找数组中的最大值
///
/// # 参数
/// - `numbers`: 整数数组
///
/// # 返回值
/// 返回最大值，如果数组为空则返回 None（JavaScript 中为 undefined）
#[wasm_bindgen]
pub fn find_max(numbers: &[i32]) -> Option<i32> {
    numbers.iter().max().copied()
}
```

**JavaScript 使用示例**:

```javascript
import { sum_array, calculate_average, find_max } from './pkg/hello_wasm.js';

// 整数数组求和
const intArray = new Int32Array([1, 2, 3, 4, 5]);
console.log(sum_array(intArray)); // 15

// 浮点数数组平均值
const floatArray = new Float64Array([1.5, 2.5, 3.5]);
console.log(calculate_average(floatArray)); // 2.5

// 查找最大值
const maxArray = new Int32Array([10, 5, 20, 15]);
console.log(find_max(maxArray)); // 20
```

### 示例 4: 结构体和方法

```rust
use wasm_bindgen::prelude::*;

/// 计数器结构体
///
/// 展示如何在 Rust 和 JavaScript 之间共享状态
///
/// # 示例
/// ```javascript
/// import { Counter } from './pkg/hello_wasm';
/// const counter = new Counter();
/// counter.increment();
/// console.log(counter.value()); // 1
/// ```
#[wasm_bindgen]
pub struct Counter {
    /// 内部计数值
    value: i32,
}

#[wasm_bindgen]
impl Counter {
    /// 创建新的计数器实例
    ///
    /// 使用 `#[wasm_bindgen(constructor)]` 标记构造函数
    #[wasm_bindgen(constructor)]
    pub fn new() -> Counter {
        Counter { value: 0 }
    }

    /// 增加计数器值
    ///
    /// 注意需要使用 `&mut self` 来修改内部状态
    #[wasm_bindgen]
    pub fn increment(&mut self) {
        self.value += 1;
    }

    /// 获取当前计数器值
    ///
    /// 使用 `#[wasm_bindgen(getter)]` 可以创建 JavaScript 的 getter
    #[wasm_bindgen(getter)]
    pub fn value(&self) -> i32 {
        self.value
    }
}
```

### 示例 5: 完整的 WAT 文本格式示例

```wat
;; 这是一个完整的 WASM 模块示例
;; 展示了模块的基本结构

(module
  ;; 内存定义：初始大小 1 页 (64KB)
  (memory 1)

  ;; 全局变量：计数器
  (global $counter (mut i32) (i32.const 0))

  ;; 函数：计算两个数的和
  (func $add (param $a i32) (param $b i32) (result i32)
    local.get $a    ;; 获取第一个参数
    local.get $b    ;; 获取第二个参数
    i32.add         ;; 相加
  )

  ;; 函数：计算斐波那契数（递归）
  (func $fib (param $n i32) (result i32)
    ;; 如果 n <= 1，返回 1
    (if (result i32)
      (i32.le_s (local.get $n) (i32.const 1))
      (then (i32.const 1))
      (else
        ;; 否则返回 fib(n-1) + fib(n-2)
        (i32.add
          (call $fib (i32.sub (local.get $n) (i32.const 1)))
          (call $fib (i32.sub (local.get $n) (i32.const 2)))
        )
      )
    )
  )

  ;; 导出函数，供外部调用
  (export "add" (func $add))
  (export "fib" (func $fib))
)
```

**使用 wat2wasm 编译**:

```bash
# 安装 wat2wasm（Binaryen 工具集的一部分）
# npm install -g wat2wasm

# 编译 WAT 为 WASM
wat2wasm example.wat -o example.wasm

# 运行（使用 wasmtime）
wasmtime example.wasm --invoke add 2 3  # 输出: 5
wasmtime example.wasm --invoke fib 10   # 输出: 89
```

---

## 📚 相关资源

- [项目概览](../tier_01_foundations/01_项目概览.md) - 了解整体架构
- [Rust 编译 WASM](./02_rust_编译_wasm.md) - 学习编译流程
- [主索引导航](../tier_01_foundations/02_主索引导航.md) - 找到学习路径

**外部资源**:

- [WebAssembly.org](https://webassembly.org/)
- [WASM 规范](https://webassembly.github.io/spec/)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-30
**适用版本**: Rust 1.92.0+ / Edition 2024, WASM 2.0 + WASI 0.2
