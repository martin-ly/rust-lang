# 扩展主题：Const泛型与编译期计算

> 深入分析Rust的常量系统和编译期计算能力

---

## 1. Const泛型概述

### 1.1 什么是Const泛型

Const泛型允许类型参数化为**编译期常量值**：

```rust
// 类型参数化为常量N
struct Array<T, const N: usize> {
    data: [T; N],
}

// 使用
let arr: Array<i32, 5> = Array { data: [0; 5] };
```

### 1.2 与普通泛型的区别

| 特性 | 普通泛型 `<T>` | Const泛型 `<const N: usize>` |
|------|----------------|------------------------------|
| 参数 | 类型 | 编译期常量值 |
| 单态化 | 为每种类型生成代码 | 为每个不同值生成代码 |
| 运行时开销 | 无 | 无 |
| 使用场景 | 抽象数据类型 | 固定大小数据结构 |

---

## 2. Const泛型的所有权语义

### 2.1 所有权在编译期确定

```rust
struct FixedVec<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    len: usize,
}

impl<T, const N: usize> FixedVec<T, N> {
    // 容量是编译期常量
    const fn capacity() -> usize {
        N
    }
    
    // 所有权语义与普通Vec相同
    fn push(&mut self, value: T) -> Result<(), T> {
        if self.len < N {
            self.data[self.len].write(value);
            self.len += 1;
            Ok(())
        } else {
            Err(value)
        }
    }
}
```

### 2.2 编译期内存布局

```rust
// 不同N值产生不同类型
let v1: FixedVec<i32, 8> = FixedVec::new();
let v2: FixedVec<i32, 16> = FixedVec::new();

// 编译器生成两个不同版本
// FixedVec<i32, 8>  : data占 8 * 4 = 32 字节
// FixedVec<i32, 16> : data占 16 * 4 = 64 字节
```

---

## 3. Const函数

### 3.1 Const函数的限制

```rust
const fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

const FIB_10: u32 = fibonacci(10); // 编译期计算
```

**限制：**
- 不能分配堆内存
- 不能调用非const函数
- 不能涉及运行时IO
- 不能有不安全的操作（部分）

### 3.2 Const函数与所有权

```rust
const fn create_array<T: Copy, const N: usize>(val: T) -> [T; N] {
    [val; N]  // 数组重复表达式
}

// 使用
const ARR: [i32; 10] = create_array(42);
```

**关键点：**
- const函数内所有权规则相同
- 但只能操作编译期已知值

---

## 4. 编译期计算能力

### 4.1 类型级别计算

```rust
// 编译期类型操作
struct TypeLevel<const N: usize>;

impl<const N: usize> TypeLevel<N> {
    const VALUE: usize = N;
    
    // 编译期算术
    type Double = TypeLevel<{ N * 2 }>;
    type Increment = TypeLevel<{ N + 1 }>;
}

// 使用
use std::marker::PhantomData;

struct Array<T, const N: usize> {
    _marker: PhantomData<TypeLevel<N>>,
    data: [T; N],
}
```

### 4.2 编译期断言

```rust
// 编译期检查
const fn assert_positive(n: i32) {
    assert!(n > 0, "n must be positive");
}

const N: i32 = 5;
const _: () = assert_positive(N); // 编译期检查通过

// const M: i32 = -1;
// const _: () = assert_positive(M); // 编译错误！
```

---

## 5. 高级应用

### 5.1 编译期状态机

```rust
// 编译期状态机验证
struct StateMachine<const STATE: u32>;

impl StateMachine<0> {
    const fn transition(self) -> StateMachine<1> {
        StateMachine
    }
}

impl StateMachine<1> {
    const fn transition(self) -> StateMachine<2> {
        StateMachine
    }
}

// 编译期验证状态转换
const SM: StateMachine<0> = StateMachine;
const SM2: StateMachine<1> = SM.transition();
// const SM3: StateMachine<3> = SM2.transition(); // 编译错误！
```

### 5.2 零成本抽象

```rust
// 编译期矩阵大小
struct Matrix<T, const ROWS: usize, const COLS: usize> {
    data: [[T; COLS]; ROWS],
}

impl<T: Default + Copy, const R: usize, const C: usize> Matrix<T, R, C> {
    fn new() -> Self {
        Self {
            data: [[T::default(); C]; R],
        }
    }
    
    // 编译期检查矩阵乘法维度
    fn multiply<const C2: usize>(
        &self,
        other: &Matrix<T, C, C2>
    ) -> Matrix<T, R, C2>
    where
        T: std::ops::Mul<Output = T> + std::ops::Add<Output = T>,
    {
        // 编译期保证维度匹配
        let mut result = Matrix::new();
        // ... 乘法实现
        result
    }
}

// 使用
let m1: Matrix<f64, 3, 4> = Matrix::new();
let m2: Matrix<f64, 4, 5> = Matrix::new();
let m3 = m1.multiply(&m2); // Matrix<f64, 3, 5>
// let m4 = m2.multiply(&m1); // 编译错误：维度不匹配！
```

---

## 6. 形式化视角

### 6.1 编译期计算的语义

```text
编译期计算可以看作：
- 在类型系统层面进行的求值
- 不生成运行时代码
- 结果作为类型的一部分
```

### 6.2 可判定性

| 计算 | 可判定性 | 限制 |
|------|----------|------|
| 常量表达式 | ✅ 完全可判定 | 无循环/递归限制 |
| Const泛型 | ✅ 可判定 | 整数/布尔/字符 |
| 类型操作 | ✅ 可判定 | 受限集合 |
| 通用编译期计算 | ⚠️ 受限 | Turing不完备（有意为之） |

### 6.3 与C++模板的比较

| 特性 | Rust Const泛型 | C++模板 |
|------|----------------|---------|
| 类型检查 | 实例化前 | 实例化后 |
| 错误信息 | 清晰 | 复杂 |
| 编译时间 | 可控 | 可能爆炸 |
| 图灵完备 | 否（有意） | 是 |

---

## 7. 实践模式

### 7.1 固定大小缓冲区

```rust
struct Buffer<const SIZE: usize> {
    data: [u8; SIZE],
    pos: usize,
}

impl<const SIZE: usize> Buffer<SIZE> {
    const fn new() -> Self {
        Self {
            data: [0; SIZE],
            pos: 0,
        }
    }
    
    fn write(&mut self, data: &[u8]) -> usize {
        let len = data.len().min(SIZE - self.pos);
        self.data[self.pos..self.pos + len].copy_from_slice(&data[..len]);
        self.pos += len;
        len
    }
}

// 不同类型
type SmallBuffer = Buffer<64>;
type LargeBuffer = Buffer<4096>;
```

### 7.2 编译期配置

```rust
struct Config<const DEBUG: bool>;

impl Config<true> {
    fn log(&self, msg: &str) {
        println!("[DEBUG] {}", msg);
    }
}

impl Config<false> {
    fn log(&self, _msg: &str) {
        // 空操作，编译期优化掉
    }
}

// 编译期选择实现
const DEBUG_MODE: bool = cfg!(debug_assertions);
type AppConfig = Config<DEBUG_MODE>;
```

---

## 8. 总结

### 核心概念

1. **Const泛型**：类型参数化为编译期常量
2. **Const函数**：编译期执行的纯函数
3. **编译期计算**：在类型系统层面求值
4. **零成本**：编译期计算不生成运行时开销

### 最佳实践

1. 使用const泛型表示固定大小的数据结构
2. 利用const函数进行编译期验证
3. 结合PhantomData进行类型级别编程
4. 注意const函数的限制

---

*Const泛型是Rust类型系统的强大扩展，使编译期计算和类型级别编程成为可能。*
