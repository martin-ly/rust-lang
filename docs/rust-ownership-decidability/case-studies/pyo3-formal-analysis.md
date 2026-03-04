# PyO3 Python绑定形式化分析

> **主题**: Rust-Python互操作
> **形式化框架**: Python C-API + GIL + 类型转换
> **参考**: PyO3 Documentation (<https://pyo3.rs>)

---

## 目录

- [PyO3 Python绑定形式化分析](#pyo3-python绑定形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. GIL管理](#2-gil管理)
    - [定义 GIL-1 ( GIL抽象 )](#定义-gil-1--gil抽象-)
    - [定义 GIL-2 ( 自动释放 )](#定义-gil-2--自动释放-)
    - [定理 GIL-T1 ( 安全释放 )](#定理-gil-t1--安全释放-)
  - [3. 类型转换](#3-类型转换)
    - [定义 CONV-1 ( 基本类型 )](#定义-conv-1--基本类型-)
    - [定义 CONV-2 ( PyObject )](#定义-conv-2--pyobject-)
  - [4. 导出模块](#4-导出模块)
    - [定义 MODULE-1 ( 模块定义 )](#定义-module-1--模块定义-)
    - [定义 MODULE-2 ( 函数导出 )](#定义-module-2--函数导出-)
  - [5. Python对象](#5-python对象)
    - [定义 PYOBJ-1 ( 类定义 )](#定义-pyobj-1--类定义-)
    - [定理 PYOBJ-T1 ( 内存安全 )](#定理-pyobj-t1--内存安全-)
  - [6. 异常处理](#6-异常处理)
    - [定义 EXCEPT-1 ( Rust结果传播 )](#定义-except-1--rust结果传播-)
    - [定义 EXCEPT-2 ( Python异常转换 )](#定义-except-2--python异常转换-)
  - [7. 定理与证明](#7-定理与证明)
    - [定理 PYO3-T1 ( GIL安全 )](#定理-pyo3-t1--gil安全-)
    - [定理 PYO3-T2 ( 类型转换安全 )](#定理-pyo3-t2--类型转换安全-)
  - [8. 代码示例](#8-代码示例)
    - [示例1: 基础模块](#示例1-基础模块)
    - [示例2: 类导出](#示例2-类导出)
    - [示例3: 处理Python对象](#示例3-处理python对象)

---

## 1. 引言

PyO3功能：

- Rust写Python扩展
- Python调用Rust函数
- 自动类型转换
- GIL安全抽象

---

## 2. GIL管理

### 定义 GIL-1 ( GIL抽象 )

```rust
Python::with_gil(|py| {
    // GIL held here
});
```

**形式化**:

$$
\text{GIL} : \text{Python} \to \text{Token} \mid \text{block until acquired}
$$

### 定义 GIL-2 ( 自动释放 )

$$
\text{drop}(\text{GILGuard}) \to \text{release\_gil}
$$

### 定理 GIL-T1 ( 安全释放 )

GIL在作用域结束时释放。

$$
\forall py : \text{Python}.\ py \text{ valid } \iff \text{GIL held}
$$

---

## 3. 类型转换

### 定义 CONV-1 ( 基本类型 )

| Rust | Python | 转换 |
| :--- | :--- | :--- |
| i32/i64 | int | FromPyObject |
| f64 | float | FromPyObject |
| String | str | FromPyObject |
| bool | bool | FromPyObject |
| Vec<T> | list | FromPyObject |
| HashMap<K,V> | dict | FromPyObject |

### 定义 CONV-2 ( PyObject )

```rust
let obj: &PyAny = ...;
let extracted: i32 = obj.extract()?;
```

---

## 4. 导出模块

### 定义 MODULE-1 ( 模块定义 )

```rust
#[pymodule]
fn mymodule(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(my_func, m)?)?;
    m.add_class::<MyClass>()?;
    Ok(())
}
```

### 定义 MODULE-2 ( 函数导出 )

```rust
#[pyfunction]
fn my_func(a: i32, b: i32) -> i32 { a + b }
```

---

## 5. Python对象

### 定义 PYOBJ-1 ( 类定义 )

```rust
#[pyclass]
struct MyClass {
    #[pyo3(get, set)]
    value: i32,
}

#[pymethods]
impl MyClass {
    #[new]
    fn new(value: i32) -> Self { MyClass { value } }

    fn method(&self) -> i32 { self.value * 2 }
}
```

### 定理 PYOBJ-T1 ( 内存安全 )

Python对象生命周期由引用计数管理。

$$
\text{Py<T>} \to \text{inc\_ref} \land \text{drop} \to \text{dec\_ref}
$$

---

## 6. 异常处理

### 定义 EXCEPT-1 ( Rust结果传播 )

```rust
#[pyfunction]
fn may_fail() -> PyResult<i32> {
    Err(PyRuntimeError::new_err("error"))
}
```

### 定义 EXCEPT-2 ( Python异常转换 )

$$
\text{panic!} \to \text{Python exception} \to \text{traceback}
$$

---

## 7. 定理与证明

### 定理 PYO3-T1 ( GIL安全 )

无GIL时不访问Python对象。

$$
\neg\text{GIL} \to \text{no\_PyObject\_access}
$$

**证明**: Python<'py> token保证。$\square$

### 定理 PYO3-T2 ( 类型转换安全 )

无效转换返回Err而非UB。

$$
\text{extract}() = \text{Err} \mid \text{Ok}(v \text{ with correct type})
$$

---

## 8. 代码示例

### 示例1: 基础模块

```rust
use pyo3::prelude::*;

/// Formats the sum of two numbers as string.
#[pyfunction]
fn sum_as_string(a: usize, b: usize) -> PyResult<String> {
    Ok((a + b).to_string())
}

/// A Python module implemented in Rust.
#[pymodule]
fn string_sum(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(sum_as_string, m)?)?;
    Ok(())
}
```

### 示例2: 类导出

```rust
use pyo3::prelude::*;

#[pyclass]
struct Counter {
    count: u32,
}

#[pymethods]
impl Counter {
    #[new]
    fn new() -> Self {
        Counter { count: 0 }
    }

    fn increment(&mut self) {
        self.count += 1;
    }

    fn get(&self) -> u32 {
        self.count
    }
}

#[pymodule]
fn counter_mod(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Counter>()?;
    Ok(())
}
```

### 示例3: 处理Python对象

```rust
use pyo3::prelude::*;
use pyo3::types::PyList;

#[pyfunction]
fn double_list(list: &PyList) -> PyResult<Vec<i64>> {
    let mut result = Vec::with_capacity(list.len());

    for item in list.iter() {
        let val: i64 = item.extract()?;
        result.push(val * 2);
    }

    Ok(result)
}

#[pyfunction]
fn call_python_callback(callback: &PyAny, value: i32) -> PyResult<i32> {
    let result: i32 = callback.call1((value,))?.extract()?;
    Ok(result)
}
```

---

**维护者**: Rust-Python Interop Formal Methods Team
**创建日期**: 2026-03-05
**PyO3版本**: 0.20+
**状态**: ✅ 已对齐
