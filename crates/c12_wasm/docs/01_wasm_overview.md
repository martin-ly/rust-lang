# C12 WebAssembly (WASM) 模块

> **模块**: C12 WASM 开发
> **难度**: 中级
> **Rust 版本**: 1.94.0+

---

## 📋 目录

- [C12 WebAssembly (WASM) 模块](#c12-webassembly-wasm-模块)
  - [📋 目录](#-目录)
  - [WASM 概述](#wasm-概述)
  - [wasm-bindgen](#wasm-bindgen)
  - [wasm-pack](#wasm-pack)

---

## WASM 概述

WebAssembly (Wasm) 是一种低级的字节码格式，可以在现代浏览器中高效运行。

```rust
// 简单的 WASM 函数
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}
```

---

## wasm-bindgen

wasm-bindgen 提供了 Rust 和 JavaScript 之间的桥梁：

```rust
use wasm_bindgen::prelude::*;
use web_sys::console;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

#[wasm_bindgen]
pub struct Calculator {
    value: f64,
}

#[wasm_bindgen]
impl Calculator {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self { value: 0.0 }
    }

    pub fn add(&mut self, n: f64) {
        self.value += n;
    }

    pub fn get_value(&self) -> f64 {
        self.value
    }
}
```

---

## wasm-pack

构建和发布 WASM 包：

```bash
# 初始化项目
wasm-pack new my-wasm-project

# 构建
wasm-pack build --target web
wasm-pack build --target bundler
wasm-pack build --target nodejs
```

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: ✅ 100% 完成
