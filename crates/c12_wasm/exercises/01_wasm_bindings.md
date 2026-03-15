# C12 WASM 绑定练习

> 难度: 中级 | 预计时间: 45 分钟

---

## 🎯 练习目标

- 掌握 wasm-bindgen 使用
- 理解 Rust 与 JavaScript 互操作
- 实现 DOM 操作

---

## 练习 1: DOM 操作

实现简单的 DOM 操作。

```rust
use wasm_bindgen::prelude::*;
use web_sys::Document;

/// 设置元素的文本内容
#[wasm_bindgen]
pub fn set_element_text(element_id: &str, text: &str) -> Result<(), JsValue> {
    let window = web_sys::window().unwrap();
    let document = window.document().unwrap();

    if let Some(element) = document.get_element_by_id(element_id) {
        element.set_text_content(Some(text));
        Ok(())
    } else {
        Err(JsValue::from_str(&format!("Element '{}' not found", element_id)))
    }
}

/// 创建新元素并添加到文档
#[wasm_bindgen]
pub fn create_element(tag: &str, text: &str) -> Result<(), JsValue> {
    let window = web_sys::window().unwrap();
    let document = window.document().unwrap();
    let body = document.body().unwrap();

    let element = document.create_element(tag)?;
    element.set_text_content(Some(text));
    body.append_child(&element)?;

    Ok(())
}
```

**HTML 使用示例**:

```html
<!DOCTYPE html>
<html>
<head>
    <title>WASM Demo</title>
</head>
<body>
    <div id="output">Loading...</div>
    <button onclick="updateText()">Update</button>

    <script type="module">
        import init, { set_element_text, create_element } from './pkg/wasm_app.js';

        await init();

        window.updateText = () => {
            set_element_text('output', 'Hello from Rust!');
            create_element('p', 'New paragraph added');
        };
    </script>
</body>
</html>
```

---

## 练习 2: Canvas 绘图

在 Canvas 上绘图。

```rust
use wasm_bindgen::prelude::*;
use web_sys::{CanvasRenderingContext2d, HtmlCanvasElement};

/// 绘制矩形
#[wasm_bindgen]
pub fn draw_rect(canvas_id: &str, x: f64, y: f64, width: f64, height: f64) -> Result<(), JsValue> {
    let document = web_sys::window().unwrap().document().unwrap();
    let canvas = document
        .get_element_by_id(canvas_id)
        .unwrap()
        .dyn_into::<HtmlCanvasElement>()?;

    let context = canvas
        .get_context("2d")?
        .unwrap()
        .dyn_into::<CanvasRenderingContext2d>()?;

    context.fill_rect(x, y, width, height);

    Ok(())
}

/// 绘制圆形
#[wasm_bindgen]
pub fn draw_circle(canvas_id: &str, x: f64, y: f64, radius: f64) -> Result<(), JsValue> {
    let document = web_sys::window().unwrap().document().unwrap();
    let canvas = document
        .get_element_by_id(canvas_id)
        .unwrap()
        .dyn_into::<HtmlCanvasElement>()?;

    let context = canvas
        .get_context("2d")?
        .unwrap()
        .dyn_into::<CanvasRenderingContext2d>()?;

    context.begin_path();
    context.arc(x, y, radius, 0.0, std::f64::consts::PI * 2.0)?;
    context.fill();

    Ok(())
}

/// 清除画布
#[wasm_bindgen]
pub fn clear_canvas(canvas_id: &str) -> Result<(), JsValue> {
    let document = web_sys::window().unwrap().document().unwrap();
    let canvas = document
        .get_element_by_id(canvas_id)
        .unwrap()
        .dyn_into::<HtmlCanvasElement>()?;

    let context = canvas
        .get_context("2d")?
        .unwrap()
        .dyn_into::<CanvasRenderingContext2d>()?;

    context.clear_rect(0.0, 0.0, canvas.width() as f64, canvas.height() as f64);

    Ok(())
}
```

---

## 练习 3: 计算器应用

实现完整的计算器。

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct Calculator {
    current_value: f64,
    memory: f64,
}

#[wasm_bindgen]
impl Calculator {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            current_value: 0.0,
            memory: 0.0,
        }
    }

    pub fn add(&mut self, value: f64) -> f64 {
        self.current_value += value;
        self.current_value
    }

    pub fn subtract(&mut self, value: f64) -> f64 {
        self.current_value -= value;
        self.current_value
    }

    pub fn multiply(&mut self, value: f64) -> f64 {
        self.current_value *= value;
        self.current_value
    }

    pub fn divide(&mut self, value: f64) -> Result<f64, JsValue> {
        if value == 0.0 {
            return Err(JsValue::from_str("Division by zero"));
        }
        self.current_value /= value;
        Ok(self.current_value)
    }

    pub fn clear(&mut self) {
        self.current_value = 0.0;
    }

    pub fn get_value(&self) -> f64 {
        self.current_value
    }

    pub fn memory_store(&mut self) {
        self.memory = self.current_value;
    }

    pub fn memory_recall(&mut self) -> f64 {
        self.current_value = self.memory;
        self.current_value
    }

    pub fn memory_clear(&mut self) {
        self.memory = 0.0;
    }
}
```

---

## 📚 相关文档

- [C12 WASM 模块](../README.md)
- [wasm-bindgen 指南](https://rustwasm.github.io/wasm-bindgen/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
