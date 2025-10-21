# Rust WebAssembly 开发指南 2025

> **最后更新**: 2025-10-20  
> **Rust 版本**: 1.83+  
> **难度**: ⭐⭐⭐⭐ (中高级)

## 📋 目录1

- [Rust WebAssembly 开发指南 2025](#rust-webassembly-开发指南-2025)
  - [📋 目录1](#-目录1)
  - [1. WebAssembly 基础](#1-webassembly-基础)
    - [1.1 为什么选择 WebAssembly?](#11-为什么选择-webassembly)
    - [1.2 环境设置](#12-环境设置)
    - [1.3 第一个 WASM 项目](#13-第一个-wasm-项目)
  - [2. wasm-bindgen 深入](#2-wasm-bindgen-深入)
    - [2.1 类型转换](#21-类型转换)
    - [2.2 与 JavaScript 互操作](#22-与-javascript-互操作)
    - [2.3 异步操作](#23-异步操作)
  - [3. Yew 框架 (React-like)](#3-yew-框架-react-like)
    - [3.1 项目设置](#31-项目设置)
    - [3.2 基础组件](#32-基础组件)
    - [3.3 Hooks](#33-hooks)
  - [4. Leptos 框架 (Next-gen)](#4-leptos-框架-next-gen)
    - [4.1 项目设置](#41-项目设置)
    - [4.2 响应式组件](#42-响应式组件)
  - [5. Tauri 桌面应用](#5-tauri-桌面应用)
    - [5.1 项目创建](#51-项目创建)
    - [5.2 Rust 后端](#52-rust-后端)
    - [5.3 前端调用](#53-前端调用)
  - [6. 与 JavaScript 互操作](#6-与-javascript-互操作)
    - [6.1 传递复杂数据](#61-传递复杂数据)
    - [6.2 回调函数](#62-回调函数)
  - [7. 性能优化](#7-性能优化)
    - [7.1 减少二进制大小](#71-减少二进制大小)
    - [7.2 懒加载](#72-懒加载)
    - [7.3 Web Workers](#73-web-workers)
  - [8. 实战案例](#8-实战案例)
    - [8.1 图像处理](#81-图像处理)
    - [8.2 数据可视化](#82-数据可视化)
  - [9. 最佳实践](#9-最佳实践)
  - [10. 常见陷阱](#10-常见陷阱)
  - [11. 参考资源](#11-参考资源)

---

## 1. WebAssembly 基础

### 1.1 为什么选择 WebAssembly?

**性能对比 (计算密集型任务):**

| 语言/平台    | 执行时间 | 相对性能 |
|--------------|----------|----------|
| Native Rust  | 100ms    | 100%     |
| WebAssembly  | 120ms    | 83%      |
| JavaScript   | 800ms    | 12.5%    |

**优势:**

- ⚡ **高性能**: 接近原生速度 (80-90%)
- 🔒 **类型安全**: 编译时检查
- 📦 **二进制格式**: 体积小，加载快
- 🌍 **跨平台**: 在浏览器、Node.js、边缘计算中运行
- 🔧 **与 JS 互操作**: 无缝集成现有 Web 生态

### 1.2 环境设置

**安装工具链:**

```bash
# 1. 安装 wasm-pack (打包工具)
cargo install wasm-pack

# 2. 添加 wasm32 目标
rustup target add wasm32-unknown-unknown

# 3. 安装 trunk (开发服务器)
cargo install trunk

# 4. 安装 cargo-generate (项目模板)
cargo install cargo-generate
```

### 1.3 第一个 WASM 项目

**创建项目:**

```bash
cargo new --lib hello-wasm
cd hello-wasm
```

**Cargo.toml:**

```toml
[package]
name = "hello-wasm"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib"]

[dependencies]
wasm-bindgen = "0.2"

[dev-dependencies]
wasm-bindgen-test = "0.3"
```

**src/lib.rs:**

```rust
use wasm_bindgen::prelude::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 导出到 JavaScript
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[wasm_bindgen]
pub fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}
```

**构建:**

```bash
# 构建为 wasm
wasm-pack build --target web

# 生成的文件:
# - pkg/hello_wasm_bg.wasm (WASM 二进制)
# - pkg/hello_wasm.js (JavaScript 包装)
# - pkg/hello_wasm.d.ts (TypeScript 类型定义)
```

**HTML 中使用:**

```html
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Hello WASM</title>
</head>
<body>
    <script type="module">
        import init, { greet, add, fibonacci } from './pkg/hello_wasm.js';

        async function run() {
            await init();
            
            console.log(greet("WebAssembly"));  // "Hello, WebAssembly!"
            console.log(add(10, 20));           // 30
            console.log(fibonacci(10));         // 55
        }

        run();
    </script>
</body>
</html>
```

---

## 2. wasm-bindgen 深入

### 2.1 类型转换

**支持的类型:**

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

#[wasm_bindgen]
impl Point {
    #[wasm_bindgen(constructor)]
    pub fn new(x: f64, y: f64) -> Point {
        Point { x, y }
    }
    
    pub fn distance(&self) -> f64 {
        (self.x * self.x + self.y * self.y).sqrt()
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 导出函数
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[wasm_bindgen]
pub fn process_numbers(numbers: Vec<i32>) -> Vec<i32> {
    numbers.iter().map(|n| n * 2).collect()
}

#[wasm_bindgen]
pub fn get_name() -> String {
    "WebAssembly".to_string()
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Result 类型
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[wasm_bindgen]
pub fn divide(a: f64, b: f64) -> Result<f64, JsValue> {
    if b == 0.0 {
        Err(JsValue::from_str("除数不能为零"))
    } else {
        Ok(a / b)
    }
}
```

### 2.2 与 JavaScript 互操作

**调用 JavaScript 函数:**

```rust
use wasm_bindgen::prelude::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 导入 JavaScript 函数
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
    
    #[wasm_bindgen(js_namespace = Math)]
    fn random() -> f64;
    
    fn alert(s: &str);
}

#[wasm_bindgen]
pub fn show_message() {
    log("Hello from Rust!");
    alert("Alert from Rust!");
}

#[wasm_bindgen]
pub fn get_random() -> f64 {
    random()
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 操作 DOM
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
use web_sys::{Document, Element, Window};

#[wasm_bindgen]
pub fn update_dom() -> Result<(), JsValue> {
    let window = web_sys::window().ok_or("没有 window 对象")?;
    let document = window.document().ok_or("没有 document 对象")?;
    
    let body = document.body().ok_or("没有 body 元素")?;
    
    let div = document.create_element("div")?;
    div.set_text_content(Some("Hello from Rust!"));
    body.append_child(&div)?;
    
    Ok(())
}
```

### 2.3 异步操作

```rust
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, RequestMode, Response};

#[wasm_bindgen]
pub async fn fetch_data(url: String) -> Result<String, JsValue> {
    let mut opts = RequestInit::new();
    opts.method("GET");
    opts.mode(RequestMode::Cors);
    
    let request = Request::new_with_str_and_init(&url, &opts)?;
    
    let window = web_sys::window().unwrap();
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;
    
    let resp: Response = resp_value.dyn_into()?;
    let text = JsFuture::from(resp.text()?).await?;
    
    Ok(text.as_string().unwrap())
}
```

---

## 3. Yew 框架 (React-like)

### 3.1 项目设置

**Cargo.toml:**

```toml
[package]
name = "yew-app"
version = "0.1.0"
edition = "2021"

[dependencies]
yew = { version = "0.21", features = ["csr"] }
```

### 3.2 基础组件

```rust
use yew::prelude::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 简单组件
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[function_component(HelloWorld)]
fn hello_world() -> Html {
    html! {
        <div>
            <h1>{ "Hello, Yew!" }</h1>
            <p>{ "欢迎使用 Yew 框架" }</p>
        </div>
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 带状态的组件
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[function_component(Counter)]
fn counter() -> Html {
    let count = use_state(|| 0);
    
    let increment = {
        let count = count.clone();
        Callback::from(move |_| count.set(*count + 1))
    };
    
    let decrement = {
        let count = count.clone();
        Callback::from(move |_| count.set(*count - 1))
    };
    
    html! {
        <div>
            <h2>{ "计数器" }</h2>
            <p>{ format!("当前值: {}", *count) }</p>
            <button onclick={increment}>{ "+1" }</button>
            <button onclick={decrement}>{ "-1" }</button>
        </div>
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Props 组件
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Properties, PartialEq)]
struct UserProps {
    name: String,
    age: u32,
}

#[function_component(UserCard)]
fn user_card(props: &UserProps) -> Html {
    html! {
        <div class="user-card">
            <h3>{ &props.name }</h3>
            <p>{ format!("年龄: {}", props.age) }</p>
        </div>
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 主应用
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[function_component(App)]
fn app() -> Html {
    html! {
        <div>
            <HelloWorld />
            <Counter />
            <UserCard name="张三" age={25} />
        </div>
    }
}

fn main() {
    yew::Renderer::<App>::new().render();
}
```

### 3.3 Hooks

```rust
use yew::prelude::*;
use gloo_net::http::Request;
use serde::Deserialize;

#[derive(Clone, PartialEq, Deserialize)]
struct User {
    id: u32,
    name: String,
}

#[function_component(UserList)]
fn user_list() -> Html {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // use_state: 状态管理
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let users = use_state(|| Vec::<User>::new());
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // use_effect: 副作用
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    {
        let users = users.clone();
        use_effect_with((), move |_| {
            wasm_bindgen_futures::spawn_local(async move {
                let fetched_users: Vec<User> = Request::get("/api/users")
                    .send()
                    .await
                    .unwrap()
                    .json()
                    .await
                    .unwrap();
                
                users.set(fetched_users);
            });
            || ()
        });
    }
    
    html! {
        <div>
            <h2>{ "用户列表" }</h2>
            <ul>
                { for users.iter().map(|user| html! {
                    <li key={user.id}>{ &user.name }</li>
                }) }
            </ul>
        </div>
    }
}
```

---

## 4. Leptos 框架 (Next-gen)

### 4.1 项目设置

**Cargo.toml:**

```toml
[dependencies]
leptos = { version = "0.6", features = ["csr"] }
```

### 4.2 响应式组件

```rust
use leptos::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 计数器组件
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[component]
fn Counter(cx: Scope) -> impl IntoView {
    let (count, set_count) = create_signal(cx, 0);
    
    view! { cx,
        <div>
            <h2>"计数器"</h2>
            <p>"当前值: " {count}</p>
            <button on:click=move |_| set_count.update(|n| *n + 1)>
                "+1"
            </button>
            <button on:click=move |_| set_count.update(|n| *n - 1)>
                "-1"
            </button>
        </div>
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 派生信号 (computed)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[component]
fn DerivedCounter(cx: Scope) -> impl IntoView {
    let (count, set_count) = create_signal(cx, 0);
    
    // 派生信号: 自动更新
    let doubled = move || count() * 2;
    
    view! { cx,
        <div>
            <p>"原始值: " {count}</p>
            <p>"两倍值: " {doubled}</p>
            <button on:click=move |_| set_count.update(|n| *n + 1)>
                "+1"
            </button>
        </div>
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 主应用
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[component]
fn App(cx: Scope) -> impl IntoView {
    view! { cx,
        <div>
            <h1>"Leptos 应用"</h1>
            <Counter />
            <DerivedCounter />
        </div>
    }
}

fn main() {
    mount_to_body(|cx| view! { cx, <App/> })
}
```

---

## 5. Tauri 桌面应用

### 5.1 项目创建

```bash
# 创建 Tauri 项目
cargo install create-tauri-app
cargo create-tauri-app

# 选择:
# - Rust (backend)
# - Yew/Leptos (frontend)
```

### 5.2 Rust 后端

```rust
// src-tauri/src/main.rs
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use tauri::command;

#[command]
fn greet(name: &str) -> String {
    format!("Hello, {}! You've been greeted from Rust!", name)
}

#[command]
async fn fetch_data() -> Result<String, String> {
    // 异步操作
    Ok("Data from Rust".to_string())
}

fn main() {
    tauri::Builder::default()
        .invoke_handler(tauri::generate_handler![greet, fetch_data])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### 5.3 前端调用

```javascript
import { invoke } from '@tauri-apps/api/tauri'

// 调用 Rust 函数
const greeting = await invoke('greet', { name: 'World' })
console.log(greeting) // "Hello, World! You've been greeted from Rust!"

const data = await invoke('fetch_data')
console.log(data) // "Data from Rust"
```

---

## 6. 与 JavaScript 互操作

### 6.1 传递复杂数据

```rust
use wasm_bindgen::prelude::*;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
pub struct User {
    id: u32,
    name: String,
    email: String,
}

#[wasm_bindgen]
pub fn create_user(id: u32, name: String, email: String) -> JsValue {
    let user = User { id, name, email };
    serde_wasm_bindgen::to_value(&user).unwrap()
}

#[wasm_bindgen]
pub fn process_user(js_user: JsValue) -> Result<String, JsValue> {
    let user: User = serde_wasm_bindgen::from_value(js_user)?;
    Ok(format!("Processing user: {}", user.name))
}
```

### 6.2 回调函数

```rust
use wasm_bindgen::prelude::*;
use wasm_bindgen::closure::Closure;

#[wasm_bindgen]
pub fn set_timeout(callback: &js_sys::Function, delay: i32) {
    let window = web_sys::window().unwrap();
    window.set_timeout_with_callback_and_timeout_and_arguments_0(callback, delay).unwrap();
}

#[wasm_bindgen]
pub fn register_click_handler(element_id: &str) -> Result<(), JsValue> {
    let window = web_sys::window().ok_or("No window")?;
    let document = window.document().ok_or("No document")?;
    let element = document.get_element_by_id(element_id).ok_or("Element not found")?;
    
    let closure = Closure::wrap(Box::new(move || {
        web_sys::console::log_1(&"Button clicked!".into());
    }) as Box<dyn FnMut()>);
    
    element.add_event_listener_with_callback("click", closure.as_ref().unchecked_ref())?;
    closure.forget(); // 防止被释放
    
    Ok(())
}
```

---

## 7. 性能优化

### 7.1 减少二进制大小

**Cargo.toml:**

```toml
[profile.release]
lto = true              # 链接时优化
opt-level = 'z'         # 优化体积
codegen-units = 1       # 减少代码单元
panic = 'abort'         # 减少 panic 开销
strip = true            # 移除符号
```

**使用 wasm-opt:**

```bash
# 安装 wasm-opt
npm install -g wasm-opt

# 优化 wasm 文件
wasm-opt -Oz -o output.wasm input.wasm

# 结果: 体积减少 30-50%
```

### 7.2 懒加载

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub async fn load_heavy_module() -> Result<(), JsValue> {
    // 动态加载重量级模块
    let module = wasm_bindgen_futures::JsFuture::from(
        js_sys::eval("import('./heavy_module.js')")?
    ).await?;
    
    Ok(())
}
```

### 7.3 Web Workers

```rust
use wasm_bindgen::prelude::*;
use web_sys::{Worker, MessageEvent};

#[wasm_bindgen]
pub fn start_worker() -> Result<(), JsValue> {
    let worker = Worker::new("./worker.js")?;
    
    let onmessage = Closure::wrap(Box::new(move |event: MessageEvent| {
        web_sys::console::log_1(&event.data());
    }) as Box<dyn FnMut(MessageEvent)>);
    
    worker.set_onmessage(Some(onmessage.as_ref().unchecked_ref()));
    onmessage.forget();
    
    worker.post_message(&"Start processing".into())?;
    
    Ok(())
}
```

---

## 8. 实战案例

### 8.1 图像处理

```rust
use wasm_bindgen::prelude::*;
use web_sys::ImageData;

#[wasm_bindgen]
pub fn apply_grayscale(image_data: ImageData) -> Result<ImageData, JsValue> {
    let mut data = image_data.data();
    
    for i in (0..data.len()).step_by(4) {
        let r = data[i] as u32;
        let g = data[i + 1] as u32;
        let b = data[i + 2] as u32;
        
        // 灰度公式
        let gray = ((r * 299 + g * 587 + b * 114) / 1000) as u8;
        
        data[i] = gray;
        data[i + 1] = gray;
        data[i + 2] = gray;
    }
    
    ImageData::new_with_u8_clamped_array_and_sh(
        wasm_bindgen::Clamped(&data),
        image_data.width(),
        image_data.height(),
    )
}
```

### 8.2 数据可视化

```rust
use wasm_bindgen::prelude::*;
use web_sys::{CanvasRenderingContext2d, HtmlCanvasElement};

#[wasm_bindgen]
pub fn draw_chart(canvas: HtmlCanvasElement, data: Vec<f64>) -> Result<(), JsValue> {
    let ctx = canvas
        .get_context("2d")?
        .ok_or("Failed to get 2d context")?
        .dyn_into::<CanvasRenderingContext2d>()?;
    
    let width = canvas.width() as f64;
    let height = canvas.height() as f64;
    let bar_width = width / data.len() as f64;
    
    ctx.clear_rect(0.0, 0.0, width, height);
    
    for (i, value) in data.iter().enumerate() {
        let bar_height = (*value / 100.0) * height;
        let x = i as f64 * bar_width;
        let y = height - bar_height;
        
        ctx.set_fill_style(&"#3498db".into());
        ctx.fill_rect(x, y, bar_width - 2.0, bar_height);
    }
    
    Ok(())
}
```

---

## 9. 最佳实践

1. **最小化 wasm 文件大小** (LTO, opt-level='z', wasm-opt)
2. **使用 Web Workers** (CPU 密集型任务)
3. **懒加载模块** (按需加载)
4. **避免频繁的 JS ↔ WASM 调用**
5. **使用 serde 序列化** (复杂数据传递)
6. **利用 SIMD** (并行计算)
7. **测试多浏览器兼容性**
8. **监控性能** (Chrome DevTools, Firefox Profiler)
9. **错误处理** (Result 类型, try_from)
10. **文档和类型定义** (TypeScript .d.ts)

---

## 10. 常见陷阱

1. **忘记调用 init()** (WASM 模块初始化)
2. **内存泄漏** (Closure::forget 滥用)
3. **过度的 JS ↔ WASM 通信**
4. **未优化二进制大小**
5. **阻塞主线程** (使用 Web Workers)
6. **不支持多线程** (WASM 线程支持有限)
7. **异步操作的复杂性**
8. **浏览器兼容性问题**

---

## 11. 参考资源

- **wasm-bindgen**: [https://rustwasm.github.io/wasm-bindgen/](https://rustwasm.github.io/wasm-bindgen/)
- **Yew**: [https://yew.rs/](https://yew.rs/)
- **Leptos**: [https://leptos.dev/](https://leptos.dev/)
- **Tauri**: [https://tauri.app/](https://tauri.app/)
- **Rust and WebAssembly Book**: [https://rustwasm.github.io/docs/book/](https://rustwasm.github.io/docs/book/)

---

> **完成！** 🎉  
> 本指南涵盖了 Rust WebAssembly 开发的核心内容，包括基础概念、wasm-bindgen、Yew/Leptos 框架、Tauri 桌面应用、JS 互操作、性能优化、实战案例、最佳实践和常见陷阱。
