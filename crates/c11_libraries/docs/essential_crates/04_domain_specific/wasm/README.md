# WebAssembly (WASM)

**类别**: 领域特定 - WebAssembly  
**重要程度**: ⭐⭐⭐⭐⭐ (Web 开发必备)  
**更新日期**: 2025-10-20

---

## 📋 概述

Rust 和 WebAssembly 是完美的组合。
Rust 的性能优势和内存安全特性使其成为 WebAssembly 开发的首选语言。

---

## 🔧 核心工具

### 1. wasm-bindgen (JS 互操作 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add wasm-bindgen`  
**用途**: Rust 与 JavaScript 之间的桥梁

#### 核心特性

- ✅ 自动生成 JS 绑定
- ✅ 类型安全
- ✅ 支持异步
- ✅ DOM 操作

#### 基础示例

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

**JavaScript 调用**:

```javascript
import init, { greet, add } from './pkg/my_wasm.js';

await init();

console.log(greet("World"));  // "Hello, World!"
console.log(add(5, 3));        // 8
```

#### DOM 操作

```rust
use wasm_bindgen::prelude::*;
use web_sys::{Document, HtmlElement, window};

#[wasm_bindgen(start)]
pub fn main() {
    let window = window().expect("no global `window` exists");
    let document = window.document().expect("should have a document on window");
    let body = document.body().expect("document should have a body");

    let val = document.create_element("p").unwrap();
    val.set_inner_html("Hello from Rust!");

    body.append_child(&val).unwrap();
}
```

#### 事件处理

```rust
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{Document, HtmlButtonElement};

#[wasm_bindgen]
pub fn setup_button() {
    let document = web_sys::window()
        .unwrap()
        .document()
        .unwrap();
    
    let button = document
        .get_element_by_id("my-button")
        .unwrap()
        .dyn_into::<HtmlButtonElement>()
        .unwrap();
    
    let closure = Closure::wrap(Box::new(move || {
        web_sys::console::log_1(&"Button clicked!".into());
    }) as Box<dyn FnMut()>);
    
    button.set_onclick(Some(closure.as_ref().unchecked_ref()));
    closure.forget();
}
```

---

### 2. wasm-pack (构建和打包 ⭐⭐⭐⭐⭐)

**安装**: `cargo install wasm-pack`  
**用途**: WASM 项目构建工具

#### 核心特性2

- ✅ 一键构建
- ✅ NPM 包生成
- ✅ TypeScript 类型定义
- ✅ 多目标支持

#### 使用流程

```bash
# 创建项目
cargo new --lib my-wasm-project
cd my-wasm-project

# 添加依赖
cargo add wasm-bindgen

# 构建 (针对 Web)
wasm-pack build --target web

# 构建 (针对 Node.js)
wasm-pack build --target nodejs

# 构建 (针对打包工具)
wasm-pack build --target bundler
```

**生成的文件结构**:

```text
pkg/
├── my_wasm_project.js
├── my_wasm_project_bg.wasm
├── my_wasm_project.d.ts
└── package.json
```

---

### 3. yew (前端框架 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add yew`  
**用途**: 类 React 的前端框架

#### 核心特性3

- ✅ 组件化
- ✅ 虚拟 DOM
- ✅ 类型安全
- ✅ Hooks 支持

#### 基础组件

```rust
use yew::prelude::*;

#[function_component(App)]
fn app() -> Html {
    let counter = use_state(|| 0);
    
    let increment = {
        let counter = counter.clone();
        Callback::from(move |_| counter.set(*counter + 1))
    };
    
    html! {
        <div>
            <h1>{"Counter: "}{*counter}</h1>
            <button onclick={increment}>{"Increment"}</button>
        </div>
    }
}

fn main() {
    yew::Renderer::<App>::new().render();
}
```

#### 组件通信

```rust
use yew::prelude::*;

#[derive(Properties, PartialEq)]
struct ChildProps {
    pub count: i32,
    pub on_click: Callback<()>,
}

#[function_component(Child)]
fn child(props: &ChildProps) -> Html {
    let onclick = {
        let on_click = props.on_click.clone();
        Callback::from(move |_| on_click.emit(()))
    };
    
    html! {
        <div>
            <p>{"Count: "}{props.count}</p>
            <button {onclick}>{"Click me!"}</button>
        </div>
    }
}

#[function_component(Parent)]
fn parent() -> Html {
    let count = use_state(|| 0);
    
    let on_click = {
        let count = count.clone();
        Callback::from(move |_| count.set(*count + 1))
    };
    
    html! {
        <Child count={*count} on_click={on_click} />
    }
}
```

---

### 4. leptos (全栈框架 ⭐⭐⭐⭐)

**添加依赖**: `cargo add leptos`  
**用途**: 现代化的全栈框架

#### 核心特性4

- ✅ 细粒度响应式
- ✅ 服务器端渲染 (SSR)
- ✅ 零 JavaScript 运行时
- ✅ 类型安全的 API

#### 基础示例4

```rust
use leptos::*;

#[component]
fn Counter() -> impl IntoView {
    let (count, set_count) = create_signal(0);
    
    view! {
        <div>
            <h1>"Counter: " {count}</h1>
            <button on:click=move |_| set_count.update(|n| *n += 1)>
                "Increment"
            </button>
        </div>
    }
}

fn main() {
    mount_to_body(|| view! { <Counter/> })
}
```

#### 异步数据获取

```rust
use leptos::*;

async fn fetch_data() -> String {
    // 模拟 API 调用
    "Hello from server!".to_string()
}

#[component]
fn DataFetcher() -> impl IntoView {
    let data = create_resource(|| (), |_| async { fetch_data().await });
    
    view! {
        <Suspense fallback=|| view! { <p>"Loading..."</p> }>
            {move || data.read().map(|data| view! {
                <p>{data}</p>
            })}
        </Suspense>
    }
}
```

---

## 💡 最佳实践

### 1. 优化 WASM 大小

```toml
[profile.release]
opt-level = "z"
lto = true
codegen-units = 1
panic = "abort"
```

```bash
# 使用 wasm-opt 进一步优化
wasm-opt -Oz -o output.wasm input.wasm
```

### 2. 避免频繁的 JS <-> Rust 调用

```rust
// ❌ 慢：频繁跨边界调用
for i in 0..1000 {
    js_function(i);
}

// ✅ 快：批量处理
let results: Vec<_> = (0..1000).map(|i| process(i)).collect();
js_function_batch(&results);
```

### 3. 使用 Web Workers

```rust
use wasm_bindgen::prelude::*;
use web_sys::{Worker, MessageEvent};

#[wasm_bindgen]
pub fn start_worker() {
    let worker = Worker::new("./worker.js").unwrap();
    
    let closure = Closure::wrap(Box::new(move |event: MessageEvent| {
        web_sys::console::log_1(&event.data());
    }) as Box<dyn FnMut(_)>);
    
    worker.set_onmessage(Some(closure.as_ref().unchecked_ref()));
    closure.forget();
    
    worker.post_message(&JsValue::from_str("Hello")).unwrap();
}
```

---

## 📊 工具对比

| 工具 | 用途 | 易用性 | 生态 | 推荐度 |
|------|------|--------|------|--------|
| **wasm-bindgen** | JS 互操作 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 🌟 必备 |
| **wasm-pack** | 构建打包 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 🌟 必备 |
| **yew** | 前端框架 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 🌟 强推 |
| **leptos** | 全栈框架 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 💡 推荐 |

---

## 🎯 实战场景

### 场景1: 性能密集型计算

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn fibonacci(n: u32) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

#[wasm_bindgen]
pub fn process_image(data: &[u8]) -> Vec<u8> {
    // 图像处理逻辑
    data.iter().map(|&x| x.saturating_add(10)).collect()
}
```

### 场景2: 单页应用 (Yew)

```rust
use yew::prelude::*;
use yew_router::prelude::*;

#[derive(Clone, Routable, PartialEq)]
enum Route {
    #[at("/")]
    Home,
    #[at("/about")]
    About,
}

fn switch(routes: Route) -> Html {
    match routes {
        Route::Home => html! { <h1>{"Home"}</h1> },
        Route::About => html! { <h1>{"About"}</h1> },
    }
}

#[function_component(App)]
fn app() -> Html {
    html! {
        <BrowserRouter>
            <Switch<Route> render={switch} />
        </BrowserRouter>
    }
}
```

---

## 🔗 相关资源

- [Rust and WebAssembly Book](https://rustwasm.github.io/docs/book/)
- [wasm-bindgen Guide](https://rustwasm.github.io/wasm-bindgen/)
- [Yew Documentation](https://yew.rs/)
- [Leptos Book](https://leptos-rs.github.io/leptos/)

---

**导航**: [返回领域特定](../README.md) | [下一领域：嵌入式系统](../embedded/README.md)
