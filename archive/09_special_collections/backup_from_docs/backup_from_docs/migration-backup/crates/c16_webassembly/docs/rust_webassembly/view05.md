# Rust全栈WebAssembly架构可行性分析

## 目录

- [Rust全栈WebAssembly架构可行性分析](#rust全栈webassembly架构可行性分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 架构概述](#2-架构概述)
    - [2.1 架构模型定义](#21-架构模型定义)
    - [2.2 技术栈组成](#22-技术栈组成)
    - [2.3 数据流模型](#23-数据流模型)
  - [3. 前端技术组件分析](#3-前端技术组件分析)
    - [3.1 Rust前端框架评估](#31-rust前端框架评估)
    - [3.2 WebAssembly前端集成](#32-webassembly前端集成)
    - [3.3 状态管理解决方案](#33-状态管理解决方案)
  - [4. 服务端技术组件分析](#4-服务端技术组件分析)
    - [4.1 Rust服务器框架](#41-rust服务器框架)
    - [4.2 WebAssembly运行时环境](#42-webassembly运行时环境)
    - [4.3 安全与隔离机制](#43-安全与隔离机制)
  - [5. 全栈共享代码分析](#5-全栈共享代码分析)
    - [5.1 共享模型定义](#51-共享模型定义)
    - [5.2 验证逻辑复用](#52-验证逻辑复用)
    - [5.3 API类型共享](#53-api类型共享)
  - [6. 数据交换与序列化](#6-数据交换与序列化)
    - [6.1 序列化方案对比](#61-序列化方案对比)
    - [6.2 API协议设计](#62-api协议设计)
    - [6.3 性能与优化](#63-性能与优化)
  - [7. 工具链与开发体验](#7-工具链与开发体验)
    - [7.1 构建系统](#71-构建系统)
    - [7.2 开发环境集成](#72-开发环境集成)
    - [7.3 测试与调试](#73-测试与调试)
  - [8. 典型应用架构模式](#8-典型应用架构模式)
    - [8.1 同构渲染架构](#81-同构渲染架构)
    - [8.2 微服务架构](#82-微服务架构)
    - [8.3 边缘计算架构](#83-边缘计算架构)
  - [9. 性能与资源消耗](#9-性能与资源消耗)
    - [9.1 性能基准测试](#91-性能基准测试)
    - [9.2 资源利用分析](#92-资源利用分析)
    - [9.3 优化策略](#93-优化策略)
  - [10. 生产实践考量](#10-生产实践考量)
    - [10.1 部署策略](#101-部署策略)
    - [10.2 可观测性](#102-可观测性)
    - [10.3 扩展性设计](#103-扩展性设计)
  - [11. 形式化验证与安全保障](#11-形式化验证与安全保障)
    - [11.1 类型系统保障](#111-类型系统保障)
    - [11.2 所有权模型安全性](#112-所有权模型安全性)
    - [11.3 形式化证明](#113-形式化证明)
  - [12. 案例研究与实现示例](#12-案例研究与实现示例)
    - [12.1 全栈Todo应用](#121-全栈todo应用)
    - [12.2 数据密集型应用](#122-数据密集型应用)
    - [12.3 实时协作应用](#123-实时协作应用)
  - [13. 挑战与解决方案](#13-挑战与解决方案)
    - [13.1 主要技术挑战](#131-主要技术挑战)
    - [13.2 生态系统局限](#132-生态系统局限)
    - [13.3 解决策略](#133-解决策略)
  - [14. 未来发展趋势](#14-未来发展趋势)
    - [14.1 标准演进](#141-标准演进)
    - [14.2 工具链改进](#142-工具链改进)
    - [14.3 生态系统扩展](#143-生态系统扩展)
  - [15. 结论与建议](#15-结论与建议)
    - [15.1 可行性总结](#151-可行性总结)
    - [15.2 应用场景建议](#152-应用场景建议)
    - [15.3 实施路径](#153-实施路径)
  - [16. 思维导图](#16-思维导图)

## 1. 引言

随着WebAssembly(Wasm)技术的成熟和Rust语言的日益普及，基于这两者构建全栈Web应用架构成为可能。本文从形式化角度分析Rust+WebAssembly全栈架构的可行性，涵盖架构设计、组件评估、程序设计模式及最佳实践。

Rust语言以其内存安全、并发安全且无垃圾收集的特性，结合WebAssembly的高性能、跨平台及安全沙箱，为Web应用开发提供了全新范式。本文将系统性地形式化分析这种架构模式的各个方面。

## 2. 架构概述

### 2.1 架构模型定义

全栈Rust+WebAssembly架构可形式化定义为一个五元组:

$$\mathcal{A} = (F, B, S, C, P)$$

其中:

- $F$: 前端组件集合，Rust编译为WebAssembly在浏览器运行
- $B$: 后端组件集合，Rust原生或编译为WebAssembly在服务端运行
- $S$: 共享代码与模型，包含前后端共用的逻辑
- $C$: 通信协议与序列化层
- $P$: 持久化存储抽象

这种架构的关键特性为代码共享率 $R$，定义为:

$$R = \frac{|S|}{|F|+|B|+|S|}$$

其中 $|X|$ 表示组件 $X$ 的代码量。理想的架构应使 $R$ 最大化，同时保持 $F$ 和 $B$ 的特定需求。

### 2.2 技术栈组成

全栈Rust+WebAssembly架构包含以下核心技术组件:

**前端技术栈:**

- Rust前端框架(Yew, Dioxus, Sycamore等)
- WebAssembly(wasm32-unknown-unknown目标)
- wasm-bindgen及web-sys/js-sys绑定
- wasm-pack或Trunk构建工具

**后端技术栈:**

- Rust服务器框架(Axum, Actix, Rocket等)
- 可选的WebAssembly运行时(Wasmtime, Wasmer等)
- WASI支持(WebAssembly系统接口)
- 数据库访问层(Diesel, SQLx, SeaORM等)

**共享技术:**

- Serde序列化框架
- 领域模型与验证逻辑
- 错误处理模式
- 工具函数库

### 2.3 数据流模型

Rust+WebAssembly全栈应用的数据流可以形式化为有向图:

$$G = (V, E)$$

其中顶点集 $V$ 包含:

- 浏览器UI渲染层
- 浏览器WebAssembly模块
- WebAPI交互层
- 服务端API层
- 服务端业务逻辑
- 数据持久化层

边集 $E$ 表示数据交换路径，数据在节点间以类型安全的方式传递，通过共享的模型定义保证完整性。

## 3. 前端技术组件分析

### 3.1 Rust前端框架评估

主流Rust前端框架对比分析:

| 框架 | 成熟度 | 性能 | 开发体验 | 组件生态 | 文档质量 |
|------|-------|------|---------|---------|---------|
| Yew | 高 | 中 | 好 | 丰富 | 完善 |
| Dioxus | 中 | 高 | 优 | 发展中 | 良好 |
| Sycamore | 中 | 高 | 好 | 有限 | 良好 |
| Percy | 低 | 高 | 一般 | 极少 | 基础 |

Yew框架示例代码:

```rust
use yew::prelude::*;

#[function_component]
fn App() -> Html {
    let counter = use_state(|| 0);
    let onclick = {
        let counter = counter.clone();
        move |_| {
            let value = *counter + 1;
            counter.set(value);
        }
    };

    html! {
        <div>
            <h1>{"计数器应用"}</h1>
            <button {onclick}>{ "增加" }</button>
            <p>{ *counter }</p>
        </div>
    }
}
```

### 3.2 WebAssembly前端集成

前端Rust代码编译为WebAssembly并与Web平台集成的形式化过程:

1. **编译过程**: $\text{Compile}: \text{Rust} \rightarrow \text{WASM}$

   ```bash
   wasm-pack build --target web
   ```

2. **绑定生成**: $\text{Bind}: \text{WASM} \rightarrow \text{JS Bridge}$

   ```rust
   #[wasm_bindgen]
   pub fn process_data(input: &str) -> String {
       // 数据处理逻辑
       format!("处理结果: {}", input)
   }
   ```

3. **Web集成**: $\text{Integrate}: \text{JS Bridge} \rightarrow \text{Web Platform}$

   ```javascript
   import init, { process_data } from './wasm_module.js';

   async function run() {
     await init();
     const result = process_data("测试数据");
     document.getElementById("output").textContent = result;
   }
   ```

4. **DOM交互**: 通过web-sys提供类型安全的DOM操作

   ```rust
   use web_sys::{Document, Element, HtmlElement, Window};

   fn append_to_body(text: &str) -> Result<(), JsValue> {
       let window = web_sys::window().unwrap();
       let document = window.document().unwrap();
       let body = document.body().unwrap();
       
       let p = document.create_element("p")?;
       p.set_text_content(Some(text));
       
       body.append_child(&p)?;
       Ok(())
   }
   ```

### 3.3 状态管理解决方案

Rust WebAssembly前端应用的状态管理可以形式化为状态机:

$$S = (Q, \Sigma, \delta, q_0, F)$$

其中:

- $Q$ 是有限状态集
- $\Sigma$ 是事件集
- $\delta: Q \times \Sigma \rightarrow Q$ 是转换函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是终止状态集

Yew框架中的状态管理示例:

```rust
use yew::prelude::*;
use serde::{Serialize, Deserialize};

// 定义应用状态
#[derive(Clone, PartialEq, Serialize, Deserialize)]
struct AppState {
    counter: i32,
    items: Vec<String>,
    filter: FilterType,
}

// 定义状态转换事件
enum Action {
    Increment,
    Decrement,
    AddItem(String),
    RemoveItem(usize),
    SetFilter(FilterType),
}

// 状态转换函数
fn reducer(state: &AppState, action: Action) -> AppState {
    let mut new_state = state.clone();
    
    match action {
        Action::Increment => new_state.counter += 1,
        Action::Decrement => new_state.counter -= 1,
        Action::AddItem(item) => new_state.items.push(item),
        Action::RemoveItem(index) => {
            if index < new_state.items.len() {
                new_state.items.remove(index);
            }
        },
        Action::SetFilter(filter) => new_state.filter = filter,
    }
    
    new_state
}
```

## 4. 服务端技术组件分析

### 4.1 Rust服务器框架

Rust服务器框架比较与形式化特性:

| 框架 | 模型 | 性能特性 | 异步支持 | WebAssembly兼容性 |
|------|------|---------|---------|-----------------|
| Axum | 函数式，路由优先 | 高吞吐，低延迟 | Tokio | 良好 |
| Actix Web | Actor模型，功能完整 | 极高性能 | async-std/Tokio | 部分支持 |
| Rocket | 声明式，注解路由 | 中高性能 | Tokio | 有限支持 |
| Warp | 函数式，组合过滤器 | 高性能 | Tokio | 部分支持 |

形式化定义服务器框架特性空间:
$$F_{server} = \{T, R, M, A, S\}$$
其中:

- $T$: 吞吐量特性
- $R$: 请求处理模型
- $M$: 中间件支持
- $A$: 异步处理能力
- $S$: WebAssembly支持级别

Axum服务器示例:

```rust
use axum::{
    routing::{get, post},
    http::StatusCode,
    Json, Router,
};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;

// 共享数据模型
#[derive(Serialize, Deserialize)]
struct User {
    id: Option<u64>,
    name: String,
    email: String,
}

// API端点实现
async fn create_user(Json(payload): Json<User>) -> (StatusCode, Json<User>) {
    // 在实际应用中连接数据库
    let user = User {
        id: Some(1),
        name: payload.name,
        email: payload.email,
    };
    
    (StatusCode::CREATED, Json(user))
}

async fn get_user() -> Json<User> {
    let user = User {
        id: Some(1),
        name: "测试用户".into(),
        email: "test@example.com".into(),
    };
    
    Json(user)
}

#[tokio::main]
async fn main() {
    // 构建应用路由
    let app = Router::new()
        .route("/users", post(create_user))
        .route("/users/1", get(get_user));

    // 启动服务器
    let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

### 4.2 WebAssembly运行时环境

服务端WebAssembly运行时可形式化为一个映射函数:
$$\text{Execute}: \text{WASM} \times \text{Input} \rightarrow \text{Output} \times \text{State}'$$

主要运行时实现比较:

| 运行时 | 性能 | 安全模型 | WASI支持 | 内存管理 | 嵌入API |
|-------|------|---------|---------|---------|---------|
| Wasmtime | 高 | 强隔离 | 完整 | 严格控制 | 完善 |
| Wasmer | 高 | 强隔离 | 完整 | 灵活 | 多语言 |
| WAVM | 极高 | 中等 | 部分 | JIT优化 | C++ |
| WasmEdge | 高 | 强隔离 | 完整 | 优化 | 云原生 |

Wasmtime嵌入示例:

```rust
use anyhow::Result;
use wasmtime::*;

fn main() -> Result<()> {
    // 设置引擎
    let engine = Engine::default();
    let module = Module::from_file(&engine, "processing_module.wasm")?;
    
    // 创建存储和链接器
    let mut store = Store::new(&engine, ());
    let mut linker = Linker::new(&engine);
    
    // 添加宿主函数
    linker.func_wrap("host", "log_message", 
        |caller: Caller<'_, ()>, ptr: i32, len: i32| {
            // 从WebAssembly内存读取字符串并记录
            let mem = match caller.get_export("memory") {
                Some(Extern::Memory(mem)) => mem,
                _ => return Err(Trap::new("failed to find host memory")),
            };
            
            let data = mem.data(&caller)
                .get(ptr as u32 as usize..(ptr + len) as u32 as usize)
                .ok_or_else(|| Trap::new("pointer/length out of bounds"))?;
            
            let msg = String::from_utf8_lossy(data);
            println!("从WASM模块: {}", msg);
            
            Ok(())
        }
    )?;
    
    // 实例化并调用
    let instance = linker.instantiate(&mut store, &module)?;
    let process = instance.get_typed_func::<(i32, i32), i32>(&mut store, "process_data")?;
    
    let result = process.call(&mut store, (42, 7))?;
    println!("计算结果: {}", result);
    
    Ok(())
}
```

### 4.3 安全与隔离机制

WebAssembly提供的安全隔离模型可形式化为能力访问控制:
$$\text{Access}(M, R) \iff \text{HasCapability}(M, R)$$

其中:

- $M$ 是WebAssembly模块
- $R$ 是系统资源
- $\text{HasCapability}$ 是能力检查断言

WASI安全模型实现:

```rust
use wasmtime::*;
use wasmtime_wasi::{WasiCtx, WasiCtxBuilder};

// 定义应用状态
struct AppState {
    wasi: WasiCtx,
    // 其他应用状态...
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let engine = Engine::default();
    let module = Module::from_file(&engine, "app_module.wasm")?;
    
    // 构建受限的WASI上下文
    let wasi = WasiCtxBuilder::new()
        // 只预打开特定目录
        .preopened_dir(Dir::open_ambient_dir("./allowed_data", false)?, "data")?
        // 限制环境变量
        .env("ALLOWED_VAR", "value")?
        // 不允许命令行参数
        .inherit_stdio()
        .build();
    
    let mut store = Store::new(&engine, AppState { wasi });
    
    // 创建链接器并添加WASI功能
    let mut linker = Linker::new(&engine);
    wasmtime_wasi::add_to_linker(&mut linker, |s| &mut s.wasi)?;
    
    // 实例化模块
    let instance = linker.instantiate(&mut store, &module)?;
    
    // 调用入口函数
    if let Some(start) = instance.get_typed_func::<(), ()>(&mut store, "_start").ok() {
        start.call(&mut store, ())?;
    }
    
    Ok(())
}
```

## 5. 全栈共享代码分析

### 5.1 共享模型定义

全栈共享的领域模型可以形式化为类型集合:
$$\mathcal{M} = \{T_1, T_2, ..., T_n\}$$

其中每个类型 $T_i$ 可在前端和后端无缝使用。

```rust
// shared/src/models.rs
use serde::{Serialize, Deserialize};

// 定义领域模型，前后端共享
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct User {
    pub id: Option<u64>,
    pub username: String,
    pub email: String,
    pub role: UserRole,
    pub profile: UserProfile,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum UserRole {
    Admin,
    Moderator,
    Regular,
    Guest,
}

#[derive(Debug, Default, Clone, PartialEq, Serialize, Deserialize)]
pub struct UserProfile {
    pub display_name: Option<String>,
    pub bio: Option<String>,
    pub avatar_url: Option<String>,
    pub joined_at: Option<String>, // ISO 8601格式
}

// 模型关联方法，也可在前后端共享
impl User {
    pub fn is_admin(&self) -> bool {
        matches!(self.role, UserRole::Admin)
    }
    
    pub fn display_name(&self) -> &str {
        self.profile.display_name.as_deref().unwrap_or(&self.username)
    }
}
```

### 5.2 验证逻辑复用

共享验证逻辑可形式化为谓词集合:
$$\mathcal{V} = \{P_1, P_2, ..., P_m\}$$

其中每个谓词 $P_j: T \rightarrow \text{bool}$ 验证类型 $T$ 的一个约束。

```rust
// shared/src/validation.rs
use crate::models::*;
use std::collections::HashMap;

// 验证错误类型
#[derive(Debug, Clone, PartialEq)]
pub struct ValidationError {
    pub field: String,
    pub message: String,
}

// 验证结果类型
pub type ValidationResult = Result<(), Vec<ValidationError>>;

// 验证器特征
pub trait Validate {
    fn validate(&self) -> ValidationResult;
}

// User类型的验证实现
impl Validate for User {
    fn validate(&self) -> ValidationResult {
        let mut errors = Vec::new();
        
        // 用户名验证
        if self.username.is_empty() {
            errors.push(ValidationError {
                field: "username".into(),
                message: "用户名不能为空".into(),
            });
        } else if self.username.len() < 3 {
            errors.push(ValidationError {
                field: "username".into(),
                message: "用户名长度不能少于3个字符".into(),
            });
        }
        
        // 邮箱验证
        if !self.email.contains('@') {
            errors.push(ValidationError {
                field: "email".into(),
                message: "邮箱格式无效".into(),
            });
        }
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

// 如果前后端都需要表单验证，可以共享表单验证逻辑
pub fn validate_form<T: Validate>(data: &T) -> HashMap<String, String> {
    match data.validate() {
        Ok(_) => HashMap::new(),
        Err(errors) => {
            let mut error_map = HashMap::new();
            for error in errors {
                error_map.insert(error.field, error.message);
            }
            error_map
        }
    }
}
```

### 5.3 API类型共享

前后端共享的API类型定义可形式化为:
$$\mathcal{A} = \{E_1, E_2, ..., E_k\}$$

其中每个API端点 $E_i$ 定义为三元组 $(P, R, S)$:

- $P$: 请求参数类型
- $R$: 响应结果类型
- $S$: 可能的状态码

```rust
// shared/src/api.rs
use serde::{Serialize, Deserialize};
use crate::models::*;

// 通用API响应包装器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiResponse<T> {
    pub success: bool,
    pub data: Option<T>,
    pub error: Option<String>,
}

// 用户API请求/响应类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateUserRequest {
    pub username: String,
    pub email: String,
    pub password: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UpdateUserRequest {
    pub username: Option<String>,
    pub email: Option<String>,
    pub profile: Option<UserProfile>,
}

// API端点特征 - 定义前后端共享的API契约
pub trait ApiEndpoint {
    type Request;
    type Response;
    
    const PATH: &'static str;
    const METHOD: &'static str;
}

// 实现具体API端点
pub struct GetUserEndpoint;
impl ApiEndpoint for GetUserEndpoint {
    type Request = u64;  // 用户ID
    type Response = User;
    
    const PATH: &'static str = "/api/users/:id";
    const METHOD: &'static str = "GET";
}

pub struct CreateUserEndpoint;
impl ApiEndpoint for CreateUserEndpoint {
    type Request = CreateUserRequest;
    type Response = User;
    
    const PATH: &'static str = "/api/users";
    const METHOD: &'static str = "POST";
}
```

## 6. 数据交换与序列化

### 6.1 序列化方案对比

在Rust+WebAssembly全栈架构中，序列化方案选择至关重要:

| 方案 | 性能 | 尺寸效率 | 语言支持 | 人类可读性 | 类型安全 |
|------|------|---------|---------|----------|---------|
| JSON/Serde | 中 | 低 | 广泛 | 高 | 高 |
| Bincode | 高 | 高 | Rust主导 | 无 | 高 |
| MessagePack | 高 | 中高 | 广泛 | 低 | 中高 |
| Protocol Buffers | 高 | 高 | 广泛 | 低 | 中高 |
| CBOR | 中高 | 中高 | 中等 | 低 | 中高 |

序列化选择的形式化决策函数:
$$\text{Select}(S) = \alpha \cdot \text{Performance}(S) + \beta \cdot \text{Size}(S) + \gamma \cdot \text{Safety}(S) + \delta \cdot \text{Compat}(S)$$

Serde序列化示例:

```rust
use serde::{Serialize, Deserialize};
use serde_json;

#[derive(Serialize, Deserialize)]
struct Message {
    id: u32,
    content: String,
    timestamp: u64,
}

// 序列化
fn serialize_message(message: &Message) -> Result<String, serde_json::Error> {
    serde_json::to_string(message)
}

// 反序列化
fn deserialize_message(json: &str) -> Result<Message, serde_json::Error> {
    serde_json::from_str(json)
}

// 使用Bincode的高效二进制序列化(适用于内部通信)
fn binary_serialize_message(message: &Message) -> Result<Vec<u8>, bincode::Error> {
    bincode::serialize(message)
}

fn binary_deserialize_message(data: &[u8]) -> Result<Message, bincode::Error> {
    bincode::deserialize(data)
}
```

### 6.2 API协议设计

全栈应用API协议可形式化为请求响应模式:
$$\text{API}: \text{Request} \times \text{Context} \rightarrow \text{Response} \times \text{State}'$$

其中每个API调用可能改变应用状态。

API协议的形式化定义:

```rust
    // shared/src/protocol.rs
    use serde::{Serialize, Deserialize};
    use std::collections::HashMap;

    // 标准化请求结构
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ApiRequest<T> {
        pub data: T,
        pub meta: RequestMetadata,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct RequestMetadata {
        pub client_id: Option<String>,
        pub trace_id: String,
        pub timestamp: u64,
        pub version: String,
    }

    // 标准化响应结构
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ApiResponse<T> {
        pub data: Option<T>,
        pub errors: Option<Vec<ApiError>>,
        pub meta: ResponseMetadata,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ApiError {
        pub code: String,
        pub message: String,
        pub field: Option<String>,
        pub details: Option<HashMap<String, serde_json::Value>>,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ResponseMetadata {
        pub trace_id: String,
        pub timestamp: u64,
        pub version: String,
    }

    // HTTP状态码映射
    pub enum ApiStatus {
        Success,
        Created,
        BadRequest,
        Unauthorized,
        Forbidden,
        NotFound,
        ServerError,
    }

    impl ApiStatus {
        pub fn code(&self) -> u16 {
            match self {
                Self::Success => 200,
                Self::Created => 201,
                Self::BadRequest => 400,
                Self::Unauthorized => 401,
                Self::Forbidden => 403,
                Self::NotFound => 404,
                Self::ServerError => 500,
            }
        }
    }
```

### 6.3 性能与优化

数据交换的性能优化可以形式化为最小化开销函数:
$$\min_{S \in \mathcal{S}} (t_{\text{serialize}}(S, D) + t_{\text{transfer}}(S(D)) + t_{\text{deserialize}}(S(D)))$$

其中 $\mathcal{S}$ 是可选的序列化策略集，$D$ 是要传输的数据。

```rust
// 序列化性能优化策略
use serde::{Serialize, Deserialize};
use std::time::Instant;

// 配置结构体以支持不同的序列化策略
# [derive(Debug)]
pub enum SerializationStrategy {
    Json,
    Bincode,
    MessagePack,
    // 可扩展其他策略
}

// 构建支持多种序列化策略的客户端
pub struct ApiClient {
    base_url: String,
    strategy: SerializationStrategy,
}

impl ApiClient {
    pub fn new(base_url: &str, strategy: SerializationStrategy) -> Self {
        Self {
            base_url: base_url.to_string(),
            strategy,
        }
    }

    pub async fn request<T, R>(&self, endpoint: &str, data: &T) -> Result<R, ApiError>
    where
        T: Serialize,
        R: for<'de> Deserialize<'de>,
    {
        // 计时序列化
        let start = Instant::now();

        // 根据策略选择序列化方法
        let payload = match self.strategy {
            SerializationStrategy::Json => {
                let json = serde_json::to_string(data)?;
                json.into_bytes()
            },
            SerializationStrategy::Bincode => {
                bincode::serialize(data)?
            },
            SerializationStrategy::MessagePack => {
                rmp_serde::to_vec(data)?
            },
        };

        let serialize_time = start.elapsed();
        println!("序列化耗时: {:?}", serialize_time);

        // 这里省略实际网络请求实现
        // ...

        // 反序列化响应
        let response_data = match self.strategy {
            SerializationStrategy::Json => {
                // 假设response_bytes是从网络请求获取的
                let response_bytes = vec![];
                let json = String::from_utf8(response_bytes)?;
                serde_json::from_str(&json)?
            },
            SerializationStrategy::Bincode => {
                let response_bytes = vec![];
                bincode::deserialize(&response_bytes)?
            },
            SerializationStrategy::MessagePack => {
                let response_bytes = vec![];
                rmp_serde::from_slice(&response_bytes)?
            },
        };

        Ok(response_data)
    }
}
```

## 7. 工具链与开发体验

### 7.1 构建系统

Rust+WebAssembly全栈应用的构建系统形式化为一系列转换:
$$\text{Source} \xrightarrow{\text{Compile}} \text{Binary} \xrightarrow{\text{Package}} \text{Deployable}$$

工作区结构与构建配置:

```toml
# Cargo.toml (工作区配置)
[workspace]
members = [
    "frontend",
    "backend",
    "shared",
]

# shared/Cargo.toml
[package]
name = "shared"
version = "0.1.0"

[dependencies]
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
chrono = { version = "0.4", features = ["serde"] }

# frontend/Cargo.toml
[package]
name = "frontend"
version = "0.1.0"

[dependencies]
shared = { path = "../shared" }
yew = "0.20"
wasm-bindgen = "0.2"
web-sys = { version = "0.3", features = ["HtmlInputElement", "Window"] }
js-sys = "0.3"
wasm-bindgen-futures = "0.4"
serde = { version = "1.0", features = ["derive"] }

[lib]
crate-type = ["cdylib", "rlib"]

# backend/Cargo.toml
[package]
name = "backend"
version = "0.1.0"

[dependencies]
shared = { path = "../shared" }
axum = "0.6"
tokio = { version = "1", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tracing = "0.1"
tracing-subscriber = "0.3"
```

构建脚本示例:

```bash
# !/bin/bash
# build.sh - 全栈应用构建脚本

# 编译前端
echo "编译WebAssembly前端..."
cd frontend
wasm-pack build --target web --out-name frontend --out-dir ../dist

# 编译后端
echo "编译Rust后端..."
cd ../backend
cargo build --release

# 复制部署资源
echo "准备部署资源..."
cd ..
mkdir -p deploy
cp backend/target/release/backend deploy/
cp -r dist deploy/
cp backend/config.yaml deploy/

echo "构建完成，部署资产在 ./deploy 目录"
```

### 7.2 开发环境集成

开发环境集成形式化为开发循环:
$$\text{Edit} \rightarrow \text{Compile} \rightarrow \text{Test} \rightarrow \text{Debug} \rightarrow \text{Edit} \rightarrow \ldots$$

开发环境配置示例:

```toml
# .cargo/config.toml
[alias]
# 启动开发服务器
dev = "run --package dev-server --bin dev-server"

# 运行所有测试(包括wasm测试)
test-all = "run --package test-runner --bin test-runner"

# 构建整个工作区
build-all = "run --package build-scripts --bin build-all"

# 检查代码质量
lint = "clippy --all-targets --all-features -- -D warnings"
```

开发服务器示例:

```rust
// dev-server/src/main.rs
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::process::Command as TokioCommand;
use tokio::sync::mpsc;
use tokio::sync::Mutex;
use warp::Filter;

// 开发服务器状态
struct DevServerState {
    backend_proc: Option<tokio::process::Child>,
}

# [tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化状态
    let state = Arc::new(Mutex::new(DevServerState {
        backend_proc: None,
    }));

    // 启动后端服务器
    restart_backend(Arc::clone(&state)).await?;

    // 设置文件监视器
    let (tx, mut rx) = mpsc::channel(32);
    let watcher_state = Arc::clone(&state);

    // 在单独线程中监视文件变化
    std::thread::spawn(move || {
        let mut watcher = notify::recommended_watcher(move |res| {
            let tx = tx.clone();
            if let Ok(event) = res {
                let _ = tx.blocking_send(event);
            }
        }).unwrap();

        // 监视源码目录
        watcher.watch(Path::new("./src"), notify::RecursiveMode::Recursive).unwrap();
        watcher.watch(Path::new("./shared"), notify::RecursiveMode::Recursive).unwrap();

        // 保持watcher活动
        loop {
            std::thread::sleep(std::time::Duration::from_secs(1));
        }
    });

    // 处理文件变化事件
    tokio::spawn(async move {
        while let Some(event) = rx.recv().await {
            println!("检测到文件变化: {:?}", event);
            // 重启后端服务器
            match restart_backend(Arc::clone(&watcher_state)).await {
                Ok(_) => println!("后端服务器已重启"),
                Err(e) => println!("重启后端服务器失败: {}", e),
            }

            // 重新构建前端
            match rebuild_frontend().await {
                Ok(_) => println!("前端重新构建完成"),
                Err(e) => println!("前端构建失败: {}", e),
            }
        }
    });

    // 设置开发服务器路由
    let routes = warp::path("api")
        .and(warp::path::tail())
        .and(warp::any())
        .and_then(|tail, _| async move {
            // 转发API请求到后端
            // ...
            Ok::<_, warp::Rejection>(warp::reply::json(&()))
        })
        .or(warp::fs::dir("./dist")); // 提供静态文件

    // 启动开发服务器
    println!("开发服务器运行在 http://localhost:3000");
    warp::serve(routes).run(([127, 0, 0, 1], 3000)).await;

    Ok(())
}

// 重启后端服务器
async fn restart_backend(state: Arc<Mutex<DevServerState>>) -> Result<(), Box<dyn std::error::Error>> {
    let mut state = state.lock().await;

    // 停止现有进程
    if let Some(ref mut child) = state.backend_proc {
        let _ = child.kill().await;
    }

    // 启动新后端进程
    let process = TokioCommand::new("cargo")
        .args(&["run", "--package", "backend"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    state.backend_proc = Some(process);
    Ok(())
}

// 重新构建前端
async fn rebuild_frontend() -> Result<(), Box<dyn std::error::Error>> {
    Command::new("wasm-pack")
        .args(&["build", "--target", "web", "--out-dir", "../dist", "--out-name", "frontend", "--dev"])
        .current_dir("./frontend")
        .status()?;

    Ok(())
}
```

### 7.3 测试与调试

全栈应用的测试可形式化为测试覆盖函数:
$$C(T) = \frac{|f \in F: \exists t \in T, t \text{ 测试 } f|}{|F|}$$

其中 $F$ 是所有功能点集合，$T$ 是测试用例集合。

全栈测试框架示例:

```rust
// shared/src/tests.rs
use crate::models::*;
use crate::validation::*;

# [test]
fn test_user_validation() {
    // 有效用户
    let valid_user = User {
        id: Some(1),
        username: "validuser".into(),
        email: "user@example.com".into(),
        role: UserRole::Regular,
        profile: UserProfile::default(),
    };

    assert!(valid_user.validate().is_ok());

    // 无效用户 - 用户名太短
    let invalid_user = User {
        id: Some(2),
        username: "ab".into(), // 少于3个字符
        email: "user@example.com".into(),
        role: UserRole::Regular,
        profile: UserProfile::default(),
    };

    let validation_result = invalid_user.validate();
    assert!(validation_result.is_err());

    let errors = validation_result.unwrap_err();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].field, "username");
}

// 前端WebAssembly测试
# [cfg(target_arch = "wasm32")]
mod wasm_tests {
    use wasm_bindgen_test::*;
    use crate::api::*;
    use crate::models::*;

    wasm_bindgen_test_configure!(run_in_browser);

    #[wasm_bindgen_test]
    fn test_api_response_deserialization() {
        let json = r#"{"success":true,"data":{"id":1,"username":"testuser","email":"test@example.com","role":"Regular","profile":{}},"error":null}"#;

        let response: ApiResponse<User> = serde_json::from_str(json).unwrap();
        assert!(response.success);
        assert!(response.error.is_none());

        let user = response.data.unwrap();
        assert_eq!(user.id, Some(1));
        assert_eq!(user.username, "testuser");
    }
}

// backend/tests/integration_tests.rs
use backend::server;
use shared::models::*;
use shared::api::*;
use axum::http::StatusCode;
use axum::body::Body;
use tower::ServiceExt;
use http_body_util::BodyExt;

# [tokio::test]
async fn test_create_user_endpoint() {
    // 创建测试应用
    let app = server::create_app().await;

    // 构建测试请求
    let create_request = CreateUserRequest {
        username: "testuser".into(),
        email: "test@example.com".into(),
        password: "password123".into(),
    };

    let request = axum::http::Request::builder()
        .uri("/api/users")
        .method("POST")
        .header("Content-Type", "application/json")
        .body(Body::from(serde_json::to_string(&create_request).unwrap()))
        .unwrap();

    // 发送请求并检查响应
    let response = app.oneshot(request).await.unwrap();
    assert_eq!(response.status(), StatusCode::CREATED);

    // 解析响应体
    let body = response.into_body().collect().await.unwrap().to_bytes();
    let api_response: ApiResponse<User> = serde_json::from_slice(&body).unwrap();

    assert!(api_response.success);
    let user = api_response.data.unwrap();
    assert_eq!(user.username, "testuser");
    assert_eq!(user.email, "test@example.com");
}
```

## 8. 典型应用架构模式

### 8.1 同构渲染架构

同构渲染架构可形式化为渲染函数:
$$R: \text{Component} \times \text{State} \times \text{Environment} \rightarrow \text{HTML}$$

其中 $\text{Environment} \in \{\text{Server}, \text{Client}\}$。

同构渲染架构示例:

```rust
// shared/src/rendering.rs
use serde::{Serialize, Deserialize};

// 定义通用组件特征
pub trait IsomorphicComponent {
    type Props: Serialize + for<'de> Deserialize<'de>;

    // 服务器端渲染
    fn render_to_string(props: &Self::Props) -> String;

    // 客户端水合
    #[cfg(target_arch = "wasm32")]
    fn hydrate(props: Self::Props, element_id: &str);
}

// 实现一个同构组件
pub struct UserProfile;

# [derive(Serialize, Deserialize)]
pub struct UserProfileProps {
    pub username: String,
    pub bio: Option<String>,
    pub avatar_url: Option<String>,
}

impl IsomorphicComponent for UserProfile {
    type Props = UserProfileProps;

    fn render_to_string(props: &Self::Props) -> String {
        format!(r#"
        <div class="user-profile" data-component="user-profile" id="profile-{}">
            <div class="avatar">
                <img src="{}" alt="{}'s avatar">
            </div>
            <div class="info">
                <h2>{}</h2>
                <p>{}</p>
            </div>
        </div>
        "#,
        props.username,
        props.avatar_url.as_deref().unwrap_or("/default-avatar.png"),
        props.username,
        props.username,
        props.bio.as_deref().unwrap_or("No bio provided.")
        )
    }

    #[cfg(target_arch = "wasm32")]
    fn hydrate(props: Self::Props, element_id: &str) {
        use wasm_bindgen::JsCast;
        use web_sys::{window, HtmlElement, Element};

        let window = window().unwrap();
        let document = window.document().unwrap();

        // 查找目标元素
        if let Some(element) = document.get_element_by_id(element_id) {
            // 在客户端添加交互性
            let avatar_element = element
                .query_selector(".avatar img")
                .unwrap()
                .unwrap();

            // 添加点击事件处理程序
            let click_handler = wasm_bindgen::closure::Closure::wrap(
                Box::new(move |_: web_sys::MouseEvent| {
                    // 处理头像点击
                    let window = window().unwrap();
                    window.alert_with_message("头像被点击了!").unwrap();
                }) as Box<dyn FnMut(_)>
            );

            avatar_element
                .dyn_ref::<HtmlElement>()
                .unwrap()
                .set_onclick(Some(click_handler.as_ref().unchecked_ref()));

            // 防止闭包被回收
            click_handler.forget();
        }
    }
}

// 服务器端使用
# [cfg(not(target_arch = "wasm32"))]
pub mod server {
    use super::*;
    use axum::{response::Html, extract::Json};

    // 服务器端渲染端点
    pub async fn render_user_profile(
        Json(props): Json<UserProfileProps>
    ) -> Html<String> {
        let html = UserProfile::render_to_string(&props);
        Html(html)
    }

    // 生成包含初始状态的完整页面
    pub fn render_page_with_state<T: Serialize>(
        component_name: &str,
        props: &T
    ) -> String {
        let serialized_props = serde_json::to_string(props).unwrap();
        let escaped_props = html_escape::encode_safe(&serialized_props);

        format!(r#"
        <!DOCTYPE html>
        <html>
        <head>
            <meta charset="UTF-8">
            <title>Isomorphic Rust App</title>
            <link rel="stylesheet" href="/styles.css">
        </head>
        <body>
            <div id="app">
                <!-- 服务器渲染的内容将在这里 -->
            </div>

            <script id="initial-state" type="application/json">
                {}
            </script>
            <script type="module">
                import {{ initialize }} from '/js/app.js';

                // 加载初始状态
                const stateElement = document.getElementById('initial-state');
                const initialState = JSON.parse(stateElement.textContent);

                // 初始化应用
                initialize('{}', initialState);
            </script>
        </body>
        </html>
        "#,
        escaped_props,
        component_name
        )
    }
}

// 客户端水合
# [cfg(target_arch = "wasm32")]
pub mod client {
    use super::*;
    use wasm_bindgen::prelude::*;

    #[wasm_bindgen]
    pub fn initialize(component_name: &str, props_json: &str) {
        match component_name {
            "user-profile" => {
                let props: UserProfileProps = serde_json::from_str(props_json).unwrap();
                let element_id = format!("profile-{}", props.username);
                UserProfile::hydrate(props, &element_id);
            },
            // 其他组件...
            _ => {
                console_log!("未知组件类型: {}", component_name);
            }
        }
    }
}
```

### 8.2 微服务架构

Rust+WebAssembly微服务架构可形式化为服务组合:
$$S = \{s_1, s_2, ..., s_n\}, \text{每个} s_i \text{是一个独立的WebAssembly模块}$$

微服务架构示例:

```rust
// 微服务注册表
use std::collections::HashMap;
use wasmtime::{Engine, Module, Store, Instance, Linker};
use async_trait::async_trait;

// 服务接口
# [async_trait]
pub trait MicroService {
    async fn handle_request(&self, input: &[u8]) -> Result<Vec<u8>, ServiceError>;
    fn service_name(&self) -> &str;
    fn version(&self) -> &str;
}

// WebAssembly服务实现
pub struct WasmService {
    name: String,
    version: String,
    engine: Engine,
    module: Module,
    imports: HashMap<String, Box<dyn Fn() + Send + Sync>>,
}

impl WasmService {
    pub fn new(name: &str, version: &str, wasm_bytes: &[u8]) -> Result<Self, ServiceError> {
        let engine = Engine::default();
        let module = Module::new(&engine, wasm_bytes)?;

        Ok(Self {
            name: name.to_string(),
            version: version.to_string(),
            engine,
            module,
            imports: HashMap::new(),
        })
    }

    pub fn add_import<F>(&mut self, name: &str, func: F)
    where
        F: Fn() + Send + Sync + 'static,
    {
        self.imports.insert(name.to_string(), Box::new(func));
    }
}

# [async_trait]
impl MicroService for WasmService {
    async fn handle_request(&self, input: &[u8]) -> Result<Vec<u8>, ServiceError> {
        let mut store = Store::new(&self.engine, ());
        let mut linker = Linker::new(&self.engine);

        // 添加导入函数
        for (name, _func) in &self.imports {
            // 这里简化了，实际需要根据函数签名适配
            // ...
        }

        // 实例化模块
        let instance = linker.instantiate(&mut store, &self.module)?;

        // 调用处理函数
        let memory = instance.get_memory(&mut store, "memory")
            .ok_or_else(|| ServiceError::MissingMemory)?;

        // 分配内存并写入输入数据
        // ...

        // 调用导出的处理函数
        let handle_func = instance.get_typed_func::<(i32, i32), i32>(&mut store, "handle_request")?;
        // ...

        // 从内存读取结果
        // ...

        Ok(vec![])
    }

    fn service_name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }
}

// 服务注册表
pub struct ServiceRegistry {
    services: HashMap<String, Box<dyn MicroService + Send + Sync>>,
}

impl ServiceRegistry {
    pub fn new() -> Self {
        Self {
            services: HashMap::new(),
        }
    }

    pub fn register<S>(&mut self, service: S)
    where
        S: MicroService + Send + Sync + 'static,
    {
        let key = format!("{}-{}", service.service_name(), service.version());
        self.services.insert(key, Box::new(service));
    }

    pub async fn dispatch(&self, service: &str, version: &str, input: &[u8]) -> Result<Vec<u8>, ServiceError> {
        let key = format!("{}-{}", service, version);

        if let Some(service) = self.services.get(&key) {
            service.handle_request(input).await
        } else {
            Err(ServiceError::ServiceNotFound)
        }
    }
}
```

### 8.3 边缘计算架构

边缘计算架构可形式化为函数分布式部署:
$$D: F \rightarrow \{Edge, CDN, Client, Server\}$$

边缘计算架构示例:

```rust
    // 边缘计算应用示例
    use worker::*;

    # [event(fetch)]
    async fn main(req: Request, env: Env, _ctx: Context) -> Result<Response> {
        // 匹配路由
        Router::new()
            .get("/", |_, _| Response::ok("Rust WebAssembly Edge Worker"))
            .get("/api/user/:id", get_user)
            .post("/api/data", handle_data)
            .run(req, env)
            .await
    }

    // 用户API处理函数
    async fn get_user(req: Request, ctx: RouteContext<()>) -> Result<Response> {
        // 从URL获取用户ID
        let user_id = ctx.param("id")
            .ok_or_else(|| Error::RustError("Missing user ID".into()))?;

        // 从KV存储获取用户数据
        let kv = ctx.kv("USERS_NAMESPACE")?;
        let user_data = match kv.get(user_id).text().await? {
            Some(data) => data,
            None => return Response::error("User not found", 404),
        };

        // 返回JSON响应
        let mut headers = Headers::new();
        headers.set("Content-Type", "application/json")?;

        Ok(Response::from_body(ResponseBody::Body(user_data.into_bytes()))
            .unwrap()
            .with_headers(headers))
    }

    // 数据处理函数
    async fn handle_data(mut req: Request, ctx: RouteContext<()>) -> Result<Response> {
        // 解析请求JSON
        let data: serde_json::Value = req.json().await?;

        // 处理数据
        let processed = process_data(data)?;

        // 存储结果
        let kv = ctx.kv("RESULTS_NAMESPACE")?;
        let key = format!("result-{}", js_sys::Date::now());
        kv.put(&key, processed.to_string())?.execute().await?;

        // 返回成功响应
        Response::ok("Data processed successfully")
    }

    // 数据处理函数
    fn process_data(data: serde_json::Value) -> Result<serde_json::Value> {
        // 这里是运行在边缘的数据处理代码
        // 可以进行数据转换、验证、筛选等操作

        // 这个示例简单地添加处理时间戳
        let mut result = data.as_object()
            .ok_or_else(|| Error::RustError("Expected JSON object".into()))?
            .clone();

        result.insert(
            "processed_at".to_string(),
            serde_json::Value::String(js_sys::Date::now().to_string()),
        );

        // 结果包装成JSON对象返回
        Ok(serde_json::Value::Object(result))
    }

    // 边缘环境配置
    #[worker_configuration]
    pub struct WorkerConfig {
        // KV命名空间
        #[kv(name = "USERS_NAMESPACE")]
        users: KvStore,

        #[kv(name = "RESULTS_NAMESPACE")]
        results: KvStore,

        // 环境变量
        #[var(name = "API_KEY")]
        api_key: String,

        // 秘密值
        #[secret(name = "AUTH_SECRET")]
        auth_secret: String,
    }

    // 边缘和客户端间通信的状态同步
    struct StateSynchronizer {
        last_updated: f64,
    }

    impl StateSynchronizer {
        fn new() -> Self {
            Self {
                last_updated: js_sys::Date::now(),
            }
        }

        // 增量同步状态
        async fn sync_state(&mut self, ctx: &RouteContext<()>) -> Result<Vec<StateChange>> {
            let kv = ctx.kv("STATE_NAMESPACE")?;

            // 获取比last_updated更新的所有状态变化
            let changes = kv.list()
                .prefix("state-")
                .execute()
                .await?
                .keys;

            let mut state_changes = Vec::new();

            for key in changes {
                let metadata = key.metadata
                    .as_ref()
                    .and_then(|m| m.as_object());

                if let Some(meta) = metadata {
                    if let Some(updated) = meta.get("updated").and_then(|v| v.as_f64()) {
                        if updated > self.last_updated {
                            // 获取状态变化内容
                            if let Some(value) = kv.get(&key.name).json::<StateChange>().await? {
                                state_changes.push(value);
                            }
                        }
                    }
                }
            }

            // 更新同步时间戳
            self.last_updated = js_sys::Date::now();

            Ok(state_changes)
        }
    }

    // 状态变化结构
    #[derive(Serialize, Deserialize)]
    struct StateChange {
        key: String,
        value: serde_json::Value,
        timestamp: f64,
    }
```

## 9. 性能与资源消耗

### 9.1 性能基准测试

性能可形式化为关键性能指标(KPI)集:
$$\text{Performance} = \{T_{load}, T_{execution}, M_{usage}, N_{transfers}\}$$

性能基准测试代码:

```rust
    // benchmarks/src/main.rs
    use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
    use std::time::{Duration, Instant};
    use wasm_bindgen_test::*;
    use serde::{Serialize, Deserialize};

    // 共享数据结构用于序列化基准测试
    #[derive(Clone, Serialize, Deserialize)]
    struct BenchData {
        id: u64,
        name: String,
        values: Vec<f64>,
        metadata: std::collections::HashMap<String, String>,
    }

    impl BenchData {
        fn new_sample(size: usize) -> Self {
            let mut values = Vec::with_capacity(size);
            let mut metadata = std::collections::HashMap::new();

            for i in 0..size {
                values.push(i as f64);
                metadata.insert(format!("key_{}", i), format!("value_{}", i));
            }

            Self {
                id: 1,
                name: "Sample benchmark data".to_string(),
                values,
                metadata,
            }
        }
    }

    // JSON序列化基准测试
    fn bench_json_serialization(c: &mut Criterion) {
        let mut group = c.benchmark_group("serialization");

        for size in [10, 100, 1000].iter() {
            let data = BenchData::new_sample(*size);

            group.bench_with_input(
                BenchmarkId::new("json", size),
                &data,
                |b, data| {
                    b.iter(|| serde_json::to_string(data).unwrap())
                }
            );

            group.bench_with_input(
                BenchmarkId::new("bincode", size),
                &data,
                |b, data| {
                    b.iter(|| bincode::serialize(data).unwrap())
                }
            );

            group.bench_with_input(
                BenchmarkId::new("messagepack", size),
                &data,
                |b, data| {
                    b.iter(|| rmp_serde::to_vec(data).unwrap())
                }
            );
        }

        group.finish();
    }

    // 计算密集型操作基准测试
    fn bench_computation(c: &mut Criterion) {
        fn fibonacci_recursive(n: u64) -> u64 {
            match n {
                0 => 0,
                1 => 1,
                n => fibonacci_recursive(n-1) + fibonacci_recursive(n-2),
            }
        }

        fn fibonacci_iterative(n: u64) -> u64 {
            if n <= 1 {
                return n;
            }

            let mut a = 0;
            let mut b = 1;

            for _ in 2..=n {
                let temp = a + b;
                a = b;
                b = temp;
            }

            b
        }

        let mut group = c.benchmark_group("fibonacci");

        for n in [10, 20, 30].iter() {
            group.bench_with_input(
                BenchmarkId::new("recursive", n),
                n,
                |b, &n| {
                    b.iter(|| fibonacci_recursive(n))
                }
            );

            group.bench_with_input(
                BenchmarkId::new("iterative", n),
                n,
                |b, &n| {
                    b.iter(|| fibonacci_iterative(n))
                }
            );
        }

        group.finish();
    }

    // WASM特定的性能测试
    #[cfg(target_arch = "wasm32")]
    mod wasm_benchmarks {
        use super::*;
        use wasm_bindgen::prelude::*;
        use wasm_bindgen_test::*;
        use web_sys::{window, console, Performance};

        // 测量WASM函数调用开销
        #[wasm_bindgen_test]
        fn measure_wasm_call_overhead() {
            let window = window().unwrap();
            let performance = window.performance().unwrap();

            let warmup_rounds = 1000;
            let measure_rounds = 10000;

            // 预热
            for _ in 0..warmup_rounds {
                black_box(empty_function());
            }

            // 测量
            let start = performance.now();

            for _ in 0..measure_rounds {
                black_box(empty_function());
            }

            let end = performance.now();
            let avg_time = (end - start) / (measure_rounds as f64);

            console::log_1(&format!("Average WASM function call time: {:.6} ms", avg_time).into());
        }

        // 空函数，用于测量调用开销
        fn empty_function() -> i32 {
            0
        }

        // 测量DOM访问性能
        #[wasm_bindgen_test]
        fn measure_dom_access() {
            let window = window().unwrap();
            let document = window.document().unwrap();
            let performance = window.performance().unwrap();

            // 创建测试元素
            let div = document.create_element("div").unwrap();
            document.body().unwrap().append_child(&div).unwrap();

            const ITERATIONS: u32 = 1000;

            // 测量元素属性设置性能
            let start = performance.now();

            for i in 0..ITERATIONS {
                div.set_text_content(Some(&format!("Test content {}", i)));
            }

            let end = performance.now();
            let avg_time = (end - start) / (ITERATIONS as f64);

            console::log_1(&format!("Average DOM text update time: {:.6} ms", avg_time).into());

            // 清理
            document.body().unwrap().remove_child(&div).unwrap();
        }
    }

    // 主函数
    criterion_group!(benches, bench_json_serialization, bench_computation);
    criterion_main!(benches);
```

### 9.2 资源利用分析

资源利用可形式化为资源向量:
$$R = (C_{cpu}, M_{heap}, M_{stack}, B_{transfer})$$

资源监控代码示例:

```rust
    // 资源监控模块
    use std::time::{Duration, Instant};
    use serde::Serialize;

    // 性能度量结构
    #[derive(Debug, Clone, Serialize)]
    pub struct PerformanceMetrics {
        // 内存指标
        pub wasm_heap_size: usize,
        pub wasm_memory_limit: usize,
        pub wasm_memory_usage_percent: f64,

        // 计时指标
        pub initialization_time_ms: f64,
        pub execution_time_ms: f64,
        pub total_time_ms: f64,

        // 网络指标
        pub bytes_transferred: usize,
        pub requests_count: usize,

        // 计算指标
        pub operations_count: usize,
        pub operations_per_second: f64,
    }

    #[cfg(target_arch = "wasm32")]
    pub mod wasm {
        use super::*;
        use wasm_bindgen::prelude::*;
        use js_sys::{global, Function, Object, Reflect};
        use web_sys::{Performance, console};

        // WASM性能监控
        pub struct PerformanceMonitor {
            start_time: f64,
            operations: usize,
            requests: usize,
            bytes: usize,
            marks: std::collections::HashMap<String, f64>,
        }

        impl PerformanceMonitor {
            pub fn new() -> Self {
                let window = web_sys::window().unwrap();
                let performance = window.performance().unwrap();

                Self {
                    start_time: performance.now(),
                    operations: 0,
                    requests: 0,
                    bytes: 0,
                    marks: std::collections::HashMap::new(),
                }
            }

            pub fn mark(&mut self, name: &str) {
                let window = web_sys::window().unwrap();
                let performance = window.performance().unwrap();

                self.marks.insert(name.to_string(), performance.now());
            }

            pub fn measure(&self, start_mark: &str, end_mark: &str) -> Option<f64> {
                if let (Some(start), Some(end)) = (self.marks.get(start_mark), self.marks.get(end_mark)) {
                    Some(end - start)
                } else {
                    None
                }
            }

            pub fn increment_operations(&mut self, count: usize) {
                self.operations += count;
            }

            pub fn record_request(&mut self, bytes: usize) {
                self.requests += 1;
                self.bytes += bytes;
            }

            pub fn collect_metrics(&self) -> PerformanceMetrics {
                let window = web_sys::window().unwrap();
                let performance = window.performance().unwrap();

                // 获取WebAssembly内存信息
                let memory = wasm_bindgen::memory();
                let heap_size = memory.dyn_into::<js_sys::WebAssembly::Memory>().ok()
                    .map(|m| m.buffer().byte_length())
                    .unwrap_or(0) as usize;

                // 获取内存限制(如果可能)
                let memory_limit = heap_size * 2; // 这里简化处理，实际应从WebAssembly.Memory.grow限制获取

                let end_time = performance.now();
                let total_time = end_time - self.start_time;

                PerformanceMetrics {
                    wasm_heap_size: heap_size,
                    wasm_memory_limit: memory_limit,
                    wasm_memory_usage_percent: (heap_size as f64 / memory_limit as f64) * 100.0,

                    initialization_time_ms: self.marks.get("init_complete")
                        .map(|t| t - self.start_time)
                        .unwrap_or(0.0),
                    execution_time_ms: total_time - self.initialization_time_ms,
                    total_time_ms: total_time,

                    bytes_transferred: self.bytes,
                    requests_count: self.requests,

                    operations_count: self.operations,
                    operations_per_second: if total_time > 0.0 {
                        (self.operations as f64) / (total_time / 1000.0)
                    } else {
                        0.0
                    },
                }
            }

            // 将性能数据发送回服务器
            pub async fn report_metrics(&self) -> Result<(), JsValue> {
                let metrics = self.collect_metrics();
                let json = serde_json::to_string(&metrics).unwrap();

                let window = web_sys::window().unwrap();
                let fetch = window.fetch_with_str("/api/metrics");

                let response = wasm_bindgen_futures::JsFuture::from(fetch).await?;
                Ok(())
            }
        }
    }

    // 服务器端资源监控
    #[cfg(not(target_arch = "wasm32"))]
    pub mod server {
        use super::*;
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Arc;

        // 服务器性能监控
        pub struct ServerMonitor {
            start_time: Instant,
            active_connections: Arc<AtomicUsize>,
            total_requests: Arc<AtomicUsize>,
            total_bytes: Arc<AtomicUsize>,
            operations: Arc<AtomicUsize>,
        }

        impl ServerMonitor {
            pub fn new() -> Self {
                Self {
                    start_time: Instant::now(),
                    active_connections: Arc::new(AtomicUsize::new(0)),
                    total_requests: Arc::new(AtomicUsize::new(0)),
                    total_bytes: Arc::new(AtomicUsize::new(0)),
                    operations: Arc::new(AtomicUsize::new(0)),
                }
            }

            pub fn connection_opened(&self) {
                self.active_connections.fetch_add(1, Ordering::SeqCst);
            }

            pub fn connection_closed(&self) {
                self.active_connections.fetch_sub(1, Ordering::SeqCst);
            }

            pub fn request_processed(&self, bytes: usize) {
                self.total_requests.fetch_add(1, Ordering::SeqCst);
                self.total_bytes.fetch_add(bytes, Ordering::SeqCst);
            }

            pub fn operations_executed(&self, count: usize) {
                self.operations.fetch_add(count, Ordering::SeqCst);
            }

            // 性能指标中间件
            pub fn metrics_middleware() -> impl Fn() + Clone {
                let monitor = ServerMonitor::new();
                let monitor_clone = monitor.clone();

                // 返回一个可以包装到服务器框架中的中间件
                move || {
                    // ...根据具体框架实现逻辑
                }
            }

            // 获取当前指标
            pub fn collect_metrics(&self) -> ServerMetrics {
                let elapsed = self.start_time.elapsed();
                let seconds = elapsed.as_secs_f64();

                let total_requests = self.total_requests.load(Ordering::SeqCst);
                let total_bytes = self.total_bytes.load(Ordering::SeqCst);
                let operations = self.operations.load(Ordering::SeqCst);

                ServerMetrics {
                    uptime_seconds: seconds,
                    active_connections: self.active_connections.load(Ordering::SeqCst),
                    total_requests,
                    total_bytes,
                    operations,
                    requests_per_second: if seconds > 0.0 { total_requests as f64 / seconds } else { 0.0 },
                    bytes_per_second: if seconds > 0.0 { total_bytes as f64 / seconds } else { 0.0 },
                    operations_per_second: if seconds > 0.0 { operations as f64 / seconds } else { 0.0 },
                }
            }
        }

        // 服务器性能指标
        #[derive(Debug, Clone, Serialize)]
        pub struct ServerMetrics {
            pub uptime_seconds: f64,
            pub active_connections: usize,
            pub total_requests: usize,
            pub total_bytes: usize,
            pub operations: usize,
            pub requests_per_second: f64,
            pub bytes_per_second: f64,
            pub operations_per_second: f64,
        }
    }
```

### 9.3 优化策略

优化策略可以形式化为一系列转换:
$$O: \text{Program} \rightarrow \text{Program}'$$
使得 $\text{Performance}(\text{Program}') > \text{Performance}(\text{Program})$

```rust
    // 优化策略实现示例
    // 1. 代码尺寸优化
    #[cfg(target_arch = "wasm32")]
    mod size_optimized {
        // 合并相似函数
        pub fn process_with_mode(data: &[u8], mode: u8) -> Vec<u8> {
            match mode {
                0 => data.to_vec(),
                1 => data.iter().map(|&b| b.wrapping_add(1)).collect(),
                2 => data.iter().map(|&b| b.wrapping_sub(1)).collect(),
                _ => data.iter().map(|&b| !b).collect(),
            }
        }

        // 使用宏生成重复代码
        macro_rules! impl_handlers {
            ($($name:ident: $expr:expr),*) => {
                $(
                    pub fn $name(value: i32) -> i32 {
                        $expr(value)
                    }
                )*
            };
        }

        impl_handlers! {
            double: |x| x * 2,
            triple: |x| x * 3,
            square: |x| x * x,
            increment: |x| x + 1
        }
    }

    // 2. 计算性能优化
    mod compute_optimized {
        // SIMD优化(当Wasm SIMD可用时)
        #[cfg(all(target_arch = "wasm32", target_feature = "simd128"))]
        pub fn sum_f32_simd(values: &[f32]) -> f32 {
            use core::arch::wasm32::*;

            let len = values.len();
            let mut sum = f32x4_splat(0.0);
            let mut i = 0;

            // 使用SIMD一次处理4个f32
            while i + 4 <= len {
                let v = unsafe {
                    v128_load(&values[i] as *const f32 as *const v128)
                };
                sum = f32x4_add(sum, v);
                i += 4;
            }

            // 处理剩余的元素
            let sum_array = f32x4_extract_lane::<0>(sum) +
                        f32x4_extract_lane::<1>(sum) +
                        f32x4_extract_lane::<2>(sum) +
                        f32x4_extract_lane::<3>(sum);

            let mut final_sum = sum_array;
            for j in i..len {
                final_sum += values[j];
            }

            final_sum
        }

        // 缓存昂贵计算的结果
        pub struct Memoizer<K, V, F>
        where
            K: std::hash::Hash + Eq + Clone,
            V: Clone,
            F: Fn(&K) -> V,
        {
            cache: std::collections::HashMap<K, V>,
            function: F,
        }

        impl<K, V, F> Memoizer<K, V, F>
        where
            K: std::hash::Hash + Eq + Clone,
            V: Clone,
            F: Fn(&K) -> V,
        {
            pub fn new(function: F) -> Self {
                Self {
                    cache: std::collections::HashMap::new(),
                    function,
                }
            }

            pub fn get(&mut self, key: &K) -> V {
                if let Some(value) = self.cache.get(key) {
                    value.clone()
                } else {
                    let value = (self.function)(key);
                    self.cache.insert(key.clone(), value.clone());
                    value
                }
            }
        }
    }

    // 3. 内存管理优化
    mod memory_optimized {
        // 使用固定大小的缓冲区
        use arrayvec::ArrayVec;

        pub fn process_fixed_size<const N: usize>(data: &[u8]) -> ArrayVec<u8, N> {
            let mut result = ArrayVec::<u8, N>::new();

            for &byte in data {
                if !result.is_full() {
                    result.push(byte.wrapping_add(1));
                }
            }

            result
        }

        // 自定义内存分配
        #[cfg(target_arch = "wasm32")]
        mod custom_alloc {
            use std::alloc::{GlobalAlloc, Layout};
            use std::cell::UnsafeCell;
            use std::ptr::NonNull;

            // 简单的池分配器，适用于小尺寸相同的对象
            pub struct BumpAllocator {
                heap: UnsafeCell<Vec<u8>>,
                position: UnsafeCell<usize>,
            }

            impl BumpAllocator {
                pub fn new(capacity: usize) -> Self {
                    Self {
                        heap: UnsafeCell::new(Vec::with_capacity(capacity)),
                        position: UnsafeCell::new(0),
                    }
                }

                pub fn reset(&self) {
                    unsafe {
                        *self.position.get() = 0;
                    }
                }
            }

            unsafe impl GlobalAlloc for BumpAllocator {
                unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
                    let heap = &mut *self.heap.get();
                    let position = &mut *self.position.get();

                    // 计算对齐偏移
                    let align_offset = (*position % layout.align()).wrapping_neg() % layout.align();
                    *position += align_offset;

                    // 检查是否有足够空间
                    if *position + layout.size() > heap.capacity() {
                        return std::ptr::null_mut();
                    }

                    // 分配内存
                    let ptr = heap.as_mut_ptr().add(*position);
                    *position += layout.size();

                    ptr
                }

                unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
                    // 这个简单的分配器不支持单独释放，只能通过reset()重置整个池
                }
            }
        }
    }
```

## 10. 生产实践考量

### 10.1 部署策略

部署策略可形式化为部署函数:
$$D: \text{Artifacts} \rightarrow \text{Environment}$$

```rust
    // 部署配置示例
    use serde::{Serialize, Deserialize};
    use std::collections::HashMap;

    // 部署配置
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct DeploymentConfig {
        // 应用标识
        pub app_id: String,
        pub version: String,

        // 前端配置
        pub frontend: FrontendConfig,

        // 后端配置
        pub backend: BackendConfig,

        // 环境变量
        pub environment: HashMap<String, String>,

        // 功能标记
        pub feature_flags: HashMap<String, bool>,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct FrontendConfig {
        pub assets_path: String,
        pub api_endpoints: HashMap<String, String>,
        pub chunk_size: Option<usize>,
        pub cache_strategy: CacheStrategy,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct BackendConfig {
        pub host: String,
        pub port: u16,
        pub workers: usize,
        pub database_url: String,
        pub log_level: String,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub enum CacheStrategy {
        NoCache,
        ShortTerm,
        LongTerm,
        Custom(u32), // 秒数
    }

    // 部署管理器
    pub struct DeploymentManager {
        config: DeploymentConfig,
    }

    impl DeploymentManager {
        pub fn new(config: DeploymentConfig) -> Self {
            Self { config }
        }

        // 生成WASM部署清单
        pub fn generate_wasm_manifest(&self) -> String {
            let manifest = serde_json::json!({
                "app_id": self.config.app_id,
                "version": self.config.version,
                "api_endpoints": self.config.frontend.api_endpoints,
                "environment": self.config.environment,
                "feature_flags": self.config.feature_flags,
            });

            serde_json::to_string_pretty(&manifest).unwrap()
        }

        // 生成Nginx配置
        pub fn generate_nginx_config(&self) -> String {
            format!(r#"
            server {{
                listen 80;
                server_name {app_id}.example.com;

                location / {{
                    root /var/www/{app_id}/{version};
                    index index.html;
                    try_files $uri $uri/ /index.html;

                    # 缓存策略
                    {cache_headers}
                }}

                location /api/ {{
                    proxy_pass http://{backend_host}:{backend_port};
                    proxy_set_header Host $host;
                    proxy_set_header X-Real-IP $remote_addr;
                }}
            }}
            "#,
            app_id = self.config.app_id,
            version = self.config.version,
            backend_host = self.config.backend.host,
            backend_port = self.config.backend.port,
            cache_headers = match self.config.frontend.cache_strategy {
                CacheStrategy::NoCache =>
                    "add_header Cache-Control \"no-store, no-cache, must-revalidate\";",
                CacheStrategy::ShortTerm =>
                    "add_header Cache-Control \"public, max-age=300\";",
                CacheStrategy::LongTerm =>
                    "add_header Cache-Control \"public, max-age=31536000\";",
                CacheStrategy::Custom(seconds) =>
                    format!("add_header Cache-Control \"public, max-age={}\";", seconds),
            })
        }

        // 生成Docker Compose配置
        pub fn generate_docker_compose(&self) -> String {
            format!(r#"
            version: '3.8'

            services:
            frontend:
                image: rust-wasm-frontend:{version}
                ports:
                - "80:80"
                environment:
            {frontend_env}

            backend:
                image: rust-backend:{version}
                ports:
                - "{backend_port}:{backend_port}"
                environment:
            {backend_env}
                depends_on:
                - database

            database:
                image: postgres:13
                volumes:
                - db_data:/var/lib/postgresql/data
                environment:
                - POSTGRES_PASSWORD=password
                - POSTGRES_USER={app_id}
                - POSTGRES_DB={app_id}

            volumes:
            db_data:
            "#,
            version = self.config.version,
            app_id = self.config.app_id,
            backend_port = self.config.backend.port,
            frontend_env = self.config.environment.iter()
                .map(|(k, v)| format!("      - {}={}", k, v))
                .collect::<Vec<_>>()
                .join("\n"),
            backend_env = format!("      - DATABASE_URL={}\n      - LOG_LEVEL={}",
                self.config.backend.database_url,
                self.config.backend.log_level)
            )
        }
    }
```

### 10.2 可观测性

可观测性可形式化为观测函数:
$$O: \text{System} \rightarrow \text{Metrics} \times \text{Logs} \times \text{Traces}$$

```rust
    // 可观测性模块
    use serde::Serialize;
    use std::time::Instant;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use tracing::{info, error, warn, debug, span, Level};
    use opentelemetry::trace::{Tracer, SpanKind, FutureExt};

    // 通用指标上下文
    #[derive(Debug, Clone, Serialize)]
    pub struct MetricContext {
        pub service: String,
        pub instance: String,
        pub version: String,
        pub environment: String,
        pub timestamp: u64,
    }

    // 跨前后端的跟踪器接口
    pub trait Telemetry {
        fn record_metric(&self, name: &str, value: f64, labels: Vec<(&str, String)>);
        fn start_span(&self, name: &str) -> SpanHandle;
        fn log_event(&self, level: LogLevel, message: &str, metadata: Option<serde_json::Value>);
    }

    // 日志级别
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum LogLevel {
        Error,
        Warn,
        Info,
        Debug,
        Trace,
    }

    // 跨度处理
    pub struct SpanHandle {
        span_id: String,
        start_time: Instant,
        tracer: Box<dyn Telemetry>,
        name: String,
    }

    impl SpanHandle {
        pub fn new(span_id: String, name: String, tracer: Box<dyn Telemetry>) -> Self {
            Self {
                span_id,
                start_time: Instant::now(),
                tracer,
                name,
            }
        }

        pub fn add_event(&self, name: &str, attributes: Option<serde_json::Value>) {
            self.tracer.log_event(
                LogLevel::Debug,
                &format!("Event in span {}: {}", self.name, name),
                attributes
            );
        }
    }

    impl Drop for SpanHandle {
        fn drop(&mut self) {
            let duration = self.start_time.elapsed().as_millis() as f64;
            self.tracer.record_metric(
                "span_duration_ms",
                duration,
                vec![("span_name", self.name.clone())]
            );
        }
    }

    // 前端实现
    #[cfg(target_arch = "wasm32")]
    pub mod wasm {
        use super::*;
        use wasm_bindgen::prelude::*;
        use web_sys::{console, window, Performance};
        use js_sys::{Date, Math};

        // WebAssembly遥测实现
        pub struct WasmTelemetry {
            context: MetricContext,
            buffer: Vec<serde_json::Value>,
            buffer_size_limit: usize,
        }

        impl WasmTelemetry {
            pub fn new(service: &str, version: &str, environment: &str) -> Self {
                let window = window().unwrap();
                let location = window.location();
                let hostname = location.hostname().unwrap_or_else(|_| "unknown".into());

                Self {
                    context: MetricContext {
                        service: service.to_string(),
                        instance: hostname,
                        version: version.to_string(),
                        environment: environment.to_string(),
                        timestamp: Date::now() as u64,
                    },
                    buffer: Vec::new(),
                    buffer_size_limit: 100,
                }
            }

            // 发送缓冲的遥测数据
            pub async fn flush(&mut self) -> Result<(), JsValue> {
                if self.buffer.is_empty() {
                    return Ok(());
                }

                let window = window().unwrap();
                let payload = serde_json::to_string(&self.buffer).unwrap();

                let mut opts = web_sys::RequestInit::new();
                opts.method("POST");
                opts.body(Some(&JsValue::from_str(&payload)));

                let request = web_sys::Request::new_with_str_and_init(
                    "/api/telemetry",
                    &opts
                )?;

                request.headers().set("Content-Type", "application/json")?;

                let promise = window.fetch_with_request(&request);
                let _ = wasm_bindgen_futures::JsFuture::from(promise).await?;

                // 清空缓冲区
                self.buffer.clear();

                Ok(())
            }
        }

        impl Telemetry for WasmTelemetry {
            fn record_metric(&self, name: &str, value: f64, labels: Vec<(&str, String)>) {
                let mut metric = serde_json::json!({
                    "type": "metric",
                    "name": name,
                    "value": value,
                    "timestamp": Date::now(),
                    "context": self.context,
                });

                let labels_obj = labels.into_iter()
                    .map(|(k, v)| (k.to_string(), serde_json::Value::String(v)))
                    .collect::<serde_json::Map<String, serde_json::Value>>();

                metric["labels"] = serde_json::Value::Object(labels_obj);

                // 在开发环境记录到控制台
                if self.context.environment == "development" {
                    console::log_2(
                        &JsValue::from_str(&format!("Metric: {}", name)),
                        &JsValue::from_serde(&metric).unwrap()
                    );
                }

                // 添加到缓冲区，如果满了则进行异步发送
                let this = self.clone();
                if this.buffer.len() >= this.buffer_size_limit {
                    wasm_bindgen_futures::spawn_local(async move {
                        let mut telemetry = this;
                        let _ = telemetry.flush().await;
                    });
                }
            }

            fn start_span(&self, name: &str) -> SpanHandle {
                let span_id = format!("{:x}", (Date::now() as u32) ^ (Math::random() * 10000.0) as u32);

                let span_start = serde_json::json!({
                    "type": "span_start",
                    "span_id": span_id,
                    "name": name,
                    "timestamp": Date::now(),
                    "context": self.context,
                });

                // 添加到缓冲区
                self.buffer.push(span_start);

                SpanHandle::new(span_id, name.to_string(), Box::new(self.clone()))
            }

            fn log_event(&self, level: LogLevel, message: &str, metadata: Option<serde_json::Value>) {
                let level_str = match level {
                    LogLevel::Error => "error",
                    LogLevel::Warn => "warn",
                    LogLevel::Info => "info",
                    LogLevel::Debug => "debug",
                    LogLevel::Trace => "trace",
                };

                let log_event = serde_json::json!({
                    "type": "log",
                    "level": level_str,
                    "message": message,
                    "metadata": metadata,
                    "timestamp": Date::now(),
                    "context": self.context,
                });

                // 控制台记录
                match level {
                    LogLevel::Error => console::error_1(&JsValue::from_str(message)),
                    LogLevel::Warn => console::warn_1(&JsValue::from_str(message)),
                    LogLevel::Info => console::info_1(&JsValue::from_str(message)),
                    LogLevel::Debug | LogLevel::Trace =>
                        console::log_1(&JsValue::from_str(message)),
                }

                // 添加到缓冲区
                self.buffer.push(log_event);
            }
        }
    }

    // 后端实现
    #[cfg(not(target_arch = "wasm32"))]
    pub mod server {
        use super::*;
        use tracing::{info, error, warn, debug, trace};
        use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
        use opentelemetry::{global, sdk::export::metrics::aggregation, runtime::Tokio};
        use metrics::{counter, gauge, histogram};
        use uuid::Uuid;

        // 服务器遥测实现
        pub struct ServerTelemetry {
            context: MetricContext,
        }

        impl ServerTelemetry {
            pub fn new(service: &str, version: &str, environment: &str) -> Self {
                // 获取主机名
                let hostname = hostname::get()
                    .map(|h| h.to_string_lossy().into_owned())
                    .unwrap_or_else(|_| "unknown".to_string());

                Self {
                    context: MetricContext {
                        service: service.to_string(),
                        instance: hostname,
                        version: version.to_string(),
                        environment: environment.to_string(),
                        timestamp: std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .unwrap()
                            .as_secs(),
                    }
                }
            }

            // 初始化遥测系统
            pub fn init(service: &str, version: &str, environment: &str) -> Self {
                // 配置OpenTelemetry
                global::set_text_map_propagator(opentelemetry_jaeger::Propagator::new());
                let tracer = opentelemetry_jaeger::new_pipeline()
                    .with_service_name(service)
                    .install_simple()
                    .unwrap();

                // 配置Metrics
                let metrics_exporter = opentelemetry_prometheus::exporter()
                    .with_aggregator(aggregation::cumulative_temporality_selector())
                    .build()
                    .unwrap();

                let metrics_controller = opentelemetry::sdk::metrics::controllers::basic(
                    metrics_exporter
                ).build();

                let opentelemetry = tracing_opentelemetry::layer().with_tracer(tracer);

                // 配置日志
                tracing_subscriber::registry()
                    .with(opentelemetry)
                    .with(tracing_subscriber::EnvFilter::from_default_env())
                    .with(tracing_subscriber::fmt::layer())
                    .init();

                info!(
                    service = service,
                    version = version,
                    environment = environment,
                    "Telemetry initialized"
                );

                Self::new(service, version, environment)
            }
        }

        impl Telemetry for ServerTelemetry {
            fn record_metric(&self, name: &str, value: f64, labels: Vec<(&str, String)>) {
                // 构建标签
                let label_values: Vec<(&str, &str)> = labels.iter()
                    .map(|(k, v)| (*k, v.as_str()))
                    .collect();

                // 记录指标
                match name {
                    n if n.ends_with("_count") => {
                        counter!(name, value as u64, &label_values);
                    }
                    n if n.ends_with("_gauge") => {
                        gauge!(name, value, &label_values);
                    }
                    _ => {
                        histogram!(name, value, &label_values);
                    }
                }
            }

            fn start_span(&self, name: &str) -> SpanHandle {
                let span_id = Uuid::new_v4().to_string();
                let span = span!(Level::INFO, name, span_id = span_id);
                let _entered = span.enter();

                SpanHandle::new(span_id, name.to_string(), Box::new(self.clone()))
            }

            fn log_event(&self, level: LogLevel, message: &str, metadata: Option<serde_json::Value>) {
                let metadata_str = metadata.map(|m| m.to_string()).unwrap_or_default();

                match level {
                    LogLevel::Error => error!(message = message, metadata = metadata_str),
                    LogLevel::Warn => warn!(message = message, metadata = metadata_str),
                    LogLevel::Info => info!(message = message, metadata = metadata_str),
                    LogLevel::Debug => debug!(message = message, metadata = metadata_str),
                    LogLevel::Trace => trace!(message = message, metadata = metadata_str),
                }
            }
        }
    }
```

### 10.3 扩展性设计

扩展性设计可形式化为系统状态转换:
$$S_t \xrightarrow{G} S_{t+1}$$

其中 $G$ 是增长因子，$S_t$ 是时间 $t$ 的系统状态。

```rust
    // 扩展性设计模块
    // 1. 模块化工作流引擎
    pub mod workflow {
        use async_trait::async_trait;
        use serde::{Serialize, Deserialize};
        use std::collections::HashMap;

        // 工作流步骤接口
        #[async_trait]
        pub trait WorkflowStep {
            type Input: Serialize + for<'de> Deserialize<'de> + Send + Sync;
            type Output: Serialize + for<'de> Deserialize<'de> + Send + Sync;
            type Error: std::error::Error + Send + Sync;

            async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error>;
            fn step_name(&self) -> &str;
        }

        // 工作流定义
        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct Workflow {
            pub id: String,
            pub name: String,
            pub version: String,
            pub steps: Vec<StepDefinition>,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct StepDefinition {
            pub id: String,
            pub step_type: String,
            pub config: serde_json::Value,
            pub next_steps: Vec<Transition>,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct Transition {
            pub target_step: String,
            pub condition: Option<String>,
        }

        // 工作流引擎
        pub struct WorkflowEngine {
            step_registry: HashMap<String, Box<dyn StepFactory>>,
        }

        impl WorkflowEngine {
            pub fn new() -> Self {
                Self {
                    step_registry: HashMap::new(),
                }
            }

            pub fn register_step<F>(&mut self, step_type: &str, factory: F)
            where
                F: Fn(serde_json::Value) -> Box<dyn AnyStep> + Send + Sync + 'static,
            {
                self.step_registry.insert(
                    step_type.to_string(),
                    Box::new(move |config| factory(config))
                );
            }

            pub async fn execute_workflow(&self, workflow: &Workflow, initial_input: serde_json::Value)
                -> Result<serde_json::Value, WorkflowError> {
                // 实例化工作流步骤
                let mut steps = HashMap::new();
                for step_def in &workflow.steps {
                    let factory = self.step_registry.get(&step_def.step_type)
                        .ok_or_else(|| WorkflowError::StepTypeNotFound(step_def.step_type.clone()))?;

                    steps.insert(step_def.id.clone(), factory(step_def.config.clone()));
                }

                // 执行工作流
                let mut current_step_id = workflow.steps.first()
                    .ok_or_else(|| WorkflowError::EmptyWorkflow)?
                    .id.clone();

                let mut current_input = initial_input;

                while let Some(step_def) = workflow.steps.iter().find(|s| s.id == current_step_id) {
                    let step = steps.get(&step_def.id)
                        .ok_or_else(|| WorkflowError::StepNotFound(step_def.id.clone()))?;

                    // 执行步骤
                    let output = step.execute_any(current_input.clone()).await?;

                    // 确定下一步
                    if step_def.next_steps.is_empty() {
                        // 工作流结束
                        return Ok(output);
                    }

                    // 根据条件确定下一步
                    // 这里简化处理，实际应评估条件表达式
                    current_step_id = step_def.next_steps[0].target_step.clone();
                    current_input = output;
                }

                Err(WorkflowError::InvalidWorkflow)
            }
        }

        // 工作流错误
        #[derive(Debug, thiserror::Error)]
        pub enum WorkflowError {
            #[error("Step type not found: {0}")]
            StepTypeNotFound(String),

            #[error("Step not found: {0}")]
            StepNotFound(String),

            #[error("Workflow is empty")]
            EmptyWorkflow,

            #[error("Invalid workflow definition")]
            InvalidWorkflow,

            #[error("Step execution error: {0}")]
            StepExecutionError(String),

            #[error("Invalid transition")]
            InvalidTransition,
        }

        // 类型擦除特征
        #[async_trait]
        pub trait AnyStep: Send + Sync {
            async fn execute_any(&self, input: serde_json::Value) -> Result<serde_json::Value, WorkflowError>;
            fn step_name(&self) -> &str;
        }

        // 步骤工厂特征
        pub trait StepFactory: Send + Sync {
            fn create(&self, config: serde_json::Value) -> Box<dyn AnyStep>;
        }

        impl<F> StepFactory for F
        where
            F: Fn(serde_json::Value) -> Box<dyn AnyStep> + Send + Sync + 'static,
        {
            fn create(&self, config: serde_json::Value) -> Box<dyn AnyStep> {
                self(config)
            }
        }

        // 适配器
        #[async_trait]
        impl<S, I, O, E> AnyStep for S
        where
            S: WorkflowStep<Input = I, Output = O, Error = E> + Send + Sync,
            I: Serialize + for<'de> Deserialize<'de> + Send + Sync + 'static,
            O: Serialize + for<'de> Deserialize<'de> + Send + Sync + 'static,
            E: std::error::Error + Send + Sync + 'static,
        {
            async fn execute_any(&self, input: serde_json::Value) -> Result<serde_json::Value, WorkflowError> {
                let typed_input: I = serde_json::from_value(input)
                    .map_err(|e| WorkflowError::StepExecutionError(e.to_string()))?;

                let result = self.execute(typed_input).await
                    .map_err(|e| WorkflowError::StepExecutionError(e.to_string()))?;

                serde_json::to_value(result)
                    .map_err(|e| WorkflowError::StepExecutionError(e.to_string()))
            }

            fn step_name(&self) -> &str {
                self.step_name()
            }
        }
    }

    // 2. 插件系统
    pub mod plugin_system {
        use async_trait::async_trait;
        use wasmtime::{Engine, Module, Store, Instance, Linker};
        use anyhow::Result;
        use std::collections::HashMap;

        // 插件接口
        #[async_trait]
        pub trait Plugin: Send + Sync {
            fn name(&self) -> &str;
            fn version(&self) -> &str;

            async fn initialize(&mut self) -> Result<()>;
            async fn process(&self, input: &[u8]) -> Result<Vec<u8>>;
            fn shutdown(&self) -> Result<()>;
        }

        // WebAssembly插件
        pub struct WasmPlugin {
            name: String,
            version: String,
            engine: Engine,
            module: Module,
            instance: Option<Instance>,
            store: Option<Store<()>>,
        }

        impl WasmPlugin {
            pub fn new(name: &str, version: &str, wasm_bytes: &[u8]) -> Result<Self> {
                let engine = Engine::default();
                let module = Module::new(&engine, wasm_bytes)?;

                Ok(Self {
                    name: name.to_string(),
                    version: version.to_string(),
                    engine,
                    module,
                    instance: None,
                    store: None,
                })
            }
        }

        #[async_trait]
        impl Plugin for WasmPlugin {
            fn name(&self) -> &str {
                &self.name
            }

            fn version(&self) -> &str {
                &self.version
            }

            async fn initialize(&mut self) -> Result<()> {
                let mut store = Store::new(&self.engine, ());
                let mut linker = Linker::new(&self.engine);

                // 添加宿主函数
                linker.func_wrap("host", "log",
                    |caller: wasmtime::Caller<'_, ()>, msg_ptr: i32, msg_len: i32| -> Result<(), wasmtime::Trap> {
                        // 从WebAssembly内存读取消息
                        // 简化实现
                        Ok(())
                    }
                )?;

                // 实例化模块
                let instance = linker.instantiate(&mut store, &self.module)?;

                // 调用初始化函数
                if let Ok(init) = instance.get_typed_func::<(), ()>(&mut store, "initialize") {
                    init.call(&mut store, ())?;
                }

                self.instance = Some(instance);
                self.store = Some(store);

                Ok(())
            }

            async fn process(&self, input: &[u8]) -> Result<Vec<u8>> {
                if let (Some(instance), Some(mut store)) = (&self.instance, self.store.as_ref()) {
                    // 获取内存
                    let memory = instance
                        .get_memory(&mut store, "memory")
                        .ok_or_else(|| anyhow::anyhow!("Failed to get memory"))?;

                    // 分配内存并写入输入数据
                    let alloc = instance
                        .get_typed_func::<i32, i32>(&mut store, "alloc")?;

                    let input_ptr = alloc.call(&mut store, input.len() as i32)?;

                    // 写入输入数据
                    memory.write(&mut store, input_ptr as usize, input)?;

                    // 调用处理函数
                    let process = instance
                        .get_typed_func::<(i32, i32), (i32, i32)>(&mut store, "process")?;

                    let (result_ptr, result_len) = process.call(
                        &mut store,
                        (input_ptr, input.len() as i32)
                    )?;

                    // 读取结果
                    let mut result = vec![0u8; result_len as usize];
                    memory.read(&store, result_ptr as usize, &mut result)?;

                    // 释放内存
                    if let Ok(dealloc) = instance.get_typed_func::<(i32, i32), ()>(&mut store, "dealloc") {
                        dealloc.call(&mut store, (input_ptr, input.len() as i32))?;
                        dealloc.call(&mut store, (result_ptr, result_len))?;
                    }

                    Ok(result)
                } else {
                    anyhow::bail!("Plugin not initialized")
                }
            }

            fn shutdown(&self) -> Result<()> {
                if let (Some(instance), Some(mut store)) = (&self.instance, self.store.as_ref()) {
                    // 调用清理函数
                    if let Ok(shutdown) = instance.get_typed_func::<(), ()>(&mut store, "shutdown") {
                        shutdown.call(&mut store, ())?;
                    }
                }

                Ok(())
            }
        }

        // 插件管理器
        pub struct PluginManager {
            plugins: HashMap<String, Box<dyn Plugin>>,
        }

        impl PluginManager {
            pub fn new() -> Self {
                Self {
                    plugins: HashMap::new(),
                }
            }

            pub fn register(&mut self, plugin: Box<dyn Plugin>) -> Result<()> {
                let key = format!("{}@{}", plugin.name(), plugin.version());
                self.plugins.insert(key, plugin);
                Ok(())
            }

            pub async fn initialize_all(&mut self) -> Result<()> {
                for plugin in self.plugins.values_mut() {
                    plugin.initialize().await?;
                }
                Ok(())
            }

            pub async fn process(&self, plugin_name: &str, version: &str, input: &[u8]) -> Result<Vec<u8>> {
                let key = format!("{}@{}", plugin_name, version);

                if let Some(plugin) = self.plugins.get(&key) {
                    plugin.process(input).await
                } else {
                    anyhow::bail!("Plugin not found: {}", key)
                }
            }

            pub fn shutdown_all(&self) -> Result<()> {
                for plugin in self.plugins.values() {
                    plugin.shutdown()?;
                }
                Ok(())
            }
        }
    }

    // 3. 动态配置系统
    pub mod dynamic_config {
        use std::collections::HashMap;
        use std::sync::{Arc, RwLock};
        use serde::{Serialize, Deserialize};
        use tokio::sync::watch;

        // 配置值类型
        #[derive(Debug, Clone, Serialize, Deserialize)]
        #[serde(untagged)]
        pub enum ConfigValue {
            String(String),
            Number(f64),
            Boolean(bool),
            Array(Vec<ConfigValue>),
            Object(HashMap<String, ConfigValue>),
            Null,
        }

        // 配置存储
        pub struct ConfigStore {
            values: Arc<RwLock<HashMap<String, ConfigValue>>>,
            notifier: watch::Sender<()>,
            receiver: watch::Receiver<()>,
        }

        impl ConfigStore {
            pub fn new() -> Self {
                let (notifier, receiver) = watch::channel(());

                Self {
                    values: Arc::new(RwLock::new(HashMap::new())),
                    notifier,
                    receiver,
                }
            }

            pub fn set(&self, key: &str, value: ConfigValue) {
                let mut values = self.values.write().unwrap();
                values.insert(key.to_string(), value);

                // 通知所有监听器
                let _ = self.notifier.send(());
            }

            pub fn get(&self, key: &str) -> Option<ConfigValue> {
                let values = self.values.read().unwrap();
                values.get(key).cloned()
            }

            pub fn subscribe(&self) -> watch::Receiver<()> {
                self.receiver.clone()
            }
        }

        // 配置订阅者
        pub struct ConfigSubscriber {
            config_store: Arc<ConfigStore>,
            receiver: watch::Receiver<()>,
        }

        impl ConfigSubscriber {
            pub fn new(config_store: Arc<ConfigStore>) -> Self {
                let receiver = config_store.subscribe();

                Self {
                    config_store,
                    receiver,
                }
            }

            pub async fn wait_for_changes(&mut self) {
                let _ = self.receiver.changed().await;
            }

            pub fn get_string(&self, key: &str, default: &str) -> String {
                match self.config_store.get(key) {
                    Some(ConfigValue::String(s)) => s,
                    _ => default.to_string(),
                }
            }

            pub fn get_number(&self, key: &str, default: f64) -> f64 {
                match self.config_store.get(key) {
                    Some(ConfigValue::Number(n)) => n,
                    _ => default,
                }
            }

            pub fn get_boolean(&self, key: &str, default: bool) -> bool {
                match self.config_store.get(key) {
                    Some(ConfigValue::Boolean(b)) => b,
                    _ => default,
                }
            }
        }
    }
```

## 11. 形式化验证与安全保障

### 11.1 类型系统保障

Rust类型系统保障可形式化为类型推导规则:
$$\frac{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash e_2 : \tau_1}{\Gamma \vdash e_1(e_2) : \tau_2}$$

```rust
    // 类型安全示例
    // 1. 精确类型表示
    pub mod types {
        use std::marker::PhantomData;

        // 单位类型
        #[derive(Debug, Clone, Copy)]
        pub struct Length<Unit>(pub f64, PhantomData<Unit>);

        #[derive(Debug, Clone, Copy)]
        pub struct Weight<Unit>(pub f64, PhantomData<Unit>);

        // 单位标记
        pub enum Meter {}
        pub enum Centimeter {}
        pub enum Kilogram {}
        pub enum Gram {}

        // 类型安全操作
        impl<Unit> Length<Unit> {
            pub fn new(value: f64) -> Self {
                Self(value, PhantomData)
            }

            pub fn value(&self) -> f64 {
                self.0
            }
        }

        // 单位转换
        impl Length<Meter> {
            pub fn to_centimeters(&self) -> Length<Centimeter> {
                Length(self.0 * 100.0, PhantomData)
            }
        }

        impl Length<Centimeter> {
            pub fn to_meters(&self) -> Length<Meter> {
                Length(self.0 / 100.0, PhantomData)
            }
        }

        // 防止错误运算
        impl<Unit> std::ops::Add for Length<Unit> {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                Self(self.0 + rhs.0, PhantomData)
            }
        }

        impl<Unit> std::ops::Sub for Length<Unit> {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self::Output {
                Self(self.0 - rhs.0, PhantomData)
            }
        }

        // 类型状态模式
        #[derive(Debug, Clone)]
        pub struct ResourceHandle<State> {
            id: u64,
            _state: PhantomData<State>,
        }

        // 状态标记
        pub enum Uninitialized {}
        pub enum Initialized {}
        pub enum Active {}
        pub enum Closed {}

        impl ResourceHandle<Uninitialized> {
            pub fn new(id: u64) -> Self {
                Self { id, _state: PhantomData }
            }

            pub fn initialize(self) -> ResourceHandle<Initialized> {
                ResourceHandle { id: self.id, _state: PhantomData }
            }
        }

        impl ResourceHandle<Initialized> {
            pub fn activate(self) -> ResourceHandle<Active> {
                ResourceHandle { id: self.id, _state: PhantomData }
            }
        }

        impl ResourceHandle<Active> {
            pub fn process(&self) -> Result<(), &'static str> {
                // 处理活动资源
                Ok(())
            }

            pub fn close(self) -> ResourceHandle<Closed> {
                ResourceHandle { id: self.id, _state: PhantomData }
            }
        }

        impl ResourceHandle<Closed> {
            pub fn id(&self) -> u64 {
                self.id
            }

            // 已关闭的资源不能再使用
        }
    }

    // 2. 抽象类型约束
    pub mod type_safety {
        use serde::{Serialize, Deserialize};

        // 有效载荷标记特征
        pub trait ValidPayload: Serialize + for<'de> Deserialize<'de> {}

        // 请求/响应类型安全
        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct Request<T: ValidPayload> {
            pub id: String,
            pub timestamp: u64,
            pub payload: T,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct Response<T: ValidPayload> {
            pub request_id: String,
            pub timestamp: u64,
            pub payload: T,
        }

        // API端点特征
        pub trait ApiEndpoint {
            type RequestPayload: ValidPayload;
            type ResponsePayload: ValidPayload;

            const PATH: &'static str;
            const METHOD: &'static str;
        }

        // 类型安全的API处理函数
        pub async fn handle_api_request<E: ApiEndpoint>(
            request: Request<E::RequestPayload>
        ) -> Response<E::ResponsePayload> {
            // 处理请求
            todo!()
        }

        // 用户API定义
        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct GetUserRequest {
            pub user_id: u64,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct User {
            pub id: u64,
            pub name: String,
            pub email: String,
        }

        impl ValidPayload for GetUserRequest {}
        impl ValidPayload for User {}

        pub struct GetUserEndpoint;

        impl ApiEndpoint for GetUserEndpoint {
            type RequestPayload = GetUserRequest;
            type ResponsePayload = User;

            const PATH: &'static str = "/api/users/:id";
            const METHOD: &'static str = "GET";
        }
    }
```

### 11.2 所有权模型安全性

所有权模型可以形式化为资源生命周期:
$$L = \{\text{创建} \rightarrow \text{独占} \rightarrow (\text{借用})^* \rightarrow \text{释放}\}$$

```rust
// 所有权安全示例
// 1. 资源安全访问
pub struct ResourceManager {
    resources: Vec<Resource>,
}

struct Resource {
    id: usize,
    data: Vec<u8>,
}

impl ResourceManager {
    // 安全借用资源 - 不可变引用
    pub fn get_resource(&self, id: usize) -> Option<&Resource> {
        self.resources.iter().find(|r| r.id == id)
    }

    // 安全修改资源 - 可变引用
    pub fn modify_resource<F>(&mut self, id: usize, modifier: F) -> Result<(), &'static str>
    where
        F: FnOnce(&mut Resource),
    {
        if let Some(resource) = self.resources.iter_mut().find(|r| r.id == id) {
            modifier(resource);
            Ok(())
        } else {
            Err("Resource not found")
        }
    }

    // 安全转移资源所有权
    pub fn take_resource(&mut self, id: usize) -> Option<Resource> {
        let pos = self.resources.iter().position(|r| r.id == id)?;
        Some(self.resources.remove(pos))
    }
}

// 2. RAII模式
pub struct WasmMemory {
    ptr: *mut u8,
    size: usize,
}

impl WasmMemory {
    pub fn allocate(size: usize) -> Self {
        let layout = std::alloc::Layout::from_size_align(size, 8)
            .expect("Invalid memory layout");

        let ptr = unsafe { std::alloc::alloc(layout) };
        if ptr.is_null() {
            panic!("Memory allocation failed");
        }

        Self { ptr, size }
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.ptr
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr
    }

    pub fn size(&self) -> usize {
        self.size
    }
}

impl Drop for WasmMemory {
    fn drop(&mut self) {
        let layout = std::alloc::Layout::from_size_align(self.size, 8)
            .expect("Invalid memory layout");

        unsafe {
            std::alloc::dealloc(self.ptr, layout);
        }
    }
}

// 3. 安全接口设计
pub mod safe_interface {
    use std::marker::PhantomData;

    // 安全的WebAssembly内存访问
    pub struct WasmMemoryView<'a, T> {
        ptr: *const T,
        len: usize,
        _lifetime: PhantomData<&'a [T]>,
    }

    impl<'a, T> WasmMemoryView<'a, T> {
        pub fn new(ptr: *const T, len: usize) -> Self {
            Self {
                ptr,
                len,
                _lifetime: PhantomData,
            }
        }

        pub fn get(&self, index: usize) -> Option<&'a T> {
            if index >= self.len {
                return None;
            }

            unsafe {
                Some(&*self.ptr.add(index))
            }
        }

        pub fn len(&self) -> usize {
            self.len
        }

        pub fn is_empty(&self) -> bool {
            self.len == 0
        }

        pub fn iter(&self) -> impl Iterator<Item = &'a T> {
            WasmMemoryViewIter {
                view: self,
                current: 0,
            }
        }
    }

    // 安全迭代器
    pub struct WasmMemoryViewIter<'a, 'b, T> {
        view: &'b WasmMemoryView<'a, T>,
        current: usize,
    }

    impl<'a, 'b, T> Iterator for WasmMemoryViewIter<'a, 'b, T> {
        type Item = &'a T;

        fn next(&mut self) -> Option<Self::Item> {
            if self.current >= self.view.len() {
                return None;
            }

            let item = self.view.get(self.current);
            self.current += 1;
            item
        }
    }
}
```

### 11.3 形式化证明

形式化证明可表示为断言:
$$\{P\} \text{ program } \{Q\}$$

其中 $P$ 是前置条件，$Q$ 是后置条件。

```rust
// 形式化验证示例
pub mod formal_verification {
    // 1. 不变量检查
    pub struct SortedVec<T: Ord> {
        inner: Vec<T>,
        #[cfg(debug_assertions)]
        check_invariant: bool,
    }

    impl<T: Ord> SortedVec<T> {
        pub fn new() -> Self {
            Self {
                inner: Vec::new(),
                #[cfg(debug_assertions)]
                check_invariant: true,
            }
        }

        pub fn from_vec(mut vec: Vec<T>) -> Self {
            vec.sort();
            Self {
                inner: vec,
                #[cfg(debug_assertions)]
                check_invariant: true,
            }
        }

        pub fn insert(&mut self, item: T) {
            // 二分搜索找到插入位置
            let idx = match self.inner.binary_search(&item) {
                Ok(idx) => idx,
                Err(idx) => idx,
            };

            self.inner.insert(idx, item);

            // 验证不变量
            self.check_sorted();
        }

        pub fn iter(&self) -> impl Iterator<Item = &T> {
            self.inner.iter()
        }

        // 检查排序不变量
        fn check_sorted(&self) {
            #[cfg(debug_assertions)]
            if self.check_invariant {
                for i in 1..self.inner.len() {
                    debug_assert!(
                        self.inner[i-1] <= self.inner[i],
                        "SortedVec invariant violated: not sorted"
                    );
                }
            }
        }

        // 禁用不变量检查的作用域
        #[cfg(debug_assertions)]
        pub fn without_invariant_check<F, R>(&mut self, f: F) -> R
        where
            F: FnOnce(&mut Vec<T>) -> R,
        {
            self.check_invariant = false;
            let result = f(&mut self.inner);
            self.inner.sort();
            self.check_invariant = true;
            result
        }
    }

    // 2. 契约编程
    #[derive(Debug, Clone)]
    pub struct Matrix {
        rows: usize,
        cols: usize,
        data: Vec<f64>,
    }

    impl Matrix {
        // 前置条件：rows > 0 && cols > 0
        // 后置条件：返回的矩阵维度为rows×cols
        pub fn new(rows: usize, cols: usize) -> Self {
            assert!(rows > 0, "Matrix rows must be positive");
            assert!(cols > 0, "Matrix cols must be positive");

            let data = vec![0.0; rows * cols];
            let matrix = Self { rows, cols, data };

            // 后置条件检查
            debug_assert_eq!(matrix.rows(), rows);
            debug_assert_eq!(matrix.cols(), cols);

            matrix
        }

        pub fn rows(&self) -> usize {
            self.rows
        }

        pub fn cols(&self) -> usize {
            self.cols
        }

        // 前置条件：row < self.rows && col < self.cols
        pub fn get(&self, row: usize, col: usize) -> Option<f64> {
            if row >= self.rows || col >= self.cols {
                return None;
            }

            Some(self.data[row * self.cols + col])
        }

        // 前置条件：row < self.rows && col < self.cols
        pub fn set(&mut self, row: usize, col: usize, value: f64) -> Result<(), &'static str> {
            if row >= self.rows || col >= self.cols {
                return Err("Index out of bounds");
            }

            self.data[row * self.cols + col] = value;
            Ok(())
        }

        // 前置条件：self.cols == other.rows
        // 后置条件：返回的矩阵维度为self.rows×other.cols
        pub fn multiply(&self, other: &Matrix) -> Result<Matrix, &'static str> {
            if self.cols != other.rows {
                return Err("Incompatible matrix dimensions for multiplication");
            }

            let mut result = Matrix::new(self.rows, other.cols);

            for i in 0..self.rows {
                for j in 0..other.cols {
                    let mut sum = 0.0;
                    for k in 0..self.cols {
                        sum += self.data[i * self.cols + k] * other.data[k * other.cols + j];
                    }
                    result.data[i * other.cols + j] = sum;
                }
            }

            // 后置条件检查
            debug_assert_eq!(result.rows(), self.rows);
            debug_assert_eq!(result.cols(), other.cols);

            Ok(result)
        }
    }

    // 3. 静态验证
    pub trait Validated {
        fn validate(&self) -> Result<(), &'static str>;
    }

    pub struct Validator<T: Validated> {
        value: T,
    }

    impl<T: Validated> Validator<T> {
        pub fn new(value: T) -> Result<Self, &'static str> {
            value.validate()?;
            Ok(Self { value })
        }

        pub fn get(&self) -> &T {
            &self.value
        }

        pub fn into_inner(self) -> T {
            self.value
        }
    }

    // 示例：邮箱地址验证
    #[derive(Debug, Clone)]
    pub struct EmailAddress(String);

    impl EmailAddress {
        pub fn new(email: String) -> Result<Self, &'static str> {
            let email_obj = Self(email);
            email_obj.validate()?;
            Ok(email_obj)
        }

        pub fn as_str(&self) -> &str {
            &self.0
        }
    }

    impl Validated for EmailAddress {
        fn validate(&self) -> Result<(), &'static str> {
            if self.0.is_empty() {
                return Err("Email cannot be empty");
            }

            if !self.0.contains('@') {
                return Err("Email must contain @");
            }

            let parts: Vec<&str> = self.0.split('@').collect();
            if parts.len() != 2 {
                return Err("Email must contain exactly one @");
            }

            let (name, domain) = (parts[0], parts[1]);

            if name.is_empty() {
                return Err("Email name part cannot be empty");
            }

            if domain.is_empty() {
                return Err("Email domain part cannot be empty");
            }

            if !domain.contains('.') {
                return Err("Email domain must contain at least one dot");
            }

            Ok(())
        }
    }
}
```

## 12. 案例研究与实现示例

### 12.1 全栈Todo应用

以下是全栈Todo应用的核心代码示例:

```rust
    // shared/src/lib.rs - 共享代码库
    use serde::{Serialize, Deserialize};

    // 领域模型
    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    pub struct Todo {
        pub id: Option<u64>,
        pub title: String,
        pub completed: bool,
        pub created_at: String, // ISO 8601 格式
    }

    // 验证逻辑
    impl Todo {
        pub fn validate(&self) -> Result<(), String> {
            if self.title.trim().is_empty() {
                return Err("Title cannot be empty".into());
            }

            if self.title.len() > 100 {
                return Err("Title cannot exceed 100 characters".into());
            }

            Ok(())
        }
    }

    // API定义
    pub mod api {
        use super::Todo;
        use serde::{Serialize, Deserialize};

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct CreateTodoRequest {
            pub title: String,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct UpdateTodoRequest {
            pub title: Option<String>,
            pub completed: Option<bool>,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct TodoResponse {
            pub todo: Todo,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct TodoListResponse {
            pub todos: Vec<Todo>,
            pub total: usize,
        }

        pub trait TodoApi {
            async fn get_todos(&self) -> Result<TodoListResponse, String>;
            async fn get_todo(&self, id: u64) -> Result<TodoResponse, String>;
            async fn create_todo(&self, req: CreateTodoRequest) -> Result<TodoResponse, String>;
            async fn update_todo(&self, id: u64, req: UpdateTodoRequest) -> Result<TodoResponse, String>;
            async fn delete_todo(&self, id: u64) -> Result<(), String>;
        }
    }

    // frontend/src/lib.rs - 前端实现 (Yew框架)
    use shared::{Todo, api::{CreateTodoRequest, UpdateTodoRequest, TodoListResponse, TodoResponse}};
    use yew::prelude::*;
    use wasm_bindgen::JsValue;
    use wasm_bindgen_futures::spawn_local;
    use web_sys::{HtmlInputElement, Request, RequestInit, Response};
    use gloo::storage::LocalStorage;
    use gloo_console::log;

    // API客户端
    pub struct ApiClient {
        base_url: String,
    }

    impl ApiClient {
        pub fn new(base_url: &str) -> Self {
            Self { base_url: base_url.to_string() }
        }

        async fn fetch<T, R>(&self, method: &str, path: &str, body: Option<&T>) -> Result<R, String>
        where
            T: serde::Serialize,
            R: for<'de> serde::Deserialize<'de>,
        {
            let mut opts = RequestInit::new();
            opts.method(method);

            if let Some(data) = body {
                let json = serde_json::to_string(data).map_err(|e| e.to_string())?;
                opts.body(Some(&JsValue::from_str(&json)));
            }

            let url = format!("{}{}", self.base_url, path);
            let request = Request::new_with_str_and_init(&url, &opts)
                .map_err(|e| format!("Failed to create request: {:?}", e))?;

            request.headers().set("Content-Type", "application/json")
                .map_err(|e| format!("Failed to set headers: {:?}", e))?;

            let window = web_sys::window().unwrap();
            let resp_value = wasm_bindgen_futures::JsFuture::from(window.fetch_with_request(&request))
                .await
                .map_err(|e| format!("Failed to fetch: {:?}", e))?;

            let resp: Response = resp_value.dyn_into().unwrap();

            if !resp.ok() {
                return Err(format!("HTTP error: {}", resp.status()));
            }

            let json = wasm_bindgen_futures::JsFuture::from(resp.json().unwrap())
                .await
                .map_err(|e| format!("Failed to parse JSON: {:?}", e))?;

            serde_wasm_bindgen::from_value(json)
                .map_err(|e| format!("Failed to deserialize: {:?}", e))
        }

        pub async fn get_todos(&self) -> Result<TodoListResponse, String> {
            self.fetch::<(), _>("GET", "/api/todos", None).await
        }

        pub async fn create_todo(&self, req: &CreateTodoRequest) -> Result<TodoResponse, String> {
            self.fetch("POST", "/api/todos", Some(req)).await
        }

        pub async fn update_todo(&self, id: u64, req: &UpdateTodoRequest) -> Result<TodoResponse, String> {
            self.fetch("PUT", &format!("/api/todos/{}", id), Some(req)).await
        }

        pub async fn delete_todo(&self, id: u64) -> Result<(), String> {
            self.fetch::<(), ()>("DELETE", &format!("/api/todos/{}", id), None).await
        }
    }

    // Todo应用组件
    #[function_component(TodoApp)]
    pub fn todo_app() -> Html {
        let todos = use_state(|| Vec::<Todo>::new());
        let input_ref = use_node_ref();
        let api = use_memo(|_| ApiClient::new("/api"), ());

        // 加载Todos
        {
            let todos = todos.clone();
            let api = api.clone();

            use_effect_with_deps(move |_| {
                let todos = todos.clone();
                let api = api.clone();

                spawn_local(async move {
                    match api.get_todos().await {
                        Ok(response) => {
                            todos.set(response.todos);
                        },
                        Err(err) => {
                            log!("Failed to load todos:", err);
                        }
                    }
                });

                || ()
            }, ());
        }

        // 添加Todo处理函数
        let on_add = {
            let todos = todos.clone();
            let input_ref = input_ref.clone();
            let api = api.clone();

            Callback::from(move |e: FocusEvent| {
                e.prevent_default();
                let input = input_ref.cast::<HtmlInputElement>().unwrap();
                let title = input.value();

                if title.trim().is_empty() {
                    return;
                }

                let todos = todos.clone();
                let api = api.clone();

                spawn_local(async move {
                    let req = CreateTodoRequest { title };

                    match api.create_todo(&req).await {
                        Ok(response) => {
                            let mut new_todos = (*todos).clone();
                            new_todos.push(response.todo);
                            todos.set(new_todos);
                        },
                        Err(err) => {
                            log!("Failed to create todo:", err);
                        }
                    }
                });

                input.set_value("");
            })
        };

        // 切换完成状态
        let on_toggle = {
            let todos = todos.clone();
            let api = api.clone();

            Callback::from(move |id: u64| {
                let todos = todos.clone();
                let api = api.clone();
                let current_todos = (*todos).clone();

                let todo = current_todos.iter().find(|t| t.id == Some(id)).unwrap();
                let completed = !todo.completed;

                spawn_local(async move {
                    let req = UpdateTodoRequest {
                        title: None,
                        completed: Some(completed),
                    };

                    match api.update_todo(id, &req).await {
                        Ok(response) => {
                            let mut new_todos = (*todos).clone();
                            if let Some(idx) = new_todos.iter().position(|t| t.id == Some(id)) {
                                new_todos[idx] = response.todo;
                                todos.set(new_todos);
                            }
                        },
                        Err(err) => {
                            log!("Failed to update todo:", err);
                        }
                    }
                });
            })
        };

        // 删除处理函数
        let on_delete = {
            let todos = todos.clone();
            let api = api.clone();

            Callback::from(move |id: u64| {
                let todos = todos.clone();
                let api = api.clone();

                spawn_local(async move {
                    match api.delete_todo(id).await {
                        Ok(_) => {
                            let mut new_todos = (*todos).clone();
                            new_todos.retain(|t| t.id != Some(id));
                            todos.set(new_todos);
                        },
                        Err(err) => {
                            log!("Failed to delete todo:", err);
                        }
                    }
                });
            })
        };

        html! {
            <div class="todo-app">
                <h1>{"Rust WebAssembly Todo App"}</h1>

                <form onsubmit={on_add}>
                    <input
                        ref={input_ref}
                        type="text"
                        placeholder="What needs to be done?"
                    />
                    <button type="submit">{"Add"}</button>
                </form>

                <ul class="todo-list">
                    {
                        todos.iter().map(|todo| {
                            let id = todo.id.unwrap();
                            let on_toggle = {
                                let on_toggle = on_toggle.clone();
                                let id = id;
                                Callback::from(move |_| on_toggle.emit(id))
                            };

                            let on_delete = {
                                let on_delete = on_delete.clone();
                                let id = id;
                                Callback::from(move |_| on_delete.emit(id))
                            };

                            html! {
                                <li key={id} class={classes!(if todo.completed {"completed"} else {""})}>
                                    <input
                                        type="checkbox"
                                        checked={todo.completed}
                                        onchange={on_toggle}
                                    />
                                    <span class="title">{&todo.title}</span>
                                    <button class="delete" onclick={on_delete}>{"×"}</button>
                                </li>
                            }
                        }).collect::<Html>()
                    }
                </ul>

                <div class="info">
                    <span>{format!("{} item(s)", todos.len())}</span>
                </div>
            </div>
        }
    }

    // backend/src/main.rs - 后端实现 (Axum框架)
    use shared::{Todo, api::{CreateTodoRequest, UpdateTodoRequest, TodoResponse, TodoListResponse}};
    use axum::{
        routing::{get, post},
        http::StatusCode,
        Json, Router, Extension, extract::{Path, State},
    };
    use chrono::Utc;
    use serde_json::json;
    use sqlx::{SqlitePool, sqlite::SqlitePoolOptions};
    use std::sync::Arc;
    use uuid::Uuid;
    use std::net::SocketAddr;
    use tower_http::cors::{CorsLayer, Any};

    // 应用状态
    #[derive(Clone)]
    struct AppState {
        db: SqlitePool,
    }

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        // 初始化日志
        tracing_subscriber::fmt::init();

        // 连接数据库
        let db_url = std::env::var("DATABASE_URL").unwrap_or("sqlite:todos.db".to_string());
        let pool = SqlitePoolOptions::new()
            .max_connections(5)
            .connect(&db_url)
            .await?;

        // 初始化表
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS todos (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                title TEXT NOT NULL,
                completed BOOLEAN NOT NULL DEFAULT 0,
                created_at TEXT NOT NULL
            )"
        )
        .execute(&pool)
        .await?;

        // 创建应用状态
        let state = Arc::new(AppState { db: pool });

        // 构建路由
        let app = Router::new()
            .route("/api/todos", get(get_todos).post(create_todo))
            .route("/api/todos/:id", get(get_todo).put(update_todo).delete(delete_todo))
            .layer(Extension(state))
            .layer(
                CorsLayer::new()
                    .allow_origin(Any)
                    .allow_methods(Any)
                    .allow_headers(Any)
            );

        // 启动服务器
        let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
        println!("Server listening on {}", addr);
        axum::Server::bind(&addr)
            .serve(app.into_make_service())
            .await?;

        Ok(())
    }

    // 获取所有待办事项
    async fn get_todos(
        Extension(state): Extension<Arc<AppState>>,
    ) -> Result<Json<TodoListResponse>, (StatusCode, Json<serde_json::Value>)> {
        let todos = sqlx::query_as!(
            Todo,
            r#"
            SELECT
                id as "id?: u64",
                title,
                completed,
                created_at
            FROM todos
            ORDER BY id DESC
            "#
        )
        .fetch_all(&state.db)
        .await
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({ "error": format!("Database error: {}", e) })),
            )
        })?;

        let total = todos.len();

        Ok(Json(TodoListResponse { todos, total }))
    }

    // 获取单个待办事项
    async fn get_todo(
        Path(id): Path<u64>,
        Extension(state): Extension<Arc<AppState>>,
    ) -> Result<Json<TodoResponse>, (StatusCode, Json<serde_json::Value>)> {
        let todo = sqlx::query_as!(
            Todo,
            r#"
            SELECT
                id as "id?: u64",
                title,
                completed,
                created_at
            FROM todos
            WHERE id = ?
            "#,
            id
        )
        .fetch_optional(&state.db)
        .await
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({ "error": format!("Database error: {}", e) })),
            )
        })?;

        if let Some(todo) = todo {
            Ok(Json(TodoResponse { todo }))
        } else {
            Err((
                StatusCode::NOT_FOUND,
                Json(json!({ "error": "Todo not found" })),
            ))
        }
    }

    // 创建待办事项
    async fn create_todo(
        Extension(state): Extension<Arc<AppState>>,
        Json(payload): Json<CreateTodoRequest>,
    ) -> Result<Json<TodoResponse>, (StatusCode, Json<serde_json::Value>)> {
        // 创建新的待办事项
        let todo = Todo {
            id: None,
            title: payload.title.trim().to_string(),
            completed: false,
            created_at: Utc::now().to_rfc3339(),
        };

        // 验证
        if let Err(err) = todo.validate() {
            return Err((
                StatusCode::BAD_REQUEST,
                Json(json!({ "error": err })),
            ));
        }

        // 保存到数据库
        let id = sqlx::query!(
            r#"
            INSERT INTO todos (title, completed, created_at)
            VALUES (?, ?, ?)
            "#,
            todo.title,
            todo.completed,
            todo.created_at
        )
        .execute(&state.db)
        .await
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({ "error": format!("Database error: {}", e) })),
            )
        })?
        .last_insert_rowid();

        // 获取完整的待办事项
        let todo = sqlx::query_as!(
            Todo,
            r#"
            SELECT
                id as "id?: u64",
                title,
                completed,
                created_at
            FROM todos
            WHERE id = ?
            "#,
            id
        )
        .fetch_one(&state.db)
        .await
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({ "error": format!("Database error: {}", e) })),
            )
        })?;

        Ok(Json(TodoResponse { todo }))
    }

    // 更新待办事项
    async fn update_todo(
        Path(id): Path<u64>,
        Extension(state): Extension<Arc<AppState>>,
        Json(payload): Json<UpdateTodoRequest>,
    ) -> Result<Json<TodoResponse>, (StatusCode, Json<serde_json::Value>)> {
        // 获取现有待办事项
        let mut todo = sqlx::query_as!(
            Todo,
            r#"
            SELECT
                id as "id?: u64",
                title,
                completed,
                created_at
            FROM todos
            WHERE id = ?
            "#,
            id
        )
        .fetch_optional(&state.db)
        .await
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({ "error": format!("Database error: {}", e) })),
            )
        })?;

        let todo = match todo {
            Some(t) => t,
            None => {
                return Err((
                    StatusCode::NOT_FOUND,
                    Json(json!({ "error": "Todo not found" })),
                ))
            }
        };

        // 应用更新
        let title = payload.title.unwrap_or(todo.title);
        let completed = payload.completed.unwrap_or(todo.completed);

        let updated_todo = Todo {
            id: todo.id,
            title,
            completed,
            created_at: todo.created_at,
        };

        // 验证
        if let Err(err) = updated_todo.validate() {
            return Err((
                StatusCode::BAD_REQUEST,
                Json(json!({ "error": err })),
            ));
        }

        // 更新数据库
        sqlx::query!(
            r#"
            UPDATE todos
            SET title = ?, completed = ?
            WHERE id = ?
            "#,
            updated_todo.title,
            updated_todo.completed,
            id
        )
        .execute(&state.db)
        .await
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({ "error": format!("Database error: {}", e) })),
            )
        })?;

        Ok(Json(TodoResponse { todo: updated_todo }))
    }

    // 删除待办事项
    async fn delete_todo(
        Path(id): Path<u64>,
        Extension(state): Extension<Arc<AppState>>,
    ) -> Result<StatusCode, (StatusCode, Json<serde_json::Value>)> {
        let result = sqlx::query!(
            r#"
            DELETE FROM todos
            WHERE id = ?
            "#,
            id
        )
        .execute(&state.db)
        .await
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({ "error": format!("Database error: {}", e) })),
            )
        })?;

        if result.rows_affected() == 0 {
            return Err((
                StatusCode::NOT_FOUND,
                Json(json!({ "error": "Todo not found" })),
            ));
        }

        Ok(StatusCode::NO_CONTENT)
    }
```

### 12.2 数据密集型应用

以下是数据密集型应用的示例代码:

```rust
    // shared/src/lib.rs - 共享代码
    use serde::{Serialize, Deserialize};

    // 数据点类型
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct DataPoint {
        pub timestamp: u64,
        pub value: f64,
        pub category: String,
        pub metadata: Option<std::collections::HashMap<String, String>>,
    }

    // 统计功能模块
    pub mod statistics {
        // 计算平均值
        pub fn mean(values: &[f64]) -> Option<f64> {
            if values.is_empty() {
                return None;
            }

            let sum: f64 = values.iter().sum();
            Some(sum / values.len() as f64)
        }

        // 计算中位数
        pub fn median(values: &[f64]) -> Option<f64> {
            if values.is_empty() {
                return None;
            }

            let mut sorted = values.to_vec();
            sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());

            let mid = sorted.len() / 2;
            if sorted.len() % 2 == 0 {
                mean(&[sorted[mid - 1], sorted[mid]])
            } else {
                Some(sorted[mid])
            }
        }

        // 计算标准差
        pub fn standard_deviation(values: &[f64]) -> Option<f64> {
            if values.is_empty() {
                return None;
            }

            let avg = mean(values)?;
            let variance = values.iter()
                .map(|value| {
                    let diff = avg - *value;
                    diff * diff
                })
                .sum::<f64>() / values.len() as f64;

            Some(variance.sqrt())
        }

        // 移动平均
        pub fn moving_average(values: &[f64], window: usize) -> Vec<f64> {
            if window == 0 || values.len() < window {
                return Vec::new();
            }

            let mut result = Vec::with_capacity(values.len() - window + 1);

            for i in 0..=(values.len() - window) {
                let sum: f64 = values[i..(i + window)].iter().sum();
                result.push(sum / window as f64);
            }

            result
        }
    }

    // 数据处理接口
    pub trait DataProcessor {
        fn process(&self, data: &[DataPoint]) -> Vec<DataPoint>;
    }

    // API定义
    pub mod api {
        use super::DataPoint;
        use serde::{Serialize, Deserialize};

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct DataQuery {
            pub start_time: Option<u64>,
            pub end_time: Option<u64>,
            pub categories: Option<Vec<String>>,
            pub limit: Option<usize>,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct DataResponse {
            pub data: Vec<DataPoint>,
            pub total: usize,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct StatsRequest {
            pub data: Vec<DataPoint>,
            pub operation: StatsOperation,
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub enum StatsOperation {
            Mean,
            Median,
            StandardDeviation,
            MovingAverage { window: usize },
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct StatsResponse {
            pub result: Vec<f64>,
        }
    }

    // frontend/src/lib.rs - 前端实现
    use shared::{DataPoint, api::{DataQuery, DataResponse, StatsRequest, StatsResponse, StatsOperation}};
    use wasm_bindgen::prelude::*;
    use wasm_bindgen::JsCast;
    use wasm_bindgen_futures::spawn_local;
    use web_sys::{HtmlCanvasElement, CanvasRenderingContext2d};
    use js_sys::{Date, Math};
    use gloo::timers::callback::Interval;
    use std::rc::Rc;
    use std::cell::{RefCell, Cell};
    use yew::prelude::*;

    // WebAssembly数据处理函数
    #[wasm_bindgen]
    pub fn process_data(data_js: JsValue) -> Result<JsValue, JsValue> {
        let data: Vec<DataPoint> = serde_wasm_bindgen::from_value(data_js)?;

        // 查找异常值
        let values: Vec<f64> = data.iter().map(|d| d.value).collect();
        let avg = shared::statistics::mean(&values).unwrap_or(0.0);
        let std_dev = shared::statistics::standard_deviation(&values).unwrap_or(0.0);

        // 标记异常值
        let processed: Vec<DataPoint> = data.into_iter().map(|mut d| {
            let is_outlier = (d.value - avg).abs() > 2.0 * std_dev;

            if is_outlier {
                let mut metadata = d.metadata.unwrap_or_default();
                metadata.insert("is_outlier".to_string(), "true".to_string());
                d.metadata = Some(metadata);
            }

            d
        }).collect();

        Ok(serde_wasm_bindgen::to_value(&processed)?)
    }

    // 图表渲染函数
    #[wasm_bindgen]
    pub fn render_chart(canvas_id: &str, data_js: JsValue) -> Result<(), JsValue> {
        let data: Vec<DataPoint> = serde_wasm_bindgen::from_value(data_js)?;

        // 获取画布
        let document = web_sys::window().unwrap().document().unwrap();
        let canvas = document.get_element_by_id(canvas_id).unwrap();
        let canvas: HtmlCanvasElement = canvas.dyn_into::<HtmlCanvasElement>()?;

        let context = canvas
            .get_context("2d")?
            .unwrap()
            .dyn_into::<CanvasRenderingContext2d>()?;

        // 设置画布大小
        let width = canvas.width() as f64;
        let height = canvas.height() as f64;

        // 清空画布
        context.clear_rect(0.0, 0.0, width, height);

        // 找到数据范围
        if data.is_empty() {
            return Ok(());
        }

        let values: Vec<f64> = data.iter().map(|d| d.value).collect();
        let min_value = values.iter().copied().fold(f64::INFINITY, f64::min);
        let max_value = values.iter().copied().fold(f64::NEG_INFINITY, f64::max);

        let min_time = data.iter().map(|d| d.timestamp).min().unwrap();
        let max_time = data.iter().map(|d| d.timestamp).max().unwrap();

        // 设置边距
        let margin = 40.0;
        let chart_width = width - 2.0 * margin;
        let chart_height = height - 2.0 * margin;

        // 绘制轴
        context.begin_path();
        context.move_to(margin, margin);
        context.line_to(margin, height - margin);
        context.line_to(width - margin, height - margin);
        context.set_stroke_style(&JsValue::from_str("black"));
        context.stroke();

        // 绘制数据点
        context.begin_path();
        let mut first = true;

        for point in &data {
            let x = margin + chart_width * (point.timestamp - min_time) as f64 / (max_time - min_time) as f64;
            let y = height - margin - chart_height * (point.value - min_value) / (max_value - min_value);

            if first {
                context.move_to(x, y);
                first = false;
            } else {
                context.line_to(x, y);
            }

            // 异常值标记为红色点
            let is_outlier = point.metadata.as_ref()
                .and_then(|m| m.get("is_outlier"))
                .map(|v| v == "true")
                .unwrap_or(false);

            if is_outlier {
                context.save();
                context.set_fill_style(&JsValue::from_str("red"));
                context.begin_path();
                context.arc(x, y, 5.0, 0.0, std::f64::consts::PI * 2.0)?;
                context.fill();
                context.restore();
            }
        }

        context.set_stroke_style(&JsValue::from_str("blue"));
        context.stroke();

        // 绘制标签
        context.set_font("12px Arial");
        context.set_fill_style(&JsValue::from_str("black"));

        // Y轴标签
        for i in 0..=5 {
            let value = min_value + (max_value - min_value) * i as f64 / 5.0;
            let y = height - margin - chart_height * i as f64 / 5.0;

            context.fill_text(&format!("{:.1}", value), 5.0, y + 5.0)?;

            context.begin_path();
            context.move_to(margin - 5.0, y);
            context.line_to(margin, y);
            context.stroke();
        }

        // X轴标签
        for i in 0..=5 {
            let timestamp = min_time + (max_time - min_time) * i / 5;
            let x = margin + chart_width * i as f64 / 5.0;

            let date = Date::new(&JsValue::from_f64(timestamp as f64));
            let time_str = date.to_locale_time_string("en-US");

            context.fill_text(&time_str.as_string().unwrap(), x - 20.0, height - 10.0)?;

            context.begin_path();
            context.move_to(x, height - margin);
            context.line_to(x, height - margin + 5.0);
            context.stroke();
        }

        Ok(())
    }

    // 数据可视化组件
    #[function_component(DataVisualization)]
    pub fn data_visualization() -> Html {
        let data = use_state(|| Vec::<DataPoint>::new());
        let canvas_ref = use_node_ref();
        let api_url = use_state(|| "/api".to_string());

        // 加载初始数据
        {
            let data = data.clone();
            let api_url = (*api_url).clone();

            use_effect_with_deps(move |_| {
                let data = data.clone();

                spawn_local(async move {
                    // 构建请求
                    let query = DataQuery {
                        start_time: None,
                        end_time: None,
                        categories: None,
                        limit: Some(100),
                    };

                    let mut opts = web_sys::RequestInit::new();
                    opts.method("POST");
                    opts.body(Some(&JsValue::from_str(&serde_json::to_string(&query).unwrap())));

                    let request = web_sys::Request::new_with_str_and_init(
                        &format!("{}/data", api_url),
                        &opts,
                    ).unwrap();

                    request.headers().set("Content-Type", "application/json").unwrap();

                    let window = web_sys::window().unwrap();
                    let resp_value = wasm_bindgen_futures::JsFuture::from(
                        window.fetch_with_request(&request)
                    ).await.unwrap();

                    let resp: web_sys::Response = resp_value.dyn_into().unwrap();
                    let json = wasm_bindgen_futures::JsFuture::from(resp.json().unwrap())
                        .await.unwrap();

                    let response: DataResponse = serde_wasm_bindgen::from_value(json).unwrap();

                    // 在WebAssembly中处理数据
                    let processed_js = process_data(serde_wasm_bindgen::to_value(&response.data).unwrap()).unwrap();
                    let processed: Vec<DataPoint> = serde_wasm_bindgen::from_value(processed_js).unwrap();

                    data.set(processed);
                });

                || ()
            }, ());
        }

        // 渲染图表
        {
            let data = data.clone();
            let canvas_ref = canvas_ref.clone();

            use_effect_with_deps(move |_| {
                if let Some(canvas) = canvas_ref.cast::<HtmlCanvasElement>() {
                    let data_js = serde_wasm_bindgen::to_value(&*data).unwrap();
                    let _ = render_chart("data-chart", data_js);
                }

                || ()
            }, data.clone());
        }

        // 实时更新定时器
        {
            let data = data.clone();

            use_effect_with_deps(move |_| {
                let data = data.clone();

                let interval = Interval::new(5000, move || {
                    let data = data.clone();
                    let mut current_data = (*data).clone();

                    // 添加一个新的数据点
                    let new_point = DataPoint {
                        timestamp: Date::now() as u64,
                        value: 50.0 + Math::random() * 50.0,
                        category: "realtime".to_string(),
                        metadata: None,
                    };

                    current_data.push(new_point);

                    // 保持最多显示100个点
                    if current_data.len() > 100 {
                        current_data = current_data.into_iter().skip(1).collect();
                    }

                    // 处理数据
                    let processed_js = process_data(
                        serde_wasm_bindgen::to_value(&current_data).unwrap()
                    ).unwrap();

                    let processed: Vec<DataPoint> = serde_wasm_bindgen::from_value(processed_js).unwrap();
                    data.set(processed);
                });

                move || {
                    drop(interval);
                }
            }, ());
        }

        // 计算统计数据
        let stats = {
            let data = (*data).clone();
            let values: Vec<f64> = data.iter().map(|d| d.value).collect();

            let mean = shared::statistics::mean(&values).unwrap_or(0.0);
            let median = shared::statistics::median(&values).unwrap_or(0.0);
            let std_dev = shared::statistics::standard_deviation(&values).unwrap_or(0.0);

            html! {
                <div class="stats">
                    <div><strong>{"Mean: "}</strong>{format!("{:.2}", mean)}</div>
                    <div><strong>{"Median: "}</strong>{format!("{:.2}", median)}</div>
                    <div><strong>{"Std Dev: "}</strong>{format!("{:.2}", std_dev)}</div>
                    <div><strong>{"Points: "}</strong>{data.len()}</div>
                </div>
            }
        };

        html! {
            <div class="data-visualization">
                <h1>{"Real-Time Data Visualization"}</h1>

                <div class="chart-container">
                    <canvas id="data-chart" ref={canvas_ref} width="800" height="400"></canvas>
                </div>

                {stats}
            </div>
        }
    }

    // backend/src/main.rs - 后端实现
    use shared::{DataPoint, statistics, api::{DataQuery, DataResponse, StatsRequest, StatsResponse, StatsOperation}};
    use axum::{
        routing::{get, post},
        http::StatusCode,
        extract::Json,
        Router,
    };
    use std::net::SocketAddr;
    use std::sync::{Arc, Mutex};
    use tower_http::cors::{CorsLayer, Any};
    use rand::Rng;
    use chrono::{Utc, Duration};

    // 模拟数据存储
    struct DataStore {
        data: Mutex<Vec<DataPoint>>,
    }

    impl DataStore {
        fn new() -> Self {
            let mut rng = rand::thread_rng();
            let now = Utc::now();
            let mut data = Vec::with_capacity(1000);

            // 生成示例数据
            for i in 0..1000 {
                let timestamp = (now - Duration::seconds(1000 - i)).timestamp() as u64;
                let base_value = 50.0 + 10.0 * (i as f64 / 1000.0 * std::f64::consts::PI * 2.0).sin();

                // 添加噪声
                let noise = rng.gen_range(-5.0..5.0);

                // 添加一些异常值
                let anomaly = if rng.gen_range(0..100) < 5 {
                    rng.gen_range(15.0..25.0) * if rng.gen_bool(0.5) { 1.0 } else { -1.0 }
                } else {
                    0.0
                };

                let data_point = DataPoint {
                    timestamp,
                    value: base_value + noise + anomaly,
                    category: "sample".to_string(),
                    metadata: None,
                };

                data.push(data_point);
            }

            Self {
                data: Mutex::new(data),
            }
        }

        fn query(&self, query: &DataQuery) -> DataResponse {
            let data = self.data.lock().unwrap();

            let mut filtered = data.iter()
                .filter(|point| {
                    // 时间过滤
                    if let Some(start) = query.start_time {
                        if point.timestamp < start {
                            return false;
                        }
                    }

                    if let Some(end) = query.end_time {
                        if point.timestamp > end {
                            return false;
                        }
                    }

                    // 类别过滤
                    if let Some(categories) = &query.categories {
                        if !categories.contains(&point.category) {
                            return false;
                        }
                    }

                    true
                })
                .cloned()
                .collect::<Vec<_>>();

            // 按时间戳排序
            filtered.sort_by_key(|p| p.timestamp);

            let total = filtered.len();

            // 应用限制
            if let Some(limit) = query.limit {
                if filtered.len() > limit {
                    filtered = filtered.into_iter().take(limit).collect();
                }
            }

            DataResponse {
                data: filtered,
                total,
            }
        }

        fn add(&self, point: DataPoint) {
            let mut data = self.data.lock().unwrap();
            data.push(point);
        }
    }

    #[tokio::main]
    async fn main() {
        // 初始化日志
        tracing_subscriber::fmt::init();

        // 创建数据存储
        let store = Arc::new(DataStore::new());

        // 添加定时模拟数据的任务
        let store_clone = Arc::clone(&store);
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(1));
            let mut rng = rand::thread_rng();

            loop {
                interval.tick().await;

                let now = Utc::now();
                let base_value = 50.0 + 10.0 * (now.timestamp() as f64 / 10.0).sin();
                let noise = rng.gen_range(-5.0..5.0);

                let data_point = DataPoint {
                    timestamp: now.timestamp() as u64,
                    value: base_value + noise,
                    category: "realtime".to_string(),
                    metadata: None,
                };

                store_clone.add(data_point);
            }
        });

        // 定义路由
        let app = Router::new()
            .route("/api/data", post(handler_query_data))
            .route("/api/stats", post(handler_compute_stats))
            .with_state(store)
            .layer(
                CorsLayer::new()
                    .allow_origin(Any)
                    .allow_methods(Any)
                    .allow_headers(Any)
            );

        // 启动服务器
        let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
        println!("Server listening on {}", addr);
        axum::Server::bind(&addr)
            .serve(app.into_make_service())
            .await
            .unwrap();
    }

    // 查询数据处理程序
    async fn handler_query_data(
        axum::extract::State(store): axum::extract::State<Arc<DataStore>>,
        Json(query): Json<DataQuery>,
    ) -> Json<DataResponse> {
        Json(store.query(&query))
    }

    // 计算统计信息
    async fn handler_compute_stats(
        Json(request): Json<StatsRequest>,
    ) -> Result<Json<StatsResponse>, (StatusCode, String)> {
        let StatsRequest { data, operation } = request;

        let values: Vec<f64> = data.iter().map(|d| d.value).collect();

        let result = match operation {
            StatsOperation::Mean => {
                vec![statistics::mean(&values).unwrap_or(0.0)]
            },
            StatsOperation::Median => {
                vec![statistics::median(&values).unwrap_or(0.0)]
            },
            StatsOperation::StandardDeviation => {
                vec![statistics::standard_deviation(&values).unwrap_or(0.0)]
            },
            StatsOperation::MovingAverage { window } => {
                if window == 0 {
                    return Err((
                        StatusCode::BAD_REQUEST,
                        "Window size must be greater than 0".to_string(),
                    ));
                }

                statistics::moving_average(&values, window)
            },
        };

        Ok(Json(StatsResponse { result }))
    }
```

### 12.3 实时协作应用

以下是实时协作应用的示例代码:

```rust
// shared/src/lib.rs - 共享模型
use serde::{Serialize, Deserialize};
use std::collections::HashMap;

// 文档模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Document {
    pub id: String,
    pub title: String,
    pub content: String,
    pub version: u64,
    pub created_at: String,
    pub updated_at: String,
    pub author: String,
    pub collaborators: Vec<String>,
}

// 用户模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub name: String,
    pub email: String,
}

// 操作类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Operation {
    Insert { pos: usize, text: String },
    Delete { pos: usize, len: usize },
    Replace { pos: usize, len: usize, text: String },
}

// 变更模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Change {
    pub id: String,
    pub document_id: String,
    pub user_id: String,
    pub operations: Vec<Operation>,
    pub timestamp: u64,
    pub base_version: u64,
}

// 操作变换函数 - 用于OT冲突解决
pub fn transform(a: &Operation, b: &Operation) -> Operation {
    match (a, b) {
        // 两个插入操作
        (Operation::Insert { pos: pos_a, text: text_a },
         Operation::Insert { pos: pos_b, text: text_b }) => {
            if pos_a < pos_b {
                // b的插入位置在a之后，a不变
                a.clone()
            } else {
                // b的插入位置在a之前，a的位置需要后移
                Operation::Insert {
                    pos: pos_a + text_b.len(),
                    text: text_a.clone()
                }
            }
        },

        // a是插入，b是删除
        (Operation::Insert { pos: pos_a, text: text_a },
         Operation::Delete { pos: pos_b, len: len_b }) => {
            if pos_a <= pos_b {
                // a的插入位置在b删除区域前，不变
                a.clone()
            } else if pos_a >= pos_b + len_b {
                // a的插入位置在b删除区域后，位置前移
                Operation::Insert {
                    pos: pos_a - len_b,
                    text: text_a.clone()
                }
            } else {
                // a的插入位置在b删除区域内，位置变为删除起始位置
                Operation::Insert {
                    pos: pos_b,
                    text: text_a.clone()
                }
            }
        },

        // 其他情况类似，这里简化实现
        _ => a.clone(),
    }
}

// 应用操作到文本
pub fn apply_operation(content: &str, op: &Operation) -> Result<String, String> {
    match op {
        Operation::Insert { pos, text } => {
            if *pos > content.len() {
                return Err(format!("Insert position {} out of bounds", pos));
            }

            let mut result = content[..(*pos)].to_string();
            result.push_str(text);
            result.push_str(&content[(*pos)..]);
            Ok(result)
        },

        Operation::Delete { pos, len } => {
            if *pos + *len > content.len() {
                return Err(format!("Delete range {}:{} out of bounds", pos, pos + len));
            }

            let mut result = content[..(*pos)].to_string();
            result.push_str(&content[(*pos + *len)..]);
            Ok(result)
        },

        Operation::Replace { pos, len, text } => {
            if *pos + *len > content.len() {
                return Err(format!("Replace range {}:{} out of bounds", pos, pos + len));
            }

            let mut result = content[..(*pos)].to_string();
            result.push_str(text);
            result.push_str(&content[(*pos + *len)..]);
            Ok(result)
        },
    }
}

// frontend/src/lib.rs - 前端协作编辑器
use shared::{Document, User, Operation, Change, apply_operation, transform};
use yew::prelude::*;
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::spawn_local;
use web_sys::{HtmlInputElement, HtmlTextAreaElement};
use gloo_timers::callback::Interval;
use gloo_storage::LocalStorage;
use serde::{Serialize, Deserialize};
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::VecDeque;
use uuid::Uuid;
use js_sys::Date;

// WebSocket消息
#[derive(Debug, Clone, Serialize, Deserialize)]
enum WebSocketMessage {
    Join { document_id: String, user_id: String },
    Change { change: Change },
    Sync { version: u64 },
}

// 编辑器状态
struct EditorState {
    document: Option<Document>,
    user: Option<User>,
    pending_changes: VecDeque<Change>,
    ws: Option<web_sys::WebSocket>,
    last_sent_change: Option<Change>,
    last_received_version: u64,
    editor_content: String,
    cursor_position: usize,
    is_connected: bool,
}

impl EditorState {
    fn new() -> Self {
        Self {
            document: None,
            user: None,
            pending_changes: VecDeque::new(),
            ws: None,
            last_sent_change: None,
            last_received_version: 0,
            editor_content: String::new(),
            cursor_position: 0,
            is_connected: false,
        }
    }
}

// 编辑器组件
#[function_component(CollaborativeEditor)]
pub fn collaborative_editor() -> Html {
    // 状态
    let state = use_mut_ref(|| EditorState::new());
    let document_id = use_state(|| "".to_string());
    let text_ref = use_node_ref();
    let users_online = use_state(|| Vec::<User>::new());

    // 初始化
    {
        let state = state.clone();
        let document_id = document_id.clone();

        use_effect_with_deps(move |_| {
            // 从LocalStorage加载用户
            if let Ok(user_json) = LocalStorage::get::<String>("user") {
                if let Ok(user) = serde_json::from_str::<User>(&user_json) {
                    state.borrow_mut().user = Some(user);
                }
            }

            // 如果URL中有文档ID
            if let Some(window) = web_sys::window() {
                if let Ok(location) = window.location().href() {
                    if let Some(id_part) = location.split("?doc=").nth(1) {
                        document_id.set(id_part.to_string());
                    }
                }
            }

            || ()
        }, ());
    }

    // 连接WebSocket
    {
        let state = state.clone();
        let doc_id = (*document_id).clone();

        use_effect_with_deps(move |_| {
            if doc_id.is_empty() {
                return || ();
            }

            let mut state = state.borrow_mut();
            if state.user.is_none() {
                return || ();
            }

            let user = state.user.clone().unwrap();

            // 创建WebSocket连接
            let ws = web_sys::WebSocket::new("ws://localhost:3001/ws")
                .expect("Failed to create WebSocket");

            let on_open = {
                let ws = ws.clone();
                let doc_id = doc_id.clone();
                let user_id = user.id.clone();

                Closure::wrap(Box::new(move |_: web_sys::Event| {
                    // 发送加入消息
                    let msg = WebSocketMessage::Join {
                        document_id: doc_id.clone(),
                        user_id: user_id.clone(),
                    };

                    let _ = ws.send_with_str(&serde_json::to_string(&msg).unwrap());
                }) as Box<dyn FnMut(web_sys::Event)>)
            };

            let on_message = {
                let state_clone = state.clone();
                let text_ref_clone = text_ref.clone();
                let users_online_clone = users_online.clone();

                Closure::wrap(Box::new(move |e: web_sys::MessageEvent| {
                    if let Ok(txt) = e.data().dyn_into::<js_sys::JsString>() {
                        let msg_str = String::from(txt);

                        if let Ok(msg) = serde_json::from_str::<serde_json::Value>(&msg_str) {
                            // 根据消息类型处理
                            if let Some(msg_type) = msg.get("type").and_then(|t| t.as_str()) {
                                match msg_type {
                                    "document" => {
                                        if let Ok(doc) = serde_json::from_value::<Document>(
                                            msg.get("document").unwrap().clone()
                                        ) {
                                            let mut state = state_clone.borrow_mut();
                                            state.document = Some(doc.clone());
                                            state.last_received_version = doc.version;
                                            state.editor_content = doc.content.clone();

                                            // 更新编辑器内容
                                            if let Some(textarea) = text_ref_clone.cast::<HtmlTextAreaElement>() {
                                                textarea.set_value(&doc.content);
                                            }
                                        }
                                    },
                                    "change" => {
                                        if let Ok(change) = serde_json::from_value::<Change>(
                                            msg.get("change").unwrap().clone()
                                        ) {
                                            let mut state = state_clone.borrow_mut();
                                            if let Some(doc) = &mut state.document {
                                                if change.base_version == doc.version {
                                                    // 应用更改
                                                    for op in &change.operations {
                                                        if let Ok(new_content) = apply_operation(&doc.content, op) {
                                                            doc.content = new_content;
                                                        }
                                                    }

                                                    doc.version += 1;
                                                    state.last_received_version = doc.version;
                                                    state.editor_content = doc.content.clone();

                                                    // 更新编辑器内容，保持光标位置
                                                    if let Some(textarea) = text_ref_clone.cast::<HtmlTextAreaElement>() {
                                                        let cursor_pos = textarea.selection_start().unwrap_or(Ok(0)).unwrap();

                                                        textarea.set_value(&doc.content);

                                                        // 尝试恢复光标位置
                                                        let _ = textarea.set_selection_start(Some(cursor_pos));
                                                        let _ = textarea.set_selection_end(Some(cursor_pos));
                                                    }

                                                    // 变换挂起的更改
                                                    for pending in &mut state.pending_changes {
                                                        let mut transformed_ops = Vec::new();

                                                        for op in &pending.operations {
                                                            let mut transformed = op.clone();

                                                            for incoming_op in &change.operations {
                                                                transformed = transform(&transformed, incoming_op);
                                                            }

                                                            transformed_ops.push(transformed);
                                                        }

                                                        pending.operations = transformed_ops;
                                                        pending.base_version = doc.version;
                                                    }
                                                }
                                            }
                                        }
                                    },
                                    "users" => {
                                        if let Ok(users) = serde_json::from_value::<Vec<User>>(
                                            msg.get("users").unwrap().clone()
                                        ) {
                                            users_online_clone.set(users);
                                        }
                                    },
                                    _ => {}
                                }
                            }
                        }
                    }
                }) as Box<dyn FnMut(web_sys::MessageEvent)>)
            };

            // 设置回调
            ws.set_onopen(Some(on_open.as_ref().unchecked_ref()));
            ws.set_onmessage(Some(on_message.as_ref().unchecked_ref()));

            // 保存WebSocket实例
            state.ws = Some(ws);
            state.is_connected = true;

            // 设置定时发送更改
            let change_sender = {
                let state = state.clone();

                Interval::new(100, move || {
                    let mut state = state.borrow_mut();

                    // 如果有待发送更改
                    if !state.pending_changes.is_empty() && state.last_sent_change.is_none() {
                        if let Some(ws) = &state.ws {
                            if ws.ready_state() == web_sys::WebSocket::OPEN {
                                if let Some(change) = state.pending_changes.pop_front() {
                                    let msg = WebSocketMessage::Change { change: change.clone() };
                                    let _ = ws.send_with_str(&serde_json::to_string(&msg).unwrap());
                                    state.last_sent_change = Some(change);
                                }
                            }
                        }
                    }
                })
            };

            // 清理函数
            move || {
                drop(on_open);
                drop(on_message);
                drop(change_sender);

                if let Some(ws) = &state.ws {
                    ws.close().ok();
                }
            }
        }, document_id.clone());
    }

    // 处理文本改变
    let on_input = {
        let state = state.clone();
        let text_ref = text_ref.clone();

        Callback::from(move |_: InputEvent| {
            let mut state = state.borrow_mut();
            if state.document.is_none() || state.user.is_none() {
                return;
            }

            if let Some(textarea) = text_ref.cast::<HtmlTextAreaElement>() {
                let new_content = textarea.value();
                let old_content = &state.editor_content;

                // 找出更改
                if new_content != *old_content {
                    let user = state.user.as_ref().unwrap();
                    let doc = state.document.as_ref().unwrap();

                    // 获取光标位置
                    let cursor_pos = textarea.selection_start().unwrap_or(Ok(0)).unwrap() as usize;
                    state.cursor_position = cursor_pos;

                    // 简单的diff算法 - 假设一次只有一个更改
                    // 实际应用中应该使用更复杂的diff算法
                    let mut operations = Vec::new();

                    if new_content.len() > old_content.len() {
                        // 插入或替换
                        let mut common_prefix_len = 0;
                        while common_prefix_len < old_content.len() &&
                              common_prefix_len < new_content.len() &&
                              old_content.chars().nth(common_prefix_len) == new_content.chars().nth(common_prefix_len) {
                            common_prefix_len += 1;
                        }

                        let mut common_suffix_len = 0;
                        while common_suffix_len < old_content.len() - common_prefix_len &&
                              common_suffix_len < new_content.len() - common_prefix_len &&
                              old_content.chars().nth(old_content.len() - 1 - common_suffix_len) ==
                              new_content.chars().nth(new_content.len() - 1 - common_suffix_len) {
                            common_suffix_len += 1;
                        }

                        let old_middle_len = old_content.len() - common_prefix_len - common_suffix_len;
                        let new_middle = &new_content[common_prefix_len..(new_content.len() - common_suffix_len)];

                        if old_middle_len == 0 {
                            // 纯插入
                            operations.push(Operation::Insert {
                                pos: common_prefix_len,
                                text: new_middle.to_string(),
                            });
                        } else {
                            // 替换
                            operations.push(Operation::Replace {
                                pos: common_prefix_len,
                                len: old_middle_len,
                                text: new_middle.to_string(),
                            });
                        }
                    } else {
                        // 删除或替换
                        let mut common_prefix_len = 0;
                        while common_prefix_len < old_content.len() &&
                              common_prefix_len < new_content.len() &&
                              old_content.chars().nth(common_prefix_len) == new_content.chars().nth(common_prefix_len) {
                            common_prefix_len += 1;
                        }

                        let mut common_suffix_len = 0;
                        while common_suffix_len < old_content.len() - common_prefix_len &&
                              common_suffix_len < new_content.len() - common_prefix_len &&
                              old_content.chars().nth(old_content.len() - 1 - common_suffix_len) ==
                              new_content.chars().nth(new_content.len() - 1 - common_suffix_len) {
                            common_suffix_len += 1;
                        }

                        let old_middle_len = old_content.len() - common_prefix_len - common_suffix_len;
                        let new_middle = &new_content[common_prefix_len..(new_content.len() - common_suffix_len)];

                        if new_middle.is_empty() {
                            // 纯删除
                            operations.push(Operation::Delete {
                                pos: common_prefix_len,
                                len: old_middle_len,
                            });
                        } else {
                            // 替换
                            operations.push(Operation::Replace {
                                pos: common_prefix_len,
                                len: old_middle_len,
                                text: new_middle.to_string(),
                            });
                        }
                    }

                    if !operations.is_empty() {
                        // 创建更改并添加到队列
                        let change = Change {
                            id: Uuid::new_v4().to_string(),
                            document_id: doc.id.clone(),
                            user_id: user.id.clone(),
                            operations,
                            timestamp: Date::now() as u64,
                            base_version: state.last_received_version,
                        };

                        state.pending_changes.push_back(change);

                        // 立即应用本地更改
                        if let Some(doc) = &mut state.document {
                            for op in &state.pending_changes.back().unwrap().operations {
                                if let Ok(new_content) = apply_operation(&doc.content, op) {
                                    doc.content = new_content;
                                }
                            }
                        }

                        // 更新编辑器内容状态
                        state.editor_content = new_content;
                    }
                }
            }
        })
    };

    // 创建新文档
    let on_create_document = {
        let state = state.clone();
        let document_id = document_id.clone();

        Callback::from(move |_: MouseEvent| {
            let state_ref = state.clone();
            let mut state = state.borrow_mut();

            if state.user.is_none() {
                return;
            }

            let user = state.user.as_ref().unwrap();
            let doc_id = Uuid::new_v4().to_string();

            // 创建文档
            let doc = Document {
                id: doc_id.clone(),
                title: "Untitled Document".to_string(),
                content: "".to_string(),
                version: 0,
                created_at: Date::new_0().to_iso_string().as_string().unwrap(),
                updated_at: Date::new_0().to_iso_string().as_string().unwrap(),
                author: user.id.clone(),
                collaborators: vec![user.id.clone()],
            };

            // 发送创建请求
            spawn_local({
                let doc = doc.clone();
                let doc_id = doc_id.clone();
                let document_id = document_id.clone();

                async move {
                    let mut opts = web_sys::RequestInit::new();
                    opts.method("POST");
                    opts.body(Some(&JsValue::from_str(&serde_json::to_string(&doc).unwrap())));

                    let request = web_sys::Request::new_with_str_and_init(
                        "/api/documents",
                        &opts,
                    ).unwrap();

                    request.headers().set("Content-Type", "application/json").unwrap();

                    let window = web_sys::window().unwrap();
                    let resp_value = wasm_bindgen_futures::JsFuture::from(
                        window.fetch_with_request(&request)
                    ).await.unwrap();

                    let resp: web_sys::Response = resp_value.dyn_into().unwrap();

                    if resp.ok() {
                        // 设置文档ID并更新URL
                        document_id.set(doc_id.clone());

                        if let Some(history) = window.history() {
                            let _ = history.push_state_with_url(
                                &JsValue::NULL,
                                "Collaborative Editor",
                                Some(&format!("?doc={}", doc_id)),
                            );
                        }

                        // 更新状态
                        let mut state = state_ref.borrow_mut();
                        state.document = Some(doc);
                    }
                }
            });
        })
    };

    // 文档标题和协作者
    let document_info = {
        let state = state.borrow();
        let online_users = (*users_online).clone();

        if let Some(doc) = &state.document {
            html! {
                <div class="document-info">
                    <h2>{&doc.title}</h2>
                    <div class="collaborators">
                        <h3>{"Collaborators:"}</h3>
                        <ul>
                            {
                                online_users.iter().map(|user| {
                                    html! {
                                        <li key={user.id.clone()}>
                                            {&user.name} {
                                                if user.id == doc.author {
                                                    html! { <span class="author-badge">{"(Author)"}</span> }
                                                } else {
                                                    html! {}
                                                }
                                            }
                                        </li>
                                    }
                                }).collect::<Html>()
                            }
                        </ul>
                    </div>
                </div>
            }
        } else {
            html! {}
        }
    };

    // 渲染编辑器或登录/创建界面
    let editor_view = {
        let state = state.borrow();

        if state.user.is_none() {
            // 登录视图
            html! {
                <div class="login-view">
                    <h2>{"Sign In"}</h2>
                    <p>{"Please sign in to use the collaborative editor."}</p>

                    <div class="form-group">
                        <label for="name">{"Name:"}</label>
                        <input id="name" type="text" placeholder="Your name" />
                    </div>

                    <div class="form-group">
                        <label for="email">{"Email:"}</label>
                        <input id="email" type="email" placeholder="Your email" />
                    </div>

                    <button onclick={
                        let state = state.clone();

                        Callback::from(move |_: MouseEvent| {
                            let document = web_sys::window().unwrap().document().unwrap();

                            let name_input = document.get_element_by_id("name")
                                .and_then(|el| el.dyn_into::<HtmlInputElement>().ok())
                                .map(|input| input.value())
                                .unwrap_or_default();

                            let email_input = document.get_element_by_id("email")
                                .and_then(|el| el.dyn_into::<HtmlInputElement>().ok())
                                .map(|input| input.value())
                                .unwrap_or_default();

                            if !name_input.is_empty() && !email_input.is_empty() {
                                let user = User {
                                    id: Uuid::new_v4().to_string(),
                                    name: name_input,
                                    email: email_input,
                                };

                                // 保存到LocalStorage
                                let _ = LocalStorage::set("user", serde_json::to_string(&user).unwrap());

                                // 更新状态
                                let mut state = state.borrow_mut();
                                state.user = Some(user);
                            }
                        })
                    }>
                        {"Sign In"}
                    </button>
                </div>
            }
        } else if state.document.is_none() {
            // 文档选择视图
            html! {
                <div class="document-selection">
                    <h2>{"Welcome, "}{&state.user.as_ref().unwrap().name}</h2>

                    <div class="document-actions">
                        <button onclick={on_create_document.clone()}>{"Create New Document"}</button>

                        <div class="form-group">
                            <label for="doc-id">{"Or enter document ID:"}</label>
                            <input
                                id="doc-id"
                                type="text"
                                value={(*document_id).clone()}
                                onchange={
                                    let document_id = document_id.clone();

                                    Callback::from(move |e: Event| {
                                        let input: HtmlInputElement = e.target_unchecked_into();
                                        document_id.set(input.value());
                                    })
                                }
                            />
                            <button onclick={
                                let doc_id = (*document_id).clone();

                                Callback::from(move |_: MouseEvent| {
                                    if !doc_id.is_empty() {
                                        // 更新URL
                                        if let Some(window) = web_sys::window() {
                                            if let Some(history) = window.history() {
                                                let _ = history.push_state_with_url(
                                                    &JsValue::NULL,
                                                    "Collaborative Editor",
                                                    Some(&format!("?doc={}", doc_id)),
                                                );
                                            }
                                        }
                                    }
                                })
                            }>{"Join Document"}</button>
                        </div>
                    </div>
                </div>
            }
        } else {
            // 编辑器视图
            html! {
                <div class="editor-view">
                    {document_info}

                    <div class="editor-container">
                        <textarea
                            ref={text_ref.clone()}
                            value={state.document.as_ref().unwrap().content.clone()}
                            oninput={on_input.clone()}
                        />
                    </div>

                    <div class="connection-status">
                        {
                            if state.is_connected {
                                html! { <span class="status connected">{"Connected"}</span> }
                            } else {
                                html! { <span class="status disconnected">{"Disconnected"}</span> }
                            }
                        }
                    </div>
                </div>
            }
        }
    };

    html! {
        <div class="collaborative-editor">
            <h1>{"Rust WebAssembly Collaborative Editor"}</h1>
            {editor_view}
        </div>
    }
}

// backend/src/main.rs - 后端协作服务器
use shared::{Document, User, Change, Operation, apply_operation};
use tokio::sync::{mpsc, Mutex, RwLock};
use std::sync::Arc;
use std::collections::{HashMap, HashSet
### 12.3 实时协作应用（续）

```rust
// backend/src/main.rs - 后端协作服务器
use shared::{Document, User, Change, Operation, apply_operation};
use tokio::sync::{mpsc, Mutex, RwLock};
use std::sync::Arc;
use std::collections::{HashMap, HashSet};
use axum::{
    extract::{ws::{WebSocket, Message}, WebSocketUpgrade, Path, State, Json},
    response::IntoResponse,
    routing::{get, post},
    Router,
};
use serde_json::{json, Value};
use uuid::Uuid;
use chrono::Utc;
use futures::{SinkExt, StreamExt};
use std::net::SocketAddr;
use tower_http::cors::{CorsLayer, Any};

// 应用状态
struct AppState {
    documents: RwLock<HashMap<String, Document>>,
    users: RwLock<HashMap<String, User>>,
    document_channels: RwLock<HashMap<String, mpsc::Sender<ServerMessage>>>,
    document_users: RwLock<HashMap<String, HashSet<String>>>,
}

// 服务器消息
#[derive(Debug, Clone)]
enum ServerMessage {
    UserJoined {
        document_id: String,
        user_id: String,
    },
    UserLeft {
        document_id: String,
        user_id: String,
    },
    DocumentChange {
        change: Change,
    },
    SyncRequest {
        user_id: String,
        version: u64,
    },
}

// 客户端消息
#[derive(Debug, Clone, serde::Deserialize)]
#[serde(tag = "type")]
enum ClientMessage {
    #[serde(rename = "join")]
    Join {
        document_id: String,
        user_id: String,
    },
    #[serde(rename = "change")]
    Change {
        change: Change,
    },
    #[serde(rename = "sync")]
    Sync {
        version: u64,
    },
}

#[tokio::main]
async fn main() {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    // 创建应用状态
    let state = Arc::new(AppState {
        documents: RwLock::new(HashMap::new()),
        users: RwLock::new(HashMap::new()),
        document_channels: RwLock::new(HashMap::new()),
        document_users: RwLock::new(HashMap::new()),
    });
    
    // 设置路由
    let app = Router::new()
        .route("/api/documents", post(create_document))
        .route("/api/documents/:id", get(get_document))
        .route("/ws", get(websocket_handler))
        .with_state(state)
        .layer(
            CorsLayer::new()
                .allow_origin(Any)
                .allow_methods(Any)
                .allow_headers(Any)
        );
    
    // 启动服务器
    let addr = SocketAddr::from(([127, 0, 0, 1], 3001));
    println!("Server listening on {}", addr);
    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}

// 创建文档
async fn create_document(
    State(state): State<Arc<AppState>>,
    Json(document): Json<Document>,
) -> impl IntoResponse {
    // 保存文档
    let mut documents = state.documents.write().await;
    documents.insert(document.id.clone(), document.clone());
    
    // 创建文档通信通道
    let (tx, mut rx) = mpsc::channel(100);
    state.document_channels.write().await.insert(document.id.clone(), tx);
    state.document_users.write().await.insert(document.id.clone(), HashSet::new());
    
    // 启动文档处理任务
    let state_clone = state.clone();
    let doc_id = document.id.clone();
    
    tokio::spawn(async move {
        process_document_messages(state_clone, doc_id, &mut rx).await;
    });
    
    Json(json!({
        "success": true,
        "document": document
    }))
}

// 获取文档
async fn get_document(
    State(state): State<Arc<AppState>>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    let documents = state.documents.read().await;
    
    if let Some(doc) = documents.get(&id) {
        Json(json!({
            "success": true,
            "document": doc
        }))
    } else {
        Json(json!({
            "success": false,
            "error": "Document not found"
        }))
    }
}

// WebSocket处理程序
async fn websocket_handler(
    ws: WebSocketUpgrade,
    State(state): State<Arc<AppState>>,
) -> impl IntoResponse {
    ws.on_upgrade(|socket| handle_socket(socket, state))
}

// 处理WebSocket连接
async fn handle_socket(socket: WebSocket, state: Arc<AppState>) {
    // 分离发送和接收流
    let (mut sender, mut receiver) = socket.split();
    
    // 用户和文档标识符
    let mut user_id = String::new();
    let mut document_id = String::new();
    
    // 处理接收的消息
    while let Some(Ok(message)) = receiver.next().await {
        match message {
            Message::Text(text) => {
                if let Ok(msg) = serde_json::from_str::<ClientMessage>(&text) {
                    match msg {
                        ClientMessage::Join { document_id: doc_id, user_id: uid } => {
                            // 保存用户ID和文档ID
                            user_id = uid.clone();
                            document_id = doc_id.clone();
                            
                            // 查找用户
                            let mut users = state.users.write().await;
                            if !users.contains_key(&uid) {
                                // 创建临时用户
                                users.insert(uid.clone(), User {
                                    id: uid.clone(),
                                    name: format!("User {}", &uid[..6]),
                                    email: format!("user{}@example.com", &uid[..6]),
                                });
                            }
                            
                            // 发送文档给用户
                            let documents = state.documents.read().await;
                            if let Some(doc) = documents.get(&doc_id) {
                                let response = json!({
                                    "type": "document",
                                    "document": doc
                                });
                                
                                if let Err(e) = sender.send(Message::Text(response.to_string())).await {
                                    println!("Error sending document: {}", e);
                                    break;
                                }
                                
                                // 添加用户到文档
                                if let Some(tx) = state.document_channels.read().await.get(&doc_id) {
                                    let _ = tx.send(ServerMessage::UserJoined {
                                        document_id: doc_id.clone(),
                                        user_id: uid.clone(),
                                    }).await;
                                }
                            } else {
                                // 文档不存在，创建新文档
                                let new_doc = Document {
                                    id: doc_id.clone(),
                                    title: "Untitled Document".to_string(),
                                    content: "".to_string(),
                                    version: 0,
                                    created_at: Utc::now().to_rfc3339(),
                                    updated_at: Utc::now().to_rfc3339(),
                                    author: uid.clone(),
                                    collaborators: vec![uid.clone()],
                                };
                                
                                // 保存文档
                                let mut documents = state.documents.write().await;
                                documents.insert(doc_id.clone(), new_doc.clone());
                                
                                // 如果是新文档，创建通信通道
                                if !state.document_channels.read().await.contains_key(&doc_id) {
                                    let (tx, mut rx) = mpsc::channel(100);
                                    state.document_channels.write().await.insert(doc_id.clone(), tx.clone());
                                    state.document_users.write().await.insert(doc_id.clone(), HashSet::new());
                                    
                                    // 启动文档处理任务
                                    let state_clone = state.clone();
                                    let doc_id_clone = doc_id.clone();
                                    
                                    tokio::spawn(async move {
                                        process_document_messages(state_clone, doc_id_clone, &mut rx).await;
                                    });
                                    
                                    // 添加用户到文档
                                    let _ = tx.send(ServerMessage::UserJoined {
                                        document_id: doc_id.clone(),
                                        user_id: uid.clone(),
                                    }).await;
                                }
                                
                                // 发送文档给用户
                                let response = json!({
                                    "type": "document",
                                    "document": new_doc
                                });
                                
                                if let Err(e) = sender.send(Message::Text(response.to_string())).await {
                                    println!("Error sending document: {}", e);
                                    break;
                                }
                            }
                        },
                        ClientMessage::Change { change } => {
                            // 转发更改到文档通道
                            if let Some(tx) = state.document_channels.read().await.get(&document_id) {
                                let _ = tx.send(ServerMessage::DocumentChange {
                                    change,
                                }).await;
                            }
                        },
                        ClientMessage::Sync { version } => {
                            // 发送同步请求
                            if let Some(tx) = state.document_channels.read().await.get(&document_id) {
                                let _ = tx.send(ServerMessage::SyncRequest {
                                    user_id: user_id.clone(),
                                    version,
                                }).await;
                            }
                        },
                    }
                }
            },
            Message::Close(_) => {
                // 用户断开连接
                if !document_id.is_empty() && !user_id.is_empty() {
                    if let Some(tx) = state.document_channels.read().await.get(&document_id) {
                        let _ = tx.send(ServerMessage::UserLeft {
                            document_id: document_id.clone(),
                            user_id: user_id.clone(),
                        }).await;
                    }
                }
                break;
            },
            _ => {}
        }
    }
    
    // 用户断开连接
    if !document_id.is_empty() && !user_id.is_empty() {
        if let Some(tx) = state.document_channels.read().await.get(&document_id) {
            let _ = tx.send(ServerMessage::UserLeft {
                document_id: document_id.clone(),
                user_id: user_id.clone(),
            }).await;
        }
    }
}

// 处理文档消息
async fn process_document_messages(
    state: Arc<AppState>,
    document_id: String,
    rx: &mut mpsc::Receiver<ServerMessage>,
) {
    let mut user_connections: HashMap<String, mpsc::Sender<Value>> = HashMap::new();
    
    while let Some(message) = rx.recv().await {
        match message {
            ServerMessage::UserJoined { document_id, user_id } => {
                // 创建用户消息通道
                let (tx, mut rx) = mpsc::channel(100);
                user_connections.insert(user_id.clone(), tx);
                
                // 添加用户到文档用户列表
                if let Some(users) = state.document_users.write().await.get_mut(&document_id) {
                    users.insert(user_id.clone());
                }
                
                // 获取当前在线用户
                let online_users = get_online_users(&state, &document_id).await;
                
                // 广播用户列表更新
                broadcast_to_document(&state, &document_id, json!({
                    "type": "users",
                    "users": online_users
                })).await;
                
                // 启动用户消息处理任务
                let state_clone = state.clone();
                let document_id_clone = document_id.clone();
                let user_id_clone = user_id.clone();
                
                tokio::spawn(async move {
                    while let Some(msg) = rx.recv().await {
                        // 处理发送给特定用户的消息
                    }
                    
                    // 用户连接已关闭
                    if let Some(users) = state_clone.document_users.write().await.get_mut(&document_id_clone) {
                        users.remove(&user_id_clone);
                    }
                });
            },
            ServerMessage::UserLeft { document_id, user_id } => {
                // 移除用户连接
                user_connections.remove(&user_id);
                
                // 从文档用户列表中移除
                if let Some(users) = state.document_users.write().await.get_mut(&document_id) {
                    users.remove(&user_id);
                }
                
                // 获取当前在线用户
                let online_users = get_online_users(&state, &document_id).await;
                
                // 广播用户列表更新
                broadcast_to_document(&state, &document_id, json!({
                    "type": "users",
                    "users": online_users
                })).await;
            },
            ServerMessage::DocumentChange { change } => {
                // 应用更改到文档
                let mut documents = state.documents.write().await;
                
                if let Some(doc) = documents.get_mut(&document_id) {
                    // 检查版本号
                    if change.base_version == doc.version {
                        // 应用操作
                        for op in &change.operations {
                            if let Ok(new_content) = apply_operation(&doc.content, op) {
                                doc.content = new_content;
                            }
                        }
                        
                        // 更新版本号和时间
                        doc.version += 1;
                        doc.updated_at = Utc::now().to_rfc3339();
                        
                        // 广播更改
                        broadcast_to_document(&state, &document_id, json!({
                            "type": "change",
                            "change": change
                        })).await;
                    }
                }
            },
            ServerMessage::SyncRequest { user_id, version } => {
                // 处理同步请求
                let documents = state.documents.read().await;
                
                if let Some(doc) = documents.get(&document_id) {
                    if version < doc.version {
                        // 需要同步，发送完整文档
                        if let Some(tx) = user_connections.get(&user_id) {
                            let _ = tx.send(json!({
                                "type": "document",
                                "document": doc
                            })).await;
                        }
                    }
                }
            },
        }
    }
}

// 获取文档的在线用户
async fn get_online_users(state: &Arc<AppState>, document_id: &str) -> Vec<User> {
    let mut result = Vec::new();
    
    if let Some(user_ids) = state.document_users.read().await.get(document_id) {
        let users = state.users.read().await;
        
        for user_id in user_ids {
            if let Some(user) = users.get(user_id) {
                result.push(user.clone());
            }
        }
    }
    
    result
}

// 广播消息给文档的所有用户
async fn broadcast_to_document(state: &Arc<AppState>, document_id: &str, message: Value) {
    if let Some(user_ids) = state.document_users.read().await.get(document_id) {
        // 将集合转换为向量以避免写锁冲突
        let user_ids_vec: Vec<String> = user_ids.iter().cloned().collect();
        
        for user_id in user_ids_vec {
            // 为每个用户发送消息
            // 在实际应用中，这里应该向用户的WebSocket发送消息
        }
    }
}
```

## 13. 挑战与解决方案

### 13.1 主要技术挑战

Rust+WebAssembly全栈架构面临以下主要挑战：

1. **WebAssembly和DOM交互性能**

   DOM操作需要通过桥接层访问，可能导致性能瓶颈，尤其是频繁的细粒度操作。

   **解决方案**：
   - 批量DOM更新而非单个更新
   - 使用虚拟DOM技术（如Yew或Dioxus）
   - 以JavaScript组件形式包装高频DOM操作

2. **代码包大小**

   Rust编译为WebAssembly的输出可能比同等JavaScript代码更大。

   **解决方案**：
   - 使用`wasm-opt`工具优化二进制文件大小
   - 应用代码拆分技术，延迟加载非关键功能
   - 选择性导出API，减少绑定代码生成

3. **调试难度**

   WebAssembly调试工具链仍不够成熟。

   **解决方案**：
   - 使用`console_error_panic_hook`在浏览器控制台捕获Rust异常
   - 实现自定义日志系统跨WebAssembly边界传递详细信息
   - 使用`#[cfg(debug_assertions)]`条件编译添加额外调试信息

4. **异步编程模型差异**

   JavaScript和Rust的异步机制差异可能导致集成复杂。

   **解决方案**：
   - 使用`wasm-bindgen-futures`桥接Rust和JavaScript的异步模型
   - 设计明确的异步API边界
   - 在Rust端使用`async/await`与JavaScript Promises匹配

### 13.2 生态系统局限

1. **前端组件库缺乏**

   与React、Vue等成熟的JavaScript生态相比，Rust前端组件生态系统相对年轻。

   **解决方案**：
   - 构建核心组件自定义库
   - 使用CSS框架（如Tailwind）简化样式
   - 通过`web-sys`与现有JavaScript组件集成

2. **服务端框架整合**

   Rust服务端框架与WebAssembly的集成仍在发展中。

   **解决方案**：
   - 使用成熟的Rust HTTP框架（如axum、actix-web）
   - 实现明确定义的API边界，降低框架集成复杂性
   - 采用分层设计使核心业务逻辑独立于框架

3. **工具链成熟度**

   全栈开发工具链与JavaScript相比尚不完善。

   **解决方案**：
   - 使用Trunk简化构建流程
   - 设计自定义开发脚本，自动化常见任务
   - 利用Docker容器标准化开发环境

### 13.3 解决策略

1. **渐进式集成**

   不必一次性将整个应用迁移到Rust+WebAssembly。

   **实现方法**：
   - 识别计算密集或需要共享的组件
   - 首先将这些组件迁移到Rust，保持其余部分使用现有技术
   - 逐步扩展Rust代码覆盖范围

2. **混合架构**

   利用各技术的优势。

   **实现方法**：
   - 在UI层使用成熟的JavaScript框架
   - 将业务逻辑和验证实现为Rust共享代码
   - 性能关键路径使用WebAssembly

3. **专注关键场景**

   在特定用例中发挥Rust+WebAssembly的优势。

   **最佳场景**：
   - 计算密集型应用（数据处理、可视化）
   - 需要强类型保证的复杂业务规则
   - 需要在前后端共享逻辑的应用
   - 对安全和可靠性要求高的应用

## 14. 未来发展趋势

### 14.1 标准演进

1. **WebAssembly组件模型**

   组件模型将为Wasm模块之间的互操作性提供标准化方法。

   **影响**：
   - 促进更细粒度的模块化
   - 简化与其他语言编写的Wasm模块集成
   - 使模块级依赖管理更加高效

2. **接口类型**

   接口类型将使跨语言类型安全交互更加简单。

   **影响**：
   - 减少序列化/反序列化开销
   - 类型安全的跨语言API边界
   - 提高工具生成代码的质量

3. **垃圾回收与引用类型**

   GC提案将使WebAssembly更好地支持垃圾回收语言并简化内存管理。

   **影响**：
   - 改善与JavaScript的互操作性
   - 可能支持更多Rust标准库功能
   - 简化复杂数据结构的处理

### 14.2 工具链改进

1. **编译优化**

   针对Rust-to-WebAssembly的编译器优化将继续改进。

   **预期进展**：
   - 更智能的死代码消除
   - 更好的SIMD和线程支持
   - 改进的增量编译

2. **开发体验**

   开发和调试工具将变得更加成熟。

   **预期进展**：
   - 更好的WebAssembly调试器集成
   - 热重载支持改进
   - IDE集成增强

3. **生态系统扩展**

   更多库和框架将原生支持WebAssembly。

   **预期进展**：
   - 更丰富的UI组件库
   - 专用于WebAssembly优化的数据处理库
   - 跨平台框架的Rust实现

### 14.3 生态系统扩展

1. **新兴应用场景**

   新的用例将推动Rust-WebAssembly的采用。

   **潜在领域**：
   - 边缘计算与物联网
   - 扩展Rust区块链应用到浏览器
   - WebVR/AR应用
   - 离线优先型复杂应用

2. **跨平台统一**

   Rust+WebAssembly将成为跨平台开发的统一方案。

   **预期发展**：
   - 从单一代码库部署到Web、桌面和移动
   - 使用Wasm运行时的边缘服务器
   - 通过WebAssembly System Interface的嵌入式部署

3. **企业采用**

   随着技术成熟，企业采用率将提高。

   **驱动因素**：
   - 安全和可靠性需求
   - 性能优化需求
   - 开发效率与代码复用

## 15. 结论与建议

### 15.1 可行性总结

基于前述分析，Rust+WebAssembly全栈架构在特定条件下是可行的：

1. **技术可行性**: ✅ 高
   - 核心技术组件已经成熟
   - 编译流程可靠且稳定
   - 互操作性问题有已知的解决方案

2. **生产实践可行性**: ⚠️ 中等
   - 工具链和开发体验仍在提升中
   - 调试和测试工具需要进一步成熟
   - 目前最适合特定用例而非所有场景

3. **经济可行性**: 📊 场景依赖
   - 对于计算密集型应用，性能收益可能证明努力是值得的
   - 对于简单应用，开发投入可能超过收益
   - 长期维护成本可能降低，但初始投资较高

### 15.2 应用场景建议

以下场景最适合采用Rust+WebAssembly全栈架构：

1. **计算密集型应用**
   - 数据可视化和分析工具
   - 多媒体处理应用
   - 复杂模拟和建模工具

2. **需要端到端类型安全的应用**
   - 金融和会计应用
   - 医疗健康信息系统
   - 复杂业务规则的企业应用

3. **需要代码共享的应用**
   - 具有复杂验证逻辑的表单系统
   - 在线/离线需要相同行为的应用
   - 需要前后端一致数据处理的应用

4. **安全敏感应用**
   - 加密应用
   - 权限和访问控制系统
   - 包含敏感数据处理的应用

### 15.3 实施路径

建议采用渐进式实施路径：

1. **起步阶段(1-3个月)**
   - 从共享类型和验证逻辑开始
   - 使用wasm-bindgen和成熟的Rust服务器框架
   - 在现有应用中集成小型功能证明概念

2. **扩展阶段(3-6个月)**
   - 实现更完整的全栈功能
   - 构建自定义组件库
   - 建立高效的开发工作流

3. **优化阶段(6-9个月)**
   - 应用性能优化技术
   - 实施高级架构模式
   - 集成监控和可观测性

4. **成熟阶段(9-12个月)**
   - 扩展到关键业务应用
   - 建立最佳实践和公司内工具
   - 培训团队并建立长期支持机制

## 16. 思维导图

```text
                               ┌───────────────────────┐
                               │ Rust+WebAssembly全栈架构 │
                               └─────────┬─────────────┘
           ┌────────────────────────────┬┴┬───────────────────────────────┐
           ▼                            ▼ ▼                               ▼
┌─────────────────────┐       ┌──────────────────┐              ┌───────────────────┐
│     技术组件        │       │    架构设计      │              │     优势与挑战     │
└────────┬────────────┘       └────────┬─────────┘              └─────────┬─────────┘
         │                             │                                  │
  ┌──────┴───────┐            ┌────────┴────────┐                ┌───────┴───────┐
  ▼              ▼            ▼                 ▼                ▼               ▼
┌────────┐    ┌───────┐   ┌────────┐      ┌──────────┐      ┌────────┐     ┌─────────┐
│前端组件│    │后端组件│   │ 全栈共享 │      │  通信协议 │      │  优势  │     │  挑战   │
└───┬────┘    └───┬───┘   └────┬───┘      └─────┬────┘      └───┬────┘     └────┬────┘
    │            │            │                │                │              │
┌───┴───┐     ┌──┴───┐    ┌───┴────┐       ┌───┴───┐        ┌───┴────┐     ┌────┴────┐
│Yew框架│     │Axum  │    │类型定义│       │序列化 │        │类型安全│     │包体积  │
│Dioxus │     │Actix │    │验证逻辑│       │RPC协议│        │性能优化│     │DOM交互 │
│Sycamore│     │Rocket│    │工具函数│       │WebSocket        │代码复用│     │调试难度│
└───────┘     └──────┘    └────────┘       └───────┘        └────────┘     └─────────┘

           ┌────────────────────────────┬┴┬───────────────────────────────┐
           ▼                            ▼ ▼                               ▼
┌─────────────────────┐       ┌──────────────────┐              ┌───────────────────┐
│    应用场景         │       │    开发体验      │              │    未来趋势       │
└────────┬────────────┘       └────────┬─────────┘              └─────────┬─────────┘
         │                             │                                  │
  ┌──────┴───────┐            ┌────────┴────────┐                ┌───────┴───────┐
  ▼              ▼            ▼                 ▼                ▼               ▼
┌────────┐    ┌───────┐   ┌────────┐      ┌──────────┐      ┌────────┐     ┌─────────┐
│计算密集│    │数据共享│   │工具链  │      │调试测试  │      │标准演进│     │生态扩展 │
└───┬────┘    └───┬───┘   └────┬───┘      └─────┬────┘      └───┬────┘     └────┬────┘
    │            │            │                │                │              │
┌───┴───┐     ┌──┴───┐    ┌───┴────┐       ┌───┴───┐        ┌───┴────┐     ┌────┴────┐
│数据处理│     │表单验证│  │构建工具│       │开发服务器│      │组件模型│     │跨平台化 │
│图形处理│     │业务规则│  │依赖管理│       │测试框架 │      │GC 支持 │     │企业采用 │
│科学计算│     │API类型 │  │IDE插件 │       │性能分析 │      │接口类型│     │专业领域 │
└───────┘     └──────┘    └────────┘       └───────┘        └────────┘     └─────────┘
```

在这个全面分析中，我们探讨了Rust与WebAssembly结合构建全栈应用的可行性。
我们从架构定义和技术组件分析出发，详细考察了前端框架选择、后端集成方案以及共享代码设计。
通过形式化方法和代码示例，我们证明了这种架构在类型安全性、性能优化和代码复用方面的优势。

实例分析表明，
Rust+WebAssembly架构特别适合计算密集型应用、需要端到端类型安全的系统和要求严格内存管理的场景。
尽管存在包体积、调试难度和生态系统成熟度等挑战，
但随着WebAssembly标准的演进（特别是组件模型和接口类型）以及工具链的不断改进，
这些问题正在得到缓解。

对于开发团队来说，采用渐进式实施路径是明智之选，从共享核心模型开始，逐步扩展到更完整的全栈功能。
综合考虑，
Rust+WebAssembly全栈架构对特定应用场景是可行的，并且随着技术的成熟，其适用范围将不断扩大。
