# GUI 开发 (Graphical User Interface)

**类别**: 领域特定 - GUI  
**重要程度**: ⭐⭐⭐⭐ (桌面应用必备)  
**更新日期**: 2025-10-20

---

## 📋 目录

- [GUI 开发 (Graphical User Interface)](#gui-开发-graphical-user-interface)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. egui (即时模式 GUI ⭐⭐⭐⭐⭐)](#1-egui-即时模式-gui-)
      - [核心特性](#核心特性)
      - [基础示例](#基础示例)
      - [有状态应用](#有状态应用)
    - [2. iced (Elm 架构 GUI ⭐⭐⭐⭐⭐)](#2-iced-elm-架构-gui-)
      - [核心特性2](#核心特性2)
      - [基础示例2](#基础示例2)
      - [表单应用](#表单应用)
    - [3. slint (声明式 UI ⭐⭐⭐⭐)](#3-slint-声明式-ui-)
      - [核心特性3](#核心特性3)
      - [基础示例3](#基础示例3)
    - [4. tauri (轻量级桌面应用 ⭐⭐⭐⭐⭐)](#4-tauri-轻量级桌面应用-)
      - [核心特性4](#核心特性4)
      - [基础示例4](#基础示例4)
  - [💡 最佳实践](#-最佳实践)
    - [1. 选择合适的框架](#1-选择合适的框架)
    - [2. 状态管理](#2-状态管理)
    - [3. 异步操作](#3-异步操作)
  - [📊 工具对比](#-工具对比)
  - [🎯 实战场景](#-实战场景)
    - [场景1: 系统监控工具 (egui)](#场景1-系统监控工具-egui)
    - [场景2: 待办事项应用 (iced)](#场景2-待办事项应用-iced)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

Rust 的 GUI 生态正在快速发展，提供多种现代化的 GUI 框架，从即时模式到声明式 UI，从纯 Rust 到 Web 技术。

---

## 🔧 核心工具

### 1. egui (即时模式 GUI ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add eframe egui`  
**用途**: 简单、快速的即时模式 GUI

#### 核心特性

- ✅ 即时模式 API（无状态）
- ✅ 跨平台（Windows, macOS, Linux, Web）
- ✅ 易于上手
- ✅ 自带主题

#### 基础示例

```rust
use eframe::egui;

fn main() -> Result<(), eframe::Error> {
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_inner_size([320.0, 240.0]),
        ..Default::default()
    };
    
    eframe::run_simple_native("My App", options, move |ctx, _frame| {
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("Hello, World!");
            
            if ui.button("Click me!").clicked() {
                println!("Button clicked!");
            }
            
            ui.separator();
            
            ui.label("Counter:");
            ui.add(egui::Slider::new(&mut 0, 0..=100));
        });
    })
}
```

#### 有状态应用

```rust
use eframe::egui;

struct MyApp {
    name: String,
    age: u32,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            name: "Alice".to_owned(),
            age: 25,
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("User Profile");
            
            ui.horizontal(|ui| {
                ui.label("Name:");
                ui.text_edit_singleline(&mut self.name);
            });
            
            ui.add(egui::Slider::new(&mut self.age, 0..=120).text("Age"));
            
            if ui.button("Save").clicked() {
                println!("Saving: {} ({})", self.name, self.age);
            }
        });
    }
}

fn main() -> Result<(), eframe::Error> {
    let options = eframe::NativeOptions::default();
    eframe::run_native(
        "My App",
        options,
        Box::new(|_cc| Box::<MyApp>::default()),
    )
}
```

---

### 2. iced (Elm 架构 GUI ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add iced`  
**用途**: 类型安全的声明式 GUI

#### 核心特性2

- ✅ Elm 架构（Model-Update-View）
- ✅ 类型安全的消息传递
- ✅ 响应式 UI
- ✅ 内置异步支持

#### 基础示例2

```rust
use iced::{executor, Application, Command, Element, Settings, Theme};
use iced::widget::{button, column, text, text_input};

#[derive(Default)]
struct Counter {
    value: i32,
}

#[derive(Debug, Clone)]
enum Message {
    Increment,
    Decrement,
}

impl Application for Counter {
    type Executor = executor::Default;
    type Message = Message;
    type Theme = Theme;
    type Flags = ();

    fn new(_flags: ()) -> (Self, Command<Message>) {
        (Self::default(), Command::none())
    }

    fn title(&self) -> String {
        String::from("Counter")
    }

    fn update(&mut self, message: Message) -> Command<Message> {
        match message {
            Message::Increment => self.value += 1,
            Message::Decrement => self.value -= 1,
        }
        Command::none()
    }

    fn view(&self) -> Element<Message> {
        column![
            button("Increment").on_press(Message::Increment),
            text(self.value).size(50),
            button("Decrement").on_press(Message::Decrement),
        ]
        .padding(20)
        .into()
    }
}

fn main() -> iced::Result {
    Counter::run(Settings::default())
}
```

#### 表单应用

```rust
use iced::widget::{column, text_input, button, text};
use iced::{Application, Command, Element};

struct Form {
    username: String,
    password: String,
}

#[derive(Debug, Clone)]
enum Message {
    UsernameChanged(String),
    PasswordChanged(String),
    Submit,
}

impl Application for Form {
    type Message = Message;
    
    fn update(&mut self, message: Message) -> Command<Message> {
        match message {
            Message::UsernameChanged(value) => {
                self.username = value;
            }
            Message::PasswordChanged(value) => {
                self.password = value;
            }
            Message::Submit => {
                println!("Login: {}", self.username);
            }
        }
        Command::none()
    }
    
    fn view(&self) -> Element<Message> {
        column![
            text("Username:"),
            text_input("Enter username", &self.username)
                .on_input(Message::UsernameChanged),
            
            text("Password:"),
            text_input("Enter password", &self.password)
                .on_input(Message::PasswordChanged)
                .password(),
            
            button("Login").on_press(Message::Submit),
        ]
        .padding(20)
        .into()
    }
}
```

---

### 3. slint (声明式 UI ⭐⭐⭐⭐)

**添加依赖**: `cargo add slint`  
**用途**: 现代声明式 UI 框架

#### 核心特性3

- ✅ 声明式标记语言
- ✅ 设计工具集成
- ✅ 高性能渲染
- ✅ 跨平台

#### 基础示例3

**ui/appwindow.slint**:

```slint
import { Button, VerticalBox } from "std-widgets.slint";

export component AppWindow inherits Window {
    in-out property <int> counter: 0;
    
    VerticalBox {
        Text {
            text: "Counter: \{counter}";
            font-size: 20px;
        }
        
        Button {
            text: "Increment";
            clicked => {
                counter += 1;
            }
        }
    }
}
```

**main.rs**:

```rust
slint::include_modules!();

fn main() {
    let app = AppWindow::new().unwrap();
    
    app.on_increment(|| {
        println!("Button clicked!");
    });
    
    app.run().unwrap();
}
```

---

### 4. tauri (轻量级桌面应用 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add tauri`  
**用途**: 使用 Web 技术构建桌面应用

#### 核心特性4

- ✅ 小体积（< 1MB）
- ✅ 使用 HTML/CSS/JS
- ✅ Rust 后端
- ✅ 跨平台

#### 基础示例4

**src-tauri/src/main.rs**:

```rust
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

#[tauri::command]
fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

fn main() {
    tauri::Builder::default()
        .invoke_handler(tauri::generate_handler![greet])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

**src/App.jsx**:

```jsx
import { invoke } from '@tauri-apps/api/tauri'
import { useState } from 'react'

function App() {
  const [name, setName] = useState('')
  const [greetMsg, setGreetMsg] = useState('')

  async function greet() {
    setGreetMsg(await invoke('greet', { name }))
  }

  return (
    <div>
      <input
        value={name}
        onChange={(e) => setName(e.target.value)}
        placeholder="Enter a name..."
      />
      <button onClick={greet}>Greet</button>
      <p>{greetMsg}</p>
    </div>
  )
}

export default App
```

---

## 💡 最佳实践

### 1. 选择合适的框架

```text
需求是什么？
├─ 快速原型 → egui
├─ 类型安全 → iced
├─ 设计师协作 → slint
└─ Web 技术栈 → tauri
```

### 2. 状态管理

```rust
// egui: 直接修改状态
struct State {
    counter: i32,
}

// iced: 消息驱动
enum Message {
    Increment,
}

fn update(state: &mut State, msg: Message) {
    match msg {
        Message::Increment => state.counter += 1,
    }
}
```

### 3. 异步操作

```rust
use iced::{Command, Subscription};

impl Application for MyApp {
    fn update(&mut self, message: Message) -> Command<Message> {
        match message {
            Message::FetchData => {
                Command::perform(
                    async { fetch_data().await },
                    Message::DataFetched
                )
            }
            _ => Command::none()
        }
    }
}
```

---

## 📊 工具对比

| 工具 | 范式 | 性能 | 易用性 | 生态 | 推荐场景 |
|------|------|------|--------|------|---------|
| **egui** | 即时模式 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 工具、原型 |
| **iced** | Elm 架构 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | 应用程序 |
| **slint** | 声明式 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | 商业应用 |
| **tauri** | Web 混合 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 桌面应用 |

---

## 🎯 实战场景

### 场景1: 系统监控工具 (egui)

```rust
use eframe::egui;
use sysinfo::{System, SystemExt};

struct Monitor {
    sys: System,
}

impl eframe::App for Monitor {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        self.sys.refresh_all();
        
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("System Monitor");
            
            ui.label(format!("CPU: {:.1}%", self.sys.global_cpu_info().cpu_usage()));
            ui.label(format!("Memory: {} MB", self.sys.used_memory() / 1024 / 1024));
            
            // 自动刷新
            ctx.request_repaint();
        });
    }
}
```

### 场景2: 待办事项应用 (iced)

```rust
use iced::widget::{column, row, checkbox, text_input, button};

struct TodoList {
    tasks: Vec<Task>,
    input: String,
}

struct Task {
    description: String,
    completed: bool,
}

#[derive(Debug, Clone)]
enum Message {
    InputChanged(String),
    AddTask,
    ToggleTask(usize),
}
```

---

## 🔗 相关资源

- [egui Documentation](https://docs.rs/egui/)
- [iced Documentation](https://docs.rs/iced/)
- [slint Documentation](https://slint.dev/)
- [tauri Documentation](https://tauri.app/)
- [Are We GUI Yet?](https://www.areweguiyet.com/)

---

**导航**: [返回领域特定](../README.md) | [下一领域：游戏开发](../game/README.md)
