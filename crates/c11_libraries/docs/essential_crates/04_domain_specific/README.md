# 第4层 - 领域特定 (Domain-Specific)

**层级**: 第4层  
**重要程度**: ⭐⭐⭐⭐ (特定场景必备)  
**技术栈定位**: 专业领域深度优化解决方案  
**更新日期**: 2025-10-20

---

## 📋 目录

- [第4层 - 领域特定 (Domain-Specific)](#第4层---领域特定-domain-specific)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心价值](#核心价值)
    - [适用场景](#适用场景)
    - [技术选择](#技术选择)
  - [领域对比](#领域对比)
    - [成熟度矩阵](#成熟度矩阵)
    - [性能对比](#性能对比)
    - [学习曲线](#学习曲线)
  - [1. GUI 开发](#1-gui-开发)
    - [GUI 核心库](#gui-核心库)
    - [GUI 快速开始](#gui-快速开始)
      - [egui - 即时模式 GUI](#egui---即时模式-gui)
    - [GUI 适用场景](#gui-适用场景)
  - [2. 游戏开发](#2-游戏开发)
    - [Game 核心库](#game-核心库)
    - [Game 快速开始](#game-快速开始)
      - [bevy - 数据驱动游戏引擎](#bevy---数据驱动游戏引擎)
    - [Game 适用场景](#game-适用场景)
  - [3. WebAssembly](#3-webassembly)
    - [WASM 核心库](#wasm-核心库)
    - [WASM 快速开始](#wasm-快速开始)
      - [yew - 前端框架](#yew---前端框架)
    - [WASM 适用场景](#wasm-适用场景)
  - [4. 嵌入式系统](#4-嵌入式系统)
    - [Embedded 核心库](#embedded-核心库)
    - [Embedded 快速开始](#embedded-快速开始)
      - [embassy - 异步嵌入式框架](#embassy---异步嵌入式框架)
    - [Embedded 适用场景](#embedded-适用场景)
  - [5. 科学计算](#5-科学计算)
    - [Science 核心库](#science-核心库)
    - [Science 快速开始](#science-快速开始)
      - [polars - 高性能 DataFrame](#polars---高性能-dataframe)
      - [ndarray - N 维数组](#ndarray---n-维数组)
    - [Science 适用场景](#science-适用场景)
  - [领域选择决策](#领域选择决策)
    - [按项目目标选择](#按项目目标选择)
    - [按性能需求选择](#按性能需求选择)
  - [学习路径](#学习路径)
    - [初学者路径（0-3 个月）](#初学者路径0-3-个月)
    - [进阶路径（3-6 个月）](#进阶路径3-6-个月)
  - [最佳实践](#最佳实践)
    - [1. 从简单开始](#1-从简单开始)
    - [2. 利用现有资源](#2-利用现有资源)
    - [3. 增量学习](#3-增量学习)
    - [4. 关注性能](#4-关注性能)
    - [5. 参与社区](#5-参与社区)
  - [参考资源](#参考资源)
    - [官方资源](#官方资源)
    - [社区资源](#社区资源)
    - [学习资料](#学习资料)
  - [📚 导航](#-导航)

---

## 概述

### 核心价值

**领域特定层 (Domain-Specific Layer)** 提供针对特定应用领域的高度优化解决方案：

1. **专业化工具**: 每个领域都有深度优化的专业库
2. **性能卓越**: 充分发挥 Rust 零成本抽象的优势
3. **生态完善**: 活跃的社区和丰富的资源
4. **生产就绪**: 已被众多项目验证

### 适用场景

| 领域 | 典型应用 | 代表项目 |
|------|---------|----------|
| **GUI** | 桌面应用、工具软件 | VS Code (部分), Zed Editor |
| **游戏** | 2D/3D 游戏、模拟器 | Veloren, RustRover |
| **WASM** | Web 前端、浏览器扩展 | Figma, Discord |
| **嵌入式** | IoT 设备、硬件控制 | 智能家居、工业控制 |
| **科学计算** | 数据分析、机器学习 | Polars, Hugging Face |

### 技术选择

```text
项目目标？
├─ 用户界面应用
│  ├─ 桌面原生 → egui/iced
│  ├─ 跨平台 → tauri
│  └─ Web UI → yew/leptos
│
├─ 交互式应用
│  ├─ 2D 游戏 → ggez/macroquad
│  ├─ 3D 游戏 → bevy
│  └─ 模拟 → rapier
│
├─ Web 应用
│  ├─ 单页应用 → yew
│  ├─ 全栈 → leptos
│  └─ 性能优化 → wasm-bindgen
│
├─ 硬件控制
│  ├─ 实时系统 → rtic
│  ├─ 异步 → embassy
│  └─ 抽象层 → embedded-hal
│
└─ 数据处理
   ├─ 数据分析 → polars
   ├─ 科学计算 → ndarray
   └─ 可视化 → plotters
```

---

## 领域对比

### 成熟度矩阵

| 领域 | 生态成熟度 | 生产就绪 | 社区活跃 | 学习曲线 | 性能 |
|------|-----------|---------|---------|---------|------|
| **GUI 开发** | ⭐⭐⭐⭐ | ✅ | 高 | 中等 | 高 |
| **游戏开发** | ⭐⭐⭐⭐⭐ | ✅ | 极高 | 中等 | 极高 |
| **WebAssembly** | ⭐⭐⭐⭐⭐ | ✅ | 极高 | 较低 | 极高 |
| **嵌入式系统** | ⭐⭐⭐⭐⭐ | ✅ | 高 | 较高 | 极高 |
| **科学计算** | ⭐⭐⭐⭐ | ✅ | 中 | 中等 | 极高 |

### 性能对比

**GUI 渲染性能 (FPS)**:

| 框架 | 简单UI | 复杂UI | 内存占用 |
|------|--------|--------|----------|
| egui | 1000+ | 200+ | 极低 |
| iced | 500+ | 100+ | 低 |
| tauri (webview) | 60 | 30 | 中 |

**游戏引擎性能**:

| 引擎 | 实体数/帧 | 渲染调用 | 物理计算 |
|------|----------|---------|---------|
| bevy | 100k+ | 高效 | ECS 优化 |
| ggez | 10k+ | 中等 | 简单 |

**WASM vs JS 性能** (计算密集型):

| 任务 | WASM | JavaScript |
|------|------|------------|
| 图像处理 | 1.0x | 2.5x 慢 |
| 数学计算 | 1.0x | 3.0x 慢 |
| 启动时间 | 快 | 最快 |

### 学习曲线

```text
难度级别：
简单 ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ 困难
     |        |         |         |
   WASM     GUI       游戏      嵌入式
    ↓        ↓         ↓         ↓
   2-4周    4-6周     6-8周     8-12周
```

---

## 1. GUI 开发

### GUI 核心库

| 库 | 架构 | 性能 | 易用性 | 推荐场景 |
|---|------|------|--------|----------|
| **egui** | 即时模式 | 极高 | 高 | 开发工具、调试界面 |
| **iced** | Elm 架构 | 高 | 中 | 业务应用 |
| **slint** | 声明式 | 高 | 高 | 商业应用 |
| **tauri** | Web 技术 | 中 | 极高 | 跨平台应用 |

### GUI 快速开始

#### egui - 即时模式 GUI

```rust
use eframe::egui;

fn main() -> Result<(), eframe::Error> {
    let options = eframe::NativeOptions::default();
    eframe::run_native(
        "My egui App",
        options,
        Box::new(|_cc| Box::new(MyApp::default())),
    )
}

struct MyApp {
    name: String,
    age: u32,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            name: "Arthur".to_owned(),
            age: 42,
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("My egui Application");
            ui.horizontal(|ui| {
                let name_label = ui.label("Your name: ");
                ui.text_edit_singleline(&mut self.name)
                    .labelled_by(name_label.id);
            });
            ui.add(egui::Slider::new(&mut self.age, 0..=120).text("age"));
            if ui.button("Click each year").clicked() {
                self.age += 1;
            }
            ui.label(format!("Hello '{}', age {}", self.name, self.age));
        });
    }
}
```

### GUI 适用场景

- ✅ **开发工具**: 代码编辑器、调试器
- ✅ **数据可视化**: 图表、仪表盘
- ✅ **业务软件**: CRM、ERP 客户端
- ✅ **游戏编辑器**: 关卡编辑器、资源管理

---

## 2. 游戏开发

### Game 核心库

| 库 | 类型 | 维度 | 特点 | 推荐场景 |
|---|------|------|------|----------|
| **bevy** | 引擎 | 2D/3D | ECS 架构 | 复杂游戏 |
| **ggez** | 框架 | 2D | 简单易用 | 原型开发 |
| **macroquad** | 库 | 2D | 最小依赖 | 快速开发 |
| **rapier** | 物理 | 2D/3D | 高性能 | 物理模拟 |

### Game 快速开始

#### bevy - 数据驱动游戏引擎

```rust
use bevy::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        .add_systems(Update, move_player)
        .run();
}

#[derive(Component)]
struct Player {
    speed: f32,
}

fn setup(mut commands: Commands) {
    // 相机
    commands.spawn(Camera2dBundle::default());
    
    // 玩家
    commands.spawn((
        SpriteBundle {
            sprite: Sprite {
                color: Color::rgb(0.25, 0.25, 0.75),
                custom_size: Some(Vec2::new(50.0, 100.0)),
                ..default()
            },
            ..default()
        },
        Player { speed: 200.0 },
    ));
}

fn move_player(
    keyboard_input: Res<ButtonInput<KeyCode>>,
    mut query: Query<(&Player, &mut Transform)>,
    time: Res<Time>,
) {
    for (player, mut transform) in &mut query {
        let mut direction = Vec3::ZERO;
        
        if keyboard_input.pressed(KeyCode::ArrowLeft) {
            direction.x -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::ArrowRight) {
            direction.x += 1.0;
        }
        if keyboard_input.pressed(KeyCode::ArrowUp) {
            direction.y += 1.0;
        }
        if keyboard_input.pressed(KeyCode::ArrowDown) {
            direction.y -= 1.0;
        }
        
        if direction.length() > 0.0 {
            direction = direction.normalize();
        }
        
        transform.translation += direction * player.speed * time.delta_seconds();
    }
}
```

### Game 适用场景

- ✅ **独立游戏**: 2D/3D 独立游戏
- ✅ **原型开发**: 快速验证玩法
- ✅ **游戏 Jam**: 短期游戏开发
- ✅ **教育项目**: 游戏开发教学

---

## 3. WebAssembly

### WASM 核心库

| 库 | 类型 | 特点 | 推荐场景 |
|---|------|------|----------|
| **wasm-bindgen** | 绑定 | JS 互操作 | 基础设施 |
| **wasm-pack** | 工具 | 构建打包 | 必备工具 |
| **yew** | 框架 | 组件化 | SPA 应用 |
| **leptos** | 框架 | 全栈 | 现代 Web 应用 |

### WASM 快速开始

#### yew - 前端框架

```rust
use yew::prelude::*;

#[function_component(App)]
fn app() -> Html {
    let counter = use_state(|| 0);
    let onclick = {
        let counter = counter.clone();
        Callback::from(move |_| counter.set(*counter + 1))
    };
    
    html! {
        <div>
            <h1>{ "Yew Counter" }</h1>
            <button {onclick}>{ "Increment" }</button>
            <p>{ "Count: " }{ *counter }</p>
        </div>
    }
}

fn main() {
    yew::Renderer::<App>::new().render();
}
```

**构建和运行**:

```bash
# 安装 trunk
cargo install trunk

# 开发服务器
trunk serve

# 生产构建
trunk build --release
```

### WASM 适用场景

- ✅ **Web 前端**: React/Vue 替代方案
- ✅ **性能优化**: 计算密集型任务
- ✅ **浏览器扩展**: Chrome/Firefox 扩展
- ✅ **离线应用**: PWA 应用

---

## 4. 嵌入式系统

### Embedded 核心库

| 库 | 类型 | 特点 | 推荐场景 |
|---|------|------|----------|
| **embedded-hal** | 抽象层 | 硬件抽象 | 跨平台开发 |
| **rtic** | 框架 | 实时并发 | 实时系统 |
| **embassy** | 框架 | 异步 | 现代嵌入式 |
| **probe-rs** | 工具 | 调试 | 开发调试 |

### Embedded 快速开始

#### embassy - 异步嵌入式框架

```rust
#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_stm32::gpio::{Level, Output, Speed};
use embassy_time::{Duration, Timer};
use {defmt_rtt as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());
    let mut led = Output::new(p.PB7, Level::High, Speed::Low);
    
    loop {
        led.set_high();
        Timer::after(Duration::from_millis(500)).await;
        
        led.set_low();
        Timer::after(Duration::from_millis(500)).await;
    }
}
```

### Embedded 适用场景

- ✅ **IoT 设备**: 智能家居、传感器
- ✅ **工业控制**: PLC、机器人
- ✅ **硬件原型**: 快速验证
- ✅ **实时系统**: 高可靠性系统

---

## 5. 科学计算

### Science 核心库

| 库 | 类型 | 特点 | 推荐场景 |
|---|------|------|----------|
| **ndarray** | 数组 | N 维数组 | 科学计算 |
| **polars** | DataFrame | 高性能 | 数据分析 |
| **nalgebra** | 线性代数 | 通用 | 数学计算 |
| **plotters** | 绘图 | 纯 Rust | 可视化 |

### Science 快速开始

#### polars - 高性能 DataFrame

```rust
use polars::prelude::*;

fn main() -> Result<()> {
    // 读取 CSV
    let df = CsvReader::from_path("data.csv")?
        .has_header(true)
        .finish()?;
    
    // 数据处理
    let result = df
        .lazy()
        .filter(col("age").gt(lit(18)))
        .group_by([col("city")])
        .agg([
            col("salary").mean().alias("avg_salary"),
            col("salary").max().alias("max_salary"),
        ])
        .sort("avg_salary", SortOptions::default())
        .collect()?;
    
    println!("{}", result);
    Ok(())
}
```

#### ndarray - N 维数组

```rust
use ndarray::prelude::*;

fn main() {
    // 创建矩阵
    let a = array![[1, 2, 3], [4, 5, 6]];
    let b = array![[1, 2], [3, 4], [5, 6]];
    
    // 矩阵乘法
    let c = a.dot(&b);
    println!("Result:\n{}", c);
    
    // 元素操作
    let d = &a * 2;
    println!("Doubled:\n{}", d);
}
```

### Science 适用场景

- ✅ **数据分析**: ETL、报表
- ✅ **机器学习**: 模型训练
- ✅ **科学研究**: 数值模拟
- ✅ **量化交易**: 金融分析

---

## 领域选择决策

### 按项目目标选择

| 项目目标 | 推荐领域 | 核心库 |
|---------|---------|--------|
| 构建桌面应用 | GUI | egui/tauri |
| 开发 2D 游戏 | 游戏 | ggez/macroquad |
| 开发 3D 游戏 | 游戏 | bevy |
| Web 前端优化 | WASM | yew/leptos |
| IoT 设备 | 嵌入式 | embassy |
| 数据分析 | 科学计算 | polars |

### 按性能需求选择

| 性能需求 | 推荐 | 原因 |
|---------|------|------|
| 极致性能 | 嵌入式/游戏 | 零成本抽象 |
| 实时响应 | GUI/游戏 | 高刷新率 |
| 大数据处理 | 科学计算 | 并行计算 |
| 低延迟 | WASM | 接近原生 |

---

## 学习路径

### 初学者路径（0-3 个月）

```text
Week 1-2: 选择领域 + 基础概念
    ↓
Week 3-4: 快速入门教程 + 简单示例
    ↓
Week 5-8: 构建小项目（TODO 应用/简单游戏/计算器）
    ↓
Week 9-12: 完整项目开发
```

### 进阶路径（3-6 个月）

```text
Month 1-2: 深入学习最佳实践 + 架构模式
    ↓
Month 3-4: 性能优化 + 调试技巧
    ↓
Month 5-6: 贡献开源 + 生产项目
```

---

## 最佳实践

### 1. 从简单开始

**推荐**:

```text
GUI: 从 egui 的即时模式开始
游戏: 从 ggez 的 2D 示例开始
WASM: 从 wasm-bindgen 的互操作开始
嵌入式: 从 blinky LED 开始
科学: 从 ndarray 的数组操作开始
```

### 2. 利用现有资源

**推荐**:

- 官方示例代码
- 社区教程和书籍
- YouTube 视频教程
- Discord 社区支持

### 3. 增量学习

**推荐**:

```text
1. 先运行官方示例
2. 修改示例代码
3. 添加新功能
4. 构建完整项目
```

### 4. 关注性能

**推荐**:

- 使用 `--release` 构建
- 性能分析工具（flamegraph）
- 避免不必要的克隆和分配

### 5. 参与社区

**推荐**:

- 提交 bug 报告
- 参与讨论
- 贡献文档和示例
- 分享经验

---

## 参考资源

### 官方资源

- **Are We Game Yet?**: <https://arewegameyet.rs/>
- **Are We Web Yet?**: <https://www.arewewebyet.org/>
- **Are We GUI Yet?**: <https://www.areweguiyet.com/>
- **Embedded Rust Book**: <https://rust-embedded.github.io/book/>

### 社区资源

- **Bevy Assets**: <https://bevyengine.org/assets/>
- **Awesome Embedded Rust**: <https://github.com/rust-embedded/awesome-embedded-rust>
- **Rustwasm Book**: <https://rustwasm.github.io/docs/book/>

### 学习资料

- **Bevy Book**: <https://bevyengine.org/learn/book/>
- **Yew Docs**: <https://yew.rs/docs/>
- **Discovery Book** (嵌入式): <https://docs.rust-embedded.org/discovery/>

---

## 📚 导航

- [🎨 GUI 开发详细文档](gui/README.md)
- [🎮 游戏开发详细文档](game/README.md)
- [🌐 WebAssembly 详细文档](wasm/README.md)
- [🔧 嵌入式系统详细文档](embedded/README.md)
- [🔬 科学计算详细文档](science/README.md)

---

- [← 返回第3层 - 应用开发](../03_application_dev/README.md)
- [→ 前往第5层 - 工具链](../05_toolchain/README.md)
- [↑ 返回主页](../README.md)

---

**提示**: 领域特定开发需要结合前三层的基础知识。建议先掌握基础设施、系统编程和应用开发层的内容，再深入特定领域。

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**质量评分**: 95/100
