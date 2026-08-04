# 🦀 Rust项目模板集合


## 📊 目录

- [📋 模板概览](#模板概览)
- [📚 基础库模板](#基础库模板)
  - [模板描述](#模板描述)
  - [项目结构](#项目结构)
  - [主要特性](#主要特性)
  - [使用示例](#使用示例)
  - [依赖配置](#依赖配置)
- [🌐 Web应用模板](#web应用模板)
  - [模板描述1](#模板描述1)
  - [项目结构1](#项目结构1)
  - [主要特性1](#主要特性1)
  - [使用示例1](#使用示例1)
  - [依赖配置1](#依赖配置1)
- [💻 CLI应用模板](#cli应用模板)
  - [模板描述6](#模板描述6)
  - [项目结构6](#项目结构6)
  - [主要特性2](#主要特性2)
  - [使用示例2](#使用示例2)
  - [依赖配置2](#依赖配置2)
- [🖥️ 桌面应用模板](#️-桌面应用模板)
  - [模板描述5](#模板描述5)
  - [项目结构5](#项目结构5)
  - [主要特性3](#主要特性3)
  - [使用示例 (Tauri)](#使用示例-tauri)
  - [依赖配置3](#依赖配置3)
- [🎮 游戏开发模板](#游戏开发模板)
  - [模板描述4](#模板描述4)
  - [项目结构4](#项目结构4)
  - [主要特性4](#主要特性4)
  - [使用示例 (Bevy)](#使用示例-bevy)
  - [依赖配置4](#依赖配置4)
- [🔧 系统编程模板](#系统编程模板)
  - [模板描述51](#模板描述51)
  - [项目结构51](#项目结构51)
  - [主要特性5](#主要特性5)
  - [使用示例5](#使用示例5)
  - [依赖配置5](#依赖配置5)
- [⛓️ 区块链模板](#️-区块链模板)
  - [模板描述61](#模板描述61)
  - [项目结构61](#项目结构61)
  - [主要特性6](#主要特性6)
  - [使用示例6](#使用示例6)
  - [依赖配置6](#依赖配置6)
- [🤖 机器学习模板](#机器学习模板)
  - [模板描述7](#模板描述7)
  - [项目结构7](#项目结构7)
  - [主要特性7](#主要特性7)
  - [使用示例7](#使用示例7)
  - [依赖配置7](#依赖配置7)
- [🚀 模板使用指南](#模板使用指南)
  - [模板选择](#模板选择)
  - [模板定制](#模板定制)
  - [最佳实践](#最佳实践)
- [📞 模板支持](#模板支持)
  - [社区支持](#社区支持)
  - [贡献指南](#贡献指南)
  - [模板更新](#模板更新)


**创建时间**: 2025年9月25日
**版本**: 1.0.0
**适用对象**: 所有Rust开发者

---

- [🦀 Rust项目模板集合](#️-区块链模板)

## 📋 模板概览

| 模板类型 | 难度 | 适用场景 | 主要技术栈 |
|----------|------|----------|------------|
| [基础库](#-基础库模板) | 初级 | 工具库、算法库 | 标准库、serde、anyhow |
| [Web应用](#-web应用模板) | 中级 | API服务、Web应用 | axum、tokio、sqlx |
| [CLI应用](#-cli应用模板) | 中级 | 命令行工具 | clap、tokio、serde |
| [桌面应用](#️-桌面应用模板) | 中级 | GUI应用 | tauri、egui、iced |
| [游戏开发](#-游戏开发模板) | 中级 | 游戏开发 | bevy、ggez、macroquad |
| [系统编程](#-系统编程模板) | 高级 | 操作系统、驱动程序 | no_std、嵌入式 |
| [区块链](#️-区块链模板) | 高级 | 区块链应用 | substrate、near |
| [机器学习](#-机器学习模板) | 高级 | ML/AI应用 | candle、tch、ort |

---

## 📚 基础库模板

### 模板描述

适用于创建Rust库项目，包含完整的项目结构、配置文件和示例代码。

### 项目结构

```text
basic-library/
├── Cargo.toml
├── README.md
├── LICENSE
├── .gitignore
├── .editorconfig
├── rustfmt.toml
├── clippy.toml
├── src/
│   ├── lib.rs
│   ├── error.rs
│   ├── types.rs
│   └── utils.rs
├── tests/
│   ├── common.rs
│   └── integration_tests.rs
├── examples/
│   └── basic_usage.rs
├── benches/
│   └── benchmark.rs
└── docs/
    └── api.md
```

### 主要特性

- **完整的项目结构**: 标准的Rust库项目布局
- **错误处理**: 使用thiserror进行错误定义
- **配置管理**: 灵活的配置系统
- **测试覆盖**: 单元测试、集成测试、基准测试
- **文档生成**: 自动生成API文档
- **代码质量**: rustfmt和clippy配置

### 使用示例

```rust
use my_library::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = Config::default();
    let processor = DataProcessor::new(config);

    let result = processor.process("example data")?;
    println!("Result: {}", result);

    Ok(())
}
```

### 依赖配置

```toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
thiserror = "1.0"
log = "0.4"

[dev-dependencies]
tokio-test = "0.4"
tempfile = "3.0"
criterion = "0.5"
proptest = "1.0"
mockall = "0.12"
rstest = "0.18"
```

---

## 🌐 Web应用模板

### 模板描述1

适用于创建Web API服务和Web应用，包含完整的Web框架配置、数据库集成和中间件。

### 项目结构1

```text
web-app/
├── Cargo.toml
├── README.md
├── LICENSE
├── .gitignore
├── .env.example
├── docker-compose.yml
├── Dockerfile
├── src/
│   ├── main.rs
│   ├── config.rs
│   ├── database.rs
│   ├── models/
│   │   ├── mod.rs
│   │   └── user.rs
│   ├── handlers/
│   │   ├── mod.rs
│   │   ├── auth.rs
│   │   └── users.rs
│   ├── middleware/
│   │   ├── mod.rs
│   │   ├── auth.rs
│   │   └── cors.rs
│   └── utils/
│       ├── mod.rs
│       └── jwt.rs
├── migrations/
│   └── 001_create_users.sql
├── tests/
│   ├── common.rs
│   └── integration_tests.rs
└── docs/
    └── api.md
```

### 主要特性1

- **Web框架**: 使用axum构建RESTful API
- **数据库集成**: 支持PostgreSQL、MySQL、SQLite
- **认证系统**: JWT认证和授权
- **中间件**: CORS、日志、错误处理
- **配置管理**: 环境变量和配置文件
- **Docker支持**: 容器化部署
- **API文档**: 自动生成OpenAPI文档

### 使用示例1

```rust
use axum::{
    extract::State,
    response::Json,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct User {
    id: u32,
    name: String,
    email: String,
}

async fn get_users(State(state): State<AppState>) -> Json<Vec<User>> {
    // 从数据库获取用户列表
    Json(vec![])
}

async fn create_user(Json(payload): Json<CreateUserRequest>) -> Json<User> {
    // 创建新用户
    Json(User {
        id: 1,
        name: payload.name,
        email: payload.email,
    })
}

fn create_app() -> Router {
    Router::new()
        .route("/users", get(get_users).post(create_user))
        .route("/health", get(health_check))
}
```

### 依赖配置1

```toml
[dependencies]
axum = { version = "0.7", features = ["macros", "tracing"] }
tokio = { version = "1.0", features = ["full"] }
tower = "0.4"
tower-http = { version = "0.5", features = ["cors", "trace"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
sqlx = { version = "0.7", features = ["runtime-tokio-rustls", "postgres", "chrono", "uuid"] }
jsonwebtoken = "9.0"
argon2 = "0.5"
anyhow = "1.0"
thiserror = "1.0"
uuid = { version = "1.0", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
validator = { version = "0.16", features = ["derive"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
config = "0.14"
dotenvy = "0.15"
reqwest = { version = "0.11", features = ["json"] }
```

---

## 💻 CLI应用模板

### 模板描述6

适用于创建命令行工具和CLI应用，包含完整的命令行解析、配置管理和用户交互。

### 项目结构6

```text
cli-app/
├── Cargo.toml
├── README.md
├── LICENSE
├── .gitignore
├── .editorconfig
├── rustfmt.toml
├── clippy.toml
├── src/
│   ├── main.rs
│   ├── config.rs
│   ├── commands/
│   │   ├── mod.rs
│   │   ├── process.rs
│   │   └── report.rs
│   ├── utils/
│   │   ├── mod.rs
│   │   ├── file.rs
│   │   └── format.rs
│   └── types/
│       ├── mod.rs
│       └── data.rs
├── tests/
│   ├── common.rs
│   └── integration_tests.rs
├── examples/
│   └── usage.rs
└── docs/
    └── cli.md
```

### 主要特性2

- **命令行解析**: 使用clap进行命令行参数解析
- **子命令支持**: 支持多个子命令和选项
- **配置管理**: 配置文件和环境变量支持
- **进度显示**: 进度条和状态显示
- **彩色输出**: 彩色终端输出
- **日志系统**: 完整的日志记录
- **错误处理**: 用户友好的错误信息

### 使用示例2

```rust
use clap::{Parser, Subcommand};
use colored::*;

#[derive(Parser)]
#[command(name = "my-cli")]
#[command(about = "A command-line tool")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Process {
        input: String,
        output: Option<String>,
    },
    Report {
        format: String,
    },
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Process { input, output } => {
            println!("{}", "Processing...".green().bold());
            // 处理逻辑
        }
        Commands::Report { format } => {
            println!("{}", "Generating report...".blue().bold());
            // 报告生成逻辑
        }
    }

    Ok(())
}
```

### 依赖配置2

```toml
[dependencies]
clap = { version = "4.0", features = ["derive", "env"] }
tokio = { version = "1.0", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
serde_yaml = "0.9"
anyhow = "1.0"
thiserror = "1.0"
uuid = { version = "1.0", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
regex = "1.0"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
config = "0.14"
dotenvy = "0.15"
walkdir = "2.0"
glob = "0.3"
reqwest = { version = "0.11", features = ["json"] }
indicatif = "0.17"
colored = "2.0"
```

---

## 🖥️ 桌面应用模板

### 模板描述5

适用于创建桌面GUI应用，支持多种GUI框架和跨平台部署。

### 项目结构5

```text
desktop-app/
├── Cargo.toml
├── README.md
├── LICENSE
├── .gitignore
├── src/
│   ├── main.rs
│   ├── app.rs
│   ├── ui/
│   │   ├── mod.rs
│   │   ├── main_window.rs
│   │   └── components/
│   ├── models/
│   │   ├── mod.rs
│   │   └── data.rs
│   └── utils/
│       ├── mod.rs
│       └── helpers.rs
├── assets/
│   ├── icons/
│   └── images/
├── tests/
│   └── integration_tests.rs
└── docs/
    └── gui.md
```

### 主要特性3

- **GUI框架**: 支持Tauri、egui、iced等
- **跨平台**: Windows、macOS、Linux支持
- **资源管理**: 图标、图片等资源管理
- **状态管理**: 应用状态和UI状态管理
- **事件处理**: 用户交互和事件处理
- **主题支持**: 深色/浅色主题切换

### 使用示例 (Tauri)

```rust
use tauri::State;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct AppData {
    count: i32,
}

#[tauri::command]
fn increment_count(state: State<'_, AppData>) -> Result<i32, String> {
    let mut data = state.inner().lock().unwrap();
    data.count += 1;
    Ok(data.count)
}

fn main() {
    tauri::Builder::default()
        .manage(AppData { count: 0 })
        .invoke_handler(tauri::generate_handler![increment_count])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### 依赖配置3

```toml
[dependencies]
tauri = { version = "1.0", features = ["api-all"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
thiserror = "1.0"
tokio = { version = "1.0", features = ["full"] }
```

---

## 🎮 游戏开发模板

### 模板描述4

适用于创建2D/3D游戏，支持多种游戏引擎和图形库。

### 项目结构4

```text
game/
├── Cargo.toml
├── README.md
├── LICENSE
├── .gitignore
├── src/
│   ├── main.rs
│   ├── game.rs
│   ├── systems/
│   │   ├── mod.rs
│   │   ├── movement.rs
│   │   └── rendering.rs
│   ├── components/
│   │   ├── mod.rs
│   │   ├── player.rs
│   │   └── enemy.rs
│   ├── resources/
│   │   ├── mod.rs
│   │   └── assets.rs
│   └── utils/
│       ├── mod.rs
│       └── math.rs
├── assets/
│   ├── sprites/
│   ├── sounds/
│   └── fonts/
├── tests/
│   └── integration_tests.rs
└── docs/
    └── game.md
```

### 主要特性4

- **游戏引擎**: 支持Bevy、ggez、macroquad等
- **ECS架构**: 实体-组件-系统架构
- **资源管理**: 纹理、音频、字体管理
- **物理引擎**: 碰撞检测和物理模拟
- **输入处理**: 键盘、鼠标、手柄输入
- **音频系统**: 音效和背景音乐

### 使用示例 (Bevy)

```rust
use bevy::prelude::*;

#[derive(Component)]
struct Player;

#[derive(Component)]
struct Velocity(Vec2);

fn setup(mut commands: Commands) {
    commands.spawn((
        Player,
        Velocity(Vec2::new(0.0, 0.0)),
        Transform::from_xyz(0.0, 0.0, 0.0),
    ));
}

fn player_movement(
    keyboard_input: Res<Input<KeyCode>>,
    mut query: Query<&mut Velocity, With<Player>>,
) {
    for mut velocity in query.iter_mut() {
        if keyboard_input.pressed(KeyCode::Left) {
            velocity.0.x -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::Right) {
            velocity.0.x += 1.0;
        }
    }
}

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        .add_systems(Update, player_movement)
        .run();
}
```

### 依赖配置4

```toml
[dependencies]
bevy = { version = "0.12", features = ["default"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
thiserror = "1.0"
```

---

## 🔧 系统编程模板

### 模板描述51

适用于创建操作系统、驱动程序、嵌入式系统等底层系统软件。

### 项目结构51

```text
system-program/
├── Cargo.toml
├── README.md
├── LICENSE
├── .gitignore
├── src/
│   ├── main.rs
│   ├── kernel/
│   │   ├── mod.rs
│   │   ├── memory.rs
│   │   └── scheduler.rs
│   ├── drivers/
│   │   ├── mod.rs
│   │   ├── keyboard.rs
│   │   └── display.rs
│   ├── arch/
│   │   ├── mod.rs
│   │   ├── x86_64.rs
│   │   └── arm.rs
│   └── utils/
│       ├── mod.rs
│       └── asm.rs
├── tests/
│   └── integration_tests.rs
└── docs/
    └── system.md
```

### 主要特性5

- **no_std支持**: 无标准库环境
- **内存管理**: 手动内存分配和管理
- **中断处理**: 硬件中断处理
- **设备驱动**: 硬件设备驱动开发
- **多核支持**: 多处理器架构支持
- **实时系统**: 实时操作系统特性

### 使用示例5

```rust
#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    kernel_main();
}

fn kernel_main() -> ! {
    // 内核初始化
    init_memory();
    init_interrupts();
    init_scheduler();

    // 主循环
    loop {
        // 内核主循环
    }
}

fn init_memory() {
    // 内存管理初始化
}

fn init_interrupts() {
    // 中断处理初始化
}

fn init_scheduler() {
    // 进程调度器初始化
}
```

### 依赖配置5

```toml
[dependencies]
# 核心依赖
core = "1.0"

# 可选依赖
alloc = { version = "1.0", optional = true }
collections = { version = "1.0", optional = true }

# 特性
[features]
default = []
std = ["alloc", "collections"]
```

---

## ⛓️ 区块链模板

### 模板描述61

适用于创建区块链应用、智能合约、DeFi协议等。

### 项目结构61

```text
blockchain/
├── Cargo.toml
├── README.md
├── LICENSE
├── .gitignore
├── src/
│   ├── main.rs
│   ├── chain/
│   │   ├── mod.rs
│   │   ├── block.rs
│   │   └── transaction.rs
│   ├── consensus/
│   │   ├── mod.rs
│   │   ├── pow.rs
│   │   └── pos.rs
│   ├── network/
│   │   ├── mod.rs
│   │   ├── p2p.rs
│   │   └── protocol.rs
│   ├── crypto/
│   │   ├── mod.rs
│   │   ├── hash.rs
│   │   └── signature.rs
│   └── storage/
│       ├── mod.rs
│       └── database.rs
├── tests/
│   └── integration_tests.rs
└── docs/
    └── blockchain.md
```

### 主要特性6

- **区块链核心**: 区块、交易、共识机制
- **加密算法**: 哈希、数字签名、密钥管理
- **网络协议**: P2P网络、协议栈
- **智能合约**: 合约执行引擎
- **存储系统**: 分布式存储
- **治理机制**: 去中心化治理

### 使用示例6

```rust
use serde::{Deserialize, Serialize};
use sha2::{Sha256, Digest};

#[derive(Serialize, Deserialize, Debug, Clone)]
struct Block {
    index: u64,
    timestamp: u64,
    previous_hash: String,
    hash: String,
    transactions: Vec<Transaction>,
    nonce: u64,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct Transaction {
    sender: String,
    receiver: String,
    amount: f64,
    timestamp: u64,
}

impl Block {
    fn new(index: u64, previous_hash: String, transactions: Vec<Transaction>) -> Self {
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut block = Self {
            index,
            timestamp,
            previous_hash,
            hash: String::new(),
            transactions,
            nonce: 0,
        };

        block.hash = block.calculate_hash();
        block
    }

    fn calculate_hash(&self) -> String {
        let mut hasher = Sha256::new();
        hasher.update(format!("{}{}{}{}{}",
            self.index,
            self.timestamp,
            self.previous_hash,
            serde_json::to_string(&self.transactions).unwrap(),
            self.nonce
        ));
        format!("{:x}", hasher.finalize())
    }

    fn mine_block(&mut self, difficulty: usize) {
        let target = "0".repeat(difficulty);

        while &self.hash[..difficulty] != target {
            self.nonce += 1;
            self.hash = self.calculate_hash();
        }
    }
}
```

### 依赖配置6

```toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
sha2 = "0.10"
ring = "0.17"
tokio = { version = "1.0", features = ["full"] }
anyhow = "1.0"
thiserror = "1.0"
```

---

## 🤖 机器学习模板

### 模板描述7

适用于创建机器学习应用、深度学习模型、AI服务等。

### 项目结构7

```text
ml-app/
├── Cargo.toml
├── README.md
├── LICENSE
├── .gitignore
├── src/
│   ├── main.rs
│   ├── models/
│   │   ├── mod.rs
│   │   ├── neural_network.rs
│   │   └── linear_regression.rs
│   ├── data/
│   │   ├── mod.rs
│   │   ├── dataset.rs
│   │   └── preprocessing.rs
│   ├── training/
│   │   ├── mod.rs
│   │   ├── trainer.rs
│   │   └── optimizer.rs
│   ├── inference/
│   │   ├── mod.rs
│   │   └── predictor.rs
│   └── utils/
│       ├── mod.rs
│       └── math.rs
├── data/
│   ├── train/
│   ├── test/
│   └── validation/
├── models/
│   └── saved/
├── tests/
│   └── integration_tests.rs
└── docs/
    └── ml.md
```

### 主要特性7

- **深度学习**: 神经网络、卷积网络、循环网络
- **传统ML**: 线性回归、决策树、随机森林
- **数据处理**: 数据加载、预处理、增强
- **模型训练**: 训练循环、优化器、损失函数
- **模型推理**: 预测、评估、部署
- **GPU加速**: CUDA、OpenCL支持

### 使用示例7

```rust
use candle_core::{Device, Tensor};
use candle_nn::{linear, Linear, Module, VarBuilder};

struct NeuralNetwork {
    layer1: Linear,
    layer2: Linear,
    layer3: Linear,
}

impl NeuralNetwork {
    fn new(vs: VarBuilder) -> Result<Self, Box<dyn std::error::Error>> {
        let layer1 = linear(784, 128, vs.pp("layer1"))?;
        let layer2 = linear(128, 64, vs.pp("layer2"))?;
        let layer3 = linear(64, 10, vs.pp("layer3"))?;

        Ok(Self {
            layer1,
            layer2,
            layer3,
        })
    }

    fn forward(&self, xs: &Tensor) -> Result<Tensor, Box<dyn std::error::Error>> {
        let xs = self.layer1.forward(xs)?;
        let xs = xs.relu()?;

        let xs = self.layer2.forward(&xs)?;
        let xs = xs.relu()?;

        let xs = self.layer3.forward(&xs)?;
        Ok(xs)
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let device = Device::Cpu;
    let vs = VarBuilder::zeros(candle_core::DType::F32, &device);

    let model = NeuralNetwork::new(vs)?;

    // 创建示例输入
    let input = Tensor::randn(0f32, 1.0, (1, 784), &device)?;

    // 前向传播
    let output = model.forward(&input)?;

    println!("Output shape: {:?}", output.shape());

    Ok(())
}
```

### 依赖配置7

```toml
[dependencies]
candle-core = "0.7"
candle-nn = "0.7"
candle-datasets = "0.7"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
thiserror = "1.0"
tokio = { version = "1.0", features = ["full"] }
```

---

## 🚀 模板使用指南

### 模板选择

1. **确定项目类型**: 根据项目需求选择合适的模板
2. **评估技术栈**: 考虑技术栈的复杂度和学习成本
3. **考虑维护性**: 选择活跃维护的技术栈
4. **评估性能**: 根据性能需求选择合适的技术栈

### 模板定制

1. **修改配置**: 根据项目需求修改Cargo.toml
2. **调整结构**: 根据项目规模调整项目结构
3. **添加依赖**: 根据功能需求添加必要的依赖
4. **修改代码**: 根据业务逻辑修改示例代码

### 最佳实践

1. **版本管理**: 使用语义化版本管理
2. **文档更新**: 及时更新项目文档
3. **测试覆盖**: 保持高测试覆盖率
4. **代码质量**: 使用rustfmt和clippy
5. **安全审计**: 定期进行安全审计

---

## 📞 模板支持

### 社区支持

- **GitHub Issues**: 在模板仓库提交问题
- **Discord**: 加入Rust社区讨论
- **Reddit**: 在r/rust分享经验
- **Stack Overflow**: 寻求技术帮助

### 贡献指南

1. **Fork仓库**: Fork模板仓库
2. **创建分支**: 创建功能分支
3. **提交更改**: 提交代码更改
4. **创建PR**: 创建Pull Request
5. **代码审查**: 参与代码审查

### 模板更新

- **定期更新**: 定期更新依赖版本
- **新特性**: 添加新的模板特性
- **Bug修复**: 修复模板中的问题
- **文档改进**: 改进模板文档

---

-**选择合适的模板，开始您的Rust项目之旅！🦀**-
