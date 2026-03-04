# Rust 应用领域总览

Rust 作为一门系统级编程语言，凭借其内存安全、零成本抽象和高性能的特性，已经在众多领域展现出强大的竞争力。
本文档将全面介绍 Rust 在各个主要应用领域的应用现状、优势特点以及生态发展。

## 目录

- [Rust 应用领域总览](#rust-应用领域总览)
  - [目录](#目录)
  - [系统编程](#系统编程)
    - [概述](#概述)
    - [核心优势](#核心优势)
    - [主要项目](#主要项目)
    - [代码示例](#代码示例)
  - [Web 开发](#web-开发)
    - [概述](#概述-1)
    - [后端框架对比](#后端框架对比)
    - [WebAssembly 生态](#webassembly-生态)
    - [全栈框架](#全栈框架)
  - [数据工程](#数据工程)
    - [概述](#概述-2)
    - [数据处理生态](#数据处理生态)
    - [高性能 DataFrame 示例](#高性能-dataframe-示例)
    - [流处理架构](#流处理架构)
  - [DevOps 工具](#devops-工具)
    - [概述](#概述-3)
    - [主要工具生态](#主要工具生态)
    - [监控代理示例](#监控代理示例)
  - [游戏开发](#游戏开发)
    - [概述](#概述-4)
    - [游戏引擎生态](#游戏引擎生态)
    - [ECS 架构示例](#ecs-架构示例)
  - [嵌入式系统](#嵌入式系统)
    - [概述](#概述-5)
    - [嵌入式特性](#嵌入式特性)
    - [嵌入式示例](#嵌入式示例)
  - [区块链与加密货币](#区块链与加密货币)
    - [概述](#概述-6)
    - [主要项目](#主要项目-1)
    - [智能合约示例](#智能合约示例)
  - [人工智能与机器学习](#人工智能与机器学习)
    - [概述](#概述-7)
    - [ML 生态](#ml-生态)
    - [神经网络推理示例](#神经网络推理示例)
  - [跨平台开发](#跨平台开发)
    - [概述](#概述-8)
    - [跨平台框架](#跨平台框架)
    - [Tauri 桌面应用示例](#tauri-桌面应用示例)
  - [网络与通信](#网络与通信)
    - [概述](#概述-9)
    - [网络生态](#网络生态)
    - [gRPC 服务示例](#grpc-服务示例)
  - [总结](#总结)
  - [学习路径建议](#学习路径建议)
    - [初学者路线](#初学者路线)
    - [进阶路线](#进阶路线)
    - [专业路线](#专业路线)
  - [参考资源](#参考资源)

---

## 系统编程

### 概述

系统编程是 Rust 最传统也是最重要的应用领域。
Rust 的设计目标之一就是成为 C/C++ 的现代替代品，用于开发操作系统、驱动程序、底层库等系统软件。

### 核心优势

| 特性 | 说明 | 价值 |
|------|------|------|
| 内存安全 | 编译时所有权检查，消除数据竞争 | 消除 70% 以上的安全漏洞 |
| 零成本抽象 | 高级特性不带来运行时开销 | 性能媲美 C/C++ |
|  fearless concurrency | 编译时保证线程安全 | 轻松编写并发代码 |
| 确定性析构 | RAII 模式，资源自动管理 | 防止资源泄漏 |

### 主要项目

- **操作系统**: Redox OS、Theseus、Tock OS
- **虚拟化**: Firecracker (AWS Lambda 底层)
- **容器**: crun、youki
- **数据库**: TiKV、SurrealDB、MeiliSearch

### 代码示例

```rust
//! 系统编程示例：简单的内存映射文件读取器

use std::fs::File;
use std::io::{self, Read, Write};
use memmap2::{Mmap, MmapMut};

/// 安全的内存映射缓冲区
pub struct MemoryMappedFile {
    mmap: Mmap,
    path: String,
}

impl MemoryMappedFile {
    /// 创建只读内存映射
    pub fn open(path: &str) -> io::Result<Self> {
        let file = File::open(path)?;
        let mmap = unsafe { Mmap::map(&file)? };
        Ok(Self {
            mmap,
            path: path.to_string(),
        })
    }

    /// 获取数据切片
    pub fn as_slice(&self) -> &[u8] {
        &self.mmap[..]
    }

    /// 搜索模式
    pub fn find_pattern(&self, pattern: &[u8]) -> Vec<usize> {
        let data = self.as_slice();
        let mut positions = Vec::new();

        for i in 0..data.len().saturating_sub(pattern.len()) {
            if &data[i..i + pattern.len()] == pattern {
                positions.push(i);
            }
        }

        positions
    }
}

/// 可写的内存映射
pub struct WritableMmap {
    mmap: MmapMut,
}

impl WritableMmap {
    pub fn create(path: &str, size: usize) -> io::Result<Self> {
        let file = File::options()
            .read(true)
            .write(true)
            .create(true)
            .open(path)?;

        file.set_len(size as u64)?;

        let mmap = unsafe { MmapMut::map_mut(&file)? };
        Ok(Self { mmap })
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.mmap[..]
    }

    pub fn flush(&mut self) -> io::Result<()> {
        self.mmap.flush()
    }
}
```

---

## Web 开发

### 概述

Rust 在 Web 开发领域的发展令人瞩目，从高性能的 HTTP 服务器到 WebAssembly 前端应用，Rust 正在改变 Web 开发的技术栈。

### 后端框架对比

| 框架 | 特点 | 适用场景 | 性能评级 |
|------|------|----------|----------|
| Actix-web | 基于 Actor 模型，极致性能 | 高并发 API | ⭐⭐⭐⭐⭐ |
| Axum | 模块化设计，Tower 生态 | 微服务、API | ⭐⭐⭐⭐⭐ |
| Rocket | 开发体验优秀，类型安全 | 快速开发 | ⭐⭐⭐⭐ |
| Tide | 异步优先，中间件友好 | 中小型项目 | ⭐⭐⭐⭐ |
| Warp | 函数式路由，组合性强 | 复杂路由场景 | ⭐⭐⭐⭐⭐ |

### WebAssembly 生态

```rust
//! WebAssembly 前端示例：使用 wasm-bindgen

use wasm_bindgen::prelude::*;
use serde::{Serialize, Deserialize};

#[wasm_bindgen]
#[derive(Serialize, Deserialize, Clone)]
pub struct User {
    id: u64,
    name: String,
    email: String,
}

#[wasm_bindgen]
impl User {
    #[wasm_bindgen(constructor)]
    pub fn new(id: u64, name: String, email: String) -> Self {
        Self { id, name, email }
    }

    #[wasm_bindgen(getter)]
    pub fn id(&self) -> u64 {
        self.id
    }

    #[wasm_bindgen(getter)]
    pub fn name(&self) -> String {
        self.name.clone()
    }

    pub fn validate_email(&self) -> bool {
        self.email.contains('@') && self.email.contains('.')
    }
}

/// 导出 JavaScript 可调用的函数
#[wasm_bindgen]
pub fn process_users_json(json_data: &str) -> Result<String, JsValue> {
    let users: Vec<User> = serde_json::from_str(json_data)
        .map_err(|e| JsValue::from_str(&e.to_string()))?;

    let valid_users: Vec<_> = users.into_iter()
        .filter(|u| u.validate_email())
        .collect();

    serde_json::to_string(&valid_users)
        .map_err(|e| JsValue::from_str(&e.to_string()))
}

/// 使用 web-sys 操作 DOM
#[wasm_bindgen]
pub fn update_dom(element_id: &str, content: &str) {
    let window = web_sys::window().unwrap();
    let document = window.document().unwrap();

    if let Some(element) = document.get_element_by_id(element_id) {
        element.set_text_content(Some(content));
    }
}
```

### 全栈框架

- **Leptos**: 现代 Reactivity 框架，支持 SSR
- **Dioxus**: 跨平台 UI 框架，支持 Web、桌面、移动端
- **Yew**: React-like 的 WebAssembly 框架
- **Tauri**: 桌面应用框架，Rust 后端 + Web 前端

---

## 数据工程

### 概述

数据工程领域对性能和可靠性有极高要求，Rust 的高性能和内存安全特性使其成为数据处理、流计算、数据库开发的理想选择。

### 数据处理生态

| 类别 | 库/工具 | 用途 |
|------|---------|------|
| 数据处理 | Polars、DataFusion | DataFrame 操作、查询 |
| 序列化 | Serde、Arrow、Parquet | 高效数据序列化 |
| 流处理 | Tokio、Fluvio、Vector | 实时数据流 |
| 存储 | RocksDB、Sled、TiKV | 键值存储、分布式存储 |

### 高性能 DataFrame 示例

```rust
//! 使用 Polars 进行数据分析

use polars::prelude::*;
use std::time::Instant;

pub struct DataProcessor {
    df: DataFrame,
}

impl DataProcessor {
    /// 从 CSV 加载数据
    pub fn from_csv(path: &str) -> Result<Self, PolarsError> {
        let df = CsvReader::from_path(path)?
            .infer_schema(None)
            .has_header(true)
            .finish()?;

        Ok(Self { df })
    }

    /// 数据清洗和转换
    pub fn clean_data(&mut self) -> Result<&mut Self, PolarsError> {
        // 移除空值
        self.df = self.df.drop_nulls(None)?;

        // 数据类型转换
        self.df = self.df.with_column(
            col("price").cast(DataType::Float64)
        )?;

        Ok(self)
    }

    /// 聚合分析
    pub fn analyze(&self) -> Result<DataFrame, PolarsError> {
        self.df.clone()
            .lazy()
            .group_by([col("category")])
            .agg([
                col("price").mean().alias("avg_price"),
                col("price").sum().alias("total_sales"),
                col("quantity").sum().alias("total_quantity"),
                col("id").count().alias("transaction_count"),
            ])
            .sort(["total_sales"], SortMultipleOptions::default().with_order_descending(true))
            .collect()
    }

    /// 时间序列分析
    pub fn time_series_analysis(&self, date_col: &str) -> Result<DataFrame, PolarsError> {
        self.df.clone()
            .lazy()
            .with_column(
                col(date_col).str().to_date(StrftimeOptions::default())
            )
            .group_by_dynamic(
                col(date_col),
                [],
                DynamicGroupOptions {
                    every: Duration::parse("1d"),
                    period: Duration::parse("1d"),
                    offset: Duration::parse("0d"),
                    truncate: true,
                    include_boundaries: false,
                    closed_window: ClosedWindow::Left,
                    start_by: StartBy::DataPoint,
                    ..Default::default()
                }
            )
            .agg([col("price").sum().alias("daily_revenue")])
            .collect()
    }
}
```

### 流处理架构

```rust
//! 实时流处理管道

use tokio::sync::mpsc;
use tokio_stream::{Stream, StreamExt};
use futures::stream;

pub struct StreamPipeline<T> {
    input_rx: mpsc::Receiver<T>,
    output_tx: mpsc::Sender<ProcessedRecord>,
}

#[derive(Debug, Clone)]
pub struct RawEvent {
    pub timestamp: u64,
    pub data: String,
    pub source: String,
}

#[derive(Debug, Clone)]
pub struct ProcessedRecord {
    pub timestamp: u64,
    pub metrics: Vec<f64>,
    pub aggregated: bool,
}

impl StreamPipeline<RawEvent> {
    pub fn new(buffer_size: usize) -> (Self, mpsc::Sender<RawEvent>, mpsc::Receiver<ProcessedRecord>) {
        let (input_tx, input_rx) = mpsc::channel(buffer_size);
        let (output_tx, output_rx) = mpsc::channel(buffer_size);

        (Self { input_rx, output_tx }, input_tx, output_rx)
    }

    /// 启动处理管道
    pub async fn run(mut self) {
        while let Some(event) = self.input_rx.recv().await {
            match self.process_event(event).await {
                Ok(record) => {
                    if let Err(e) = self.output_tx.send(record).await {
                        eprintln!("Failed to send processed record: {}", e);
                    }
                }
                Err(e) => eprintln!("Processing error: {}", e),
            }
        }
    }

    async fn process_event(&self, event: RawEvent) -> Result<ProcessedRecord, String> {
        // 解析数据
        let values: Vec<f64> = event.data
            .split(',')
            .filter_map(|s| s.parse().ok())
            .collect();

        // 计算指标
        let metrics = self.calculate_metrics(&values)?;

        Ok(ProcessedRecord {
            timestamp: event.timestamp,
            metrics,
            aggregated: false,
        })
    }

    fn calculate_metrics(&self, values: &[f64]) -> Result<Vec<f64>, String> {
        if values.is_empty() {
            return Err("Empty values".to_string());
        }

        let sum: f64 = values.iter().sum();
        let avg = sum / values.len() as f64;
        let max = values.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
        let min = values.iter().cloned().fold(f64::INFINITY, f64::min);

        Ok(vec![sum, avg, max, min])
    }
}
```

---

## DevOps 工具

### 概述

DevOps 工具需要高可靠性、低资源消耗和快速启动，Rust 的这些特性使其成为构建现代 DevOps 工具链的理想选择。

### 主要工具生态

| 类别 | 工具 | 功能 | 替代方案 |
|------|------|------|----------|
| 容器运行时 | youki、crun | OCI 容器运行 | runc |
| 镜像构建 | packer-rs、buildah-rs | 容器镜像构建 | Docker Build |
| CI/CD | Woodpecker、Drone | 持续集成 | Jenkins, GitLab CI |
| 监控 | Vector、OpenTelemetry | 日志/指标收集 | Fluentd, Logstash |
| 部署 | Flux-rs、Argo Rollouts | GitOps 部署 | Flux, ArgoCD |

### 监控代理示例

```rust
//! 系统监控代理

use sysinfo::{System, SystemExt, ProcessExt, CpuExt, NetworkExt};
use std::time::{Duration, Instant};
use tokio::time::interval;
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct SystemMetrics {
    pub timestamp: u64,
    pub cpu_usage: f32,
    pub memory_used: u64,
    pub memory_total: u64,
    pub disk_usage: Vec<DiskInfo>,
    pub network_io: NetworkStats,
    pub top_processes: Vec<ProcessInfo>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DiskInfo {
    pub mount_point: String,
    pub used: u64,
    pub total: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct NetworkStats {
    pub rx_bytes: u64,
    pub tx_bytes: u64,
    pub rx_packets: u64,
    pub tx_packets: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ProcessInfo {
    pub pid: i32,
    pub name: String,
    pub cpu_usage: f32,
    pub memory: u64,
}

pub struct MetricsCollector {
    system: System,
    collection_interval: Duration,
}

impl MetricsCollector {
    pub fn new(collection_interval_secs: u64) -> Self {
        Self {
            system: System::new_all(),
            collection_interval: Duration::from_secs(collection_interval_secs),
        }
    }

    /// 收集系统指标
    pub fn collect(&mut self) -> SystemMetrics {
        self.system.refresh_all();

        SystemMetrics {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            cpu_usage: self.system.global_cpu_info().cpu_usage(),
            memory_used: self.system.used_memory(),
            memory_total: self.system.total_memory(),
            disk_usage: self.collect_disk_info(),
            network_io: self.collect_network_stats(),
            top_processes: self.collect_top_processes(10),
        }
    }

    fn collect_disk_info(&self) -> Vec<DiskInfo> {
        use sysinfo::DiskExt;

        self.system.disks()
            .iter()
            .map(|disk| DiskInfo {
                mount_point: disk.mount_point().to_string_lossy().to_string(),
                used: disk.total_space() - disk.available_space(),
                total: disk.total_space(),
            })
            .collect()
    }

    fn collect_network_stats(&self) -> NetworkStats {
        let networks = self.system.networks();
        let mut stats = NetworkStats {
            rx_bytes: 0,
            tx_bytes: 0,
            rx_packets: 0,
            tx_packets: 0,
        };

        for (_, network) in networks {
            stats.rx_bytes += network.received();
            stats.tx_bytes += network.transmitted();
            stats.rx_packets += network.packets_received();
            stats.tx_packets += network.packets_transmitted();
        }

        stats
    }

    fn collect_top_processes(&self, limit: usize) -> Vec<ProcessInfo> {
        let mut processes: Vec<_> = self.system.processes()
            .values()
            .map(|p| ProcessInfo {
                pid: p.pid().into(),
                name: p.name().to_string(),
                cpu_usage: p.cpu_usage(),
                memory: p.memory(),
            })
            .collect();

        processes.sort_by(|a, b| b.cpu_usage.partial_cmp(&a.cpu_usage).unwrap());
        processes.into_iter().take(limit).collect()
    }

    /// 启动持续收集
    pub async fn start_collection<F>(mut self, callback: F)
    where
        F: Fn(SystemMetrics) + Send + 'static,
    {
        let mut ticker = interval(self.collection_interval);

        loop {
            ticker.tick().await;
            let metrics = self.collect();
            callback(metrics);
        }
    }
}
```

---

## 游戏开发

### 概述

Rust 在游戏开发领域正在快速崛起，其高性能和内存安全特性特别适合游戏引擎和性能关键的游戏系统。

### 游戏引擎生态

| 引擎 | 特点 | 成熟度 |
|------|------|--------|
| Bevy | 数据驱动、ECS 架构、现代设计 | ⭐⭐⭐⭐ |
| Fyrox | 3D 游戏引擎，内置编辑器 | ⭐⭐⭐ |
| Amethyst | 模块化 ECS 引擎（ archived） | ⭐⭐⭐ |
| Macroquad | 轻量级 2D 游戏框架 | ⭐⭐⭐⭐ |
| ggez | 简单 2D 游戏框架 | ⭐⭐⭐⭐ |

### ECS 架构示例

```rust
//! Bevy ECS 示例

use bevy::prelude::*;

// 组件定义
#[derive(Component)]
struct Player {
    speed: f32,
    health: i32,
}

#[derive(Component)]
struct Position(Vec3);

#[derive(Component)]
struct Velocity(Vec3);

#[derive(Component)]
struct Enemy {
    damage: i32,
}

// 系统定义
fn player_movement(
    time: Res<Time>,
    keyboard_input: Res<Input<KeyCode>>,
    mut query: Query<(&Player, &mut Position, &mut Velocity)>,
) {
    for (player, mut position, mut velocity) in query.iter_mut() {
        let mut direction = Vec3::ZERO;

        if keyboard_input.pressed(KeyCode::W) {
            direction.y += 1.0;
        }
        if keyboard_input.pressed(KeyCode::S) {
            direction.y -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::A) {
            direction.x -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::D) {
            direction.x += 1.0;
        }

        velocity.0 = direction.normalize_or_zero() * player.speed;
        position.0 += velocity.0 * time.delta_seconds();
    }
}

fn enemy_ai(
    time: Res<Time>,
    mut enemies: Query<(&Enemy, &mut Position, &mut Velocity)>,
    players: Query<&Position, With<Player>>,
) {
    if let Ok(player_pos) = players.get_single() {
        for (_enemy, mut enemy_pos, mut velocity) in enemies.iter_mut() {
            let direction = (player_pos.0 - enemy_pos.0).normalize_or_zero();
            velocity.0 = direction * 2.0; // 敌人速度
            enemy_pos.0 += velocity.0 * time.delta_seconds();
        }
    }
}

fn collision_detection(
    mut players: Query<(&mut Player, &Position)>,
    enemies: Query<(&Enemy, &Position)>,
) {
    for (mut player, player_pos) in players.iter_mut() {
        for (enemy, enemy_pos) in enemies.iter() {
            let distance = player_pos.0.distance(enemy_pos.0);
            if distance < 1.0 {
                player.health -= enemy.damage;
                println!("Player hit! Health: {}", player.health);
            }
        }
    }
}
```

---

## 嵌入式系统

### 概述

Rust 的零成本抽象和无运行时特性使其成为嵌入式开发的理想选择，能够在资源受限的环境中提供高级语言的安全性和生产力。

### 嵌入式特性

| 特性 | 说明 |
|------|------|
| 无标准库 | `#![no_std]` 支持，最小化二进制体积 |
| 无全局分配器 | 可选堆分配，支持静态分配 |
| 裸机支持 | 自定义 panic handler 和 allocator |
| 硬件抽象层 | embedded-hal 提供统一接口 |

### 嵌入式示例

```rust
//! 裸机嵌入式程序（STM32）

#![no_std]
#![no_main]

use cortex_m_rt::entry;
use panic_halt as _;
use stm32f4xx_hal as hal;

use hal::{pac, prelude::*, gpio::GpioExt, rcc::RccExt};
use embedded_hal::digital::v2::OutputPin;

#[entry]
fn main() -> ! {
    // 获取外设访问
    let dp = pac::Peripherals::take().unwrap();
    let cp = cortex_m::peripheral::Peripherals::take().unwrap();

    // 配置时钟
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr
        .use_hse(25.MHz())
        .sysclk(84.MHz())
        .freeze();

    // 配置 GPIO
    let gpioa = dp.GPIOA.split();
    let mut led = gpioa.pa5.into_push_pull_output();

    // 配置延时
    let mut delay = cp.SYST.delay(&clocks);

    // 主循环
    loop {
        led.set_high().unwrap();
        delay.delay_ms(500u16);

        led.set_low().unwrap();
        delay.delay_ms(500u16);
    }
}
```

---

## 区块链与加密货币

### 概述

区块链行业对安全和性能有极高要求，Rust 凭借其内存安全和并发特性，成为多个主流区块链项目的首选语言。

### 主要项目

| 项目 | 类型 | 特点 |
|------|------|------|
| Solana | 公链 | 高吞吐量 PoH 共识 |
| Polkadot | 跨链协议 | Substrate 框架 |
| Near | 公链 | Nightshade 分片 |
| Diem | 稳定币 | Meta 发起（已转型） |
| Fuel | 模块化执行层 | UTXO 模型 |

### 智能合约示例

```rust
//! Solana Anchor 智能合约

use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS");

#[program]
pub mod my_token {
    use super::*;

    /// 初始化代币账户
    pub fn initialize(ctx: Context<Initialize>, amount: u64) -> Result<()> {
        let account = &mut ctx.accounts.token_account;
        account.owner = ctx.accounts.owner.key();
        account.amount = amount;
        Ok(())
    }

    /// 转账
    pub fn transfer(ctx: Context<Transfer>, amount: u64) -> Result<()> {
        let from = &mut ctx.accounts.from;
        let to = &mut ctx.accounts.to;

        require!(from.amount >= amount, ErrorCode::InsufficientFunds);
        require!(from.owner == ctx.accounts.authority.key(), ErrorCode::Unauthorized);

        from.amount -= amount;
        to.amount += amount;

        emit!(TransferEvent {
            from: from.key(),
            to: to.key(),
            amount,
        });

        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(init, payer = owner, space = 8 + TokenAccount::SIZE)]
    pub token_account: Account<'info, TokenAccount>,
    #[account(mut)]
    pub owner: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Transfer<'info> {
    #[account(mut)]
    pub from: Account<'info, TokenAccount>,
    #[account(mut)]
    pub to: Account<'info, TokenAccount>,
    pub authority: Signer<'info>,
}

#[account]
pub struct TokenAccount {
    pub owner: Pubkey,
    pub amount: u64,
}

impl TokenAccount {
    pub const SIZE: usize = 32 + 8;
}

#[event]
pub struct TransferEvent {
    pub from: Pubkey,
    pub to: Pubkey,
    pub amount: u64,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Insufficient funds")]
    InsufficientFunds,
    #[msg("Unauthorized")]
    Unauthorized,
}
```

---

## 人工智能与机器学习

### 概述

虽然 Python 主导了 AI/ML 领域，但 Rust 正在这个领域快速发展，特别是在推理引擎和 ML 基础设施方面。

### ML 生态

| 库 | 用途 | 特点 |
|----|------|------|
| burn | 深度学习框架 | 纯 Rust，多后端支持 |
| candle | LLM 推理 | Hugging Face 出品 |
| tch-rs | PyTorch 绑定 | 使用 libtorch |
| ort | ONNX Runtime | 高性能推理 |
| tokenizers | 文本分词 | Hugging Face |

### 神经网络推理示例

```rust
//! 使用 Candle 进行 LLM 推理

use candle_core::{DType, Device, Tensor};
use candle_transformers::generation::LogitsProcessor;
use candle_transformers::models::llama as model;
use model::{Llama, LlamaConfig};
use tokenizers::Tokenizer;

pub struct TextGenerator {
    model: Llama,
    tokenizer: Tokenizer,
    device: Device,
}

impl TextGenerator {
    pub fn new(model_path: &str, tokenizer_path: &str) -> anyhow::Result<Self> {
        let device = Device::cuda_if_available(0)?;

        let config = std::fs::read_to_string(format!("{}/config.json", model_path))?;
        let config: LlamaConfig = serde_json::from_str(&config)?;

        let weights = unsafe {
            candle_core::safetensors::MmapedSafetensors::new(
                format!("{}/model.safetensors", model_path)
            )?
        };

        let vb = candle_transformers::VarBuilder::from_mmaped_safetensors(
            &[format!("{}/model.safetensors", model_path)],
            DType::F32,
            &device,
        )?;

        let model = Llama::load(vb, &config)?;
        let tokenizer = Tokenizer::from_file(tokenizer_path).map_err(anyhow::Error::msg)?;

        Ok(Self { model, tokenizer, device })
    }

    pub fn generate(&self, prompt: &str, max_tokens: usize) -> anyhow::Result<String> {
        let tokens = self.tokenizer.encode(prompt, true).map_err(anyhow::Error::msg)?;
        let mut tokens: Vec<u32> = tokens.get_ids().to_vec();

        let mut logits_processor = LogitsProcessor::new(1337, None, None);
        let mut generated = prompt.to_string();

        for _ in 0..max_tokens {
            let input = Tensor::new(tokens.clone(), &self.device)?.unsqueeze(0)?;
            let logits = self.model.forward(&input, 0)?;
            let logits = logits.squeeze(0)?.to_dtype(DType::F32)?;

            let next_token = logits_processor.sample(&logits)?;
            tokens.push(next_token);

            let token_str = self.tokenizer.decode(&[next_token], true)
                .map_err(anyhow::Error::msg)?;
            generated.push_str(&token_str);

            if next_token == self.tokenizer.token_to_id("</s>").unwrap_or(2) {
                break;
            }
        }

        Ok(generated)
    }
}
```

---

## 跨平台开发

### 概述

Rust 的跨平台能力使其能够构建运行在多个操作系统和架构上的应用程序，从移动端到桌面端再到 Web。

### 跨平台框架

| 框架 | 目标平台 | 特点 |
|------|----------|------|
| Tauri | 桌面 (Win/Mac/Linux) | 轻量、安全、Web 前端 |
| Dioxus | 全平台 | 单次编写，到处运行 |
| Uniffi | 移动端 (iOS/Android) | 生成 FFI 绑定 |
| objc-rs | macOS/iOS | Objective-C 互操作 |
| jni | Android | JNI 绑定 |

### Tauri 桌面应用示例

```rust
//! Tauri 命令和状态管理

use tauri::{State, Manager};
use serde::{Serialize, Deserialize};
use std::sync::{Arc, Mutex};

// 应用状态
pub struct AppState {
    counter: Mutex<i32>,
    config: Mutex<AppConfig>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct AppConfig {
    pub theme: String,
    pub language: String,
    pub auto_save: bool,
}

#[derive(Debug, Serialize)]
pub struct ApiResponse<T> {
    success: bool,
    data: Option<T>,
    error: Option<String>,
}

// Tauri 命令
#[tauri::command]
pub fn increment_counter(state: State<Arc<AppState>>) -> i32 {
    let mut counter = state.counter.lock().unwrap();
    *counter += 1;
    *counter
}

#[tauri::command]
pub fn get_counter(state: State<Arc<AppState>>) -> i32 {
    *state.counter.lock().unwrap()
}

#[tauri::command]
pub fn update_config(
    state: State<Arc<AppState>>,
    config: AppConfig,
) -> ApiResponse<AppConfig> {
    match state.config.lock() {
        Ok(mut cfg) => {
            *cfg = config.clone();
            ApiResponse {
                success: true,
                data: Some(config),
                error: None,
            }
        }
        Err(e) => ApiResponse {
            success: false,
            data: None,
            error: Some(format!("Failed to update config: {}", e)),
        },
    }
}

#[tauri::command]
pub async fn open_file_dialog(window: tauri::Window) -> Result<Option<String>, String> {
    let dialog = tauri::api::dialog::FileDialogBuilder::new();

    let (tx, rx) = std::sync::mpsc::channel();
    dialog.pick_file(move |path| {
        let _ = tx.send(path);
    });

    rx.recv()
        .map_err(|e| e.to_string())
        .map(|p| p.map(|p| p.to_string_lossy().to_string()))
}

// 初始化状态
pub fn init_state() -> Arc<AppState> {
    Arc::new(AppState {
        counter: Mutex::new(0),
        config: Mutex::new(AppConfig {
            theme: "dark".to_string(),
            language: "zh-CN".to_string(),
            auto_save: true,
        }),
    })
}
```

---

## 网络与通信

### 概述

网络编程对性能和可靠性要求极高，Rust 的所有权模型和异步运行时使其成为构建高性能网络服务的理想选择。

### 网络生态

| 类别 | 库/工具 | 用途 |
|------|---------|------|
| 异步运行时 | Tokio、async-std | 异步 I/O |
| HTTP 客户端 | reqwest、hyper | HTTP 通信 |
| gRPC | tonic | RPC 服务 |
| WebSocket | tokio-tungstenite | 实时通信 |
| QUIC | quinn | 现代传输协议 |
| MQTT | rumqtt | IoT 通信 |

### gRPC 服务示例

```rust
//! Tonic gRPC 服务实现

use tonic::{transport::Server, Request, Response, Status};
use tokio_stream::wrappers::ReceiverStream;
use tokio::sync::mpsc;
use std::pin::Pin;

pub mod pb {
    tonic::include_proto!("myservice");
}

use pb::{
    greeter_server::{Greeter, GreeterServer},
    HelloRequest, HelloReply,
    StreamRequest, StreamResponse,
};

#[derive(Debug, Default)]
pub struct MyGreeter {
    request_count: std::sync::atomic::AtomicU64,
}

#[tonic::async_trait]
impl Greeter for MyGreeter {
    /// 一元 RPC
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status> {
        let count = self.request_count.fetch_add(1, std::sync::atomic::Ordering::SeqCst);

        println!("Request #{}: {:?}", count, request);

        let reply = HelloReply {
            message: format!("Hello, {}! (request #{})", request.into_inner().name, count),
        };

        Ok(Response::new(reply))
    }

    /// 服务端流
    type SayHelloStreamStream = ReceiverStream<Result<StreamResponse, Status>>;

    async fn say_hello_stream(
        &self,
        request: Request<StreamRequest>,
    ) -> Result<Response<Self::SayHelloStreamStream>, Status> {
        let (tx, rx) = mpsc::channel(4);
        let count = request.into_inner().count;

        tokio::spawn(async move {
            for i in 0..count {
                let response = StreamResponse {
                    message: format!("Stream message {}", i),
                    index: i,
                };

                if tx.send(Ok(response)).await.is_err() {
                    break;
                }

                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        });

        Ok(Response::new(ReceiverStream::new(rx)))
    }
}

// 中间件：认证
pub mod middleware {
    use super::*;
    use tonic::{body::BoxBody, metadata::MetadataValue};
    use tower::{Service, ServiceBuilder};

    #[derive(Clone)]
    pub struct AuthInterceptor;

    impl<B> Service<Request<B>> for AuthInterceptor {
        type Response = Request<B>;
        type Error = Status;
        type Future = std::future::Ready<Result<Self::Response, Self::Error>>;

        fn poll_ready(
            &mut self,
            _cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<Result<(), Self::Error>> {
            std::task::Poll::Ready(Ok(()))
        }

        fn call(&mut self, req: Request<B>) -> Self::Future {
            let token = req.metadata().get("authorization");

            match token {
                Some(t) if t.to_str().unwrap_or("").starts_with("Bearer ") => {
                    std::future::ready(Ok(req))
                }
                _ => std::future::ready(Err(Status::unauthenticated("Missing token"))),
            }
        }
    }
}

// 启动服务器
pub async fn run_server(addr: &str) -> Result<(), Box<dyn std::error::Error>> {
    let addr = addr.parse()?;
    let greeter = MyGreeter::default();

    Server::builder()
        .add_service(GreeterServer::new(greeter))
        .serve(addr)
        .await?;

    Ok(())
}
```

---

## 总结

Rust 凭借其独特的内存安全保证、零成本抽象和出色的性能，已经在多个应用领域确立了重要地位：

1. **系统编程**: 作为 C/C++ 的现代替代品，用于操作系统、驱动和底层开发
2. **Web 开发**: 高性能后端服务和 WebAssembly 前端应用
3. **数据工程**: 大数据处理、流计算和数据库系统
4. **DevOps**: 容器工具、监控代理和 CI/CD 系统
5. **游戏开发**: 高性能游戏引擎和 ECS 架构
6. **嵌入式**: 资源受限环境中的安全编程
7. **区块链**: 安全和性能并重的分布式系统
8. **AI/ML**: 推理引擎和 ML 基础设施
9. **跨平台**: 桌面、移动和 Web 应用
10. **网络**: 高性能网络服务和通信协议

随着 Rust 生态系统的不断成熟和完善，我们可以预见 Rust 将在更多领域发挥重要作用，成为构建可靠、高性能软件的首选语言。

---

## 学习路径建议

### 初学者路线

1. 掌握 Rust 基础语法和所有权系统
2. 学习 Cargo 和 crates.io 生态
3. 完成一个 CLI 工具项目
4. 学习异步编程和 Tokio

### 进阶路线

1. 深入理解生命周期和泛型
2. 学习 unsafe Rust 和 FFI
3. 掌握宏编程
4. 贡献开源项目

### 专业路线

1. 选择一个应用领域深入研究
2. 阅读该领域优秀项目的源码
3. 构建生产级项目
4. 参与标准库或知名框架的开发

---

## 参考资源

- [The Rust Programming Language](https://doc.rust-lang.org/book/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)
- [Rustlings](https://github.com/rust-lang/rustlings)
- [This Week in Rust](https://this-week-in-rust.org/)
- [Rust 官方博客](https://blog.rust-lang.org/)
