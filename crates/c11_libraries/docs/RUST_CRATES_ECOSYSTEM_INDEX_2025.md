# Rust 开源库生态索引 (2025)

> **一站式导航**: 快速查找所需的 Rust 库  
> **更新日期**: 2025-10-20 | **基于**: Rust 1.90

---


## 📊 目录

- [Rust 开源库生态索引 (2025)](#rust-开源库生态索引-2025)
  - [📊 目录](#-目录)
  - [📚 文档导航](#-文档导航)
    - [核心文档](#核心文档)
  - [🔍 快速查找](#-快速查找)
    - [按功能查找](#按功能查找)
      - [基础功能](#基础功能)
      - [系统编程](#系统编程)
      - [应用开发](#应用开发)
      - [工具开发](#工具开发)
    - [按场景查找](#按场景查找)
  - [📦 库详情索引](#-库详情索引)
    - [A](#a)
      - [anyhow](#anyhow)
      - [argon2](#argon2)
      - [async-nats](#async-nats)
      - [async-std](#async-std)
      - [async-trait](#async-trait)
      - [axum](#axum)
    - [B](#b)
      - [bevy](#bevy)
      - [bincode](#bincode)
      - [bytes](#bytes)
    - [C](#c)
      - [chrono](#chrono)
      - [clap](#clap)
      - [colored](#colored)
      - [criterion](#criterion)
      - [crossbeam](#crossbeam)
    - [D](#d)
      - [dashmap](#dashmap)
      - [diesel](#diesel)
      - [dioxus](#dioxus)
      - [dotenv](#dotenv)
    - [E](#e)
      - [egui](#egui)
      - [env\_logger](#env_logger)
    - [F](#f)
      - [fake](#fake)
      - [flamegraph](#flamegraph)
      - [flume](#flume)
      - [futures](#futures)
    - [H](#h)
      - [hyper](#hyper)
    - [I](#i)
      - [iced](#iced)
      - [indicatif](#indicatif)
    - [J](#j)
      - [jsonwebtoken](#jsonwebtoken)
    - [L](#l)
      - [lapin](#lapin)
      - [lazy\_static](#lazy_static)
      - [leptos](#leptos)
      - [log](#log)
    - [M](#m)
      - [mockall](#mockall)
      - [mongodb](#mongodb)
    - [O](#o)
      - [once\_cell](#once_cell)
      - [opentelemetry](#opentelemetry)
    - [P](#p)
      - [parking\_lot](#parking_lot)
      - [prometheus](#prometheus)
      - [proptest](#proptest)
      - [prost](#prost)
    - [R](#r)
      - [rand](#rand)
      - [rayon](#rayon)
      - [rdkafka](#rdkafka)
      - [redis](#redis)
      - [regex](#regex)
      - [reqwest](#reqwest)
      - [ring](#ring)
      - [rocket](#rocket)
      - [rustls](#rustls)
    - [S](#s)
      - [sea-orm](#sea-orm)
      - [serde](#serde)
      - [serde\_json](#serde_json)
      - [slog](#slog)
      - [smol](#smol)
      - [sqlx](#sqlx)
    - [T](#t)
      - [tauri](#tauri)
      - [thiserror](#thiserror)
      - [time](#time)
      - [tokio](#tokio)
      - [toml](#toml)
      - [tonic](#tonic)
      - [tower](#tower)
      - [tracing](#tracing)
    - [U](#u)
      - [uuid](#uuid)
    - [W](#w)
      - [warp](#warp)
      - [wasm-bindgen](#wasm-bindgen)
      - [wgpu](#wgpu)
    - [Y](#y)
      - [yew](#yew)
  - [场景快速启动](#场景快速启动)
    - [后端服务](#后端服务)
    - [CLI工具](#cli工具)
    - [数据处理](#数据处理)
    - [微服务](#微服务)
  - [📖 学习路径](#-学习路径)
    - [第1周: 基础库](#第1周-基础库)
    - [第2周: 异步编程](#第2周-异步编程)
    - [第3周: Web 开发](#第3周-web-开发)
    - [第4周: 完整应用](#第4周-完整应用)
  - [🔗 相关资源](#-相关资源)


## 📚 文档导航

### 核心文档

| 文档 | 描述 | 适用人群 |
|------|------|---------|
| **[必备库指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md)** | 详细介绍核心库用法和示例 | 所有开发者 |
| **[分类体系](./RUST_CRATES_CLASSIFICATION_2025.md)** | 按功能、场景系统分类 | 架构师、技术选型 |
| **[成熟度评估](./RUST_CRATES_MATURITY_MATRIX_2025.md)** | 库的成熟度、性能对比 | 技术决策 |
| **[本索引](./RUST_CRATES_ECOSYSTEM_INDEX_2025.md)** | 快速查找和导航 | 快速参考 |

---

## 🔍 快速查找

### 按功能查找

#### 基础功能

- **序列化**: [serde](#serde), [serde_json](#serde_json), [toml](#toml), [bincode](#bincode)
- **文本处理**: [regex](#regex)
- **时间日期**: [chrono](#chrono), [time](#time)
- **随机数**: [rand](#rand), [uuid](#uuid)

#### 系统编程

- **异步运行时**: [tokio](#tokio), [async-std](#async-std), [smol](#smol)
- **并发**: [rayon](#rayon), [crossbeam](#crossbeam), [parking_lot](#parking_lot)
- **内存**: [bytes](#bytes)

#### 应用开发

- **Web框架**: [axum](#axum), [rocket](#rocket)
- **HTTP客户端**: [reqwest](#reqwest), [hyper](#hyper)
- **数据库**: [sqlx](#sqlx), [diesel](#diesel), [sea-orm](#sea-orm)
- **消息队列**: [rdkafka](#rdkafka), [lapin](#lapin), [async-nats](#async-nats)

#### 工具开发

- **CLI**: [clap](#clap), [indicatif](#indicatif), [colored](#colored)
- **日志**: [tracing](#tracing), [log](#log)
- **错误**: [anyhow](#anyhow), [thiserror](#thiserror)

### 按场景查找

- [后端服务](#后端服务)
- [CLI工具](#cli工具)
- [数据处理](#数据处理)
- [微服务](#微服务)

---

## 📦 库详情索引

### A

#### anyhow

- **用途**: 应用程序错误处理
- **版本**: 1.0.89+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#错误处理)

#### argon2

- **用途**: 密码哈希
- **版本**: 0.5+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#密码学与安全)

#### async-nats

- **用途**: NATS 客户端
- **版本**: 0.35+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#消息队列与流处理)

#### async-std

- **用途**: 异步运行时
- **版本**: 1.12+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#异步运行时)

#### async-trait

- **用途**: trait 异步方法
- **版本**: 0.1+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#异步与并发)

#### axum

- **用途**: Web 框架
- **版本**: 0.7+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#web-框架)

### B

#### bevy

- **用途**: 游戏引擎
- **版本**: 0.14+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#游戏开发)

#### bincode

- **用途**: 二进制序列化
- **版本**: 1.3+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#序列化与数据格式)

#### bytes

- **用途**: 字节缓冲区
- **版本**: 1.7+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#内存管理)

### C

#### chrono

- **用途**: 时间日期处理
- **版本**: 0.4+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#核心基础库)

#### clap

- **用途**: CLI 参数解析
- **版本**: 4.5+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#命令行工具)

#### colored

- **用途**: 终端彩色输出
- **版本**: 2.1+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#命令行工具)

#### criterion

- **用途**: 基准测试
- **版本**: 0.5+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#测试工具)

#### crossbeam

- **用途**: 并发数据结构
- **版本**: 0.8+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#并发与并行)

### D

#### dashmap

- **用途**: 并发 HashMap
- **版本**: 6.1+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#并发数据结构)

#### diesel

- **用途**: SQL ORM
- **版本**: 2.2+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#数据库与-orm)

#### dioxus

- **用途**: WebAssembly 前端框架
- **版本**: 0.5+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#webassembly)

#### dotenv

- **用途**: 环境变量加载
- **版本**: 0.15+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#配置管理)

### E

#### egui

- **用途**: 即时模式 GUI
- **版本**: 0.28+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#图形与-gui)

#### env_logger

- **用途**: log 日志实现
- **版本**: 0.11+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#日志)

### F

#### fake

- **用途**: 假数据生成
- **版本**: 2.9+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#测试)

#### flamegraph

- **用途**: 火焰图生成
- **版本**: 0.6+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#性能分析)

#### flume

- **用途**: MPMC 通道
- **版本**: 0.11+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#并发数据结构)

#### futures

- **用途**: Future 组合器
- **版本**: 0.3+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#异步工具库)

### H

#### hyper

- **用途**: HTTP 底层库
- **版本**: 1.4+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#http-客户端)

### I

#### iced

- **用途**: Elm 架构 GUI
- **版本**: 0.13+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#图形与-gui)

#### indicatif

- **用途**: 进度条
- **版本**: 0.17+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#命令行工具)

### J

#### jsonwebtoken

- **用途**: JWT 认证
- **版本**: 9.3+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#web-相关工具)

### L

#### lapin

- **用途**: RabbitMQ 客户端
- **版本**: 2.5+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#消息队列与流处理)

#### lazy_static

- **用途**: 静态变量初始化
- **版本**: 1.5+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#文本处理)

#### leptos

- **用途**: WebAssembly 前端框架
- **版本**: 0.6+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#webassembly)

#### log

- **用途**: 日志门面
- **版本**: 0.4+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#日志与可观测性)

### M

#### mockall

- **用途**: Mock 框架
- **版本**: 0.13+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#测试工具)

#### mongodb

- **用途**: MongoDB 客户端
- **版本**: 3.1+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#nosql-数据库)

### O

#### once_cell

- **用途**: 懒加载静态变量
- **版本**: 1.20+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#文本处理)

#### opentelemetry

- **用途**: 分布式追踪
- **版本**: 0.24+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#可观测性)

### P

#### parking_lot

- **用途**: 高性能锁
- **版本**: 0.12+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#并发与并行)

#### prometheus

- **用途**: 指标收集
- **版本**: 0.13+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#日志与可观测性)

#### proptest

- **用途**: 属性测试
- **版本**: 1.5+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#测试工具)

#### prost

- **用途**: Protocol Buffers
- **版本**: 0.13+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#序列化与数据格式)

### R

#### rand

- **用途**: 随机数生成
- **版本**: 0.8+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#核心基础库)

#### rayon

- **用途**: 数据并行
- **版本**: 1.10+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#并发与并行)

#### rdkafka

- **用途**: Kafka 客户端
- **版本**: 0.36+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#消息队列与流处理)

#### redis

- **用途**: Redis 客户端
- **版本**: 0.27+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#nosql-数据库)

#### regex

- **用途**: 正则表达式
- **版本**: 1.10+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#核心基础库)

#### reqwest

- **用途**: HTTP 客户端
- **版本**: 0.12+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#http-客户端)

#### ring

- **用途**: 密码学基元
- **版本**: 0.17+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#密码学与安全)

#### rocket

- **用途**: Web 框架
- **版本**: 0.5+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#web-框架)

#### rustls

- **用途**: TLS 库
- **版本**: 0.23+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#密码学与安全)

### S

#### sea-orm

- **用途**: 异步 ORM
- **版本**: 1.0+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#数据库与-orm)

#### serde

- **用途**: 序列化框架
- **版本**: 1.0.210+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#核心基础库)

#### serde_json

- **用途**: JSON 序列化
- **版本**: 1.0.128+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#序列化与数据格式)

#### slog

- **用途**: 结构化日志
- **版本**: 2.7+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#日志)

#### smol

- **用途**: 轻量异步运行时
- **版本**: 2.0+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#异步运行时)

#### sqlx

- **用途**: 异步 SQL 查询
- **版本**: 0.8+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#数据库与-orm)

### T

#### tauri

- **用途**: 桌面应用框架
- **版本**: 2.0+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#gui)

#### thiserror

- **用途**: 库错误处理
- **版本**: 1.0.64+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#错误处理)

#### time

- **用途**: 时间日期处理
- **版本**: 0.3+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#核心基础库)

#### tokio

- **用途**: 异步运行时
- **版本**: 1.40+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#异步运行时)

#### toml

- **用途**: TOML 解析
- **版本**: 0.8+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#序列化与反序列化)

#### tonic

- **用途**: gRPC 框架
- **版本**: 0.12+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#grpc)

#### tower

- **用途**: 服务抽象
- **版本**: 0.4+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#web-相关工具)

#### tracing

- **用途**: 结构化日志追踪
- **版本**: 0.1.40+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#日志与可观测性)

### U

#### uuid

- **用途**: UUID 生成
- **版本**: 1.10+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#随机数与哈希)

### W

#### warp

- **用途**: Web 框架
- **版本**: 0.3+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#web-框架)

#### wasm-bindgen

- **用途**: WebAssembly JS 互操作
- **版本**: 0.2.93+
- **成熟度**: ⭐⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#webassembly)

#### wgpu

- **用途**: WebGPU 图形 API
- **版本**: 22.0+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_CRATES_CLASSIFICATION_2025.md#游戏开发)

### Y

#### yew

- **用途**: WebAssembly 前端框架
- **版本**: 0.21+
- **成熟度**: ⭐⭐⭐⭐
- **文档**: [详细指南](./RUST_ESSENTIAL_CRATES_GUIDE_2025.md#webassembly)

---

## 场景快速启动

### 后端服务

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
axum = "0.7"
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tracing = "0.1"
anyhow = "1.0"
```

### CLI工具

```toml
[dependencies]
clap = { version = "4", features = ["derive"] }
anyhow = "1.0"
indicatif = "0.17"
colored = "2.1"
serde = { version = "1.0", features = ["derive"] }
toml = "0.8"
```

### 数据处理

```toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
csv = "1.3"
regex = "1.10"
rayon = "1.10"
```

### 微服务

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
axum = "0.7"
tonic = "0.12"
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres"] }
rdkafka = "0.36"
tracing = "0.1"
opentelemetry = "0.24"
prometheus = "0.13"
```

---

## 📖 学习路径

### 第1周: 基础库

- serde, regex, rand, chrono
- 掌握基础数据处理

### 第2周: 异步编程

- tokio, futures
- 理解 async/await

### 第3周: Web 开发

- axum, sqlx, reqwest
- 构建 RESTful API

### 第4周: 完整应用

- 结合所有知识
- 构建生产级项目

---

## 🔗 相关资源

- [Awesome Rust](https://github.com/rust-unofficial/awesome-rust)
- [crates.io](https://crates.io/)
- [This Week in Rust](https://this-week-in-rust.org/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)

---

**文档版本**: 1.0  
**最后更新**: 2025-10-20  
**维护者**: C11 Middlewares Team
