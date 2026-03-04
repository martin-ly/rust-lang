# OpenTelemetry Rust形式化分析

> **主题**: 可观测性数据收集与导出
>
> **形式化框架**: Span上下文传播 + 采样
>
> **参考**: opentelemetry-rust Documentation

---

## 目录

- [OpenTelemetry Rust形式化分析](#opentelemetry-rust形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. TracerProvider架构](#2-tracerprovider架构)
    - [定理 2.1 (全局注册)](#定理-21-全局注册)
  - [3. Span上下文传播](#3-span上下文传播)
    - [定理 3.1 (上下文传递)](#定理-31-上下文传递)
    - [定理 3.2 (Baggage传播)](#定理-32-baggage传播)
  - [4. 采样策略](#4-采样策略)
    - [定理 4.1 (采样决策)](#定理-41-采样决策)
  - [5. 导出器模型](#5-导出器模型)
    - [定理 5.1 (批量导出)](#定理-51-批量导出)
  - [6. 反例](#6-反例)
    - [反例 6.1 (Span未结束)](#反例-61-span未结束)
    - [反例 6.2 (阻塞导出器)](#反例-62-阻塞导出器)

---

## 1. 引言

OpenTelemetry提供:

- Traces/Metrics/Logs
- 跨语言标准
- 可插拔导出器
- 自动Instrumentation

---

## 2. TracerProvider架构

### 定理 2.1 (全局注册)

> TracerProvider全局注册，线程安全。

```rust
let provider = TracerProvider::builder()
    .with_simple_exporter(exporter)
    .build();

global::set_tracer_provider(provider);
```

∎

---

## 3. Span上下文传播

### 定理 3.1 (上下文传递)

> SpanContext跨服务边界传播。

```rust
// 提取上游上下文
let parent_context = propagator.extract(&headers);

// 创建子span
let span = tracer
    .span_builder("process_request")
    .with_parent_context(parent_context)
    .start(&tracer);
```

∎

### 定理 3.2 (Baggage传播)

> Baggage跨边界传递键值数据。

```rust
// 设置baggage
let _ = Context::current_with_baggage(vec![
    KeyValue::new("user.id", user_id),
]);

// 下游服务可访问
```

∎

---

## 4. 采样策略

### 定理 4.1 (采样决策)

> 采样可在根span或传播中决策。

| 策略 | 说明 |
|------|------|
| AlwaysOn | 全部采集 |
| AlwaysOff | 全部丢弃 |
| TraceIdRatioBased | 按比例采样 |
| ParentBased | 跟随父span决策 |

∎

---

## 5. 导出器模型

### 定理 5.1 (批量导出)

> BatchSpanProcessor聚合后导出。

```rust
BatchSpanProcessor::builder(exporter)
    .with_max_queue_size(2048)
    .with_scheduled_delay(Duration::from_secs(5))
    .build();
```

∎

---

## 6. 反例

### 反例 6.1 (Span未结束)

```rust
// 错误: span未结束
{
    let span = tracer.start("operation");
    // 忘记 drop(span);
}  // span结束

// 正确: 使用guard模式
{
    let _span = tracer.start("operation");
    // 自动结束
}

// 或显式结束
span.end();
```

### 反例 6.2 (阻塞导出器)

```rust
// 错误: 使用简单导出器生产环境
TracerProvider::builder()
    .with_simple_exporter(exporter)  // 阻塞!
    .build();

// 正确: 使用批处理
TracerProvider::builder()
    .with_batch_exporter(exporter)
    .build();
```

---

*文档版本: 1.0.0*
*定理数量: 7个*
