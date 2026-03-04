# tarpc RPC框架形式化分析

> **主题**: 基于Tokio的异步RPC
>
> **形式化框架**: 类型安全RPC + 背压控制
>
> **参考**: tarpc Documentation

---

## 目录

- [tarpc RPC框架形式化分析](#tarpc-rpc框架形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 服务定义](#2-服务定义)
    - [定义 2.1 (Service Trait)](#定义-21-service-trait)
    - [定理 2.1 (编译时契约)](#定理-21-编译时契约)
  - [3. 类型安全保证](#3-类型安全保证)
    - [定理 3.1 (请求-响应类型匹配)](#定理-31-请求-响应类型匹配)
    - [定理 3.2 (序列化安全)](#定理-32-序列化安全)
  - [4. 请求上下文](#4-请求上下文)
    - [定理 4.1 (上下文传播)](#定理-41-上下文传播)
  - [5. 背压与限流](#5-背压与限流)
    - [定理 5.1 (Channel背压)](#定理-51-channel背压)
  - [6. 反例](#6-反例)
    - [反例 6.1 (忘记处理Cancel)](#反例-61-忘记处理cancel)

---

## 1. 引言

tarpc提供:

- 异步RPC
- 类型安全接口
- 请求上下文
- 拦截器支持

---

## 2. 服务定义

### 定义 2.1 (Service Trait)

```rust
#[tarpc::service]
trait World {
    async fn hello(name: String) -> String;
}
```

展开后生成:

- `WorldClient`: 客户端stub
- `World`: 服务端trait

### 定理 2.1 (编译时契约)

> 服务定义在编译时生成客户端和服务端契约。

∎

---

## 3. 类型安全保证

### 定理 3.1 (请求-响应类型匹配)

> RPC调用类型在编译时验证。

```rust
// 客户端
let client = WorldClient::new(config).spawn();
let response = client.hello(context::current(), "World".into()).await?;
// response类型: String (编译时确定)
```

**形式化**:

$$
\text{World::hello}: \text{String} \rightarrow \text{String}
$$

∎

### 定理 3.2 (序列化安全)

> tarpc使用serde，保证序列化安全。

---

## 4. 请求上下文

### 定理 4.1 (上下文传播)

> 请求上下文自动传递。

```rust
async fn hello(self, ctx: context::Context, name: String) -> String {
    // ctx包含:
    // - deadline
    // - tracing spans
    // - 自定义元数据
    format!("Hello, {}!", name)
}
```

∎

---

## 5. 背压与限流

### 定理 5.1 (Channel背压)

> 基于Tokio channel的背压。

```rust
Channel::builder(
    tokio::net::TcpStream::connect(addr).await?
)
.limit(100)  // 在途请求限制
.connect()
```

∎

---

## 6. 反例

### 反例 6.1 (忘记处理Cancel)

```rust
async fn long_operation(&self) -> Result<()> {
    sleep(10).await;  // 客户端可能已取消
    // 资源可能泄漏

    // 正确: 定期检查取消
    select! {
        _ = sleep(10) => {},
        _ = ctx.deadline() => return Err(Timeout),
    }
}
```

---

*文档版本: 1.0.0*
*定理数量: 7个*
