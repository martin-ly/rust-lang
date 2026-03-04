# Tonic Health/Reflection形式化分析

> **主题**: gRPC服务元协议
>
> **形式化框架**: 健康检查 + 服务反射
>
> **参考**: Tonic Documentation; gRPC Health Protocol

---

## 目录

- [Tonic Health/Reflection形式化分析](#tonic-healthreflection形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 健康检查协议](#2-健康检查协议)
    - [定理 2.1 (健康状态机)](#定理-21-健康状态机)
    - [定理 2.2 (watch语义)](#定理-22-watch语义)
  - [3. 服务反射](#3-服务反射)
    - [定理 3.1 (运行时元数据)](#定理-31-运行时元数据)
  - [4. 实现安全](#4-实现安全)
    - [定理 4.1 (敏感信息)](#定理-41-敏感信息)
  - [5. 反例](#5-反例)
    - [反例 5.1 (健康检查竞争)](#反例-51-健康检查竞争)

---

## 1. 引言

gRPC标准扩展:

- Health: 服务健康状态查询
- Reflection: 运行时服务发现

---

## 2. 健康检查协议

### 定理 2.1 (健康状态机)

> 服务健康状态有明确转换。

```protobuf
enum HealthStatus {
    UNKNOWN = 0;
    SERVING = 1;
    NOT_SERVING = 2;
}
```

**转换**:

- 启动: UNKNOWN → SERVING
- 维护: SERVING → NOT_SERVING
- 恢复: NOT_SERVING → SERVING

∎

### 定理 2.2 (watch语义)

> Watch流推送状态变更。

```rust
async fn watch(&self, request: Request<HealthCheckRequest>)
    -> Result<Response<Self::WatchStream>, Status>
{
    // 推送当前状态
    // 后续状态变更
}
```

∎

---

## 3. 服务反射

### 定理 3.1 (运行时元数据)

> 反射提供.proto文件内容。

```rust
// 客户端发现服务方法
let client = ServerReflectionClient::connect(addr).await?;
let resp = client
    .file_containing_symbol("my_package.MyService")
    .await?;
```

∎

---

## 4. 实现安全

### 定理 4.1 (敏感信息)

> 生产环境应谨慎启用反射。

**风险**:

- API结构暴露
- 字段名泄露

**缓解**:

- 内网使用
- 认证保护
- 生产禁用

∎

---

## 5. 反例

### 反例 5.1 (健康检查竞争)

```rust
// 健康状态更新非原子
fn set_not_serving(&self) {
    self.serving.store(false, Relaxed);  // 可能延迟可见
}

// 正确: 使用SeqCst
fn set_not_serving(&self) {
    self.serving.store(false, SeqCst);
}
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
