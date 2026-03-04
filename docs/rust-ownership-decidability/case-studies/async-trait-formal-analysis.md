# async-trait形式化分析

> **主题**: 异步trait方法支持
> **形式化框架**: 过程宏 + Future类型擦除 + Send边界
> **参考**: async-trait Documentation (<https://docs.rs/async-trait>)

---

## 目录

- [async-trait形式化分析](#async-trait形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 问题背景](#2-问题背景)
    - [定义 PROBLEM-1 ( 原生限制 )](#定义-problem-1--原生限制-)
    - [定义 PROBLEM-2 ( RPITIT限制 )](#定义-problem-2--rpitit限制-)
  - [3. 宏转换机制](#3-宏转换机制)
    - [定义 TRANSFORM-1 ( 转换规则 )](#定义-transform-1--转换规则-)
    - [定义 TRANSFORM-2 ( 具体实现转换 )](#定义-transform-2--具体实现转换-)
  - [4. Send边界问题](#4-send边界问题)
    - [定义 SEND-1 ( Send要求 )](#定义-send-1--send要求-)
    - [定义 SEND-2 ( Send传播 )](#定义-send-2--send传播-)
    - [定理 SEND-T1 ( 自动推断 )](#定理-send-t1--自动推断-)
  - [5. 生命周期处理](#5-生命周期处理)
    - [定义 LIFETIME-1 ( 隐式生命周期 )](#定义-lifetime-1--隐式生命周期-)
    - [定理 LIFETIME-T1 ( 生命周期保留 )](#定理-lifetime-t1--生命周期保留-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 ASYNC\_TRAIT-T1 ( 语义保持 )](#定理-async_trait-t1--语义保持-)
    - [定理 ASYNC\_TRAIT-T2 ( 开销边界 )](#定理-async_trait-t2--开销边界-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: 基础trait](#示例1-基础trait)
    - [示例2: 泛型trait](#示例2-泛型trait)
    - [示例3: 非Send边界](#示例3-非send边界)

---

## 1. 引言

async-trait解决的问题：

- Rust原生不支持`async fn`在trait中
- 通过过程宏将异步trait方法转换为返回`Pin<Box<dyn Future>>`

---

## 2. 问题背景

### 定义 PROBLEM-1 ( 原生限制 )

```rust
// 编译错误: trait不能包含async fn
trait MyTrait {
    async fn method(&self) -> i32;  // ❌
}
```

**形式化**:

$$
\text{trait } T \{ \text{async fn } f() \} \to \text{compile\_error (native Rust)}
$$

### 定义 PROBLEM-2 ( RPITIT限制 )

Rust 1.75+支持RPITIT但存在限制：

- 返回类型必须显式指定Send/Sync
- 复杂trait继承场景受限

---

## 3. 宏转换机制

### 定义 TRANSFORM-1 ( 转换规则 )

```rust
#[async_trait]
trait MyTrait {
    async fn method(&self) -> i32;
}

// 转换为:
trait MyTrait {
    fn method(&self) -> Pin<Box<dyn Future<Output = i32> + Send + '_>>;
}
```

**形式化**:

$$
\text{async\_fn}() \xrightarrow{\text{macro}} \text{fn}() \to \text{Pin}<\text{Box}<\text{dyn Future} + \text{Send} + '\_>>
$$

### 定义 TRANSFORM-2 ( 具体实现转换 )

```rust
#[async_trait]
impl MyTrait for MyStruct {
    async fn method(&self) -> i32 { 42 }
}

// 转换为:
impl MyTrait for MyStruct {
    fn method(&self) -> Pin<Box<dyn Future<Output = i32> + Send + '_>> {
        Box::pin(async move { 42 })
    }
}
```

---

## 4. Send边界问题

### 定义 SEND-1 ( Send要求 )

```rust
#[async_trait]
trait MyTrait {
    async fn method(&self) -> i32;  // 默认+Send
}

#[async_trait(?Send)]  // 可选: 不要求Send
trait LocalTrait {
    async fn method(&self) -> i32;
}
```

### 定义 SEND-2 ( Send传播 )

$$
\text{async\_trait} \to \text{Future} : \text{Send} \text{ if all await points Send}
$$

### 定理 SEND-T1 ( 自动推断 )

宏自动推断Send需求。

$$
\forall t : \text{Trait}.\ t\text{'s methods} \to \text{Send} \lor \text{?Send} \text{ (explicit)}
$$

---

## 5. 生命周期处理

### 定义 LIFETIME-1 ( 隐式生命周期 )

```rust
#[async_trait]
trait MyTrait<'a> {
    async fn method(&'a self) -> &'a str;
}
```

### 定理 LIFETIME-T1 ( 生命周期保留 )

宏转换保留生命周期约束。

$$
\text{async\_trait}(<'a>) \to \text{Box}<\text{dyn Future} + 'a>
$$

---

## 6. 定理与证明

### 定理 ASYNC_TRAIT-T1 ( 语义保持 )

宏转换不改变语义。

$$
\text{async\_fn\_body} \equiv \text{Box::pin}(\text{async\_move\_body})
$$

**证明**: 生成的代码与手写等价的`Box::pin(async move { ... })`相同。$\square$

### 定理 ASYNC_TRAIT-T2 ( 开销边界 )

动态分配开销固定。

$$
\text{overhead} = O(1) \text{ (Box allocation per call)}
$$

---

## 7. 代码示例

### 示例1: 基础trait

```rust
use async_trait::async_trait;

#[async_trait]
trait Database {
    async fn fetch(&self, id: u64) -> Option<String>;
    async fn store(&mut self, id: u64, value: String) -> Result<(), Error>;
}

struct Postgres { /* ... */ }

#[async_trait]
impl Database for Postgres {
    async fn fetch(&self, id: u64) -> Option<String> {
        // 异步数据库查询
        sqlx::query!("SELECT value FROM data WHERE id = $1", id)
            .fetch_optional(&self.pool)
            .await
            .ok()
            .flatten()
            .map(|r| r.value)
    }

    async fn store(&mut self, id: u64, value: String) -> Result<(), Error> {
        sqlx::query!("INSERT INTO data (id, value) VALUES ($1, $2)", id, value)
            .execute(&self.pool)
            .await?;
        Ok(())
    }
}
```

### 示例2: 泛型trait

```rust
use async_trait::async_trait;

#[async_trait]
trait Cache<K, V>
where
    K: Send + Sync + 'static,
    V: Send + Sync + Clone + 'static,
{
    async fn get(&self, key: &K) -> Option<V>;
    async fn set(&self, key: K, value: V);
    async fn remove(&self, key: &K) -> Option<V>;
}

#[async_trait]
impl<K, V> Cache<K, V> for HashMapCache<K, V>
where
    K: Send + Sync + Eq + std::hash::Hash + 'static,
    V: Send + Sync + Clone + 'static,
{
    async fn get(&self, key: &K) -> Option<V> {
        self.inner.read().await.get(key).cloned()
    }

    async fn set(&self, key: K, value: V) {
        self.inner.write().await.insert(key, value);
    }

    async fn remove(&self, key: &K) -> Option<V> {
        self.inner.write().await.remove(key)
    }
}
```

### 示例3: 非Send边界

```rust
use async_trait::async_trait;

// 本地trait，不要求Send（用于单线程上下文）
#[async_trait(?Send)]
trait LocalFileSystem {
    async fn read(&self, path: &Path) -> Vec<u8>;
}

struct LocalFS;

#[async_trait(?Send)]
impl LocalFileSystem for LocalFS {
    async fn read(&self, path: &Path) -> Vec<u8> {
        // 使用 !Send 的本地资源
        tokio::fs::read(path).await.unwrap()
    }
}
```

---

**维护者**: Rust Async Formal Methods Team
**创建日期**: 2026-03-05
**async-trait版本**: 0.1+
**状态**: ✅ 已对齐
