# Figment 配置合并形式化分析

> **主题**: 优先级驱动的配置合并
>
> **形式化框架**: 配置源优先级 + 配置提取
>
> **参考**: figment Documentation

---

## 目录

- [Figment 配置合并形式化分析](#figment-配置合并形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 配置源优先级](#2-配置源优先级)
    - [定理 2.1 (后进优先)](#定理-21-后进优先)
  - [3. 配置提取](#3-配置提取)
    - [定理 3.1 (类型提取)](#定理-31-类型提取)
  - [4. 配置文件](#4-配置文件)
    - [定理 4.1 (Profile支持)](#定理-41-profile支持)
  - [5. 反例](#5-反例)
    - [反例 5.1 (类型不匹配)](#反例-51-类型不匹配)

---

## 1. 引言

Figment提供:

- 优先级驱动的配置合并
- 多格式支持
- 环境变量集成
- 类型安全提取

---

## 2. 配置源优先级

### 定理 2.1 (后进优先)

> 后加入的配置源覆盖先加入的。

```rust
let figment = Figment::new()
    .merge(Toml::file("Rocket.toml"))
    .merge(Env::prefixed("APP_"))
    .merge(Serialized::defaults(Config::default()));
// 优先级: defaults < toml < env
```

∎

---

## 3. 配置提取

### 定理 3.1 (类型提取)

> 通过serde反序列化提取配置。

```rust
#[derive(Deserialize)]
struct Config {
    port: u16,
    workers: usize,
}

let config: Config = figment.extract()?;
```

∎

---

## 4. 配置文件

### 定理 4.1 (Profile支持)

> 支持按profile选择配置。

```rust
let figment = Figment::from(rocket::Config::default())
    .select(Profile::from_env_or("APP_PROFILE", "default"));
```

∎

---

## 5. 反例

### 反例 5.1 (类型不匹配)

```rust
// TOML中port是字符串
port = "8080"

// 但Config中port是u16
// 需确保格式匹配
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
