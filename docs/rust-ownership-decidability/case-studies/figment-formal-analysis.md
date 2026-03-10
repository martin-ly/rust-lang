# Figment 配置管理库形式化分析

> **主题**: 优先级驱动的配置合并与类型安全提取
>
> **形式化框架**: 配置源优先级 + 配置提取 + Profile选择
>
> **参考**: Figment Documentation, Rocket Framework, serde

---

## 目录

- [Figment 配置管理库形式化分析](#figment-配置管理库形式化分析)
  - [目录](#目录)
  - [1. 项目概览](#1-项目概览)
    - [1.1 Figment 是什么](#11-figment-是什么)
    - [1.2 解决的核心问题](#12-解决的核心问题)
    - [1.3 与同类库对比](#13-与同类库对比)
  - [2. 配置源系统](#2-配置源系统)
    - [2.1 Provider Trait 设计](#21-provider-trait-设计)
    - [2.2 内置 Provider 类型](#22-内置-provider-类型)
  - [3. 优先级与合并](#3-优先级与合并)
    - [3.1 后进优先原理](#31-后进优先原理)
    - [3.2 嵌套值合并](#32-嵌套值合并)
    - [3.3 数组处理](#33-数组处理)
  - [4. Profile 系统](#4-profile-系统)
    - [4.1 多环境配置](#41-多环境配置)
    - [4.2 Profile 选择策略](#42-profile-选择策略)
  - [5. 类型安全提取](#5-类型安全提取)
    - [5.1 deserialize_into 原理](#51-deserialize_into-原理)
    - [5.2 错误处理](#52-错误处理)
    - [5.3 验证机制](#53-验证机制)
  - [6. 环境变量集成](#6-环境变量集成)
    - [6.1 Env Provider](#61-env-provider)
    - [6.2 前缀处理](#62-前缀处理)
    - [6.3 嵌套变量映射](#63-嵌套变量映射)
  - [7. 配置文件支持](#7-配置文件支持)
    - [7.1 JSON/YAML/TOML 解析](#71-jsonyamltoml-解析)
    - [7.2 文件监听](#72-文件监听)
  - [8. 自定义 Provider](#8-自定义-provider)
    - [8.1 实现自定义配置源](#81-实现自定义配置源)
    - [8.2 数据库/远程配置](#82-数据库远程配置)
  - [9. 与 Web 框架集成](#9-与-web-框架集成)
    - [9.1 Rocket 配置](#91-rocket-配置)
    - [9.2 Axum 集成示例](#92-axum-集成示例)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 配置结构设计](#101-配置结构设计)
    - [10.2 敏感信息处理](#102-敏感信息处理)
    - [10.3 默认值策略](#103-默认值策略)
  - [11. 完整代码示例](#11-完整代码示例)
    - [11.1 复杂配置场景实现](#111-复杂配置场景实现)
  - [定理汇总](#定理汇总)

---

## 1. 项目概览

### 1.1 Figment 是什么

Figment 是一个 Rust 生态中的配置管理库，由 Sergio Benitez（Rocket Web 框架作者）开发。它提供了一个统一、类型安全且可扩展的配置管理解决方案。

**核心特性**:

| 特性 | 说明 |
|------|------|
| 多源合并 | 支持从文件、环境变量、默认值等多个来源合并配置 |
| 优先级控制 | 明确的后进优先合并策略 |
| Profile 支持 | 按环境（dev/staging/prod）分离配置 |
| 类型安全 | 基于 serde 的类型安全提取 |
| 可扩展 | 通过 Provider trait 自定义配置源 |

### 1.2 解决的核心问题

在应用程序开发中，配置管理通常面临以下挑战：

```rust
// ❌ 传统方式的痛点
// 1. 硬编码默认值
const PORT: u16 = 8080;

// 2. 手动解析环境变量
let port = env::var("PORT")
    .unwrap_or_else(|_| "8080".to_string())
    .parse::<u16>()
    .expect("PORT must be a number");

// 3. 缺乏验证
if port > 65535 {
    panic!("Invalid port");
}

// 4. 配置文件和代码分离
// - 配置文件格式不一致
// - 类型转换容易出错
```

Figment 通过统一的配置模型解决这些问题：

```rust
// ✅ Figment 方式
#[derive(Deserialize)]
struct AppConfig {
    #[serde(default = "default_port")]
    port: u16,
    #[serde(default)]
    debug: bool,
}

fn default_port() -> u16 { 8080 }

let config: AppConfig = Figment::new()
    .merge(Toml::file("App.toml"))
    .merge(Env::prefixed("APP_"))
    .extract()?;
```

### 1.3 与同类库对比

| 库 | 类型安全 | 多源合并 | Profile 支持 | 生态集成 |
|----|----------|----------|--------------|----------|
| **Figment** | ✅ 原生支持 | ✅ 后进优先 | ✅ 内置 | Rocket 原生 |
| envy | ✅ serde | ❌ 单源 | ❌ 需手动 | 通用 |
| config-rs | ✅ serde | ✅ 可配置 | ⚠️ 有限 | 通用 |
| clap | ✅ 参数解析 | ❌ 不适用 | ❌ 不适用 | CLI 专用 |

**选择建议**:

- **Figment**: 需要复杂配置合并、使用 Rocket、需要 Profile 分离
- **envy**: 仅需环境变量，简单场景
- **config-rs**: 需要 TOML/JSON/YAML/ENV 统一处理，但不需要复杂合并逻辑

---

## 2. 配置源系统

### 2.1 Provider Trait 设计

Provider 是 Figment 的核心抽象，定义配置数据的来源：

```rust
/// Provider trait 的核心定义
pub trait Provider {
    /// 提供数据的元数据描述
    fn metadata(&self) -> Metadata;
    
    /// 提供配置数据，返回 Dict（嵌套的字符串键值对）
    fn data(&self) -> Result<Map<Profile, Dict>, Error>;
    
    /// 指定此 Provider 提供的 Profile
    fn profile(&self) -> Option<Profile> {
        None
    }
}
```

**设计要点**:

1. **返回值是 Map<Profile, Dict>**: 一个 Provider 可以为多个 Profile 提供数据
2. **Dict 是嵌套结构**: `Dict = Map<String, Value>`，支持任意嵌套
3. **错误处理**: 使用 figment::Error 统一错误类型

### 2.2 内置 Provider 类型

Figment 内置了多种常用 Provider：

| Provider | 用途 | 示例 |
|----------|------|------|
| `Toml::file(path)` | TOML 文件 | `Toml::file("Rocket.toml")` |
| `Yaml::file(path)` | YAML 文件 | `Yaml::file("config.yaml")` |
| `Json::file(path)` | JSON 文件 | `Json::file("app.json")` |
| `Env::prefixed(prefix)` | 环境变量 | `Env::prefixed("APP_")` |
| `Serialized::defaults(obj)` | 序列化默认值 | `Serialized::defaults(Config::default())` |
| `Env::raw()` | 原始环境变量 | `Env::raw().filter(|k| k.starts_with("APP"))` |

**嵌套环境变量示例**:

```rust
// 环境变量: APP_DATABASE__URL=postgres://localhost/db
// 双下划线表示嵌套层级

let figment = Figment::new()
    .merge(Env::prefixed("APP_").split("__"));

// 结果: {"database": {"url": "postgres://localhost/db"}}
```

---

## 3. 优先级与合并

### 3.1 后进优先原理

Figment 使用后进优先（Last-Write-Wins）策略合并配置源：

```rust
/// 后进优先合并原理
let figment = Figment::new()
    .merge(Toml::file("defaults.toml"))  // 优先级: 1 (最低)
    .merge(Toml::file("app.toml"))       // 优先级: 2
    .merge(Env::prefixed("APP_"));       // 优先级: 3 (最高)

// 合并规则:
// 1. 同名键，后加入的覆盖先加入的
// 2. 不同键，全部保留
// 3. 嵌套对象，递归合并
```

**形式化定义**:

```
设 C₁, C₂, ..., Cₙ 为配置源，按加入顺序排列

合并结果 M 满足:
∀ key ∈ keys(M): 
    M[key] = Cᵢ[key] where i = max{j | key ∈ keys(Cⱼ)}
```

### 3.2 嵌套值合并

对于嵌套对象，Figment 执行深度合并而非简单替换：

```rust
// defaults.toml
[database]
host = "localhost"
port = 5432

// app.toml (覆盖)
[database]
host = "prod.db.example.com"
// port 保持 defaults.toml 的值

// 合并结果:
// database.host = "prod.db.example.com"
// database.port = 5432
```

**合并算法伪代码**:

```rust
fn merge_deep(base: Value, override: Value) -> Value {
    match (base, override) {
        // 都是对象，递归合并
        (Value::Object(mut b), Value::Object(o)) => {
            for (key, val) in o {
                let merged = match b.remove(&key) {
                    Some(existing) => merge_deep(existing, val),
                    None => val,
                };
                b.insert(key, merged);
            }
            Value::Object(b)
        }
        // 否则，override 完全覆盖
        (_, o) => o,
    }
}
```

### 3.3 数组处理

数组在合并时有特殊行为：**整个数组被替换，而非数组合并**：

```rust
// config.toml
hosts = ["localhost:8080"]

// override.toml
hosts = ["server1:8080", "server2:8080"]

// 合并结果:
// hosts = ["server1:8080", "server2:8080"]
// 不是合并后的 ["localhost:8080", "server1:8080", "server2:8080"]
```

**设计原因**: 数组通常表示完整的列表配置，追加可能导致意外行为。

---

## 4. Profile 系统

### 4.1 多环境配置

Profile 允许在同一份配置文件中定义多个环境的配置：

```toml
# Rocket.toml
[default]
address = "127.0.0.1"
port = 8000
workers = 4
log_level = "normal"

[debug]
address = "127.0.0.1"
port = 8000
log_level = "debug"

[release]
address = "0.0.0.0"
port = 8080
workers = 16
log_level = "critical"

# 自定义 Profile
[staging]
address = "0.0.0.0"
port = 8080
workers = 8
log_level = "normal"
```

### 4.2 Profile 选择策略

Figment 提供多种方式选择当前 Profile：

```rust
use figment::{Figment, Profile};
use figment::providers::{Toml, Env};

// 方式1: 硬编码选择
let figment = Figment::new()
    .merge(Toml::file("Rocket.toml"))
    .select("release");

// 方式2: 从环境变量选择（带默认值）
let profile = Profile::from_env_or("ROCKET_PROFILE", "default");
let figment = Figment::new()
    .merge(Toml::file("Rocket.toml"))
    .select(profile);

// 方式3: Provider 自带 Profile
let figment = Figment::new()
    .merge(Toml::file("base.toml").nested())  // 使用 default
    .merge(Toml::file("dev.toml").profile("debug"));  // 特定 Profile
```

**Profile 继承机制**:

```rust
// 使用 .select() 时，Figment 会:
// 1. 优先使用选定 Profile 的配置
// 2. 对于缺失的键，回退到 default Profile
// 3. 实现配置的渐进式定义

let figment = Figment::new()
    .merge(Toml::file("config.toml"))
    .select("staging");

// 查找顺序:
// 1. [staging] 中的配置
// 2. [default] 中的配置（作为默认值）
```

---

## 5. 类型安全提取

### 5.1 deserialize_into 原理

Figment 的核心提取机制基于 serde：

```rust
use serde::Deserialize;

#[derive(Deserialize, Debug)]
struct DatabaseConfig {
    url: String,
    #[serde(default = "default_pool_size")]
    pool_size: u32,
}

#[derive(Deserialize, Debug)]
struct AppConfig {
    #[serde(default = "default_port")]
    port: u16,
    database: DatabaseConfig,
    #[serde(default)]
    features: Vec<String>,
}

fn default_port() -> u16 { 8080 }
fn default_pool_size() -> u32 { 10 }

// 提取配置
let config: AppConfig = figment.extract()?;
```

**提取流程**:

```
1. Figment 内部数据 → 2. serde_json::Value → 3. 目标类型

核心原理: Figment 实现了 Deserializer trait
         将内部 Dict 结构序列化为目标类型
```

### 5.2 错误处理

Figment 提供详细的错误信息：

```rust
use figment::Error;

match figment.extract::<AppConfig>() {
    Ok(config) => println!("{:?}", config),
    Err(e) => {
        // 错误包含路径、类型、原因
        eprintln!("Config error: {}", e);
        // 输出示例:
        // Config error: missing field `url` for key "database"
    }
}
```

**错误类型**:

| 错误类型 | 说明 | 示例 |
|----------|------|------|
| MissingField | 缺少必填字段 | `missing field 'database'` |
| TypeMismatch | 类型不匹配 | `invalid type: string "8080", expected u16` |
| UnknownField | 未知字段（严格模式）| `unknown field 'extra', expected one of...` |
| Custom | 自定义验证错误 | `port must be > 1024` |

### 5.3 验证机制

结合 serde 和自定义验证：

```rust
use serde::{Deserialize, Deserializer};
use validator::{Validate, ValidationError};

#[derive(Deserialize, Validate, Debug)]
struct ServerConfig {
    #[serde(deserialize_with = "validate_port")]
    #[validate(range(min = 1024, max = 65535))]
    port: u16,
    
    #[validate(length(min = 1, max = 100))]
    host: String,
}

fn validate_port<'de, D>(deserializer: D) -> Result<u16, D::Error>
where
    D: Deserializer<'de>,
{
    let port = u16::deserialize(deserializer)?;
    if port < 1024 {
        return Err(serde::de::Error::custom(
            "port must be >= 1024 (privileged ports not allowed)"
        ));
    }
    Ok(port)
}

// 使用验证
let config: ServerConfig = figment.extract()?;
config.validate()?;  // 运行 validator 验证
```

---

## 6. 环境变量集成

### 6.1 Env Provider

Figment 的 Env Provider 提供强大的环境变量处理能力：

```rust
use figment::providers::Env;

// 基本用法：带前缀的环境变量
let figment = Figment::new()
    .merge(Env::prefixed("APP_"));

// 匹配: APP_PORT, APP_DATABASE_URL, etc.
```

### 6.2 前缀处理

灵活的前缀和过滤策略：

```rust
use figment::providers::Env;

// 方式1: 简单前缀
let env = Env::prefixed("MYAPP_");

// 方式2: 前缀 + 过滤
let env = Env::prefixed("APP_")
    .filter(|key| !key.starts_with("APP_SECRET"));

// 方式3: 忽略大小写
let env = Env::prefixed("APP_")
    .ignore_case();

// 方式4: 映射键名
let env = Env::prefixed("APP_")
    .map(|key| key.to_lowercase());
```

### 6.3 嵌套变量映射

通过分隔符实现嵌套配置映射：

```rust
// 环境变量定义
// APP_DATABASE__URL=postgres://localhost/mydb
// APP_DATABASE__POOL__SIZE=20
// APP_SERVER__HOST=0.0.0.0
// APP_SERVER__PORT=8080

let figment = Figment::new()
    .merge(Env::prefixed("APP_").split("__"));

// 解析结果:
// {
//   "database": {
//     "url": "postgres://localhost/mydb",
//     "pool": {
//       "size": "20"
//     }
//   },
//   "server": {
//     "host": "0.0.0.0",
//     "port": "8080"
//   }
// }
```

**常见分隔符约定**:

| 分隔符 | 使用场景 | 示例 |
|--------|----------|------|
| `__` (双下划线) | 嵌套层级 | `APP_DB__HOST` |
| `_` (单下划线) | 单词分隔 | `APP_DB_HOST` |

---

## 7. 配置文件支持

### 7.1 JSON/YAML/TOML 解析

Figment 原生支持三种主流配置格式：

```rust
use figment::providers::{Json, Yaml, Toml};

let figment = Figment::new()
    // JSON 支持
    .merge(Json::file("config.json"))
    // YAML 支持
    .merge(Yaml::file("config.yaml"))
    // TOML 支持
    .merge(Toml::file("config.toml"));
```

**格式特性对比**:

| 格式 | 注释 | 类型安全 | 可读性 | 适用场景 |
|------|------|----------|--------|----------|
| TOML | ✅ 支持 | ⚠️ 弱类型 | ⭐⭐⭐ 高 | 简单配置、人类编辑 |
| YAML | ✅ 支持 | ⚠️ 弱类型 | ⭐⭐⭐ 高 | 复杂嵌套、Kubernetes |
| JSON | ❌ 不支持 | ✅ 明确 | ⭐⭐ 中 | 机器生成、API 配置 |

**格式特定语法**:

```toml
# TOML: 清晰的表结构
[server]
host = "localhost"
port = 8080

[database]
url = "postgres://localhost/db"

# 数组
features = ["metrics", "logging"]
```

```yaml
# YAML: 更灵活的语法
server:
  host: localhost
  port: 8080

database:
  url: postgres://localhost/db

# 多行字符串
description: |
  This is a multi-line
  configuration description.
```

```json
// JSON: 严格的类型
{
  "server": {
    "host": "localhost",
    "port": 8080
  },
  "database": {
    "url": "postgres://localhost/db"
  }
}
```

### 7.2 文件监听

虽然 Figment 本身不提供文件监听，但可结合 `notify` crate 实现：

```rust
use notify::{Watcher, RecursiveMode, watcher};
use std::sync::mpsc::channel;
use std::time::Duration;

struct ReloadableConfig<T: for<'de> Deserialize<'de>> {
    figment: Arc<RwLock<Figment>>,
    current: Arc<RwLock<T>>,
    _watcher: RecommendedWatcher,
}

impl<T: for<'de> Deserialize<'de> + Send + Sync + 'static> ReloadableConfig<T> {
    fn new(figment: Figment, config_path: &str) -> Result<Self, Box<dyn Error>> {
        let config: T = figment.extract()?;
        let figment = Arc::new(RwLock::new(figment));
        let current = Arc::new(RwLock::new(config));
        
        let (tx, rx) = channel();
        let mut watcher = watcher(tx, Duration::from_secs(2))?;
        watcher.watch(config_path, RecursiveMode::NonRecursive)?;
        
        let figment_clone = Arc::clone(&figment);
        let current_clone = Arc::clone(&current);
        let path = config_path.to_string();
        
        std::thread::spawn(move || {
            loop {
                match rx.recv() {
                    Ok(event) => {
                        println!("Config file changed: {:?}", event);
                        // 重新加载配置
                        let new_figment = Figment::new()
                            .merge(Toml::file(&path));
                        
                        match new_figment.extract::<T>() {
                            Ok(new_config) => {
                                *figment_clone.write().unwrap() = new_figment;
                                *current_clone.write().unwrap() = new_config;
                                println!("Config reloaded successfully");
                            }
                            Err(e) => eprintln!("Failed to reload config: {}", e),
                        }
                    }
                    Err(e) => eprintln!("Watch error: {}", e),
                }
            }
        });
        
        Ok(Self {
            figment,
            current,
            _watcher: watcher,
        })
    }
    
    fn get(&self) -> T
    where
        T: Clone,
    {
        self.current.read().unwrap().clone()
    }
}
```

---

## 8. 自定义 Provider

### 8.1 实现自定义配置源

实现 Provider trait 可创建自定义配置源：

```rust
use figment::{Provider, Error, Profile};
use figment::value::{Dict, Map};

/// 数据库配置 Provider
struct DatabaseProvider {
    connection_string: String,
    profile: Profile,
}

impl DatabaseProvider {
    fn new(connection_string: &str) -> Self {
        Self {
            connection_string: connection_string.to_string(),
            profile: Profile::Default,
        }
    }
    
    fn profile(mut self, profile: impl Into<Profile>) -> Self {
        self.profile = profile.into();
        self
    }
}

impl Provider for DatabaseProvider {
    fn metadata(&self) -> figment::Metadata {
        figment::Metadata::named("Database Provider")
            .about("从数据库加载配置")
    }
    
    fn data(&self) -> Result<Map<Profile, Dict>, Error> {
        // 模拟从数据库读取配置
        // 实际应用中使用 sqlx/diesel 等 ORM
        let mut dict = Dict::new();
        
        // 假设从数据库读取了这些配置
        dict.insert("database_url".to_string(), 
            Value::from(self.connection_string.clone()));
        dict.insert("max_connections".to_string(), Value::from(100));
        dict.insert("timeout_ms".to_string(), Value::from(5000));
        
        let mut map = Map::new();
        map.insert(self.profile.clone(), dict);
        
        Ok(map)
    }
    
    fn profile(&self) -> Option<Profile> {
        Some(self.profile.clone())
    }
}

// 使用自定义 Provider
let figment = Figment::new()
    .merge(DatabaseProvider::new("postgres://localhost/config_db"));
```

### 8.2 数据库/远程配置

更完整的远程配置 Provider 示例：

```rust
use reqwest;
use serde_json::Value as JsonValue;

/// HTTP 远程配置 Provider
struct RemoteConfigProvider {
    url: String,
    api_key: Option<String>,
    timeout: Duration,
}

impl RemoteConfigProvider {
    fn new(url: &str) -> Self {
        Self {
            url: url.to_string(),
            api_key: None,
            timeout: Duration::from_secs(30),
        }
    }
    
    fn with_api_key(mut self, key: &str) -> Self {
        self.api_key = Some(key.to_string());
        self
    }
    
    async fn fetch_config(&self) -> Result<Dict, Error> {
        let client = reqwest::Client::new();
        let mut request = client.get(&self.url).timeout(self.timeout);
        
        if let Some(key) = &self.api_key {
            request = request.header("Authorization", format!("Bearer {}", key));
        }
        
        let response = request
            .send()
            .await
            .map_err(|e| Error::from(e.to_string()))?;
        
        let json: JsonValue = response
            .json()
            .await
            .map_err(|e| Error::from(e.to_string()))?;
        
        // 将 JSON Value 转换为 Figment Dict
        Self::json_to_dict(json)
    }
    
    fn json_to_dict(value: JsonValue) -> Result<Dict, Error> {
        match value {
            JsonValue::Object(map) => {
                let mut dict = Dict::new();
                for (k, v) in map {
                    dict.insert(k, Self::json_to_value(v)?);
                }
                Ok(dict)
            }
            _ => Err(Error::from("Root must be an object")),
        }
    }
    
    fn json_to_value(value: JsonValue) -> Result<figment::value::Value, Error> {
        use figment::value::{Value, Num};
        
        match value {
            JsonValue::Null => Ok(Value::Empty),
            JsonValue::Bool(b) => Ok(Value::Bool(b)),
            JsonValue::Number(n) => {
                if let Some(i) = n.as_i64() {
                    Ok(Value::Num(Num::from(i)))
                } else if let Some(f) = n.as_f64() {
                    Ok(Value::Num(Num::from(f)))
                } else {
                    Err(Error::from("Invalid number"))
                }
            }
            JsonValue::String(s) => Ok(Value::String(s)),
            JsonValue::Array(arr) => {
                let values: Result<Vec<_>, _> = arr
                    .into_iter()
                    .map(Self::json_to_value)
                    .collect();
                Ok(Value::Array(values?))
            }
            JsonValue::Object(obj) => {
                let dict = Self::json_to_dict(JsonValue::Object(obj))?;
                Ok(Value::Dict(dict))
            }
        }
    }
}

impl Provider for RemoteConfigProvider {
    fn metadata(&self) -> figment::Metadata {
        figment::Metadata::named("Remote Config")
            .about(format!("从 {} 获取配置", self.url))
    }
    
    fn data(&self) -> Result<Map<Profile, Dict>, Error> {
        // 注意：这里使用 block_on 将 async 转为 sync
        // 生产环境建议使用 tokio::runtime 或专用线程
        let dict = tokio::runtime::Runtime::new()
            .unwrap()
            .block_on(self.fetch_config())?;
        
        let mut map = Map::new();
        map.insert(Profile::Default, dict);
        Ok(map)
    }
}

// 使用
let figment = Figment::new()
    .merge(RemoteConfigProvider::new("https://config.example.com/api/v1/config")
        .with_api_key("secret_key_123"));
```

---

## 9. 与 Web 框架集成

### 9.1 Rocket 配置

Figment 最初为 Rocket 设计，集成最为原生：

```rust
use rocket::figment::{Figment, Profile};
use rocket::figment::providers::{Toml, Env};

#[rocket::main]
async fn main() -> Result<(), rocket::Error> {
    let figment = Figment::from(rocket::Config::default())
        .merge(Toml::file("Rocket.toml").nested())
        .merge(Env::prefixed("ROCKET_").global())
        .select(Profile::from_env_or("ROCKET_PROFILE", "default"));
    
    let _rocket = rocket::custom(figment)
        .mount("/", routes![index])
        .launch()
        .await?;
    
    Ok(())
}
```

**Rocket.toml 结构**:

```toml
[default]
address = "127.0.0.1"
port = 8000
workers = 4
log_level = "normal"

# 自定义配置节
[default.databases.postgres]
url = "postgres://localhost/rocket_db"

[release]
address = "0.0.0.0"
port = 8080

[release.databases.postgres]
url = "postgres://prod-db.example.com/rocket_db"
```

### 9.2 Axum 集成示例

在 Axum 中使用 Figment：

```rust
use axum::{routing::get, Router, extract::State};
use std::sync::Arc;
use figment::{Figment, Provider};
use figment::providers::{Toml, Env, Serialized};
use serde::Deserialize;

#[derive(Deserialize, Clone, Debug)]
struct ServerConfig {
    #[serde(default = "default_host")]
    host: String,
    #[serde(default = "default_port")]
    port: u16,
}

#[derive(Deserialize, Clone, Debug)]
struct AppConfig {
    server: ServerConfig,
    database_url: String,
}

fn default_host() -> String { "127.0.0.1".to_string() }
fn default_port() -> u16 { 3000 }

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: default_host(),
            port: default_port(),
        }
    }
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            server: ServerConfig::default(),
            database_url: "postgres://localhost/app".to_string(),
        }
    }
}

struct AppState {
    config: AppConfig,
}

async fn health_check(State(state): State<Arc<AppState>>) -> String {
    format!("Server running on {}:{}", 
        state.config.server.host, 
        state.config.server.port
    )
}

#[tokio::main]
async fn main() {
    // 构建 Figment
    let figment = Figment::new()
        .merge(Serialized::defaults(AppConfig::default()))
        .merge(Toml::file("app.toml"))
        .merge(Env::prefixed("APP_").split("__"));
    
    // 提取配置
    let config: AppConfig = figment
        .extract()
        .expect("Failed to load configuration");
    
    println!("Loaded config: {:?}", config);
    
    let state = Arc::new(AppState { config: config.clone() });
    
    let app = Router::new()
        .route("/health", get(health_check))
        .with_state(state);
    
    let addr = format!("{}:{}", config.server.host, config.server.port);
    let listener = tokio::net::TcpListener::bind(&addr).await.unwrap();
    
    println!("Listening on http://{}", addr);
    axum::serve(listener, app).await.unwrap();
}
```

---

## 10. 最佳实践

### 10.1 配置结构设计

推荐的配置分层结构：

```rust
use serde::Deserialize;

// 顶层配置
#[derive(Deserialize, Clone, Debug)]
struct AppConfig {
    /// 服务器配置
    #[serde(default)]
    server: ServerConfig,
    
    /// 数据库配置
    database: DatabaseConfig,
    
    /// 缓存配置
    #[serde(default)]
    cache: CacheConfig,
    
    /// 日志配置
    #[serde(default)]
    logging: LogConfig,
    
    /// 功能开关
    #[serde(default)]
    features: FeatureFlags,
}

#[derive(Deserialize, Clone, Debug)]
struct ServerConfig {
    #[serde(default = "default_host")]
    host: String,
    #[serde(default = "default_port")]
    port: u16,
    #[serde(default = "default_workers")]
    workers: usize,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: default_host(),
            port: default_port(),
            workers: default_workers(),
        }
    }
}

// ... 其他配置子结构
```

### 10.2 敏感信息处理

敏感信息的安全处理方案：

```rust
use std::env;
use figment::providers::Env;

// ❌ 不要：将敏感信息硬编码或提交到仓库
const DATABASE_PASSWORD: &str = "secret123";

// ✅ 推荐：从环境变量或密钥管理服务获取
let figment = Figment::new()
    // 非敏感配置从文件加载
    .merge(Toml::file("config.toml"))
    // 敏感信息从环境变量加载（优先级更高）
    .merge(Env::prefixed("APP_SECRET_"));

// config.toml（提交到仓库）
[database]
host = "localhost"
port = 5432
name = "myapp"
# password 不在文件中

// 环境变量（仅部署环境设置）
// APP_SECRET_DATABASE_PASSWORD=actual_secret_password
```

**使用密钥管理服务**（如 AWS Secrets Manager、Azure Key Vault）：

```rust
/// 密钥管理 Provider
struct SecretsManagerProvider {
    client: aws_sdk_secretsmanager::Client,
    secret_name: String,
}

impl Provider for SecretsManagerProvider {
    fn data(&self) -> Result<Map<Profile, Dict>, Error> {
        // 从 AWS Secrets Manager 获取
        let secret = self.runtime.block_on(
            self.client.get_secret_value()
                .secret_id(&self.secret_name)
                .send()
        ).map_err(|e| Error::from(e.to_string()))?;
        
        let secret_string = secret.secret_string()
            .ok_or_else(|| Error::from("Secret is binary"))?;
        
        // 解析 JSON 并转为 Dict
        let value: serde_json::Value = serde_json::from_str(secret_string)
            .map_err(|e| Error::from(e.to_string()))?;
        
        // ... 转换为 Dict
        todo!()
    }
    // ...
}
```

### 10.3 默认值策略

合理的默认值设计模式：

```rust
use serde::Deserialize;

#[derive(Deserialize, Clone, Debug)]
#[serde(default)]  // 启用字段级默认值
struct DatabaseConfig {
    host: String,           // 必填，无默认值
    #[serde(default = "default_port")]
    port: u16,              // 默认 5432
    #[serde(default = "default_pool_size")]
    pool_size: u32,         // 默认 10
    #[serde(default)]
    ssl_mode: SslMode,      // 使用 SslMode::default()
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            host: "localhost".to_string(),
            port: default_port(),
            pool_size: default_pool_size(),
            ssl_mode: SslMode::default(),
        }
    }
}

fn default_port() -> u16 { 5432 }
fn default_pool_size() -> u32 { 10 }

#[derive(Deserialize, Clone, Debug, Default)]
enum SslMode {
    #[default]
    Prefer,
    Require,
    Disable,
}
```

---

## 11. 完整代码示例

### 11.1 复杂配置场景实现

以下是一个生产级应用的完整配置实现：

```rust
//! 生产级配置管理示例
//! 
//! 演示 Figment 在复杂场景下的完整使用方式

use figment::{Figment, Provider, Error, Profile, Metadata};
use figment::value::{Dict, Map, Value};
use figment::providers::{Toml, Yaml, Json, Env, Serialized, Format};
use serde::{Deserialize, Deserializer, Serialize};
use validator::{Validate, ValidationError};
use std::collections::HashMap;
use std::net::SocketAddr;
use std::path::PathBuf;

// =============================================================================
// 配置结构定义
// =============================================================================

/// 应用根配置
#[derive(Deserialize, Serialize, Clone, Debug, Validate)]
#[serde(default)]
pub struct AppConfig {
    /// 应用名称
    #[validate(length(min = 1, max = 100))]
    pub app_name: String,
    
    /// 运行环境
    pub environment: Environment,
    
    /// 服务器配置
    #[validate]
    pub server: ServerConfig,
    
    /// 数据库配置
    #[validate]
    pub database: DatabaseConfig,
    
    /// Redis 缓存配置
    #[serde(default)]
    pub redis: Option<RedisConfig>,
    
    /// 日志配置
    #[serde(default)]
    pub logging: LoggingConfig,
    
    /// 外部服务配置
    #[serde(default)]
    pub external_services: HashMap<String, ServiceConfig>,
    
    /// 功能开关
    #[serde(default)]
    pub features: FeatureFlags,
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            app_name: "MyApp".to_string(),
            environment: Environment::Development,
            server: ServerConfig::default(),
            database: DatabaseConfig::default(),
            redis: None,
            logging: LoggingConfig::default(),
            external_services: HashMap::new(),
            features: FeatureFlags::default(),
        }
    }
}

/// 运行环境
#[derive(Deserialize, Serialize, Clone, Debug, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Environment {
    Development,
    Staging,
    Production,
    Testing,
}

impl Default for Environment {
    fn default() -> Self { Self::Development }
}

/// 服务器配置
#[derive(Deserialize, Serialize, Clone, Debug, Validate)]
#[serde(default)]
pub struct ServerConfig {
    /// 监听地址
    #[validate(custom = "validate_host")]
    pub host: String,
    
    /// 监听端口
    #[validate(range(min = 1, max = 65535))]
    pub port: u16,
    
    /// 工作线程数
    #[validate(range(min = 1, max = 1024))]
    pub workers: usize,
    
    /// 请求超时（秒）
    #[validate(range(min = 1, max = 300))]
    pub timeout_secs: u64,
    
    /// 最大请求体大小（MB）
    #[validate(range(min = 1, max = 100))]
    pub max_body_size_mb: usize,
    
    /// TLS 配置
    #[serde(default)]
    pub tls: Option<TlsConfig>,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: "127.0.0.1".to_string(),
            port: 8080,
            workers: num_cpus::get(),
            timeout_secs: 30,
            max_body_size_mb: 10,
            tls: None,
        }
    }
}

/// TLS 配置
#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct TlsConfig {
    pub cert_path: PathBuf,
    pub key_path: PathBuf,
}

/// 数据库配置
#[derive(Deserialize, Serialize, Clone, Debug, Validate)]
#[serde(default)]
pub struct DatabaseConfig {
    /// 数据库 URL
    #[validate(url)]
    pub url: String,
    
    /// 连接池大小
    #[validate(range(min = 1, max = 1000))]
    pub pool_size: u32,
    
    /// 连接超时（秒）
    #[validate(range(min = 1, max = 60))]
    pub connect_timeout_secs: u64,
    
    /// 空闲超时（秒）
    #[validate(range(min = 60, max = 3600))]
    pub idle_timeout_secs: u64,
    
    /// 是否启用日志
    #[serde(default)]
    pub logging: bool,
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            url: "postgres://localhost/myapp".to_string(),
            pool_size: 10,
            connect_timeout_secs: 10,
            idle_timeout_secs: 600,
            logging: false,
        }
    }
}

/// Redis 配置
#[derive(Deserialize, Serialize, Clone, Debug, Validate)]
#[serde(default)]
pub struct RedisConfig {
    /// Redis URL
    #[validate(url)]
    pub url: String,
    
    /// 连接池大小
    #[validate(range(min = 1, max = 100))]
    pub pool_size: u32,
}

impl Default for RedisConfig {
    fn default() -> Self {
        Self {
            url: "redis://localhost:6379".to_string(),
            pool_size: 10,
        }
    }
}

/// 日志配置
#[derive(Deserialize, Serialize, Clone, Debug)]
#[serde(default)]
pub struct LoggingConfig {
    /// 日志级别
    pub level: LogLevel,
    
    /// 输出格式
    pub format: LogFormat,
    
    /// 是否输出到文件
    pub file_output: bool,
    
    /// 日志文件路径
    pub file_path: Option<PathBuf>,
    
    /// 日志轮转配置
    pub rotation: Option<LogRotation>,
}

impl Default for LoggingConfig {
    fn default() -> Self {
        Self {
            level: LogLevel::Info,
            format: LogFormat::Json,
            file_output: false,
            file_path: None,
            rotation: None,
        }
    }
}

#[derive(Deserialize, Serialize, Clone, Debug, Default)]
#[serde(rename_all = "lowercase")]
pub enum LogLevel {
    Trace,
    Debug,
    #[default]
    Info,
    Warn,
    Error,
}

#[derive(Deserialize, Serialize, Clone, Debug, Default)]
#[serde(rename_all = "lowercase")]
pub enum LogFormat {
    #[default]
    Json,
    Pretty,
    Compact,
}

#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct LogRotation {
    pub max_files: usize,
    pub max_size_mb: usize,
}

/// 外部服务配置
#[derive(Deserialize, Serialize, Clone, Debug, Validate)]
pub struct ServiceConfig {
    #[validate(url)]
    pub base_url: String,
    
    #[validate(range(min = 1, max = 60))]
    pub timeout_secs: u64,
    
    #[serde(default)]
    pub retry_count: u32,
    
    pub api_key: Option<String>,
}

/// 功能开关
#[derive(Deserialize, Serialize, Clone, Debug, Default)]
pub struct FeatureFlags {
    #[serde(default)]
    pub enable_metrics: bool,
    
    #[serde(default)]
    pub enable_caching: bool,
    
    #[serde(default)]
    pub enable_rate_limiting: bool,
    
    #[serde(default)]
    pub beta_features: bool,
}

// =============================================================================
// 验证函数
// =============================================================================

fn validate_host(host: &str) -> Result<(), ValidationError> {
    // 验证主机名或 IP 地址
    if host.is_empty() {
        return Err(ValidationError::new("host_empty"));
    }
    
    // 简单验证：非空且长度合理
    if host.len() > 253 {
        return Err(ValidationError::new("host_too_long"));
    }
    
    Ok(())
}

// =============================================================================
// 配置加载器
// =============================================================================

pub struct ConfigLoader;

impl ConfigLoader {
    /// 加载配置的推荐顺序：
    /// 1. 内置默认值
    /// 2. 配置文件（按优先级：toml > yaml > json）
    /// 3. 环境变量
    /// 4. 命令行参数（如需要）
    pub fn load() -> Result<AppConfig, ConfigError> {
        let figment = Self::build_figment()?;
        
        let config: AppConfig = figment.extract()
            .map_err(|e| ConfigError::ExtractError(e.to_string()))?;
        
        // 运行验证
        config.validate()
            .map_err(|e| ConfigError::ValidationError(e.to_string()))?;
        
        Ok(config)
    }
    
    /// 构建 Figment 实例
    fn build_figment() -> Result<Figment, ConfigError> {
        let mut figment = Figment::new();
        
        // 1. 加载内置默认值
        figment = figment.merge(Serialized::defaults(AppConfig::default()));
        
        // 2. 按优先级尝试加载配置文件
        // 先尝试 TOML
        if std::path::Path::new("config.toml").exists() {
            figment = figment.merge(Toml::file("config.toml"));
        }
        // 再尝试 YAML
        else if std::path::Path::new("config.yaml").exists() {
            figment = figment.merge(Yaml::file("config.yaml"));
        }
        // 最后尝试 JSON
        else if std::path::Path::new("config.json").exists() {
            figment = figment.merge(Json::file("config.json"));
        }
        
        // 3. 加载环境变量（优先级最高）
        // 支持嵌套：APP_DATABASE__URL → database.url
        figment = figment.merge(
            Env::prefixed("APP_")
                .split("__")
                .map(|key| key.to_lowercase())
        );
        
        // 4. 根据环境选择 Profile
        let profile = Profile::from_env_or("APP_ENV", "development");
        figment = figment.select(profile);
        
        Ok(figment)
    }
    
    /// 从特定路径加载配置
    pub fn load_from(path: impl AsRef<std::path::Path>) -> Result<AppConfig, ConfigError> {
        let path = path.as_ref();
        
        let figment = Figment::new()
            .merge(Serialized::defaults(AppConfig::default()));
        
        let figment = match path.extension().and_then(|s| s.to_str()) {
            Some("toml") => figment.merge(Toml::file(path)),
            Some("yaml") | Some("yml") => figment.merge(Yaml::file(path)),
            Some("json") => figment.merge(Json::file(path)),
            _ => return Err(ConfigError::UnsupportedFormat(
                path.to_string_lossy().to_string()
            )),
        };
        
        let config: AppConfig = figment.extract()
            .map_err(|e| ConfigError::ExtractError(e.to_string()))?;
        
        config.validate()
            .map_err(|e| ConfigError::ValidationError(e.to_string()))?;
        
        Ok(config)
    }
}

// =============================================================================
// 错误类型
// =============================================================================

#[derive(Debug)]
pub enum ConfigError {
    ExtractError(String),
    ValidationError(String),
    UnsupportedFormat(String),
    FileNotFound(String),
}

impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExtractError(e) => write!(f, "配置提取错误: {}", e),
            Self::ValidationError(e) => write!(f, "配置验证错误: {}", e),
            Self::UnsupportedFormat(p) => write!(f, "不支持的配置文件格式: {}", p),
            Self::FileNotFound(p) => write!(f, "配置文件未找到: {}", p),
        }
    }
}

impl std::error::Error for ConfigError {}

// =============================================================================
// 便捷方法
// =============================================================================

impl AppConfig {
    /// 获取 SocketAddr
    pub fn socket_addr(&self) -> Result<SocketAddr, std::net::AddrParseError> {
        format!("{}:{}", self.server.host, self.server.port)
            .parse()
    }
    
    /// 检查是否在开发环境
    pub fn is_dev(&self) -> bool {
        self.environment == Environment::Development
    }
    
    /// 检查是否在生产环境
    pub fn is_prod(&self) -> bool {
        self.environment == Environment::Production
    }
    
    /// 获取日志级别（用于 tracing）
    pub fn tracing_level(&self) -> tracing::Level {
        match self.logging.level {
            LogLevel::Trace => tracing::Level::TRACE,
            LogLevel::Debug => tracing::Level::DEBUG,
            LogLevel::Info => tracing::Level::INFO,
            LogLevel::Warn => tracing::Level::WARN,
            LogLevel::Error => tracing::Level::ERROR,
        }
    }
}

// =============================================================================
// 示例配置文件
// =============================================================================

/*
config.toml:

app_name = "My Production App"
environment = "production"

[server]
host = "0.0.0.0"
port = 8080
workers = 8
timeout_secs = 60
max_body_size_mb = 50

[server.tls]
cert_path = "/etc/ssl/cert.pem"
key_path = "/etc/ssl/key.pem"

[database]
url = "postgres://prod-db.example.com:5432/myapp"
pool_size = 50
connect_timeout_secs = 5
logging = false

[redis]
url = "redis://redis.example.com:6379"
pool_size = 20

[logging]
level = "info"
format = "json"
file_output = true
file_path = "/var/log/myapp/app.log"

[logging.rotation]
max_files = 10
max_size_mb = 100

[external_services.payment]
base_url = "https://api.payment.com/v1"
timeout_secs = 30
retry_count = 3

[external_services.notification]
base_url = "https://api.notify.com"
timeout_secs = 10

[features]
enable_metrics = true
enable_caching = true
enable_rate_limiting = true
beta_features = false
*/

// =============================================================================
// 使用示例
// =============================================================================

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 加载配置
    let config = ConfigLoader::load()?;
    
    println!("应用名称: {}", config.app_name);
    println!("运行环境: {:?}", config.environment);
    println!("服务器地址: {}:{}", config.server.host, config.server.port);
    println!("数据库 URL: {}", config.database.url);
    
    if let Some(redis) = &config.redis {
        println!("Redis URL: {}", redis.url);
    }
    
    // 获取 SocketAddr
    let addr = config.socket_addr()?;
    println!("监听地址: {:?}", addr);
    
    // 检查功能开关
    if config.features.enable_metrics {
        println!("指标收集已启用");
    }
    
    Ok(())
}
```

---

## 定理汇总

### 定理 2.1 (后进优先)

> 后加入的配置源覆盖先加入的，这是 Figment 配置合并的核心原则。

**形式化表述**:

```
设配置源序列为 C₁, C₂, ..., Cₙ，合并函数为 M(C₁, C₂, ..., Cₙ)

∀ key ∈ ⋃ keys(Cᵢ):
    M[key] = Cₖ[key] 
    where k = max{j | key ∈ keys(Cⱼ) ∧ 1 ≤ j ≤ n}
```

**性质**:
- 交换律不成立: M(C₁, C₂) ≠ M(C₂, C₁)
- 幂等性: M(C, C) = M(C)
- 结合律: M(M(C₁, C₂), C₃) = M(C₁, M(C₂, C₃))

### 定理 3.1 (类型提取)

> 通过 serde 反序列化将配置数据提取为强类型结构，在编译期保证类型安全。

**依赖关系**:
```
Figment 内部数据 → serde Deserializer → 目标类型 T: Deserialize
```

### 定理 4.1 (Profile 支持)

> Profile 系统支持按环境分离配置，选择 Profile 时会自动继承 default Profile 的默认值。

**查找顺序**:
```
1. 选定 Profile 的配置值
2. default Profile 的同名配置值（如果存在）
3. 结构体定义的默认值
```

### 定理 5.1 (嵌套合并)

> 对于嵌套对象，Figment 执行深度递归合并；对于数组，执行完全替换。

```rust
// 对象：深度合并
{a: {b: 1, c: 2}} + {a: {c: 3, d: 4}} = {a: {b: 1, c: 3, d: 4}}

// 数组：完全替换
{a: [1, 2]} + {a: [3, 4]} = {a: [3, 4]}
```

### 定理 6.1 (环境变量嵌套)

> 通过分隔符（如 `__`）可在环境变量名称中表示嵌套结构，实现扁平到嵌套的映射。

```
PREFIX_KEY__SUBKEY__VALUE → {"key": {"subkey": {"value": ...}}}
```

---

*文档版本: 2.0.0*
*最后更新: 2026-03-10*
*定理数量: 5个*
*代码示例: 11个完整示例*
