# C19 AI API 参考文档

## 概述

C19 AI 是一个基于 Rust 1.90 的现代 AI/ML 框架，提供高性能、类型安全的机器学习功能。

## 核心 API

### AIEngine

主要的 AI 引擎类，负责管理所有 AI/ML 模块和配置。

#### 构造函数

```rust
pub fn new() -> Result<Self, AIError>
```

创建一个新的 AI 引擎实例。

**返回值:**

- `Ok(AIEngine)`: 成功创建引擎
- `Err(AIError)`: 创建失败

**示例:**

```rust
use c19_ai::AIEngine;

let engine = AIEngine::new()?;
```

#### 方法

##### register_module

```rust
pub fn register_module(&mut self, module: AIModule) -> Result<(), AIError>
```

注册一个新的 AI 模块。

**参数:**

- `module`: 要注册的 AI 模块

**返回值:**

- `Ok(())`: 注册成功
- `Err(AIError)`: 注册失败

**示例:**

```rust
use c19_ai::{AIEngine, AIModule};

let mut engine = AIEngine::new()?;
let module = AIModule::new("machine_learning", "1.0.0");
engine.register_module(module)?;
```

##### get_module

```rust
pub fn get_module(&self, name: &str) -> Option<&AIModule>
```

获取已注册的 AI 模块。

**参数:**

- `name`: 模块名称

**返回值:**

- `Some(&AIModule)`: 找到模块
- `None`: 模块不存在

**示例:**

```rust
let module = engine.get_module("machine_learning");
if let Some(module) = module {
    println!("找到模块: {}", module.name());
}
```

##### has_module

```rust
pub fn has_module(&self, name: &str) -> bool
```

检查模块是否已注册。

**参数:**

- `name`: 模块名称

**返回值:**

- `true`: 模块存在
- `false`: 模块不存在

**示例:**

```rust
if engine.has_module("machine_learning") {
    println!("机器学习模块已注册");
}
```

##### list_modules

```rust
pub fn list_modules(&self) -> Vec<&AIModule>
```

获取所有已注册的模块列表。

**返回值:**

- `Vec<&AIModule>`: 模块列表

**示例:**

```rust
let modules = engine.list_modules();
for module in modules {
    println!("模块: {} v{}", module.name(), module.version());
}
```

##### set_config

```rust
pub fn set_config(&mut self, name: &str, config: ModelConfig) -> Result<(), AIError>
```

设置模型配置。

**参数:**

- `name`: 配置名称
- `config`: 模型配置

**返回值:**

- `Ok(())`: 设置成功
- `Err(AIError)`: 设置失败

**示例:**

```rust
use c19_ai::{AIEngine, ModelConfig};
use std::collections::HashMap;

let mut engine = AIEngine::new()?;
let config = ModelConfig {
    name: "my_model".to_string(),
    version: "1.0.0".to_string(),
    model_type: "classification".to_string(),
    framework: "candle".to_string(),
    parameters: HashMap::new(),
};
engine.set_config("my_model", config)?;
```

##### get_config

```rust
pub fn get_config(&self, name: &str) -> Option<&ModelConfig>
```

获取模型配置。

**参数:**

- `name`: 配置名称

**返回值:**

- `Some(&ModelConfig)`: 找到配置
- `None`: 配置不存在

**示例:**

```rust
let config = engine.get_config("my_model");
if let Some(config) = config {
    println!("模型: {} v{}", config.name, config.version);
}
```

##### record_metric

```rust
pub fn record_metric(&mut self, name: &str, value: f64) -> Result<(), AIError>
```

记录性能指标。

**参数:**

- `name`: 指标名称
- `value`: 指标值

**返回值:**

- `Ok(())`: 记录成功
- `Err(AIError)`: 记录失败

**示例:**

```rust
engine.record_metric("inference_time", 100.0)?;
engine.record_metric("accuracy", 0.95)?;
```

##### get_metrics

```rust
pub fn get_metrics(&self) -> &HashMap<String, f64>
```

获取所有性能指标。

**返回值:**

- `&HashMap<String, f64>`: 指标映射

**示例:**

```rust
let metrics = engine.get_metrics();
for (name, value) in metrics {
    println!("{}: {}", name, value);
}
```

##### set_state

```rust
pub fn set_state(&mut self, key: &str, value: &str) -> Result<(), AIError>
```

设置引擎状态。

**参数:**

- `key`: 状态键
- `value`: 状态值

**返回值:**

- `Ok(())`: 设置成功
- `Err(AIError)`: 设置失败

**示例:**

```rust
engine.set_state("processing", "true")?;
engine.set_state("current_model", "my_model")?;
```

##### get_state

```rust
pub fn get_state(&self, key: &str) -> Option<String>
```

获取引擎状态。

**参数:**

- `key`: 状态键

**返回值:**

- `Some(String)`: 找到状态值
- `None`: 状态不存在

**示例:**

```rust
let processing = engine.get_state("processing");
if let Some(status) = processing {
    println!("处理状态: {}", status);
}
```

##### remove_state

```rust
pub fn remove_state(&mut self, key: &str) -> Result<(), AIError>
```

删除引擎状态。

**参数:**

- `key`: 状态键

**返回值:**

- `Ok(())`: 删除成功
- `Err(AIError)`: 删除失败

**示例:**

```rust
engine.remove_state("processing")?;
```

##### on_event

```rust
pub fn on_event<F>(&mut self, event_name: &str, callback: F) -> Result<(), AIError>
where
    F: Fn(&str) + 'static
```

注册事件监听器。

**参数:**

- `event_name`: 事件名称
- `callback`: 事件回调函数

**返回值:**

- `Ok(())`: 注册成功
- `Err(AIError)`: 注册失败

**示例:**

```rust
engine.on_event("model_loaded", Box::new(|model_name| {
    println!("模型已加载: {}", model_name);
}))?;
```

##### emit_event

```rust
pub fn emit_event(&self, event_name: &str, data: &str) -> Result<(), AIError>
```

触发事件。

**参数:**

- `event_name`: 事件名称
- `data`: 事件数据

**返回值:**

- `Ok(())`: 触发成功
- `Err(AIError)`: 触发失败

**示例:**

```rust
engine.emit_event("model_loaded", "my_model")?;
```

##### set_resource_limit

```rust
pub fn set_resource_limit(&mut self, resource: &str, limit: usize) -> Result<(), AIError>
```

设置资源限制。

**参数:**

- `resource`: 资源名称
- `limit`: 限制值

**返回值:**

- `Ok(())`: 设置成功
- `Err(AIError)`: 设置失败

**示例:**

```rust
engine.set_resource_limit("max_modules", 100)?;
```

##### cleanup

```rust
pub fn cleanup(&mut self) -> Result<(), AIError>
```

清理所有资源。

**返回值:**

- `Ok(())`: 清理成功
- `Err(AIError)`: 清理失败

**示例:**

```rust
engine.cleanup()?;
```

##### version

```rust
pub fn version(&self) -> &str
```

获取引擎版本。

**返回值:**

- `&str`: 版本字符串

**示例:**

```rust
println!("引擎版本: {}", engine.version());
```

### AIModule

AI 模块类，表示一个具体的 AI/ML 功能模块。

#### 构造函数1

```rust
pub fn new(name: &str, version: &str) -> Self
```

创建一个新的 AI 模块。

**参数:**

- `name`: 模块名称
- `version`: 模块版本

**返回值:**

- `AIModule`: 新创建的模块

**示例:**

```rust
use c19_ai::AIModule;

let module = AIModule::new("machine_learning", "1.0.0");
```

#### 方法1

##### name

```rust
pub fn name(&self) -> &str
```

获取模块名称。

**返回值:**

- `&str`: 模块名称

**示例:**

```rust
println!("模块名称: {}", module.name());
```

##### version1

```rust
pub fn version(&self) -> &str
```

获取模块版本。

**返回值:**

- `&str`: 模块版本

**示例:**

```rust
println!("模块版本: {}", module.version());
```

### ModelConfig

模型配置结构体，包含模型的元数据信息。

#### 字段

```rust
pub struct ModelConfig {
    pub name: String,           // 模型名称
    pub version: String,        // 模型版本
    pub model_type: String,     // 模型类型
    pub framework: String,      // 框架名称
    pub parameters: HashMap<String, String>, // 参数字典
}
```

**字段说明:**

- `name`: 模型的唯一名称
- `version`: 模型版本号
- `model_type`: 模型类型（如 "classification", "regression", "clustering"）
- `framework`: 使用的框架（如 "candle", "burn", "tch"）
- `parameters`: 模型参数字典

**示例:**

```rust
use c19_ai::ModelConfig;
use std::collections::HashMap;

let mut parameters = HashMap::new();
parameters.insert("learning_rate".to_string(), "0.001".to_string());
parameters.insert("batch_size".to_string(), "32".to_string());

let config = ModelConfig {
    name: "my_classifier".to_string(),
    version: "1.0.0".to_string(),
    model_type: "classification".to_string(),
    framework: "candle".to_string(),
    parameters,
};
```

### AIError

错误类型枚举，表示可能发生的各种错误。

#### 变体

```rust
pub enum AIError {
    ModuleNotFound(String),      // 模块未找到
    ConfigNotFound(String),      // 配置未找到
    InvalidConfig(String),       // 无效配置
    ResourceLimitExceeded(String), // 资源限制超出
    InternalError(String),       // 内部错误
    ValidationError(String),     // 验证错误
}
```

**变体说明:**

- `ModuleNotFound`: 指定的模块不存在
- `ConfigNotFound`: 指定的配置不存在
- `InvalidConfig`: 配置格式无效
- `ResourceLimitExceeded`: 超出资源限制
- `InternalError`: 内部系统错误
- `ValidationError`: 数据验证失败

**示例:**

```rust
use c19_ai::AIError;

match result {
    Ok(_) => println!("操作成功"),
    Err(AIError::ModuleNotFound(name)) => {
        println!("模块未找到: {}", name);
    }
    Err(AIError::ConfigNotFound(name)) => {
        println!("配置未找到: {}", name);
    }
    Err(e) => {
        println!("其他错误: {:?}", e);
    }
}
```

## 特性标志

C19 AI 支持多种特性标志，允许用户根据需要启用不同的功能。

### 基础特性

- `basic-ai`: 基础 AI 功能（默认启用）
- `candle`: Candle 深度学习框架支持
- `burn`: Burn 深度学习框架支持
- `tch`: PyTorch Rust 绑定支持
- `dfdx`: DFDx 自动微分支持

### 应用特性

- `llm`: 大语言模型支持
- `nlp`: 自然语言处理
- `vision`: 计算机视觉
- `data`: 数据处理
- `search`: 向量搜索

### 高级特性

- `security`: 安全加密功能
- `monitoring`: 监控和指标
- `multimodal`: 多模态 AI
- `federated`: 联邦学习
- `edge`: 边缘 AI
- `quantum`: 量子机器学习

### 完整特性

- `full`: 启用所有特性

**示例:**

```toml
[dependencies]
c19_ai = { version = "0.3.0", features = ["candle", "nlp", "data"] }
```

## 使用示例

### 基础使用

```rust
use c19_ai::{AIEngine, AIModule, ModelConfig};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 AI 引擎
    let mut engine = AIEngine::new()?;
    
    // 注册模块
    let ml_module = AIModule::new("machine_learning", "1.0.0");
    engine.register_module(ml_module)?;
    
    // 设置配置
    let config = ModelConfig {
        name: "my_model".to_string(),
        version: "1.0.0".to_string(),
        model_type: "classification".to_string(),
        framework: "candle".to_string(),
        parameters: HashMap::new(),
    };
    engine.set_config("my_model", config)?;
    
    // 记录指标
    engine.record_metric("accuracy", 0.95)?;
    
    // 设置状态
    engine.set_state("processing", "true")?;
    
    // 注册事件监听器
    engine.on_event("model_loaded", Box::new(|model_name| {
        println!("模型已加载: {}", model_name);
    }))?;
    
    // 触发事件
    engine.emit_event("model_loaded", "my_model")?;
    
    // 获取信息
    println!("引擎版本: {}", engine.version());
    println!("模块数量: {}", engine.list_modules().len());
    println!("指标数量: {}", engine.get_metrics().len());
    
    Ok(())
}
```

### 高级使用

```rust
use c19_ai::{AIEngine, AIModule, ModelConfig};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建共享引擎
    let engine = Arc::new(Mutex::new(AIEngine::new()?));
    
    // 设置资源限制
    engine.lock().await.set_resource_limit("max_modules", 100)?;
    
    // 并发注册模块
    let mut handles = Vec::new();
    for i in 0..10 {
        let engine_clone = engine.clone();
        let handle = tokio::spawn(async move {
            let mut engine_guard = engine_clone.lock().await;
            let module = AIModule::new(&format!("module_{}", i), "1.0.0");
            engine_guard.register_module(module)
        });
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        handle.await??;
    }
    
    // 验证结果
    let engine_guard = engine.lock().await;
    println!("注册的模块数量: {}", engine_guard.list_modules().len());
    
    Ok(())
}
```

## 错误处理

C19 AI 使用 `anyhow` 和 `thiserror` 提供强大的错误处理功能。

### 错误类型

```rust
use c19_ai::AIError;

// 处理特定错误
match engine.register_module(module) {
    Ok(_) => println!("模块注册成功"),
    Err(AIError::ResourceLimitExceeded(resource)) => {
        println!("资源限制超出: {}", resource);
    }
    Err(e) => {
        println!("其他错误: {}", e);
    }
}
```

### 错误链

```rust
use anyhow::Context;

// 添加上下文信息
let result = engine.register_module(module)
    .context("注册机器学习模块失败")?;
```

## 性能优化

### 编译优化

```toml
[profile.release]
opt-level = 3
lto = true
codegen-units = 1
```

### 运行时优化

```rust
// 使用对象池
let mut engine = AIEngine::new()?;
engine.set_resource_limit("max_modules", 1000)?;

// 批量操作
for i in 0..1000 {
    let module = AIModule::new(&format!("module_{}", i), "1.0.0");
    engine.register_module(module)?;
}
```

## 最佳实践

1. **资源管理**: 及时调用 `cleanup()` 方法释放资源
2. **错误处理**: 使用适当的错误处理策略
3. **并发安全**: 在多线程环境中使用 `Arc<Mutex<AIEngine>>`
4. **性能监控**: 定期记录和检查性能指标
5. **配置验证**: 在设置配置前进行验证

## 版本兼容性

- **Rust 版本**: 1.90+
- **特性标志**: 向后兼容
- **API 稳定性**: 遵循语义版本控制

## 贡献指南

1. Fork 项目
2. 创建特性分支
3. 添加测试
4. 提交更改
5. 创建 Pull Request

## 许可证

MIT License - 详见 LICENSE 文件
