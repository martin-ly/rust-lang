# Rust模型实现示例

本目录包含了使用Rust语言实现的各种模型示例，展示了如何用Rust的语义和语法来实现这些理论模型。

## 示例文件

### 1. 系统建模示例 (`system_modeling_examples.rs`)

展示了如何使用Rust实现系统建模技术：

- **M/M/1排队系统** - 经典的排队论模型
- **性能分析器** - 系统性能指标收集和分析
- **可靠性分析器** - 系统可靠性建模和仿真
- **可扩展性分析器** - 系统扩展性能分析

**运行示例：**

```bash
cargo run --example system_modeling_examples
```

### 2. 机器学习示例 (`machine_learning_examples.rs`)

展示了如何使用Rust实现机器学习算法：

- **线性回归** - 最小二乘法实现
- **逻辑回归** - 二分类算法
- **KMeans聚类** - 无监督学习算法
- **决策树** - 分类算法

**运行示例：**

```bash
cargo run --example machine_learning_examples
```

### 3. 形式化方法示例 (`formal_methods_examples.rs`)

展示了如何使用Rust实现形式化方法：

- **有限状态机** - 状态转换系统
- **时序逻辑** - 模型检查
- **进程代数** - 并发进程建模

**运行示例：**

```bash
cargo run --example formal_methods_examples
```

## Rust实现的优势

### 1. 类型安全

Rust的强类型系统确保模型实现的正确性：

```rust
pub struct MM1Queue {
    pub arrival_rate: f64,    // 到达率
    pub service_rate: f64,    // 服务率
    pub capacity: Option<usize>, // 可选容量限制
}
```

### 2. 内存安全

Rust的所有权系统防止内存泄漏和悬空指针：

```rust
impl MM1Queue {
    pub fn new(arrival_rate: f64, service_rate: f64) -> Self {
        Self {
            arrival_rate,
            service_rate,
            capacity: None,
        }
    }
}
```

### 3. 并发安全

Rust 的并发模型确保多线程环境下的安全性；本库当前示例以串行为主，便于理解核心算法。

### 4. 零成本抽象

Rust的抽象不会带来运行时开销：

```rust
pub trait QuantumGate {
    fn apply(&self, qubit: &mut Qubit);
}
```

## 工程实践

### 1. 错误处理

使用Rust的Result类型进行优雅的错误处理：

```rust
pub fn average_queue_length(&self) -> Result<f64, String> {
    if self.utilization() >= 1.0 {
        return Err("系统不稳定：利用率 >= 1.0".to_string());
    }
    Ok(self.arrival_rate / (self.service_rate - self.arrival_rate))
}
```

### 2. 测试驱动开发

每个模块都包含完整的单元测试：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mm1_queue_calculations() {
        let queue = MM1Queue::new(1.0, 2.0);
        assert_eq!(queue.utilization(), 0.5);
        assert_eq!(queue.average_queue_length().unwrap(), 1.0);
    }
}
```

### 3. 文档化

使用Rust的文档注释系统：

```rust
/// 排队论模型 - M/M/1 排队系统
/// 
/// 实现经典的M/M/1排队模型，用于分析系统性能
#[derive(Debug, Clone)]
pub struct MM1Queue {
    /// 到达率 (λ)
    pub arrival_rate: f64,
    /// 服务率 (μ)
    pub service_rate: f64,
}
```

## 运行所有示例

要运行所有示例，可以使用以下命令：

```bash
# 运行系统建模示例
cargo run --example system_modeling_examples

# 运行机器学习示例
cargo run --example machine_learning_examples

# 运行形式化方法示例
cargo run --example formal_methods_examples

# 运行所有测试
cargo test

# 运行特定示例的测试
cargo test --example system_modeling_examples
```

## 扩展建议

1. **添加更多算法** - 可以继续添加更多机器学习算法和系统建模技术
2. **性能优化** - 使用Rust的性能分析工具优化关键路径
3. **可视化** - 可结合外部工具对结果进行绘图
4. **Web接口** - 使用 Rust Web 框架创建 API 接口

## 依赖项说明

- `fastrand` - 快速随机数生成
- `petgraph` - 图数据结构
- `serde` - 序列化和反序列化
- `thiserror` - 错误处理
- `uuid` - 唯一标识符生成
- `chrono` - 日期和时间处理
