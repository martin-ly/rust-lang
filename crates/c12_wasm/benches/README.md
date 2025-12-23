# C12 WASM Benchmarks

本目录包含性能基准测试，使用 Criterion.rs 框架进行性能分析。

## 📚 基准测试列表

| 基准测试文件 | 描述 | 测试项数 |
| --- | --- | --- |
| [array_processing_bench.rs](./array_processing_bench.rs) | 数组操作性能测试 | 5+ |
| [string_operations_bench.rs](./string_operations_bench.rs) | 字符串操作性能测试 | 4+ |
| [design_patterns_bench.rs](./design_patterns_bench.rs) | 设计模式性能测试 | 4+ |

## 🚀 运行基准测试

### 运行所有基准测试

```bash
# 运行所有基准测试
cargo bench

# 只运行特定的基准测试文件
cargo bench --bench array_processing_bench
cargo bench --bench string_operations_bench
cargo bench --bench design_patterns_bench

# 运行特定的测试函数
cargo bench --bench array_processing_bench -- sum_array
```

### 查看基准测试结果

基准测试结果会自动生成 HTML 报告：

```bash
# 运行基准测试
cargo bench

# 查看 HTML 报告
# 浏览器打开 target/criterion/report/index.html
```

### 比较基准测试结果

```bash
# 保存基线
cargo bench -- --save-baseline my-baseline

# 与基线比较
cargo bench -- --baseline my-baseline

# 比较两次运行
cargo bench -- --save-baseline before
# ... 进行代码更改 ...
cargo bench -- --baseline before
```

## 📊 基准测试详情

### array_processing_bench.rs - 数组处理性能

测试各种数组操作在不同数据规模下的性能：

**测试项**：

- `sum_array` - 数组求和 (10, 100, 1K, 10K 元素)
- `find_max` - 查找最大值 (10, 100, 1K, 10K 元素)
- `filter_operations` - 过滤操作 (10K 元素)
- `reverse_array` - 数组反转 (100, 1K, 10K 元素)
- `double_elements` - 元素翻倍 (10K 元素)

**运行命令**：

```bash
cargo bench --bench array_processing_bench
```

**性能指标**：

- 小数据集 (< 100): 应该 < 1μs
- 中等数据集 (100-1K): 应该 < 10μs
- 大数据集 (10K): 应该 < 100μs

### string_operations_bench.rs - 字符串操作性能

测试字符串操作在不同长度字符串上的性能：

**测试项**：

- `reverse_string` - 字符串反转 (短/中/长)
- `is_palindrome` - 回文检测 (短/长)
- `count_words` - 单词计数 (短/中/长)
- `case_conversion` - 大小写转换 (长字符串)

**运行命令**：

```bash
cargo bench --bench string_operations_bench
```

**性能指标**：

- 短字符串 (< 50字符): 应该 < 100ns
- 中等字符串 (50-500字符): 应该 < 1μs
- 长字符串 (> 5000字符): 应该 < 50μs

### design_patterns_bench.rs - 设计模式性能

测试不同设计模式实现的性能开销：

**测试项**：

- `factory_pattern` - 工厂模式创建开销
- `builder_pattern` - 建造者模式构建开销
- `strategy_pattern` - 策略模式排序性能
- `observer_pattern` - 观察者模式通知开销

**运行命令**：

```bash
cargo bench --bench design_patterns_bench
```

**关键发现**：

- 工厂模式创建开销应该 < 50ns
- 建造者模式构建开销应该 < 100ns
- 策略模式：快速排序比冒泡排序快 10-100x (取决于数据大小)
- 观察者模式通知 10 个观察者应该 < 1μs

## 🔍 性能分析工具

### 1. Criterion 统计分析

Criterion 提供详细的统计分析：

- **平均值 (Mean)**: 平均执行时间
- **标准差 (Std Dev)**: 性能波动
- **中位数 (Median)**: 中间值
- **MAD (Median Absolute Deviation)**: 稳定性指标

### 2. 火焰图生成

```bash
# 安装 cargo-flamegraph
cargo install flamegraph

# 生成火焰图
cargo flamegraph --bench array_processing_bench

# 查看火焰图
# 浏览器打开 flamegraph.svg
```

### 3. 性能对比

```bash
# 保存优化前的基线
git checkout old-version
cargo bench -- --save-baseline old

# 切换到优化后的版本
git checkout new-version
cargo bench -- --baseline old

# Criterion 会自动显示性能提升百分比
```

### 4. 详细分析

```bash
# 使用 --verbose 查看详细信息
cargo bench -- --verbose

# 增加样本数以提高精度
cargo bench -- --sample-size 1000

# 增加测试时间
cargo bench -- --measurement-time 10
```

## 📈 性能优化建议

### 1. 数组操作优化

```rust
// ❌ 不好：多次迭代
let filtered: Vec<i32> = data.iter().filter(|&&x| x > 0).copied().collect();
let doubled: Vec<i32> = filtered.iter().map(|&x| x * 2).collect();

// ✅ 好：链式操作，单次迭代
let result: Vec<i32> = data.iter()
    .filter(|&&x| x > 0)
    .map(|&x| x * 2)
    .collect();
```

### 2. 字符串操作优化

```rust
// ❌ 不好：多次分配
let mut result = String::new();
for word in words {
    result.push_str(word);
    result.push(' ');
}

// ✅ 好：预分配容量
let capacity = words.iter().map(|s| s.len() + 1).sum();
let mut result = String::with_capacity(capacity);
for word in words {
    result.push_str(word);
    result.push(' ');
}
```

### 3. 避免不必要的克隆

```rust
// ❌ 不好：克隆整个向量
fn process(data: Vec<i32>) -> Vec<i32> {
    data.clone().into_iter().filter(|&x| x > 0).collect()
}

// ✅ 好：使用引用
fn process(data: &[i32]) -> Vec<i32> {
    data.iter().filter(|&&x| x > 0).copied().collect()
}
```

### 4. 使用 SIMD（单指令多数据）

```rust
// 对于大规模数值计算，考虑使用 SIMD
use std::simd::*;

fn sum_simd(data: &[f32]) -> f32 {
    // 使用 SIMD 加速求和
    // 性能提升可达 4-8x
}
```

## 🎯 性能目标

### WASM 环境性能目标

| 操作类型 | 目标性能 | 备注 |
| --- | --- | --- |
| 简单算术 | < 10ns | 如加法、比较 |
| 数组遍历 | < 1ns/元素 | 线性时间 |
| 字符串操作 | < 2ns/字符 | 取决于操作复杂度 |
| 对象创建 | < 100ns | 工厂/建造者模式 |
| 函数调用 | < 5ns | 内联后可能为零 |
| JS 互操作 | < 100ns | wasm-bindgen 开销 |

### 性能回归检测

在 CI/CD 中集成基准测试：

```yaml
# .github/workflows/bench.yml
name: Benchmark
on: [push, pull_request]

jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions-rs/toolchain@v1
        with:
          toolchain: stable

      - name: Run benchmarks
        run: cargo bench

      - name: Store benchmark results
        uses: benchmark-action/github-action-benchmark@v1
        with:
          tool: 'cargo'
          output-file-path: target/criterion/*/new/estimates.json
```

## 📚 参考资源

### 工具和库

- [Criterion.rs](https://github.com/bheisler/criterion.rs) - 统计基准测试框架
- [cargo-flamegraph](https://github.com/flamegraph-rs/flamegraph) - 火焰图生成
- [cargo-benchcmp](https://github.com/BurntSushi/cargo-benchcmp) - 比较基准测试结果

### 性能优化指南

- [The Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [WASM Performance Guide](https://rustwasm.github.io/docs/book/reference/code-size.html)
- [Criterion User Guide](https://bheisler.github.io/criterion.rs/book/)

### 最佳实践

- 始终在 release 模式下运行基准测试
- 多次运行以获得稳定结果
- 关闭后台应用以减少干扰
- 使用相同的硬件进行对比

---

**最后更新**: 2025-12-11
**Criterion 版本**: 0.5.x
**Rust 版本**: 1.92.0+
