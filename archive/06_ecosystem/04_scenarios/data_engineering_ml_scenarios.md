# 数据工程与机器学习场景

> **Bloom 层级**: 应用 → 分析
> **[来源: Polars Documentation]** · **[来源: Apache Arrow]** · **[来源: ndarray crate]** · **[来源: candle (Hugging Face)]** ✅

---

## 场景 1：实时流数据处理管道

**背景**: 替代 Python pandas，处理每秒 10K+ 事件的实时数据流。

**约束**:

- 延迟: p99 < 50ms
- 吞吐量: 100K events/s 单核
- 内存: 流式处理，不缓存全量数据
- 查询: SQL-like 过滤 + 聚合

**Rust 方案**:

```rust
use polars::prelude::*;
use arrow::array::{StringArray, Float64Array};

fn process_stream(events: &[Event]) -> DataFrame {
    // 零拷贝 Arrow 内存格式
    let df = df! {
        "timestamp" => events.iter().map(|e| e.ts).collect::<Vec<_>>(),
        "user_id" => events.iter().map(|e| e.user_id.clone()).collect::<Vec<_>>(),
        "value" => events.iter().map(|e| e.value).collect::<Vec<_>>(),
    }.unwrap();

    // 流式聚合：窗口函数 + 分组
    df.lazy()
        .filter(col("value").gt(lit(100.0)))
        .group_by_dynamic(
            col("timestamp"),
            [],
            DynamicGroupOptions {
                every: Duration::new(5_000), // 5 秒窗口
                period: Duration::new(5_000),
                offset: Duration::new(0),
                truncate: false,
                include_boundaries: false,
                closed_window: ClosedWindow::Left,
                start_by: StartBy::DataPoint,
                ..Default::default()
            },
        )
        .agg([col("value").mean().alias("avg_value")])
        .collect()
        .unwrap()
}
```

**关键决策**:

- 框架: Polars（比 pandas 快 5–50x）
- 内存: Apache Arrow 列式格式（跨语言零拷贝）
- 流式: `polars-stream` 实验性流处理引擎

---

## 场景 2：边缘 ML 推理

**背景**: 在嵌入式设备上运行轻量级神经网络（图像分类）。

**约束**:

- 模型大小: < 10MB
- 推理延迟: < 100ms
- 无 GPU / 无 Python 运行时

**Rust 方案**:

```rust
use candle_core::{Device, Tensor, DType};
use candle_nn::Module;

fn classify_image(model: &dyn Module, image: &[f32]) -> Result<usize> {
    let device = Device::Cpu;
    let input = Tensor::from_slice(image, (1, 3, 224, 224), &device)?;

    // 前向传播
    let logits = model.forward(&input)?;
    let probs = candle_nn::ops::softmax(&logits, 1)?;

    // 取最大概率类别
    let max_idx = probs.argmax(1)?.to_scalar::<u32>()? as usize;
    Ok(max_idx)
}
```

**关键决策**:

- 框架: Candle（Hugging Face，纯 Rust）或 `tflite-rs`
- 量化: INT8 权重减少 4x 内存
- 目标: `no_std` + `alloc` 嵌入式环境

---

## 场景 3：科学计算与数值分析

**背景**: 替代 NumPy/SciPy，进行大规模矩阵运算和微分方程求解。

**Rust 方案**:

```rust
use ndarray::{Array2, Axis, s};
use ndarray_linalg::{Solve, Inverse};

fn linear_regression(x: &Array2<f64>, y: &Array2<f64>) -> Array2<f64> {
    // 正规方程: β = (X^T X)^(-1) X^T y
    let xt = x.t();
    let xtx = xt.dot(x);
    let xty = xt.dot(y);
    let beta = xtx.inv().unwrap().dot(&xty);
    beta
}

fn main() {
    let a = array![[1.0, 2.0], [3.0, 4.0]];
    let b = array![[5.0], [6.0]];
    let x = a.solve(&b).unwrap();
    println!("Solution: {:?}", x);
}
```

**关键决策**:

- 框架: `ndarray` + `ndarray-linalg`（BLAS/LAPACK 绑定）
- 性能: 与 NumPy 相当（均调用 BLAS）
- 安全: 编译期维度检查（`Array2` vs `Array3`）

---

## 工具生态矩阵

| 领域 | Python 工具 | Rust 替代 | 优势 |
|:---|:---|:---|:---|
| DataFrame | pandas | Polars | 5–50x 更快，流式，Arrow 原生 |
| 矩阵运算 | NumPy | ndarray | 类型安全，无 GIL |
| ML 推理 | PyTorch/TF | Candle, tflite-rs | 无 Python 依赖，边缘部署 |
| 特征工程 | scikit-learn | linfa | 纯 Rust，可嵌入 |
| 可视化 | matplotlib | plotters | 可编译为 WASM |
| ETL | Apache Spark | datafusion, ballista | 列式执行，向量化 |

---

> **文档版本**: 1.0
> **最后更新**: 2026-05-21
> **状态**: ✅ 初版完成
