#!/usr/bin/env python3
"""
为 L6 缺示例文件补充核心代码示例，替换"社区贡献欢迎"标记。
"""

import re
from pathlib import Path

ROOT = Path("e:/_src/rust-lang")

# 每个文件的代码示例（插入到"社区贡献欢迎"标记位置）
EXAMPLES = {
    "concept/06_ecosystem/09_cargo_script.md": """
## 代码示例：Cargo Script 单文件程序

以下是一个完整的 Cargo Script 示例，演示 frontmatter 依赖声明与单文件执行：

```rust,ignore
#!/usr/bin/env cargo
```cargo
[package]
name = "csv-filter"
edition = "2024"

[dependencies]
clap = { version = "4", features = ["derive"] }
chrono = "0.4"
```

use clap::Parser;
use chrono::Local;

#[derive(Parser)]
struct Args {
    #[arg(help = "输入 CSV 文件路径")]
    input: String,
    #[arg(short, long, default_value = "output.csv")]
    output: String,
}

fn main() {
    let args = Args::parse();
    println!("[{}] 处理: {} -> {}", Local::now(), args.input, args.output);
    // 实际过滤逻辑...
}
```

运行方式：
```bash
# 直接执行（Rust 1.79+）
cargo run --manifest-path csv_filter.rs

# 或赋予执行权限后运行
chmod +x csv_filter.rs && ./csv_filter.rs
```
""",

    "concept/06_ecosystem/10_public_private_deps.md": """
## 代码示例：Public/Private Dependencies 配置

以下 `Cargo.toml` 演示如何显式控制依赖可见性，避免"依赖泄漏"：

```toml
[package]
name = "my-api"
version = "0.1.0"
edition = "2024"

[dependencies]
# public = true: 下游 crate 可通过本 crate 的公共 API 使用 serde
serde = { version = "1.0", features = ["derive"], public = true }

# public = false (默认): 仅限内部使用，不暴露给下游
thiserror = "2.0"

[features]
default = []
std = ["serde/std"]
```

编译器可见性规则效果：
```rust,ignore
// 下游 crate 使用 my-api
use my_api::SomeStruct;

// ✅ 可以，因为 serde 被标记为 public
let _ = serde_json::to_string(&s);

// ❌ 编译错误：thiserror 是 private dependency
// use my_api::thiserror::Error; // error: thiserror is private
```
""",

    "concept/06_ecosystem/39_os_kernel.md": """
## 代码示例：最小 `no_std` 内核入口

以下展示一个极简的裸机 Rust 内核启动框架（基于 `riscv64`）：

```rust,ignore
#![no_std]
#![no_main]

use core::panic::PanicInfo;

// 内核入口点
#[no_mangle]
pub extern "C" fn _start() -> ! {
    // 初始化 UART 串口输出
    unsafe {
        let uart = 0x1000_0000 as *mut u8;
        for b in b"Hello from Rust kernel!\n" {
            uart.write_volatile(*b);
        }
    }
    loop {}
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
```

对应 `.cargo/config.toml`：
```toml
[build]
target = "riscv64gc-unknown-none-elf"

[target.riscv64gc-unknown-none-elf]
rustflags = ["-C", "link-arg=-Tsrc/linker.ld"]
```
""",

    "concept/06_ecosystem/45_compiler_internals.md": """
## 代码示例：自定义过程宏（编译器插件雏形）

以下演示如何通过过程宏实现编译期代码生成，这是深入 Rust 编译器内部的入口：

```rust,ignore
// proc-macro crate: trace_var
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn trace_var(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let fn_name = &input.sig.ident;
    let fn_body = &input.block;

    let expanded = quote! {
        fn #fn_name() {
            println!("[TRACE] Entering {}", stringify!(#fn_name));
            #fn_body
            println!("[TRACE] Exiting {}", stringify!(#fn_name));
        }
    };
    expanded.into()
}
```

使用方式：
```rust,ignore
use trace_var::trace_var;

#[trace_var]
fn compute() -> i32 {
    let x = 1 + 2;
    x * 3
}
```
""",

    "concept/06_ecosystem/48_industrial_case_studies.md": """
## 代码示例：工业级并发流水线（日志 ETL）

以下展示基于通道的无锁并发流水线模式，典型用于工业级日志/数据 ETL：

```rust,ignore
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread;

// Stage 1: 解析原始日志行
fn parser_stage(input: Receiver<String>, output: Sender<LogEntry>) {
    for line in input {
        if let Ok(entry) = parse_log(&line) {
            let _ = output.send(entry);
        }
    }
}

// Stage 2: 过滤与聚合
fn filter_stage(input: Receiver<LogEntry>, output: Sender<Metric>) {
    let mut counter = 0u64;
    for entry in input {
        if entry.level == "ERROR" {
            counter += 1;
        }
        if counter % 1000 == 0 {
            let _ = output.send(Metric::ErrorRate(counter));
        }
    }
}

// Stage 3: 输出到持久化存储
fn sink_stage(input: Receiver<Metric>) {
    for metric in input {
        persist_to_disk(metric);
    }
}
```
""",

    "concept/06_ecosystem/51_quantum_computing_rust.md": """
## 代码示例：量子门操作模拟（概念性实现）

以下展示用量子计算核心概念（叠加态、幺正变换）在 Rust 中的数学表达：

```rust,ignore
use nalgebra::{Matrix2, Vector2, Complex};

// 复数类型简写
type C = Complex<f64>;

/// 量子比特状态 |ψ⟩ = α|0⟩ + β|1⟩
struct Qubit {
    state: Vector2<C>,
}

impl Qubit {
    fn new(alpha: C, beta: C) -> Self {
        let state = Vector2::new(alpha, beta);
        // 归一化: |α|² + |β|² = 1
        assert!((state.norm_squared() - 1.0).abs() < 1e-9);
        Self { state }
    }

    /// 应用 Hadamard 门: H = 1/√2 [[1, 1], [1, -1]]
    fn hadamard(&mut self) {
        let h = C::new(1.0 / 2.0f64.sqrt(), 0.0);
        let gate = Matrix2::new(h, h, h, -h);
        self.state = gate * self.state;
    }

    /// 测量概率: P(|0⟩) = |α|²
    fn prob_zero(&self) -> f64 {
        self.state.x.norm_squared()
    }
}
```

> **注意**: 真实量子计算需要使用专用库（如 `qiskit-rust` 或 `qudit`），以上为数学原理演示。
""",

    "concept/06_ecosystem/53_embedded_graphics.md": """
## 代码示例：egui 即时模式 GUI（嵌入式场景）

以下演示使用 `egui` 在资源受限环境下构建交互式界面：

```rust,ignore
use egui::{Context, CentralPanel, Slider};

struct SensorApp {
    temperature: f32,
    threshold: f32,
}

impl eframe::App for SensorApp {
    fn update(&mut self, ctx: &Context, _frame: &mut eframe::Frame) {
        CentralPanel::default().show(ctx, |ui| {
            ui.heading("传感器监控面板");
            ui.add(Slider::new(&mut self.threshold, 0.0..=100.0)
                .text("报警阈值 (°C)"));

            let color = if self.temperature > self.threshold {
                egui::Color32::RED
            } else {
                egui::Color32::GREEN
            };
            ui.colored_label(color, format!("当前温度: {:.1}°C", self.temperature));
        });
    }
}
```

> **嵌入式约束**: 在 `no_std` 环境下，可使用 `embedded-graphics` + `lvgl` 替代 egui。
""",

    "concept/06_ecosystem/54_webassembly_advanced.md": """
## 代码示例：wasm-bindgen 高级 FFI 绑定

以下演示 Rust ↔ JavaScript 之间传递复杂数据结构，使用 `wasm-bindgen`：

```rust
use wasm_bindgen::prelude::*;
use serde::{Serialize, Deserialize};

#[wasm_bindgen]
#[derive(Serialize, Deserialize)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

#[wasm_bindgen]
pub struct GeometryEngine;

#[wasm_bindgen]
impl GeometryEngine {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self { Self }

    /// 计算两点间欧几里得距离
    pub fn distance(&self, a: &Point, b: &Point) -> f64 {
        ((b.x - a.x).powi(2) + (b.y - a.y).powi(2)).sqrt()
    }

    /// 批量处理（避免反复跨边界调用开销）
    pub fn batch_distances(&self, points_js: JsValue) -> Result<JsValue, JsValue> {
        let points: Vec<Point> = serde_wasm_bindgen::from_value(&points_js)?;
        let distances: Vec<f64> = points.windows(2)
            .map(|w| self.distance(&w[0], &w[1]))
            .collect();
        Ok(serde_wasm_bindgen::to_value(&distances)?)
    }
}
```

编译目标：`wasm32-unknown-unknown`
""",

    "concept/06_ecosystem/55_rust_for_data_science.md": """
## 代码示例：ndarray 数值计算与矩阵操作

以下演示 Rust 数据科学核心库 `ndarray` 的典型用法：

```rust
use ndarray::{Array2, Axis, array};

fn main() {
    // 创建 3×3 矩阵
    let a = array![[1.0, 2.0, 3.0],
                   [4.0, 5.0, 6.0],
                   [7.0, 8.0, 9.0]];

    // 按行求和
    let row_sums = a.sum_axis(Axis(1));
    println!("行和: {:?}", row_sums); // [6.0, 15.0, 24.0]

    // 逐元素乘法
    let b = array![[0.5, 1.0, 1.5],
                   [2.0, 2.5, 3.0],
                   [3.5, 4.0, 4.5]];
    let c = &a * &b;
    println!("逐元素乘: {:?}", c);

    // 切片: 提取子矩阵
    let sub = c.slice(ndarray::s![1..3, 0..2]);
    println!("子矩阵:\n{:?}", sub);
}
```

> **性能对比**: 上述操作在 release 模式下通过 SIMD 优化，单核性能接近 C/BLAS 级别。
""",
}


def replace_marker(path: Path, example: str) -> bool:
    """替换文件中的'社区贡献欢迎'标记为代码示例"""
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()

    # 匹配各种形式的社区贡献欢迎标记
    pattern = r'>\s*⚠️\s*\*\*\[社区贡献欢迎\]\*\*.*?\n'
    if not re.search(pattern, content):
        # 尝试更宽松的匹配
        pattern = r'>\s*⚠️\s*\*\*\[社区贡献欢迎\].*?(?:\n|$)'

    new_content, count = re.subn(pattern, example.lstrip() + "\n", content, count=1)
    if count == 0:
        print(f"  ⚠️ 未找到标记: {path}")
        return False

    with open(path, "w", encoding="utf-8") as f:
        f.write(new_content)
    return True


def main():
    for rel_path, example in EXAMPLES.items():
        path = ROOT / rel_path
        if path.exists():
            if replace_marker(path, example):
                print(f"  ✅ {rel_path}")
        else:
            print(f"  ❌ 文件不存在: {rel_path}")


if __name__ == "__main__":
    main()
