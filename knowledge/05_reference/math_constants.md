# 数学常量

> **Rust 1.94 新增**
> **权威来源**: [std::f64::consts](https://doc.rust-lang.org/std/f64/consts/index.html)

## 🆕 新增常量 (Rust 1.94)

| 常量 | 值 | 说明 |
|------|-----|------|
| `EULER_GAMMA` | γ ≈ 0.5772 | 欧拉-马歇罗尼常数 |
| `GOLDEN_RATIO` | φ ≈ 1.6180 | 黄金比例 |
| `GOLDEN_RATIO_CONJUGATE` | Φ ≈ -0.6180 | 黄金比例共轭 |

## 使用示例

```rust
fn main() {
    // f64 常量
    println!("Euler's Gamma: {}", f64::EULER_GAMMA);
    println!("Golden Ratio: {}", f64::GOLDEN_RATIO);

    // f32 常量
    println!("Euler's Gamma (f32): {}", f32::EULER_GAMMA);
}
```

## 应用示例

### 黄金比例搜索

```rust
fn golden_section_search<F>(f: F, a: f64, b: f64, epsilon: f64) -> f64
where
    F: Fn(f64) -> f64,
{
    let phi = f64::GOLDEN_RATIO;
    let resphi = 2.0 - phi;

    let mut a = a;
    let mut b = b;
    let mut c = b - resphi * (b - a);
    let mut d = a + resphi * (b - a);

    while (b - a) > epsilon {
        if f(c) < f(d) {
            b = d;
        } else {
            a = c;
        }

        c = b - resphi * (b - a);
        d = a + resphi * (b - a);
    }

    (b + a) / 2.0
}

fn main() {
    let min = golden_section_search(|x| x * x - 2.0 * x + 1.0, -10.0, 10.0, 1e-6);
    println!("Minimum at: {}", min);  // 约 1.0
}
```

### 欧拉-马歇罗尼近似

```rust
fn harmonic_number(n: u64) -> f64 {
    (1..=n).map(|k| 1.0 / k as f64).sum()
}

fn main() {
    let n = 10000;
    let h_n = harmonic_number(n);
    let approx = f64::ln(n as f64) + f64::EULER_GAMMA;

    println!("H({}) = {}", n, h_n);
    println!("ln(n) + γ = {}", approx);
    println!("Difference: {}", (h_n - approx).abs());
}
```

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
