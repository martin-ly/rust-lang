# nalgebra / ndarray Crate 架构解构

> **Bloom 层级**: L3 (高级应用) / L4 (数值计算类型系统)
> **目标读者**: 已掌握 Rust 泛型与 trait 系统，从事科学计算、图形学或机器学习基础设施的开发者
> [来源: nalgebra 官方文档](https://docs.rs/nalgebra/latest/nalgebra/)
> [来源: ndarray 官方文档](https://docs.rs/ndarray/latest/ndarray/)
> [来源: Rust Reference — Const Generics](https://doc.rust-lang.org/reference/items/generics.html#const-generics)

---

## 1. 引言
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

Rust 的科学计算生态虽然在成熟度上不及 Python 的 NumPy/SciPy，但在**类型安全与性能可预测性**方面具有独特优势。`nalgebra` 和 `ndarray` 是这一领域的两大基石库：

| 库 | 定位 | 核心抽象 | 最佳场景 |
|:---|:---|:---|:---|
| **nalgebra** | 线性代数 | `Matrix<T, R, C, S>` — 类型级维度 | 固定维度的几何/物理计算（3D 图形、机器人学） |
| **ndarray** | N 维数组 | `ArrayBase<S, D>` — 泛型存储与维度 | 通用数值计算、图像处理、与 BLAS 集成 |

两者共同展示了 Rust 类型系统的强大表达力：**在编译期验证矩阵维度匹配、在零运行时开销下提供视图抽象、通过特征门控可选地接入工业级 BLAS 后端**。

> [来源: nalgebra 文档 — Overview](https://www.nalgebra.org/)
> [来源: ndarray 文档 — ArrayBase](https://docs.rs/ndarray/latest/ndarray/struct.ArrayBase.html)

---

## 2. nalgebra 核心: 编译时矩阵维度
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

nalgebra 的设计目标是让矩阵运算在**编译期尽可能多地捕获错误**，尤其是维度不匹配错误。

### 2.1 `Matrix<T, R, C, S>` 四参数结构
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
pub struct Matrix<T, R, C, S>
where
    S: RawStorage<T, R, C>,
{
    data: S,
    _phantom: PhantomData<(T, R, C)>,
}
```

| 参数 | 含义 | 典型值 |
|:---|:---|:---|
| `T` | 元素类型 | `f32`, `f64`, `i32`, `Complex<f64>` |
| `R` | 行数 | `U2`, `U3`, `U4`, `Dynamic` |
| `C` | 列数 | `U2`, `U3`, `Dynamic` |
| `S` | 存储策略 | `MatrixArray` (栈), `MatrixVec` (堆) |

> [来源: nalgebra 源码 — `src/base/matrix.rs`]

### 2.2 类型级维度: `U2`, `U3`, `Dynamic`
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

nalgebra 使用类型来编码维度信息：

```rust,ignore
use nalgebra::{Matrix3, Matrix2x3, DMatrix, U3, Dynamic};

// 编译期已知维度 —— 存储在栈上
let a: Matrix3<f64> = Matrix3::new(
    1.0, 2.0, 3.0,
    4.0, 5.0, 6.0,
    7.0, 8.0, 9.0,
);

// 2x3 矩阵
let b: Matrix2x3<f64> = Matrix2x3::new(
    1.0, 2.0, 3.0,
    4.0, 5.0, 6.0,
);

// 动态维度 —— 运行时确定，存储在堆上
let c: DMatrix<f64> = DMatrix::from_element(100, 100, 0.0);
```

`U2`、`U3` 等是零大小类型 (ZST)，运行时不占空间，仅用于类型检查。

### 2.3 `DimName` Trait 与 Const Generics 演进
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

nalgebra 早期使用 `DimName` trait 实现类型级整数：

```rust,ignore
pub trait DimName: Any + Debug + Copy + PartialEq + 'static {
    type Value: Unsigned;
    fn name() -> Self::Value;
    fn dim() -> usize;
}

// 实现示例
impl DimName for U3 {
    type Value = U3;
    fn name() -> Self::Value { U3 }
    fn dim() -> usize { 3 }
}
```

Rust 1.51+ 引入 const generics 后，nalgebra 逐步引入了 `Const<N>` 作为现代替代方案：

```rust,ignore
use nalgebra::{SMatrix, Const};

// 使用 const generics (Rust 1.51+)
let m: SMatrix<f64, 3, 3> = SMatrix::identity();
// 等价于：Matrix<f64, Const<3>, Const<3>, _>
```

`Const<N>` 将编译期整数直接嵌入类型系统，比 `DimName` 更直接、更符合 Rust 语言演进方向。

> [来源: Rust Reference — Const Generics](https://doc.rust-lang.org/reference/items/generics.html#const-generics)
> [来源: nalgebra 文档 — Const generics](https://docs.rs/nalgebra/latest/nalgebra/base/dimension/struct.Const.html)

### 2.4 编译时维度检查
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

nalgebra 的核心价值在于：**矩阵维度不匹配是编译错误，而非运行时 panic**。

```rust,ignore
use nalgebra::{Matrix3, Vector3};

let m: Matrix3<f64> = Matrix3::identity();
let v: Vector3<f64> = Vector3::new(1.0, 2.0, 3.0);

// 编译通过：3x3 * 3x1 = 3x1
let result = m * v;

// 编译错误：若尝试 3x3 * 4x1
// let bad = m * Vector4::new(1.0, 2.0, 3.0, 4.0);
// ERROR: mismatched types: expected `Const<3>`, found `Const<4>`
```

---

## 3. ndarray 核心: 泛型存储与 N 维视图
>
> **[来源: [crates.io](https://crates.io/)]**

ndarray 的设计目标是**通用性**：支持任意维度、多种存储后端、零成本视图切片。

### 3.1 `ArrayBase<S, D>` 双参数结构
>
> **[来源: [docs.rs](https://docs.rs/)]**

```rust,ignore
pub struct ArrayBase<S, D>
where
    S: RawData,
    D: Dimension,
{
    data: S,
    dim: D,
    strides: D,
}
```

| 参数 | 含义 | 典型值 |
|:---|:---|:---|
| `S` | 数据存储 | `OwnedRepr<T>` (Vec), `ViewRepr<&T>`, `ViewRepr<&mut T>` |
| `D` | 维度类型 | `Ix1`, `Ix2`, `Ix3`, `IxDyn` |

> [来源: ndarray 源码 — `src/lib.rs`](https://docs.rs/ndarray/latest/src/ndarray/lib.rs.html)

### 3.2 存储抽象: 拥有、视图、可变视图
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

ndarray 通过 `S` 参数区分三种核心类型：

```rust,ignore
use ndarray::{Array1, Array2, ArrayView1, ArrayViewMut2, arr2};

// 拥有的数组 —— 类似 Vec
let owned: Array2<f64> = Array2::zeros((3, 4));

// 不可变视图 —— 零成本引用切片
let view: ArrayView2<f64> = owned.slice(s![..2, ..3]);

// 可变视图
let mut data = Array2::zeros((3, 4));
let mut_view: ArrayViewMut2<f64> = data.slice_mut(s![0..2, 0..2]);
```

**关键洞察**: `ArrayView` 不拥有数据，仅持有指向底层存储的指针、维度信息和 strides。创建视图是 O(1) 操作，没有数据复制。

### 3.3 `Dimension` Trait 与形状抽象
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
pub trait Dimension: Clone + Eq + Debug + Send + Sync + Default {
    fn ndim(&self) -> usize;
    fn size(&self) -> usize;
    fn default_strides(&self) -> Self;
    fn for_each<F>(&self, f: F)
    where
        F: FnMut(&Self);
    // ...
}
```

`Dimension` trait 使 ndarray 能够统一处理静态维度（`Ix1`, `Ix2`）和动态维度（`IxDyn`）：

```rust,ignore
use ndarray::{Array, ArrayD, IxDyn};

// 编译时 2D
let a2d = Array::zeros((3, 4));

// 运行时动态维度
let shape = vec![2, 3, 4];
let adyn: ArrayD<f64> = ArrayD::zeros(IxDyn(&shape));
```

> [来源: ndarray 文档 — Dimension trait](https://docs.rs/ndarray/latest/ndarray/trait.Dimension.html)

---

## 4. 类型系统利用
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 4.1 nalgebra: `Const<N>` 与 const generics
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
use nalgebra::{SVector, SMatrix, Const};

// 编译时确定维度的向量
let v: SVector<f64, 5> = SVector::from_fn(|i, _| i as f64);

// 编译时确定维度的矩阵
let m: SMatrix<f64, 2, 3> = SMatrix::from_fn(|r, c| (r + c) as f64);

// 类型别名简化
pub type Mat4<T> = SMatrix<T, 4, 4>;
let transform: Mat4<f64> = Mat4::identity();
```

`Const<N>` 的优势在于：**维度信息完全由编译期整数决定，不依赖复杂的类型级编程**，更易于阅读与维护。

### 4.2 ndarray: `Dimension` + 广播
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

ndarray 实现了 NumPy 风格的广播规则，但将其编码在类型系统中：

```rust,ignore
use ndarray::{Array2, Array1, arr1, arr2};

let a: Array2<f64> = arr2(&[[1.0, 2.0, 3.0],
                             [4.0, 5.0, 6.0]]); // shape (2, 3)
let b: Array1<f64> = arr1(&[10.0, 20.0, 30.0]); // shape (3,)

// 广播: (2, 3) + (3,) -> (2, 3)
let c = &a + &b;
assert_eq!(c.shape(), &[2, 3]);
```

广播规则在编译期部分验证，运行时检查剩余维度兼容性。

> [来源: ndarray 文档 — Broadcasting](https://docs.rs/ndarray/latest/ndarray/doc/ndarray/struct.ArrayBase.html#broadcasting)

---

## 5. BLAS 集成
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

纯 Rust 实现的线性代数在峰值性能上难以匹敌 decades 优化的 Fortran BLAS/LAPACK。nalgebra 和 ndarray 都通过可选特征门控接入这些工业级后端。

### 5.1 `ndarray-linalg`
>
> **[来源: [crates.io](https://crates.io/)]**

```tomoml
[dependencies]
ndarray = "0.15"
ndarray-linalg = { version = "0.16", features = ["openblas-static"] }
# 或 "intel-mkl-static", "netlib-static"
```

```rust,ignore
use ndarray::{array, Array2};
use ndarray_linalg::{Solve, Inverse, Eigh};

// 解线性方程组 A * x = b
let a: Array2<f64> = array![[3.0, 2.0], [2.0, -3.0]];
let b: Array2<f64> = array![[18.0], [3.0]];
let x = a.solve(&b).unwrap();

// 矩阵求逆
let a_inv = a.inv().unwrap();

// 特征值分解（对称矩阵）
let (eigvals, eigvecs) = a.eigh(ndarray_linalg::UPLO::Upper).unwrap();
```

> [来源: ndarray-linalg 文档](https://docs.rs/ndarray-linalg/latest/ndarray_linalg/)

### 5.2 `nalgebra-lapack`
>
> **[来源: [docs.rs](https://docs.rs/)]**

```toml
[dependencies]
nalgebra = "0.32"
nalgebra-lapack = "0.23"  # 绑定 LAPACK
```

nalgebra-lapack 为 nalgebra 的 `OMatrix`（ owned matrix ）类型提供 LAPACK 功能：SVD、QR、LU、Cholesky 分解等。

### 5.3 特征门控的设计优势
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```mermaid
flowchart LR
    subgraph RustCode["Rust 源代码"]
        PureRust["纯 Rust 回退实现"]
        BLAS["BLAS 后端 (可选)"]
    end

    subgraph Build["构建配置"]
        Features["features = []<br/>features = ['blas']"]
    end

    subgraph Runtime["运行时"]
        NoBLAS["无外依赖，可移植"]
        WithBLAS["链接 OpenBLAS/MKL/Netlib"]
    end

    Features -->|默认| PureRust --> NoBLAS
    Features -->|启用 BLAS| BLAS --> WithBLAS

    style BLAS fill:#c8e6c9
    style PureRust fill:#fff9c4
```

**关键设计**: 不启用 BLAS 时，代码仍可编译运行，使用纯 Rust 实现；启用后自动路由到优化后端。这使依赖 crate 无需强制下游链接系统库。

> [来源: BLAS Standard — Netlib](https://www.netlib.org/blas/)
> [来源: ndarray 文档 — BLAS Integration](https://docs.rs/ndarray/latest/ndarray/doc/ndarray/struct.ArrayBase.html#blas-integration)

---

## 6. 与 Python NumPy 的对比
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 维度 | nalgebra / ndarray | NumPy |
|:---|:---|:---|
| **类型安全** | 编译期维度检查；元素类型严格 | 运行时维度检查；动态类型 (`dtype`) |
| **所有权** | 显式所有权与生命周期；视图不拥有数据 | 引用计数 + GC；切片共享底层数据 |
| **广播规则** | ndarray 支持 NumPy 风格广播；nalgebra 更严格 | 灵活的广播规则 |
| **性能** | 零成本抽象；可选 BLAS；无 GIL | 底层 C 优化；受 GIL 限制（多线程扩展有限） |
| **错误处理** | 维度不匹配 = 编译错误（静态）或 `Result`（动态） | 运行时异常 (`ValueError`, `IndexError`) |
| **生态系统** | 较小但快速增长；ndarray 是 Rust ML 基础 | 极其成熟；SciPy, Pandas, scikit-learn 等 |
| **可移植性** | 静态链接；无 Python 依赖；适合嵌入式 | 需要 Python 运行时；体积较大 |
| **学习曲线** | 需要掌握 Rust 泛型与生命周期 | 更平缓；动态类型降低入门门槛 |

### 6.1 代码对比示例
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

**nalgebra（静态维度）**:

```rust,ignore
use nalgebra::Matrix3;

fn transform_point(m: &Matrix3<f64>, p: &Matrix3x1<f64>) -> Matrix3x1<f64> {
    m * p  // 编译时验证 3x3 * 3x1 合法
}
```

**ndarray（动态维度）**:

```rust,ignore
use ndarray::{Array2, ArrayView1};

fn transform_point(m: &Array2<f64>, p: &ArrayView1<f64>) -> ndarray::Result<Array2<f64>> {
    m.dot(&p.insert_axis(ndarray::Axis(1)))
}
```

**NumPy（Python）**:

```python
import numpy as np

def transform_point(m: np.ndarray, p: np.ndarray) -> np.ndarray:
    return m @ p  # 运行时验证维度
```

> [来源: NumPy 文档 — Broadcasting](https://numpy.org/doc/stable/user/basics.broadcasting.html)

---

## 7. 选择指南
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 场景 | 推荐库 | 原因 |
|:---|:---|:---|
| 3D 图形、物理仿真、机器人学 | **nalgebra** | 固定维度（3, 4, 6 DOF），编译时检查 invaluable |
| 通用数值计算、图像处理、信号处理 | **ndarray** | 灵活维度，视图切片，广播，BLAS 集成 |
| 机器学习模型推理 | **ndarray** + `tract` / `candle` | ndarray 是 Rust ML 生态的事实标准基础 |
| 嵌入式/无堆分配环境 | **nalgebra** (`SMatrix`) | 小矩阵可在栈上分配，无动态分配 |
| 与 Python 互操作 | **ndarray** + `numpy` crate | `numpy` crate 提供零拷贝 Python 数组视图 |

---

## 8. 来源
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 来源 | 类型 | 引用位置 |
|:---|:---|:---|
| [nalgebra 官方文档](https://www.nalgebra.org/) | 一级 | 全文 |
| [ndarray 官方文档](https://docs.rs/ndarray/latest/ndarray/) | 一级 | 全文 |
| [Rust Reference — Const Generics](https://doc.rust-lang.org/reference/items/generics.html#const-generics) | 一级 | 第 2、4 节 |
| [BLAS Standard (Netlib)](https://www.netlib.org/blas/) | 一级 | 第 5 节 |
| [LAPACK User's Guide](https://www.netlib.org/lapack/lug/) | 一级 | 第 5 节 |
| [NumPy 官方文档](https://numpy.org/doc/stable/) | 二级 | 第 6 节 |

---

> **相关文件**:
>
> - `docs/research_notes/software_design_theory/07_crate_architectures/10_tokio_architecture.md` — Tokio 运行时架构
> - `concept/02_intermediate/02_trait.md` — Trait 系统与泛型编程
> - `concept/02_intermediate/02_02_type_system.md` — Rust 类型系统深度解析
> - `crates/c04_generic/` — 泛型与 trait 边界实践 crate

---

## 相关架构与延伸阅读
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- 类型系统与所有权
- [泛型与特化](../../../../concept/02_intermediate/20_type_system_advanced.md)

---

## 权威来源索引

> **[来源: [crates.io](https://crates.io/)]**
>
> **[来源: [docs.rs](https://docs.rs/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-22 补全权威来源标注 [来源: Authority Source Sprint Batch 9]

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
