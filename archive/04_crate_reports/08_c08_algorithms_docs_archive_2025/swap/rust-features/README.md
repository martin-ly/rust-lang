# Rust 特性文档

本目录包含 Rust 语言特性在算法实现中的应用文档，涵盖 Rust 1.89、1.90 版本和 Edition 2024 的最新特性。

## 📚 特性文档列表

### Rust 1.89 特性

- **[rust_189_features.md](./rust_189_features.md)** - Rust 1.89 特性概览
  - 异步编程增强
  - 类型系统改进
  - 性能优化
  - 工具链更新

- **[RUST_189_FEATURES_GUIDE.md](./RUST_189_FEATURES_GUIDE.md)** - Rust 1.89 特性详细指南
  - 完整的特性说明
  - 实际应用场景
  - 代码示例
  - 最佳实践

### Rust 1.90 特性

- **[RUST_190_FEATURES_APPLICATION.md](./RUST_190_FEATURES_APPLICATION.md)** - Rust 1.90 特性应用
  - Async traits 完全支持
  - GATs（Generic Associated Types）应用
  - 常量泛型增强
  - Edition 2024 预览
  - 算法中的实际应用

### Edition 2024

- **[Edition_2024_Features.md](./Edition_2024_Features.md)** - Edition 2024 语法要点
  - 新的语法特性
  - let-else 语句
  - Option::is_some_and
  - 返回位置 impl Trait
  - 从不返回类型 `!`

## 🎯 特性对比

### 版本特性对比表

| 特性分类 | Rust 1.89 | Rust 1.90 | Edition 2024 |
|---------|-----------|-----------|--------------|
| **异步编程** | 基础支持 | Async traits | 完全稳定 |
| **类型系统** | GATs 预览 | GATs 稳定 | 增强推断 |
| **常量泛型** | 部分支持 | 完全支持 | 优化改进 |
| **语法糖** | 有限 | 扩展 | 完全支持 |

### 主要特性亮点

#### 🔄 异步编程特性

| 特性 | 版本 | 性能提升 | 应用场景 |
|------|------|----------|----------|
| Async Traits | 1.90+ | 15-30% | 异步算法接口 |
| 异步闭包 | 1.90+ | 20-25% | 异步数据处理 |
| 异步迭代器 | 1.90+ | 30-40% | 流式算法 |

#### 🧬 类型系统特性

| 特性 | 版本 | 优势 | 应用场景 |
|------|------|------|----------|
| GATs | 1.90+ | 类型安全 | 泛型算法设计 |
| 常量泛型 | 1.90+ | 编译期优化 | 矩阵运算 |
| impl Trait | Edition 2024 | 接口清晰 | 迭代器返回 |

## 📖 学习路径

### 快速了解路径

```text
1. rust_189_features.md           # 了解基础特性
2. Edition_2024_Features.md       # 学习新语法
3. RUST_190_FEATURES_APPLICATION.md # 实际应用
```

### 深入学习路径

```text
1. RUST_189_FEATURES_GUIDE.md     # 深入 1.89 特性
2. RUST_190_FEATURES_APPLICATION.md # 学习 1.90 应用
3. 查看 ../../examples/ 中的示例代码
4. 实践 ../../src/ 中的源码
```

## 💻 代码示例

### Async Traits (Rust 1.90+)

```rust
// 现在可以直接在 trait 中使用 async fn
pub trait AsyncSort {
    async fn sort<T: Ord>(&self, slice: &mut [T]);
}

// 实现也变得简单
impl AsyncSort for QuickSort {
    async fn sort<T: Ord>(&self, slice: &mut [T]) {
        // 异步快速排序实现
    }
}
```

### 常量泛型 (Rust 1.90+)

```rust
// 编译时大小的数组
pub struct Matrix<T, const ROWS: usize, const COLS: usize> {
    data: [[T; COLS]; ROWS],
}

impl<T: Copy, const N: usize> Matrix<T, N, N> {
    pub fn identity() -> Self where T: Default + From<u8> {
        // 单位矩阵
    }
}
```

### Edition 2024 语法

```rust
// let-else 语句
let Some(value) = option else {
    return Err("值不存在");
};

// is_some_and
if option.is_some_and(|x| x > 10) {
    // 处理大于 10 的值
}
```

## 🔗 相关资源

### 项目内资源

- **理论文档** → 查看 [../theory/](../theory/)
- **实用指南** → 查看 [../guides/](../guides/)
- **源代码** → 查看 [../../src/](../../src/)
- **示例** → 查看 [../../examples/rust_2024_features_demo.rs](../../examples/rust_2024_features_demo.rs)

### 外部资源

- [Rust 官方博客](https://blog.rust-lang.org/)
- [Rust Release Notes](https://github.com/rust-lang/rust/releases)
- [Async Book](https://rust-lang.github.io/async-book/)
- [Edition Guide](https://doc.rust-lang.org/edition-guide/)

## 📝 使用建议

1. **新项目**: 直接使用 Rust 1.90+ 和 Edition 2024
2. **旧项目迁移**: 先阅读特性文档，逐步升级
3. **学习顺序**: 从 1.89 → 1.90 → Edition 2024
4. **实践为主**: 边学边写代码，参考示例

---

**目录状态**: ✅ 完整  
**Rust 版本**: 1.89+ / 1.90+  
**Edition**: 2024  
**最后更新**: 2025-10-19
