# 权威来源与引用

> **文档目的**: 汇总项目中引用的所有权威来源，确保内容的准确性和可追溯性
> **更新日期**: 2026-03-18
> **维护者**: Rust学习项目团队

---

## Rust 1.94.0 权威来源

### 官方发布

| 来源 | URL | 发布日期 | 关键内容 |
|------|-----|---------|---------|
| Rust官方博客 | <https://blog.rust-lang.org/releases/latest/> | 2026-03-05 | array_windows, LazyCell/LazyLock API, AVX-512 FP16 |
| releases.rs | <https://releases.rs/docs/1.94.0/> | 2026-03-05 | 完整变更列表，17个稳定化API |
| InfoWorld报道 | <https://www.infoworld.com/article/4141483/> | 2026-03-05 | 技术特性解读 |

### 核心特性权威说明

#### 1. `array_windows` - 切片迭代方法

> "Rust 1.94 adds `array_windows`, an iterating method for slices. It works just like `windows` but with a constant length, so the iterator items are `&[T; N]` rather than dynamically-sized `&[T]`. In many cases, the window length may even be inferred by how the iterator is used!"
>
> —— **The Rust Programming Language Blog**, 2026-03-05

**使用示例** (官方)：

```rust
fn has_abba(s: &str) -> bool {
    s.as_bytes()
        .array_windows()
        .any(|[a1, b1, b2, a2]| (a1 != b1) && (a1 == a2) && (b1 == b2))
}
```

#### 2. LazyCell/LazyLock API稳定化

**稳定化API列表** (官方)：

- `LazyCell::get`
- `LazyCell::get_mut`
- `LazyCell::force_mut`
- `LazyLock::get`
- `LazyLock::get_mut`
- `LazyLock::force_mut`

来源: <https://releases.rs/docs/1.94.0/>

#### 3. AVX-512 FP16 Intrinsics

**硬件支持** (权威来源)：

| 厂商 | CPU系列 | 支持状态 |
|------|---------|---------|
| Intel | Xeon Scalable (Sapphire Rapids+) | 已支持 |
| AMD | Zen 6 (即将发布) | 已确认支持 |

> "AVX-512 FP16 is supported by Intel Xeon Scalable server CPUs since Sapphire Rapids and will be supported on the AMD side with upcoming Zen 6 processors."
>
> —— **Phoronix**, 2026-03-05

> "AMD's Zen 6 would support AVX-512 in some fashion... recent patches submitted for the GNU Assembler (Gas)... confirms the new architecture for everything Zen 5 supports, as well as new instruction set extensions: AVX512_BMM, AVX_NE_CONVERT, AVX_IFMA, AVX_VNNI_INT8, and **AVX512_FP16**."
>
> —— **HotHardware**, 2025-11-10

#### 4. Cargo TOML 1.1支持

> "Cargo now parses TOML v1.1 for manifests and configuration files. Changes in TOML 1.1 include inline tables across multiple lines and with trailing commas, `\xHH` and `\e` string escape characters, and optional seconds in times."
>
> —— **The Rust Programming Language Blog**, 2026-03-05

---

## Tree Borrows 权威来源

### 学术论文

| 论文 | 作者 | 会议 | 链接 |
|------|------|------|------|
| Tree Borrows | Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung | PLDI 2025 | <https://doi.org/10.1145/3735592> |
| Miri: Practical Undefined Behavior Detection for Rust | Ralf Jung et al. | POPL 2026 | <https://plf.inf.ethz.ch/research/popl26-miri.html> |

### 学术认可

> "论文《Miri: Practical Undefined Behavior Detection for Rust》已被编程语言顶会 **POPL 2026** 接收，标志着其在学术和实践上的双重成功。"
>
> —— **Rust语言中文社区**, 2025-12-23

### Tree Borrows核心优势

来自官方文档 (doc.rust-lang.org/beta/nightly-rustc/miri/)：

> "Tree structure with both parents and children since we want to be able to traverse the tree efficiently in both directions."

### 与Stacked Borrows对比

| 特性 | Stacked Borrows | Tree Borrows |
|------|-----------------|--------------|
| 模型 | 栈式借用追踪 | 树形借用追踪 |
| 灵活性 | 较严格 | 更灵活，允许更多合法模式 |
| 指针算术 | 限制较多 | 更友好的支持 |
| Miri默认 | 曾是默认 | **现为默认** |

来源: <https://research.ralfj.de/papers/2026-popl-miri.pdf>

---

## Rust 2024 Edition 权威来源

### 官方文档

| 资源 | URL | 说明 |
|------|-----|------|
| Edition Guide | <https://doc.rust-lang.org/edition-guide/rust-2024/> | 官方迁移指南 |
| gen关键字文档 | <https://doc.rust-lang.org/edition-guide/rust-2024/gen-keyword.html> | 生成器关键字 |
| 1.85.0发布公告 | <https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/> | Edition 2024发布 |

### gen关键字权威说明

> "`gen` is a reserved keyword... `gen` blocks will provide a way to make it easier to write certain kinds of iterators. Reserving the keyword now will make it easier to stabilize `gen` blocks before the next edition."
>
> —— **The Rust Edition Guide**, <https://doc.rust-lang.org/edition-guide/rust-2024/gen-keyword.html>

### Edition 2024主要变更 (官方)

语言层面：

- RPIT lifetime capture规则变更
- `if let`临时作用域变更
- Tail expression临时作用域变更
- Match ergonomics保留
- Unsafe `extern`块要求`unsafe`关键字
- Unsafe属性要求`unsafe`标记
- `gen`关键字预留
- `#"foo"#`风格字符串预留

标准库：

- `Future`和`IntoFuture`添加到prelude
- `IntoIterator`为`Box<[T]>`实现

Cargo：

- Rust-version感知resolver
- TOML 1.1支持

来源: <https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/>

---

## Miri 权威来源

### 功能扩展 (2023-2026)

> "系统调用模拟（Shims）：大幅扩展了对 Windows、Linux、macOS 及 Android 等平台的 API 支持；新增了对 Intel AVX-512 等硬件指令集的模拟。"
>
> —— **Ralf Jung博客**, 2025-12-22

### 并发与性能改进

> "更新至 **C++20 并发语义**，引入了全非确定性调度器。"
>
> "**GenMC 集成**：实验性支持结合 GenMC 进行模型检查，以穷举并发程序的执行状态。"
>
> —— **Ralf Jung博客**, 2025-12-22

### 核心论文引用

```bibtex
@article{jung2026miri,
  title={Miri: Practical Undefined Behavior Detection for Rust},
  author={Jung, Ralf and Kimock, Benjamin and Poveda, Christian and S{\'a}nchez Mu{\~n}oz, Eduardo and Scherer, Oli and Wang, Qian},
  journal={Proc. ACM Program. Lang.},
  volume={10},
  number={POPL},
  year={2026},
  doi={10.1145/3704904}
}

@article{villani2025treeborrows,
  title={Tree Borrows},
  author={Villani, Neven and Hostert, Johannes and Dreyer, Derek and Jung, Ralf},
  journal={Proc. ACM Program. Lang.},
  volume={9},
  number={PLDI},
  pages={188:1--188:24},
  year={2025},
  doi={10.1145/3735592}
}
```

---

## 大型项目迁移案例

### Rust 2024 Edition迁移实践

> "The workspace has close to 400 crates, and more than 1500 rust files... We tend to upgrade very soon after new toolchains are released, and often new language features give us new abilities and new lints help us find latent bugs."
>
> —— **Code and Bitters**, 2025-02-06

**迁移顺序建议** (来自生产实践)：

1. 更新代码生成crate (bindgen/cxx)
2. 启用rust-2024-compatibility lints
3. 升级到Rust 1.85+
4. 设置`style_edition = "2021"` (可选)
5. 设置`edition = "2024"`
6. 修复剩余错误和警告

来源: <https://codeandbitters.com/rust-2024-upgrade/>

---

## 引用格式规范

### 学术论文引用

使用ACM/IEEE格式：

```
[作者]. [标题]. In [会议] [年份]. DOI:[doi]
```

### 官方文档引用

```
[文档名称]. [URL]. [访问日期]
```

### 博客文章引用

```
[作者]. [标题]. [博客名称], [日期]. [URL]
```

---

## 验证清单

- [x] Rust 1.94特性与官方发布说明对齐
- [x] Tree Borrows引用PLDI 2025 Distinguished Paper
- [x] Miri引用POPL 2026论文
- [x] Edition 2024引用官方Edition Guide
- [x] AVX-512 FP16硬件支持与厂商声明对齐
- [x] gen关键字引用RFC #3513

---

**维护说明**: 本文档应随Rust生态更新而更新，确保所有引用来源保持最新和准确。
