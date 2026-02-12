# Bridge 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 结构型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Bridge 结构）**

设 $\mathcal{A}$ 为抽象类型，$\mathcal{I}$ 为实现类型。Bridge 满足：

- $\mathcal{A}$ 持有 $\mathcal{I}$：$\mathcal{A} \supset \mathcal{I}$
- 抽象与实现可独立变化；二者通过 trait 解耦
- trait 定义 $\mathcal{I}$，$\mathcal{A}$ 通过泛型 `T: Impl` 或 `Box<dyn Impl>` 使用

**Axiom BR1**：抽象与实现解耦，二者可独立扩展。

**Axiom BR2**：委托时借用：$\mathcal{A}.\mathit{op}$ 调用 $\mathcal{I}.\mathit{impl\_op}$，满足借用规则。

**定理 BR-T1**：由 [trait_system_formalization](../../../type_theory/trait_system_formalization.md)，trait 对象或泛型保证类型安全。

---

## Rust 实现与代码示例

```rust
trait Renderer {
    fn render_circle(&self, radius: f32);
}

struct VectorRenderer;
impl Renderer for VectorRenderer {
    fn render_circle(&self, radius: f32) {
        println!("Drawing circle (vector) r={}", radius);
    }
}

struct RasterRenderer;
impl Renderer for RasterRenderer {
    fn render_circle(&self, radius: f32) {
        println!("Drawing circle (raster) r={}", radius);
    }
}

struct Circle<R: Renderer> {
    radius: f32,
    renderer: R,
}

impl<R: Renderer> Circle<R> {
    fn new(radius: f32, renderer: R) -> Self {
        Self { radius, renderer }
    }
    fn draw(&self) {
        self.renderer.render_circle(self.radius);
    }
}

// 使用：抽象（Circle）与实现（Renderer）独立
let c = Circle::new(5.0, VectorRenderer);
c.draw();
```

**形式化对应**：`Circle` 即 $\mathcal{A}$；`Renderer` 即 $\mathcal{I}$；`draw` 委托 `renderer.render_circle`。

---

## 证明思路

1. **解耦**：`Circle` 不依赖具体 `VectorRenderer` 或 `RasterRenderer`；可替换。
2. **类型安全**：`R: Renderer` 约束保证 `render_circle` 存在；由 trait_system。

---

## 典型场景

| 场景 | 说明 |
|------|------|
| 渲染后端 | 向量/光栅、OpenGL/Vulkan |
| 存储抽象 | 内存/文件/网络 |
| 序列化 | JSON/MessagePack/Binary |
| 平台抽象 | Win/Mac/Linux 实现 |

---

## 相关模式

| 模式 | 关系 |
|------|------|
| [Adapter](adapter.md) | Bridge 解耦；Adapter 适配已有接口 |
| [Strategy](../03_behavioral/strategy.md) | 实现可视为策略 |
| [Abstract Factory](../01_creational/abstract_factory.md) | 工厂可创建抽象+实现组合 |

---

## 实现变体

| 变体 | 说明 | 适用 |
|------|------|------|
| 泛型 `A<R: Impl>` | 编译期；零成本 | 实现类型已知 |
| `Box<dyn Impl>` | 运行时多态 | 动态选择实现 |
| 枚举实现 | `enum Impl { A, B }` | 有限实现集 |

---

## 反例：抽象与实现紧耦合

**错误**：抽象类型直接依赖具体实现类型，无法替换。

```rust
struct BadCircle {
    renderer: VectorRenderer,  // 写死，无法换成 RasterRenderer
}
```

**后果**：违反 Axiom BR1；扩展需修改抽象类型。

---

## 选型决策树

```
抽象与实现需独立变化？
├── 是 → 实现类型有限？ → 泛型 `A<R: Impl>`（零成本）
│       └── 实现类型运行时决定？ → `Box<dyn Impl>`
├── 否 → 直接依赖具体类型
└── 仅适配已有接口？ → Adapter
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
|-----|-----------|------|
| 抽象类 + 实现类 | trait + impl | trait 无状态 |
| 继承层次 | 组合 + trait | 无继承 |
| 运行时绑定 | `Box<dyn Impl>` | 等价 |

---

## 边界

| 维度 | 分类 |
|------|------|
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
