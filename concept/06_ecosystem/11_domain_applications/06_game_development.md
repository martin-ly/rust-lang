# Rust 游戏开发（已合并）

> **EN**: Game Development (Merged Redirect)
> **Bloom 层级**: L5-L6
> **Summary**: Merged Redirect stub — this page has been merged into the canonical Game Development page at `concept/06_ecosystem/11_domain_applications/05_game_development.md`.
> **权威来源**: 本主题已合并至同目录唯一权威页：
> [`05_game_development.md`](05_game_development.md)
>
> 根据 AGENTS.md §2 Canonical 规则，同一概念只能有一个权威页；本文件与原
> `05_game_development.md` 为同目录同主题双文件（EN 标题均为 Game Development，
> 内容均覆盖 ECS 架构、wgpu 渲染、音频/输入、反命题与边界测试），已于 2026-07-12 合并。
>
> **合并说明**: 本页独有内容（winit 窗口/输入层、gltf 资产管道、hecs 轻量 ECS、
> 热重载工程折衷、archetype 变更/序列化循环引用（Reference）等边界场景）已以「补充生态工具」
> 形式迁入权威页的「六、来源与延伸阅读」一节；进阶边界场景指向
> [ECS 架构](02_game_ecs.md) 与 [游戏引擎内部机制](15_game_engine_internals.md)。
> 本文件保留路径作为重定向 stub，不再维护重复正文。
> **前置概念**: [Game ECS](02_game_ecs.md)
> **后置概念**: [Game Engine Internals](15_game_engine_internals.md)
>
>
> **受众**: [进阶]
> **内容分级**: [综述级]
>
> ---
>
> ## 国际权威参考 / International Authority References（P0 · P1 · P2）
>
> > 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。
>
> - **P0 官方**: [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)
> - **P1 学术/形式化**: [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
> - **P2 生态/社区**: [docs.rs/bevy](https://docs.rs/bevy) · [docs.rs/wgpu](https://docs.rs/wgpu)

---

## 知识表征：游戏技术栈选型决策树（重定向页速查）

> 本页为合并重定向 stub，正文权威内容见 [`05_game_development.md`](05_game_development.md)；本节仅提供选型速查与可编译的循环骨架示例（rustc 1.99.0，Edition 2024 实测）。

### 决策树：游戏项目该选哪条技术栈？

```text
要做什么类型的游戏/工具？
├─ 完整游戏框架（ECS + 渲染 + 音频 + 热重载开箱即用）
│    → Bevy（MIT/Apache-2.0；官方书 bevyengine.org/learn）
├─ 只要跨平台 GPU 渲染层，引擎逻辑自己写？
│    → wgpu-rs（WebGPU 语义， Vulkan/Metal/DX12/WebGPU 后端）
├─ 窗口 + 输入自己管，渲染走 wgpu？
│    → winit（事件循环模型：WindowEvent 回调驱动）
├─ 原型 / 教学 / 小游戏（不想碰 ECS 与渲染管线）
│    → macroquad（单 crate，立即模式绘图）
├─ 已有自研引擎，只补 ECS 数据层？
│    → hecs（轻量 archetype ECS）或自实现（见 02_game_ecs.md）
└─ 确定性回放 / lockstep 联网？
     → 必须固定时间步长模拟（下方骨架），禁止用帧间隔直接驱动物理
```

### 骨架：固定时间步长游戏循环（可编译，纯 std）

```rust
use std::time::{Duration, Instant};

fn main() {
    let dt = 1.0 / 60.0; // 固定模拟步长（秒）：确定性回放的前提
    let frame_budget = Duration::from_millis(20); // 模拟慢帧：每帧至少 1 个固定步
    let mut last = Instant::now();
    let mut acc = 0.0_f64;
    let mut steps = 0u32;
    let mut frames = 0;
    while frames < 10 {
        std::thread::sleep(frame_budget);
        let now = Instant::now();
        acc += now.duration_since(last).as_secs_f64();
        last = now;
        while acc >= dt {      // 每帧可跑 0..N 个固定步：物理与帧率解耦
            steps += 1;        // ← 固定步 update（物理/模拟）放这里
            acc -= dt;
        }
        let _alpha = acc / dt; // 渲染插值系数 ∈ [0,1)
        frames += 1;           // ← render 放这里
    }
    assert!(steps >= 10);
}
```

### 反例：组件按值传参后被再次使用（预期 E0382）

```rust,compile_fail,E0382
struct Position { x: f32 }
fn draw(p: Position) { let _ = p.x; } // p 按值接收 → move
fn main() {
    let p = Position { x: 1.0 };
    draw(p);
    draw(p); // ❌ p 已在第一次调用时被移动
}
```

**实测错误**：`error[E0382]: use of moved value: \`p\``。游戏循环里每帧复用组件时，参数应写 `&Position` 或让组件实现 `Copy`。

> **来源**: [Bevy 官方书](https://bevyengine.org/learn/) · [docs.rs/wgpu](https://docs.rs/wgpu) · [docs.rs/winit](https://docs.rs/winit) · [docs.rs/hecs](https://docs.rs/hecs) · [E0382 错误解释](https://doc.rust-lang.org/error_codes/E0382.html)
