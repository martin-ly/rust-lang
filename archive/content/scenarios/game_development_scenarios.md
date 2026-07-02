# 游戏开发场景

> **Bloom 层级**: 应用 → 分析
> **来源: [Bevy Engine Documentation](https://bevyengine.org/)** · **[来源: wgpu]** · **来源: [Rust GameDev Working Group](https://gamedev.rs/)** ✅

---

## 场景 1：2D 独立游戏（Bevy）

**背景**: 使用 Bevy ECS 架构开发 2D 平台跳跃游戏。

**约束**:

- 目标平台: Windows/macOS/Linux + Web (WASM)
- 帧率: 60 FPS 稳定
- 实体数量: 1000+（敌人、粒子、道具）

**Rust 方案**:

```rust
use bevy::prelude::*;

// ECS 组件
#[derive(Component)]
struct Player {
    speed: f32,
    health: i32,
}

#[derive(Component)]
struct Velocity(Vec2);

// 系统：玩家移动
fn player_movement(
    mut query: Query<(&Player, &mut Velocity, &mut Transform)>,
    input: Res<ButtonInput<KeyCode>>,
    time: Res<Time>,
) {
    for (player, mut velocity, mut transform) in &mut query {
        let mut direction = Vec2::ZERO;

        if input.pressed(KeyCode::ArrowLeft) {
            direction.x -= 1.0;
        }
        if input.pressed(KeyCode::ArrowRight) {
            direction.x += 1.0;
        }

        velocity.0 = direction.normalize_or_zero() * player.speed;
        transform.translation += velocity.0.extend(0.0) * time.delta_seconds();
    }
}

// 系统：碰撞检测
fn collision_detection(
    mut player_query: Query<(&Transform, &mut Player), With<Player>>,
    enemy_query: Query<&Transform, With<Enemy>>,
) {
    for (player_transform, mut player) in &mut player_query {
        for enemy_transform in &enemy_query {
            if player_transform.translation.distance(enemy_transform.translation) < 32.0 {
                player.health -= 1;
            }
        }
    }
}
```

**关键决策**:

- 引擎: Bevy（数据驱动 ECS，编译期系统调度）
- 渲染: wgpu（跨平台 GPU API）
- 音频: `bevy_kira_audio`

---

## 场景 2：自定义渲染引擎（wgpu）

**背景**: 需要自定义渲染管线的 3D 可视化工具。

**Rust 方案**:

```rust
use wgpu::{Device, Queue, Surface, RenderPipeline};

struct Renderer {
    device: Device,
    queue: Queue,
    surface: Surface<'static>,
    pipeline: RenderPipeline,
}

impl Renderer {
    fn render(&self) {
        let output = self.surface.get_current_texture().unwrap();
        let view = output.texture.create_view(&Default::default());

        let mut encoder = self.device.create_command_encoder(&Default::default());
        {
            let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("Render Pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: &view,
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Clear(wgpu::Color::BLACK),
                        store: wgpu::StoreOp::Store,
                    },
                })],
                ..Default::default()
            });
            render_pass.set_pipeline(&self.pipeline);
            render_pass.draw(0..3, 0..1); // 三角形
        }

        self.queue.submit(std::iter::once(encoder.finish()));
        output.present();
    }
}
```

**关键决策**:

- 渲染: wgpu（WebGPU 标准，Vulkan/Metal/DX12 抽象）
- 着色器: WGSL 或 SPIR-V
- 跨平台: Windows/macOS/Linux/Web/iOS/Android

---

## 场景 3：多人联机游戏网络层

**背景**: 实时多人游戏（如 .io 类型），100 玩家同屏。

**约束**:

- 延迟: < 100ms（客户端预测 + 服务端校验）
- 带宽: < 20KB/s 每玩家
- 反作弊: 服务端权威

**Rust 方案**:

```rust
use tokio::net::UdpSocket;
use bincode::{encode_into_std_write, decode_from_std_read};

// 紧凑二进制协议
#[derive(Encode, Decode)]
struct PlayerInput {
    frame: u32,
    buttons: u8,      // 位掩码: WASD + 动作
    aim_angle: u16,   // 0-65535 映射到 0-2π
}

async fn game_server() {
    let socket = UdpSocket::bind("0.0.0.0:7777").await.unwrap();
    let mut buf = [0u8; 1024];

    loop {
        let (len, addr) = socket.recv_from(&mut buf).await.unwrap();
        let input: PlayerInput = bincode::decode(&buf[..len]).unwrap();

        // 服务端权威校验
        if validate_input(&input) {
            apply_input(input, addr);
        }
    }
}
```

**关键决策**:

- 网络: `tokio` + 自定义 UDP 协议
- 序列化: `bincode` 或 `bitcode`（最小带宽）
- 架构: 客户端预测 + 服务端回滚（GGPO 风格）

---

## Rust 游戏开发生态

| 领域 | 推荐 Crate | 说明 |
|:---|:---|:---|
| **引擎** | Bevy | ECS 架构，数据驱动 |
| **渲染** | wgpu | WebGPU 原生 |
| **物理** | Rapier | 2D/3D 刚体 + 流体 |
| **音频** | kira | 交互式音频 |
| **输入** | winit | 跨平台窗口/输入 |
| **资产** | bevy_asset | 热重载 |
| **网络** | tokio + Quinn | 异步 + QUIC |
| **UI** | bevy_ui / egui | 游戏内 UI |

---

> **文档版本**: 1.0
> **最后更新**: 2026-05-21
> **状态**: ✅ 初版完成
