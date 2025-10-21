# 游戏开发 (Game Development)

**类别**: 领域特定 - 游戏  
**重要程度**: ⭐⭐⭐⭐⭐ (游戏开发必备)  
**更新日期**: 2025-10-20

---

## 📋 概述

Rust 游戏开发生态蓬勃发展，从 ECS 游戏引擎到物理引擎，从 2D 到 3D，提供了完整的游戏开发工具链。

---

## 🔧 核心工具

### 1. bevy (数据驱动游戏引擎 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add bevy`  
**用途**: 现代化的数据驱动游戏引擎

#### 核心特性

- ✅ ECS 架构 (Entity Component System)
- ✅ 数据驱动设计
- ✅ 模块化插件系统
- ✅ 2D 和 3D 支持

#### Hello World

```rust
use bevy::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        .add_systems(Update, hello_world_system)
        .run();
}

fn setup(mut commands: Commands) {
    // Spawn a camera
    commands.spawn(Camera2dBundle::default());
}

fn hello_world_system() {
    println!("Hello, Bevy!");
}
```

#### 2D 精灵示例

```rust
use bevy::prelude::*;

#[derive(Component)]
struct Player;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        .add_systems(Update, move_player)
        .run();
}

fn setup(mut commands: Commands, asset_server: Res<AssetServer>) {
    commands.spawn(Camera2dBundle::default());
    
    // Spawn player
    commands.spawn((
        SpriteBundle {
            texture: asset_server.load("player.png"),
            transform: Transform::from_xyz(0.0, 0.0, 0.0),
            ..default()
        },
        Player,
    ));
}

fn move_player(
    time: Res<Time>,
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut Transform, With<Player>>,
) {
    for mut transform in &mut query {
        let mut direction = Vec3::ZERO;
        
        if keyboard.pressed(KeyCode::KeyW) {
            direction.y += 1.0;
        }
        if keyboard.pressed(KeyCode::KeyS) {
            direction.y -= 1.0;
        }
        if keyboard.pressed(KeyCode::KeyA) {
            direction.x -= 1.0;
        }
        if keyboard.pressed(KeyCode::KeyD) {
            direction.x += 1.0;
        }
        
        if direction.length() > 0.0 {
            direction = direction.normalize();
        }
        
        transform.translation += direction * 100.0 * time.delta_seconds();
    }
}
```

#### 碰撞检测

```rust
use bevy::prelude::*;
use bevy::sprite::collide_aabb::collide;

#[derive(Component)]
struct Player {
    speed: f32,
}

#[derive(Component)]
struct Enemy;

fn collision_system(
    player_query: Query<(&Transform, &Sprite), With<Player>>,
    enemy_query: Query<(&Transform, &Sprite), With<Enemy>>,
) {
    for (player_transform, player_sprite) in player_query.iter() {
        let player_size = player_sprite.custom_size.unwrap_or(Vec2::ONE);
        
        for (enemy_transform, enemy_sprite) in enemy_query.iter() {
            let enemy_size = enemy_sprite.custom_size.unwrap_or(Vec2::ONE);
            
            let collision = collide(
                player_transform.translation,
                player_size,
                enemy_transform.translation,
                enemy_size,
            );
            
            if collision.is_some() {
                println!("Collision detected!");
            }
        }
    }
}
```

---

### 2. ggez (轻量级 2D 游戏框架 ⭐⭐⭐⭐)

**添加依赖**: `cargo add ggez`  
**用途**: 简单易用的 2D 游戏框架

#### 核心特性2

- ✅ 简洁的 API
- ✅ 2D 图形渲染
- ✅ 音频支持
- ✅ 输入处理

#### 基础示例

```rust
use ggez::{Context, GameResult};
use ggez::graphics::{self, Color};
use ggez::event::{self, EventHandler};

struct MainState {
    pos_x: f32,
}

impl MainState {
    fn new() -> GameResult<MainState> {
        Ok(MainState { pos_x: 100.0 })
    }
}

impl EventHandler for MainState {
    fn update(&mut self, _ctx: &mut Context) -> GameResult {
        self.pos_x += 1.0;
        if self.pos_x > 800.0 {
            self.pos_x = 0.0;
        }
        Ok(())
    }

    fn draw(&mut self, ctx: &mut Context) -> GameResult {
        graphics::clear(ctx, Color::BLACK);
        
        let circle = graphics::Mesh::new_circle(
            ctx,
            graphics::DrawMode::fill(),
            [self.pos_x, 380.0],
            20.0,
            0.1,
            Color::WHITE,
        )?;
        
        graphics::draw(ctx, &circle, graphics::DrawParam::default())?;
        graphics::present(ctx)?;
        
        Ok(())
    }
}

fn main() -> GameResult {
    let (ctx, event_loop) = ggez::ContextBuilder::new("game", "author")
        .build()?;
    
    let state = MainState::new()?;
    event::run(ctx, event_loop, state)
}
```

---

### 3. macroquad (跨平台游戏库 ⭐⭐⭐⭐)

**添加依赖**: `cargo add macroquad`  
**用途**: 简单的跨平台游戏库

#### 核心特性3

- ✅ 极简 API
- ✅ 跨平台（包括 Web）
- ✅ 无运行时
- ✅ 快速原型开发

#### 基础示例3

```rust
use macroquad::prelude::*;

#[macroquad::main("BasicShapes")]
async fn main() {
    loop {
        clear_background(BLACK);
        
        draw_line(40.0, 40.0, 100.0, 200.0, 15.0, BLUE);
        draw_rectangle(screen_width() / 2.0 - 60.0, 100.0, 120.0, 60.0, GREEN);
        draw_circle(screen_width() - 30.0, screen_height() - 30.0, 15.0, YELLOW);
        
        draw_text("HELLO", 20.0, 20.0, 30.0, WHITE);
        
        next_frame().await
    }
}
```

#### 交互式游戏

```rust
use macroquad::prelude::*;

struct Player {
    pos: Vec2,
    size: Vec2,
}

#[macroquad::main("Game")]
async fn main() {
    let mut player = Player {
        pos: vec2(screen_width() / 2.0, screen_height() / 2.0),
        size: vec2(20.0, 20.0),
    };
    
    loop {
        clear_background(DARKBLUE);
        
        // Input
        if is_key_down(KeyCode::Right) {
            player.pos.x += 2.0;
        }
        if is_key_down(KeyCode::Left) {
            player.pos.x -= 2.0;
        }
        if is_key_down(KeyCode::Down) {
            player.pos.y += 2.0;
        }
        if is_key_down(KeyCode::Up) {
            player.pos.y -= 2.0;
        }
        
        // Draw
        draw_rectangle(
            player.pos.x,
            player.pos.y,
            player.size.x,
            player.size.y,
            RED,
        );
        
        next_frame().await
    }
}
```

---

### 4. rapier (物理引擎 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add rapier2d` 或 `cargo add rapier3d`  
**用途**: 高性能物理引擎

#### 核心特性4

- ✅ 2D/3D 物理模拟
- ✅ 刚体动力学
- ✅ 碰撞检测
- ✅ 关节约束

#### 2D 物理示例

```rust
use rapier2d::prelude::*;

fn main() {
    let mut rigid_body_set = RigidBodySet::new();
    let mut collider_set = ColliderSet::new();
    
    // Create the ground
    let collider = ColliderBuilder::cuboid(100.0, 0.1).build();
    collider_set.insert(collider);
    
    // Create a dynamic rigid-body
    let rigid_body = RigidBodyBuilder::dynamic()
        .translation(vector![0.0, 10.0])
        .build();
    let ball_body_handle = rigid_body_set.insert(rigid_body);
    
    let collider = ColliderBuilder::ball(0.5).restitution(0.7).build();
    collider_set.insert_with_parent(collider, ball_body_handle, &mut rigid_body_set);
    
    // Create physics pipeline
    let gravity = vector![0.0, -9.81];
    let integration_parameters = IntegrationParameters::default();
    let mut physics_pipeline = PhysicsPipeline::new();
    let mut island_manager = IslandManager::new();
    let mut broad_phase = BroadPhase::new();
    let mut narrow_phase = NarrowPhase::new();
    let mut impulse_joint_set = ImpulseJointSet::new();
    let mut multibody_joint_set = MultibodyJointSet::new();
    let mut ccd_solver = CCDSolver::new();
    let physics_hooks = ();
    let event_handler = ();
    
    // Run simulation
    for _ in 0..200 {
        physics_pipeline.step(
            &gravity,
            &integration_parameters,
            &mut island_manager,
            &mut broad_phase,
            &mut narrow_phase,
            &mut rigid_body_set,
            &mut collider_set,
            &mut impulse_joint_set,
            &mut multibody_joint_set,
            &mut ccd_solver,
            None,
            &physics_hooks,
            &event_handler,
        );
        
        let ball_body = &rigid_body_set[ball_body_handle];
        println!("Ball altitude: {}", ball_body.translation().y);
    }
}
```

---

## 💡 最佳实践

### 1. 选择合适的引擎

```text
项目需求？
├─ 完整游戏引擎 → Bevy
├─ 2D 游戏 → ggez
├─ 快速原型 → macroquad
└─ 物理模拟 → rapier
```

### 2. ECS 模式 (Bevy)

```rust
// Components
#[derive(Component)]
struct Health(i32);

#[derive(Component)]
struct Damage(i32);

// Systems
fn damage_system(
    mut health_query: Query<&mut Health>,
    damage_query: Query<&Damage>,
) {
    for mut health in health_query.iter_mut() {
        for damage in damage_query.iter() {
            health.0 -= damage.0;
        }
    }
}
```

### 3. 状态管理

```rust
#[derive(States, Default, Debug, Clone, PartialEq, Eq, Hash)]
enum GameState {
    #[default]
    Menu,
    Playing,
    GameOver,
}

fn main() {
    App::new()
        .add_state::<GameState>()
        .add_systems(OnEnter(GameState::Menu), setup_menu)
        .add_systems(Update, menu_system.run_if(in_state(GameState::Menu)))
        .run();
}
```

---

## 📊 工具对比

| 工具 | 类型 | 学习曲线 | 性能 | 生态 | 推荐场景 |
|------|------|---------|------|------|---------|
| **bevy** | 完整引擎 | 中等 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 2D/3D 游戏 |
| **ggez** | 2D 框架 | 低 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 2D 游戏 |
| **macroquad** | 跨平台库 | 极低 | ⭐⭐⭐⭐ | ⭐⭐⭐ | 原型/小游戏 |
| **rapier** | 物理引擎 | 中等 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 物理模拟 |

---

## 🎯 实战场景

### 场景1: 简单射击游戏

```rust
use bevy::prelude::*;

#[derive(Component)]
struct Bullet {
    velocity: Vec3,
}

fn shoot_system(
    mut commands: Commands,
    keyboard: Res<ButtonInput<KeyCode>>,
    player_query: Query<&Transform, With<Player>>,
) {
    if keyboard.just_pressed(KeyCode::Space) {
        for player_transform in player_query.iter() {
            commands.spawn((
                SpriteBundle {
                    transform: Transform::from_translation(player_transform.translation),
                    ..default()
                },
                Bullet {
                    velocity: Vec3::new(0.0, 500.0, 0.0),
                },
            ));
        }
    }
}

fn move_bullets(
    time: Res<Time>,
    mut bullet_query: Query<(&mut Transform, &Bullet)>,
) {
    for (mut transform, bullet) in bullet_query.iter_mut() {
        transform.translation += bullet.velocity * time.delta_seconds();
    }
}
```

---

## 🔗 相关资源

- [Bevy Book](https://bevyengine.org/learn/book/)
- [ggez Documentation](https://docs.rs/ggez/)
- [macroquad Documentation](https://macroquad.rs/)
- [Rapier Documentation](https://rapier.rs/)
- [Are We Game Yet?](https://arewegameyet.rs/)

---

**导航**: [返回领域特定](../README.md) | [下一领域：WebAssembly](../wasm/README.md)
