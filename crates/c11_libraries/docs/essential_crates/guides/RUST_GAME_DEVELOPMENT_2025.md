# Rust 游戏开发指南 (2025)

> **目标读者**: 希望使用 Rust 进行游戏开发、了解游戏引擎架构，或开发高性能游戏系统的开发者。


## 📊 目录

- [📋 目录](#目录)
- [1. 游戏开发概述](#1-游戏开发概述)
  - [1.1 为什么选择 Rust?](#11-为什么选择-rust)
  - [1.2 Rust 游戏生态](#12-rust-游戏生态)
  - [1.3 开发环境搭建](#13-开发环境搭建)
- [2. Bevy 游戏引擎](#2-bevy-游戏引擎)
  - [2.1 ECS 架构](#21-ecs-架构)
  - [2.2 核心概念](#22-核心概念)
  - [2.3 Hello World 游戏](#23-hello-world-游戏)
- [3. 游戏架构设计](#3-游戏架构设计)
  - [3.1 游戏循环](#31-游戏循环)
  - [3.2 场景管理](#32-场景管理)
  - [3.3 资源管理](#33-资源管理)
- [4. 渲染系统](#4-渲染系统)
  - [4.1 2D 渲染](#41-2d-渲染)
  - [4.2 3D 渲染](#42-3d-渲染)
  - [4.3 着色器编程](#43-着色器编程)
- [5. 物理引擎](#5-物理引擎)
  - [5.1 Rapier 物理引擎](#51-rapier-物理引擎)
  - [5.2 碰撞检测](#52-碰撞检测)
  - [5.3 刚体动力学](#53-刚体动力学)
- [6. 音频系统](#6-音频系统)
  - [6.1 音效播放](#61-音效播放)
  - [6.2 背景音乐](#62-背景音乐)
  - [6.3 空间音频](#63-空间音频)
- [7. 输入处理](#7-输入处理)
  - [7.1 键盘鼠标](#71-键盘鼠标)
  - [7.2 游戏手柄](#72-游戏手柄)
  - [7.3 触摸屏](#73-触摸屏)
- [8. 实战案例](#8-实战案例)
  - [8.1 案例1: 太空射击游戏](#81-案例1-太空射击游戏)
  - [8.2 案例2: 2D 平台跳跃游戏](#82-案例2-2d-平台跳跃游戏)
  - [8.3 案例3: 3D 第一人称游戏](#83-案例3-3d-第一人称游戏)
- [9. 最佳实践](#9-最佳实践)
- [10. 常见问题](#10-常见问题)
- [11. 参考资源](#11-参考资源)


## 📋 目录

- [Rust 游戏开发指南 (2025)](#rust-游戏开发指南-2025)
  - [📋 目录](#-目录)
  - [1. 游戏开发概述](#1-游戏开发概述)
    - [1.1 为什么选择 Rust?](#11-为什么选择-rust)
    - [1.2 Rust 游戏生态](#12-rust-游戏生态)
    - [1.3 开发环境搭建](#13-开发环境搭建)
  - [2. Bevy 游戏引擎](#2-bevy-游戏引擎)
    - [2.1 ECS 架构](#21-ecs-架构)
    - [2.2 核心概念](#22-核心概念)
    - [2.3 Hello World 游戏](#23-hello-world-游戏)
  - [3. 游戏架构设计](#3-游戏架构设计)
    - [3.1 游戏循环](#31-游戏循环)
    - [3.2 场景管理](#32-场景管理)
    - [3.3 资源管理](#33-资源管理)
  - [4. 渲染系统](#4-渲染系统)
    - [4.1 2D 渲染](#41-2d-渲染)
    - [4.2 3D 渲染](#42-3d-渲染)
    - [4.3 着色器编程](#43-着色器编程)
  - [5. 物理引擎](#5-物理引擎)
    - [5.1 Rapier 物理引擎](#51-rapier-物理引擎)
    - [5.2 碰撞检测](#52-碰撞检测)
    - [5.3 刚体动力学](#53-刚体动力学)
  - [6. 音频系统](#6-音频系统)
    - [6.1 音效播放](#61-音效播放)
    - [6.2 背景音乐](#62-背景音乐)
    - [6.3 空间音频](#63-空间音频)
  - [7. 输入处理](#7-输入处理)
    - [7.1 键盘鼠标](#71-键盘鼠标)
    - [7.2 游戏手柄](#72-游戏手柄)
    - [7.3 触摸屏](#73-触摸屏)
  - [8. 实战案例](#8-实战案例)
    - [8.1 案例1: 太空射击游戏](#81-案例1-太空射击游戏)
    - [8.2 案例2: 2D 平台跳跃游戏](#82-案例2-2d-平台跳跃游戏)
    - [8.3 案例3: 3D 第一人称游戏](#83-案例3-3d-第一人称游戏)
  - [9. 最佳实践](#9-最佳实践)
  - [10. 常见问题](#10-常见问题)
  - [11. 参考资源](#11-参考资源)

---

## 1. 游戏开发概述

### 1.1 为什么选择 Rust?

```text
┌────────────────────────────────────────────────────────────┐
│           Rust 游戏开发的核心优势                          │
├────────────────────────────────────────────────────────────┤
│                                                            │
│  ⚡ 性能                                                    │
│     - 零成本抽象                                           │
│     - 无垃圾回收 (GC)                                      │
│     - 编译时优化                                           │
│     - 接近 C++ 的性能                                      │
│                                                            │
│  🔒 安全性                                                  │
│     - 内存安全 (无空指针/野指针)                           │
│     - 线程安全 (无数据竞争)                                │
│     - 减少运行时崩溃                                       │
│                                                            │
│  🛠️  开发体验                                               │
│     - Cargo 包管理                                         │
│     - 强大的类型系统                                       │
│     - 友好的编译错误                                       │
│     - 现代化的工具链                                       │
│                                                            │
│  🌍 跨平台                                                  │
│     - Windows, macOS, Linux                                │
│     - WebAssembly (浏览器游戏)                             │
│     - 移动平台 (Android, iOS)                              │
│                                                            │
└────────────────────────────────────────────────────────────┘
```

### 1.2 Rust 游戏生态

**主流游戏引擎**:

| 引擎 | 类型 | 特点 | 适用场景 |
|------|------|------|----------|
| **Bevy** | ECS | 现代化, 数据驱动 | 2D/3D 游戏, 推荐初学者 |
| **Godot (gdext)** | 场景图 | 成熟的编辑器 | 全功能游戏开发 |
| **Fyrox** | 场景图 | 内置编辑器 | 3D 游戏 |
| **Macroquad** | 轻量级 | 简单易用 | 原型开发, 游戏 Jam |
| **ggez** | 2D | 类似 LÖVE | 2D 游戏, 学习用 |
| **Amethyst** | ECS | 已停止维护 | 不推荐 |

**核心库**:

- **渲染**: `wgpu`, `glium`, `vulkano`
- **物理**: `rapier`, `nphysics`
- **音频**: `rodio`, `kira`
- **数学**: `glam`, `nalgebra`
- **UI**: `egui`, `iced`
- **网络**: `tokio`, `bevy_networking`

### 1.3 开发环境搭建

```bash
# 1. 安装 Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 2. 安装 Bevy 依赖 (Linux)
sudo apt-get install g++ pkg-config libx11-dev libasound2-dev libudev-dev libwayland-dev libxkbcommon-dev

# 3. 创建新项目
cargo new my_game
cd my_game

# 4. 添加 Bevy 依赖
cargo add bevy

# 5. 启用动态链接 (加快编译)
# .cargo/config.toml
[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = ["-C", "link-arg=-fuse-ld=mold"]

# 6. 启用 Bevy 动态链接
# Cargo.toml
[dependencies]
bevy = { version = "0.12", features = ["dynamic_linking"] }
```

---

## 2. Bevy 游戏引擎

### 2.1 ECS 架构

**实体-组件-系统 (Entity-Component-System)**:

```text
┌──────────────────────────────────────────────────────────────┐
│                    ECS 架构原理                               │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  Entity (实体): 唯一标识符                                    │
│    - Player (Entity ID: 1)                                   │
│    - Enemy  (Entity ID: 2)                                   │
│    - Bullet (Entity ID: 3)                                   │
│                                                              │
│  Component (组件): 纯数据                                     │
│    - Position { x, y }                                       │
│    - Velocity { vx, vy }                                     │
│    - Health { hp }                                           │
│    - Sprite { texture, ... }                                 │
│                                                              │
│  System (系统): 逻辑处理                                     │
│    - MovementSystem:                                         │
│        查询 (Position, Velocity)                             │
│        更新: position.x += velocity.vx * delta_time          │
│                                                              │
│    - RenderSystem:                                           │
│        查询 (Position, Sprite)                               │
│        绘制: draw_sprite(sprite, position)                   │
│                                                              │
│  ┌─────────────────────────────────────────────────┐        │
│  │  Entity 1: [Position, Velocity, Health, Sprite] │        │
│  │  Entity 2: [Position, Velocity, Enemy]          │        │
│  │  Entity 3: [Position, Velocity, Bullet]         │        │
│  └─────────────────────────────────────────────────┘        │
│                       │                                      │
│                       ▼                                      │
│  ┌─────────────────────────────────────────────────┐        │
│  │ MovementSystem → 更新所有 (Position, Velocity)  │        │
│  │ CollisionSystem → 检测所有碰撞                  │        │
│  │ RenderSystem → 绘制所有 (Position, Sprite)      │        │
│  └─────────────────────────────────────────────────┘        │
│                                                              │
│  ✅ 优势:                                                    │
│     - 数据局部性 (高性能)                                    │
│     - 灵活组合 (复用组件)                                    │
│     - 并行处理 (系统独立)                                    │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### 2.2 核心概念

**组件 (Component)**:

```rust
use bevy::prelude::*;

// 组件是纯数据结构
#[derive(Component)]
struct Position {
    x: f32,
    y: f32,
}

#[derive(Component)]
struct Velocity {
    vx: f32,
    vy: f32,
}

#[derive(Component)]
struct Health {
    hp: i32,
    max_hp: i32,
}

#[derive(Component)]
struct Player;

#[derive(Component)]
struct Enemy;
```

**系统 (System)**:

```rust
// 系统是处理逻辑的函数
fn movement_system(
    time: Res<Time>,
    mut query: Query<(&mut Position, &Velocity)>,
) {
    for (mut pos, vel) in query.iter_mut() {
        pos.x += vel.vx * time.delta_seconds();
        pos.y += vel.vy * time.delta_seconds();
    }
}

fn health_system(
    mut commands: Commands,
    query: Query<(Entity, &Health)>,
) {
    for (entity, health) in query.iter() {
        if health.hp <= 0 {
            // 销毁实体
            commands.entity(entity).despawn();
        }
    }
}
```

**资源 (Resource)**:

```rust
// 资源是全局共享的数据
#[derive(Resource)]
struct Score {
    value: u32,
}

#[derive(Resource)]
struct GameState {
    level: u32,
    paused: bool,
}

fn update_score_system(
    mut score: ResMut<Score>,
    query: Query<&Enemy, With<Dead>>,
) {
    // 每个死亡的敌人增加 10 分
    score.value += query.iter().count() as u32 * 10;
}
```

### 2.3 Hello World 游戏

**最小化示例**:

```rust
use bevy::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        .add_systems(Update, (movement, input))
        .run();
}

// 启动时执行一次
fn setup(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
) {
    // 生成相机
    commands.spawn(Camera2dBundle::default());
    
    // 生成玩家
    commands.spawn((
        SpriteBundle {
            texture: asset_server.load("player.png"),
            transform: Transform::from_xyz(0.0, 0.0, 0.0),
            ..default()
        },
        Player,
        Velocity { vx: 0.0, vy: 0.0 },
    ));
}

#[derive(Component)]
struct Player;

#[derive(Component)]
struct Velocity {
    vx: f32,
    vy: f32,
}

// 每帧执行
fn movement(
    time: Res<Time>,
    mut query: Query<(&mut Transform, &Velocity)>,
) {
    for (mut transform, velocity) in query.iter_mut() {
        transform.translation.x += velocity.vx * time.delta_seconds();
        transform.translation.y += velocity.vy * time.delta_seconds();
    }
}

fn input(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut Velocity, With<Player>>,
) {
    let mut velocity = query.single_mut();
    
    velocity.vx = 0.0;
    velocity.vy = 0.0;
    
    if keyboard.pressed(KeyCode::KeyW) {
        velocity.vy = 200.0;
    }
    if keyboard.pressed(KeyCode::KeyS) {
        velocity.vy = -200.0;
    }
    if keyboard.pressed(KeyCode::KeyA) {
        velocity.vx = -200.0;
    }
    if keyboard.pressed(KeyCode::KeyD) {
        velocity.vx = 200.0;
    }
}
```

---

## 3. 游戏架构设计

### 3.1 游戏循环

**Bevy 游戏循环**:

```text
┌──────────────────────────────────────────────────────────────┐
│                    Bevy 游戏循环                              │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────────┐                                        │
│  │  Startup Systems │  (初始化, 只执行一次)                   │
│  └────────┬─────────┘                                        │
│           │                                                  │
│           ▼                                                  │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  每帧循环:                                           │   │
│  │                                                      │   │
│  │  1. First (最先执行)                                 │   │
│  │      - 清理标记                                      │   │
│  │      - 准备输入                                      │   │
│  │           ▼                                          │   │
│  │  2. PreUpdate                                        │   │
│  │      - 处理事件                                      │   │
│  │      - 输入系统                                      │   │
│  │           ▼                                          │   │
│  │  3. Update (主要游戏逻辑)                            │   │
│  │      - 移动                                          │   │
│  │      - AI                                            │   │
│  │      - 战斗                                          │   │
│  │           ▼                                          │   │
│  │  4. PostUpdate                                       │   │
│  │      - 碰撞检测                                      │   │
│  │      - 相机更新                                      │   │
│  │           ▼                                          │   │
│  │  5. Render (渲染)                                    │   │
│  │      - 准备渲染数据                                  │   │
│  │      - GPU 绘制                                      │   │
│  │           ▼                                          │   │
│  │  6. Last (最后执行)                                  │   │
│  │      - 清理临时数据                                  │   │
│  │                                                      │   │
│  └──────────────────┬───────────────────────────────────┘   │
│                     │                                        │
│                     └──────> 返回步骤 1 (下一帧)              │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

**自定义调度**:

```rust
use bevy::prelude::*;

#[derive(SystemSet, Debug, Clone, PartialEq, Eq, Hash)]
enum GameSet {
    Input,
    Logic,
    Physics,
    Render,
}

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .configure_sets(
            Update,
            (
                GameSet::Input,
                GameSet::Logic,
                GameSet::Physics,
                GameSet::Render,
            )
                .chain(),  // 按顺序执行
        )
        .add_systems(Update, input_system.in_set(GameSet::Input))
        .add_systems(Update, game_logic.in_set(GameSet::Logic))
        .add_systems(Update, physics_system.in_set(GameSet::Physics))
        .add_systems(Update, render_system.in_set(GameSet::Render))
        .run();
}
```

### 3.2 场景管理

**状态管理**:

```rust
use bevy::prelude::*;

#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash, States)]
enum GameState {
    #[default]
    MainMenu,
    InGame,
    Paused,
    GameOver,
}

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .init_state::<GameState>()
        .add_systems(OnEnter(GameState::MainMenu), setup_menu)
        .add_systems(OnExit(GameState::MainMenu), cleanup_menu)
        .add_systems(OnEnter(GameState::InGame), setup_game)
        .add_systems(Update, game_logic.run_if(in_state(GameState::InGame)))
        .run();
}

fn setup_menu(mut commands: Commands) {
    // 创建菜单 UI
    commands.spawn((
        NodeBundle {
            style: Style {
                width: Val::Percent(100.0),
                height: Val::Percent(100.0),
                align_items: AlignItems::Center,
                justify_content: JustifyContent::Center,
                ..default()
            },
            ..default()
        },
        MenuScreen,
    ));
}

#[derive(Component)]
struct MenuScreen;

fn cleanup_menu(
    mut commands: Commands,
    query: Query<Entity, With<MenuScreen>>,
) {
    for entity in query.iter() {
        commands.entity(entity).despawn_recursive();
    }
}
```

### 3.3 资源管理

**资产加载**:

```rust
use bevy::prelude::*;

#[derive(Resource)]
struct GameAssets {
    player_texture: Handle<Image>,
    enemy_texture: Handle<Image>,
    bullet_texture: Handle<Image>,
    explosion_sound: Handle<AudioSource>,
}

fn load_assets(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
) {
    let assets = GameAssets {
        player_texture: asset_server.load("sprites/player.png"),
        enemy_texture: asset_server.load("sprites/enemy.png"),
        bullet_texture: asset_server.load("sprites/bullet.png"),
        explosion_sound: asset_server.load("sounds/explosion.ogg"),
    };
    
    commands.insert_resource(assets);
}

fn spawn_player(
    mut commands: Commands,
    assets: Res<GameAssets>,
) {
    commands.spawn((
        SpriteBundle {
            texture: assets.player_texture.clone(),
            ..default()
        },
        Player,
    ));
}
```

**资源池 (Object Pooling)**:

```rust
use bevy::prelude::*;
use std::collections::VecDeque;

#[derive(Resource)]
struct BulletPool {
    inactive: VecDeque<Entity>,
}

fn create_pool(mut commands: Commands) {
    let mut pool = BulletPool {
        inactive: VecDeque::new(),
    };
    
    // 预创建 100 颗子弹
    for _ in 0..100 {
        let entity = commands
            .spawn((
                SpriteBundle {
                    visibility: Visibility::Hidden,
                    ..default()
                },
                Bullet,
            ))
            .id();
        
        pool.inactive.push_back(entity);
    }
    
    commands.insert_resource(pool);
}

fn spawn_bullet(
    mut pool: ResMut<BulletPool>,
    mut query: Query<(&mut Transform, &mut Visibility), With<Bullet>>,
) {
    if let Some(entity) = pool.inactive.pop_front() {
        if let Ok((mut transform, mut visibility)) = query.get_mut(entity) {
            transform.translation = Vec3::new(0.0, 0.0, 0.0);
            *visibility = Visibility::Visible;
        }
    }
}

fn return_bullet(
    mut pool: ResMut<BulletPool>,
    entity: Entity,
    mut query: Query<&mut Visibility, With<Bullet>>,
) {
    if let Ok(mut visibility) = query.get_mut(entity) {
        *visibility = Visibility::Hidden;
        pool.inactive.push_back(entity);
    }
}

#[derive(Component)]
struct Bullet;
```

---

## 4. 渲染系统

### 4.1 2D 渲染

**精灵渲染**:

```rust
use bevy::prelude::*;

fn spawn_sprite(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
) {
    commands.spawn(SpriteBundle {
        texture: asset_server.load("player.png"),
        transform: Transform {
            translation: Vec3::new(0.0, 0.0, 0.0),
            rotation: Quat::from_rotation_z(0.0),
            scale: Vec3::new(2.0, 2.0, 1.0),
        },
        sprite: Sprite {
            color: Color::rgb(1.0, 1.0, 1.0),
            flip_x: false,
            flip_y: false,
            custom_size: Some(Vec2::new(64.0, 64.0)),
            ..default()
        },
        ..default()
    });
}
```

**精灵动画**:

```rust
use bevy::prelude::*;

#[derive(Component)]
struct Animation {
    frames: Vec<Handle<Image>>,
    current_frame: usize,
    timer: Timer,
}

fn animate_sprites(
    time: Res<Time>,
    mut query: Query<(&mut Animation, &mut Handle<Image>)>,
) {
    for (mut anim, mut texture) in query.iter_mut() {
        anim.timer.tick(time.delta());
        
        if anim.timer.just_finished() {
            anim.current_frame = (anim.current_frame + 1) % anim.frames.len();
            *texture = anim.frames[anim.current_frame].clone();
        }
    }
}

fn spawn_animated_sprite(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
) {
    let frames = vec![
        asset_server.load("walk_1.png"),
        asset_server.load("walk_2.png"),
        asset_server.load("walk_3.png"),
        asset_server.load("walk_4.png"),
    ];
    
    commands.spawn((
        SpriteBundle {
            texture: frames[0].clone(),
            ..default()
        },
        Animation {
            frames,
            current_frame: 0,
            timer: Timer::from_seconds(0.1, TimerMode::Repeating),
        },
    ));
}
```

### 4.2 3D 渲染

**3D 模型**:

```rust
use bevy::prelude::*;

fn spawn_3d_model(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
) {
    // 生成 3D 相机
    commands.spawn(Camera3dBundle {
        transform: Transform::from_xyz(0.0, 5.0, 10.0)
            .looking_at(Vec3::ZERO, Vec3::Y),
        ..default()
    });
    
    // 生成光源
    commands.spawn(PointLightBundle {
        point_light: PointLight {
            intensity: 1500.0,
            ..default()
        },
        transform: Transform::from_xyz(4.0, 8.0, 4.0),
        ..default()
    });
    
    // 加载 GLTF 模型
    commands.spawn(SceneBundle {
        scene: asset_server.load("models/character.glb#Scene0"),
        transform: Transform::from_xyz(0.0, 0.0, 0.0),
        ..default()
    });
}
```

**材质系统**:

```rust
use bevy::prelude::*;
use bevy::pbr::StandardMaterial;

fn create_custom_material(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
    asset_server: Res<AssetServer>,
) {
    let material = materials.add(StandardMaterial {
        base_color: Color::rgb(0.8, 0.7, 0.6),
        base_color_texture: Some(asset_server.load("textures/diffuse.png")),
        metallic: 0.5,
        perceptual_roughness: 0.3,
        normal_map_texture: Some(asset_server.load("textures/normal.png")),
        ..default()
    });
    
    commands.spawn(PbrBundle {
        mesh: meshes.add(Mesh::from(shape::Cube { size: 1.0 })),
        material,
        transform: Transform::from_xyz(0.0, 0.5, 0.0),
        ..default()
    });
}
```

### 4.3 着色器编程

**自定义着色器 (WGSL)**:

```rust
// Cargo.toml
[dependencies]
bevy = { version = "0.12", features = ["shader_imports"] }
```

```wgsl
// assets/shaders/custom.wgsl
#import bevy_pbr::mesh_view_bindings
#import bevy_pbr::mesh_bindings

struct Vertex {
    @location(0) position: vec3<f32>,
    @location(1) color: vec4<f32>,
};

struct VertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) color: vec4<f32>,
};

@vertex
fn vertex(vertex: Vertex) -> VertexOutput {
    var out: VertexOutput;
    out.clip_position = mesh_view_bindings::view.view_proj * vec4<f32>(vertex.position, 1.0);
    out.color = vertex.color;
    return out;
}

@fragment
fn fragment(in: VertexOutput) -> @location(0) vec4<f32> {
    return in.color;
}
```

```rust
// Rust 代码
use bevy::prelude::*;
use bevy::reflect::TypePath;
use bevy::render::render_resource::{AsBindGroup, ShaderRef};

#[derive(Asset, TypePath, AsBindGroup, Debug, Clone)]
struct CustomMaterial {
    #[uniform(0)]
    color: Color,
}

impl Material for CustomMaterial {
    fn fragment_shader() -> ShaderRef {
        "shaders/custom.wgsl".into()
    }
}

fn setup(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<CustomMaterial>>,
) {
    commands.spawn(MaterialMeshBundle {
        mesh: meshes.add(Mesh::from(shape::Cube { size: 1.0 })),
        material: materials.add(CustomMaterial {
            color: Color::rgb(0.8, 0.2, 0.2),
        }),
        ..default()
    });
}
```

---

## 5. 物理引擎

### 5.1 Rapier 物理引擎

**集成 Rapier**:

```toml
# Cargo.toml
[dependencies]
bevy = "0.12"
bevy_rapier2d = { version = "0.25", features = ["simd-stable", "debug-render-2d"] }
# 或 3D 版本:
# bevy_rapier3d = { version = "0.25", features = ["simd-stable", "debug-render-3d"] }
```

```rust
use bevy::prelude::*;
use bevy_rapier2d::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_plugins(RapierPhysicsPlugin::<NoUserData>::pixels_per_meter(100.0))
        .add_plugins(RapierDebugRenderPlugin::default())
        .add_systems(Startup, setup_physics)
        .run();
}

fn setup_physics(mut commands: Commands) {
    // 生成相机
    commands.spawn(Camera2dBundle::default());
    
    // 生成地面 (静态刚体)
    commands.spawn((
        SpriteBundle {
            sprite: Sprite {
                color: Color::rgb(0.3, 0.3, 0.3),
                custom_size: Some(Vec2::new(800.0, 20.0)),
                ..default()
            },
            transform: Transform::from_xyz(0.0, -200.0, 0.0),
            ..default()
        },
        RigidBody::Fixed,
        Collider::cuboid(400.0, 10.0),
    ));
    
    // 生成动态方块
    commands.spawn((
        SpriteBundle {
            sprite: Sprite {
                color: Color::rgb(0.8, 0.2, 0.2),
                custom_size: Some(Vec2::new(50.0, 50.0)),
                ..default()
            },
            transform: Transform::from_xyz(0.0, 200.0, 0.0),
            ..default()
        },
        RigidBody::Dynamic,
        Collider::cuboid(25.0, 25.0),
        Restitution::coefficient(0.7),  // 弹性系数
        Friction::coefficient(0.5),     // 摩擦系数
    ));
}
```

### 5.2 碰撞检测

**碰撞事件**:

```rust
use bevy::prelude::*;
use bevy_rapier2d::prelude::*;

fn collision_system(
    mut collision_events: EventReader<CollisionEvent>,
    query: Query<&Name>,
) {
    for event in collision_events.read() {
        match event {
            CollisionEvent::Started(e1, e2, _flags) => {
                if let (Ok(name1), Ok(name2)) = (query.get(*e1), query.get(*e2)) {
                    println!("碰撞开始: {} 与 {}", name1, name2);
                }
            }
            CollisionEvent::Stopped(e1, e2, _flags) => {
                if let (Ok(name1), Ok(name2)) = (query.get(*e1), query.get(*e2)) {
                    println!("碰撞结束: {} 与 {}", name1, name2);
                }
            }
        }
    }
}

fn spawn_with_collision(mut commands: Commands) {
    commands.spawn((
        SpriteBundle { ..default() },
        RigidBody::Dynamic,
        Collider::ball(25.0),
        Name::new("球体"),
        ActiveEvents::COLLISION_EVENTS,  // 启用碰撞事件
    ));
}
```

### 5.3 刚体动力学

**施加力和冲量**:

```rust
use bevy::prelude::*;
use bevy_rapier2d::prelude::*;

#[derive(Component)]
struct Player;

fn player_movement(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut ExternalImpulse, With<Player>>,
) {
    let mut impulse = query.single_mut();
    
    impulse.impulse = Vec2::ZERO;
    
    if keyboard.pressed(KeyCode::KeyW) {
        impulse.impulse.y += 500.0;
    }
    if keyboard.pressed(KeyCode::KeyS) {
        impulse.impulse.y -= 500.0;
    }
    if keyboard.pressed(KeyCode::KeyA) {
        impulse.impulse.x -= 500.0;
    }
    if keyboard.pressed(KeyCode::KeyD) {
        impulse.impulse.x += 500.0;
    }
}

fn spawn_player(mut commands: Commands) {
    commands.spawn((
        SpriteBundle { ..default() },
        RigidBody::Dynamic,
        Collider::ball(25.0),
        ExternalImpulse::default(),
        Damping { linear_damping: 0.5, angular_damping: 1.0 },
        Player,
    ));
}
```

---

## 6. 音频系统

### 6.1 音效播放

**基本音效**:

```rust
use bevy::prelude::*;
use bevy::audio::{Audio, AudioSink};

fn play_sound(
    asset_server: Res<AssetServer>,
    audio: Res<Audio>,
) {
    audio.play(asset_server.load("sounds/jump.ogg"));
}

fn play_with_volume(
    asset_server: Res<AssetServer>,
    audio: Res<Audio>,
    audio_sinks: Res<Assets<AudioSink>>,
) {
    let handle = audio_sinks.get_handle(
        audio.play_with_settings(
            asset_server.load("sounds/explosion.ogg"),
            PlaybackSettings {
                volume: bevy::audio::Volume::new_relative(0.5),
                ..default()
            },
        )
    );
}
```

### 6.2 背景音乐

**循环播放**:

```rust
use bevy::prelude::*;

#[derive(Resource)]
struct BackgroundMusic {
    handle: Handle<AudioSink>,
}

fn play_background_music(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
    audio: Res<Audio>,
    audio_sinks: Res<Assets<AudioSink>>,
) {
    let handle = audio_sinks.get_handle(
        audio.play_with_settings(
            asset_server.load("music/background.ogg"),
            PlaybackSettings::LOOP.with_volume(bevy::audio::Volume::new_relative(0.3)),
        )
    );
    
    commands.insert_resource(BackgroundMusic { handle });
}

fn pause_music(
    background_music: Res<BackgroundMusic>,
    audio_sinks: Res<Assets<AudioSink>>,
) {
    if let Some(sink) = audio_sinks.get(&background_music.handle) {
        sink.pause();
    }
}
```

### 6.3 空间音频

**3D 音效定位**:

```rust
use bevy::prelude::*;

fn play_spatial_audio(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
    audio: Res<Audio>,
) {
    commands.spawn((
        AudioBundle {
            source: asset_server.load("sounds/ambient.ogg"),
            settings: PlaybackSettings::LOOP
                .with_spatial(true),
        },
        SpatialListener::new(10.0),  // 最大听音距离
        TransformBundle::from_transform(
            Transform::from_xyz(5.0, 0.0, 0.0)
        ),
    ));
}
```

---

## 7. 输入处理

### 7.1 键盘鼠标

**键盘输入**:

```rust
use bevy::prelude::*;

fn keyboard_input(
    keyboard: Res<ButtonInput<KeyCode>>,
) {
    // 检查按键是否按下
    if keyboard.pressed(KeyCode::Space) {
        println!("空格键按下");
    }
    
    // 检查按键是否刚按下
    if keyboard.just_pressed(KeyCode::Enter) {
        println!("回车键刚按下");
    }
    
    // 检查按键是否刚释放
    if keyboard.just_released(KeyCode::Escape) {
        println!("ESC 键刚释放");
    }
}
```

**鼠标输入**:

```rust
use bevy::prelude::*;
use bevy::window::PrimaryWindow;

fn mouse_input(
    mouse: Res<ButtonInput<MouseButton>>,
    window_query: Query<&Window, With<PrimaryWindow>>,
    camera_query: Query<(&Camera, &GlobalTransform)>,
) {
    if mouse.just_pressed(MouseButton::Left) {
        let window = window_query.single();
        
        if let Some(cursor_position) = window.cursor_position() {
            let (camera, camera_transform) = camera_query.single();
            
            // 将屏幕坐标转换为世界坐标
            if let Some(world_position) = camera.viewport_to_world_2d(
                camera_transform,
                cursor_position,
            ) {
                println!("鼠标点击位置: {:?}", world_position);
            }
        }
    }
}
```

### 7.2 游戏手柄

**手柄输入**:

```rust
use bevy::prelude::*;
use bevy::input::gamepad::{Gamepad, GamepadButton, GamepadAxis};

fn gamepad_input(
    gamepads: Res<Gamepads>,
    button_inputs: Res<ButtonInput<GamepadButton>>,
    axes: Res<Axis<GamepadAxis>>,
) {
    for gamepad in gamepads.iter() {
        // 按钮输入
        if button_inputs.just_pressed(GamepadButton::new(gamepad, GamepadButtonType::South)) {
            println!("A 按钮按下 (手柄 {:?})", gamepad);
        }
        
        // 摇杆输入
        if let Some(left_stick_x) = axes.get(GamepadAxis::new(gamepad, GamepadAxisType::LeftStickX)) {
            if left_stick_x.abs() > 0.1 {
                println!("左摇杆 X: {}", left_stick_x);
            }
        }
    }
}
```

### 7.3 触摸屏

**触摸输入**:

```rust
use bevy::prelude::*;
use bevy::input::touch::{TouchPhase, Touches};

fn touch_input(
    touches: Res<Touches>,
) {
    for touch in touches.iter() {
        match touch.phase() {
            TouchPhase::Started => {
                println!("触摸开始: {:?}", touch.position());
            }
            TouchPhase::Moved => {
                println!("触摸移动: {:?}", touch.position());
            }
            TouchPhase::Ended => {
                println!("触摸结束: {:?}", touch.position());
            }
            TouchPhase::Canceled => {
                println!("触摸取消: {:?}", touch.position());
            }
        }
    }
}
```

---

## 8. 实战案例

### 8.1 案例1: 太空射击游戏

```rust
use bevy::prelude::*;
use bevy_rapier2d::prelude::*;

#[derive(Component)]
struct Player;

#[derive(Component)]
struct Enemy;

#[derive(Component)]
struct Bullet {
    lifetime: Timer,
}

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_plugins(RapierPhysicsPlugin::<NoUserData>::pixels_per_meter(100.0))
        .add_systems(Startup, setup)
        .add_systems(Update, (
            player_movement,
            player_shoot,
            bullet_lifetime,
            spawn_enemies,
            collision_detection,
        ))
        .run();
}

fn setup(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
) {
    commands.spawn(Camera2dBundle::default());
    
    // 生成玩家
    commands.spawn((
        SpriteBundle {
            texture: asset_server.load("player.png"),
            transform: Transform::from_xyz(0.0, -200.0, 0.0),
            ..default()
        },
        Player,
        RigidBody::Dynamic,
        Collider::ball(25.0),
        LockedAxes::ROTATION_LOCKED,
    ));
}

fn player_movement(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut Transform, With<Player>>,
    time: Res<Time>,
) {
    let mut transform = query.single_mut();
    let speed = 300.0;
    
    if keyboard.pressed(KeyCode::KeyA) {
        transform.translation.x -= speed * time.delta_seconds();
    }
    if keyboard.pressed(KeyCode::KeyD) {
        transform.translation.x += speed * time.delta_seconds();
    }
}

fn player_shoot(
    mut commands: Commands,
    keyboard: Res<ButtonInput<KeyCode>>,
    query: Query<&Transform, With<Player>>,
    asset_server: Res<AssetServer>,
) {
    if keyboard.just_pressed(KeyCode::Space) {
        let player_transform = query.single();
        
        commands.spawn((
            SpriteBundle {
                texture: asset_server.load("bullet.png"),
                transform: Transform::from_translation(
                    player_transform.translation + Vec3::new(0.0, 30.0, 0.0)
                ),
                ..default()
            },
            Bullet {
                lifetime: Timer::from_seconds(3.0, TimerMode::Once),
            },
            RigidBody::Dynamic,
            Collider::ball(5.0),
            Velocity::linear(Vec2::new(0.0, 500.0)),
            ActiveEvents::COLLISION_EVENTS,
        ));
    }
}

fn bullet_lifetime(
    mut commands: Commands,
    time: Res<Time>,
    mut query: Query<(Entity, &mut Bullet)>,
) {
    for (entity, mut bullet) in query.iter_mut() {
        bullet.lifetime.tick(time.delta());
        
        if bullet.lifetime.finished() {
            commands.entity(entity).despawn();
        }
    }
}

fn spawn_enemies(
    mut commands: Commands,
    time: Res<Time>,
    asset_server: Res<AssetServer>,
) {
    // 每秒生成一个敌人 (简化版)
    if time.elapsed_seconds() as u32 % 2 == 0 {
        commands.spawn((
            SpriteBundle {
                texture: asset_server.load("enemy.png"),
                transform: Transform::from_xyz(
                    rand::random::<f32>() * 400.0 - 200.0,
                    300.0,
                    0.0,
                ),
                ..default()
            },
            Enemy,
            RigidBody::Dynamic,
            Collider::ball(20.0),
            Velocity::linear(Vec2::new(0.0, -100.0)),
            ActiveEvents::COLLISION_EVENTS,
        ));
    }
}

fn collision_detection(
    mut commands: Commands,
    mut collision_events: EventReader<CollisionEvent>,
    bullet_query: Query<&Bullet>,
    enemy_query: Query<&Enemy>,
) {
    for event in collision_events.read() {
        if let CollisionEvent::Started(e1, e2, _) = event {
            // 子弹击中敌人
            if bullet_query.get(*e1).is_ok() && enemy_query.get(*e2).is_ok() {
                commands.entity(*e1).despawn();
                commands.entity(*e2).despawn();
            }
        }
    }
}
```

### 8.2 案例2: 2D 平台跳跃游戏

**核心跳跃机制**:

```rust
use bevy::prelude::*;
use bevy_rapier2d::prelude::*;

#[derive(Component)]
struct Player {
    on_ground: bool,
}

fn player_jump(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<(&mut Player, &mut Velocity)>,
) {
    let (mut player, mut velocity) = query.single_mut();
    
    if keyboard.just_pressed(KeyCode::Space) && player.on_ground {
        velocity.linvel.y = 400.0;  // 跳跃速度
        player.on_ground = false;
    }
}

fn check_ground_collision(
    mut player_query: Query<(Entity, &mut Player)>,
    rapier_context: Res<RapierContext>,
) {
    let (player_entity, mut player) = player_query.single_mut();
    
    // 射线检测地面
    let ray_origin = Vec2::new(0.0, 0.0);
    let ray_dir = Vec2::new(0.0, -1.0);
    let max_distance = 1.0;
    
    if let Some((_, _)) = rapier_context.cast_ray(
        ray_origin,
        ray_dir,
        max_distance,
        true,
        QueryFilter::default().exclude_rigid_body(player_entity),
    ) {
        player.on_ground = true;
    } else {
        player.on_ground = false;
    }
}
```

### 8.3 案例3: 3D 第一人称游戏

**第一人称相机控制**:

```rust
use bevy::prelude::*;
use bevy::input::mouse::MouseMotion;

#[derive(Component)]
struct FirstPersonCamera {
    sensitivity: f32,
}

fn camera_look(
    mut motion_events: EventReader<MouseMotion>,
    mut query: Query<&mut Transform, With<FirstPersonCamera>>,
    camera_query: Query<&FirstPersonCamera>,
) {
    let camera = camera_query.single();
    let mut transform = query.single_mut();
    
    for event in motion_events.read() {
        let delta = event.delta;
        
        // 左右旋转 (Yaw)
        transform.rotate_y(-delta.x * camera.sensitivity * 0.01);
        
        // 上下旋转 (Pitch)
        transform.rotate_local_x(-delta.y * camera.sensitivity * 0.01);
    }
}

fn player_movement_3d(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut Transform, With<FirstPersonCamera>>,
    time: Res<Time>,
) {
    let mut transform = query.single_mut();
    let speed = 5.0;
    
    let forward = transform.forward();
    let right = transform.right();
    
    if keyboard.pressed(KeyCode::KeyW) {
        transform.translation += forward * speed * time.delta_seconds();
    }
    if keyboard.pressed(KeyCode::KeyS) {
        transform.translation -= forward * speed * time.delta_seconds();
    }
    if keyboard.pressed(KeyCode::KeyA) {
        transform.translation -= right * speed * time.delta_seconds();
    }
    if keyboard.pressed(KeyCode::KeyD) {
        transform.translation += right * speed * time.delta_seconds();
    }
}
```

---

## 9. 最佳实践

**1. 性能优化**:

- ✅ 使用对象池避免频繁创建/销毁实体
- ✅ 利用 Bevy 的并行系统调度
- ✅ 批量渲染相同的精灵
- ✅ 使用空间哈希加速碰撞检测
- ✅ 启用 `dynamic_linking` 加快迭代速度

**2. 代码组织**:

- ✅ 使用插件 (Plugin) 模块化功能
- ✅ 使用 SystemSet 管理系统执行顺序
- ✅ 使用 States 管理游戏状态
- ✅ 使用 Events 解耦系统之间的通信

**3. 资源管理**:

- ✅ 预加载常用资源
- ✅ 使用资源池复用对象
- ✅ 及时清理未使用的资源
- ✅ 使用资产热重载加速开发

**4. 调试技巧**:

- ✅ 使用 `dbg!()` 宏打印调试信息
- ✅ 启用 Rapier 的调试渲染
- ✅ 使用 `bevy_inspector_egui` 查看实体和组件
- ✅ 使用 `bevy_framepace` 限制帧率

**5. 发布优化**:

- ✅ 启用 LTO 和优化编译选项
- ✅ 使用 `strip` 移除调试符号
- ✅ 压缩资源文件 (图片、音频)
- ✅ 使用 `cargo-auditable` 审计依赖

---

## 10. 常见问题

**Q1: Bevy vs Unity/Unreal?**

| 特性 | Bevy | Unity | Unreal |
|------|------|-------|--------|
| 学习曲线 | 中等 | 低 | 高 |
| 性能 | 高 | 中 | 高 |
| 跨平台 | 好 | 好 | 好 |
| 编辑器 | 无 (开发中) | 成熟 | 成熟 |
| 社区 | 快速增长 | 庞大 | 庞大 |
| 适用场景 | 独立游戏, 学习 | 商业游戏 | AAA 游戏 |

**Q2: 如何提高编译速度?**

```toml
# .cargo/config.toml
[build]
jobs = 8  # 并行编译任务数

# Cargo.toml
[dependencies]
bevy = { version = "0.12", features = ["dynamic_linking"] }

[profile.dev]
opt-level = 1  # 轻量优化

[profile.dev.package."*"]
opt-level = 3  # 依赖全优化
```

**Q3: 如何处理不同分辨率?**

```rust
use bevy::prelude::*;
use bevy::window::WindowResized;

fn handle_resize(
    mut resize_events: EventReader<WindowResized>,
    mut camera_query: Query<&mut OrthographicProjection, With<Camera2d>>,
) {
    for event in resize_events.read() {
        let mut projection = camera_query.single_mut();
        projection.scaling_mode = bevy::render::camera::ScalingMode::AutoMin {
            min_width: 800.0,
            min_height: 600.0,
        };
    }
}
```

**Q4: 如何实现存档系统?**

```rust
use bevy::prelude::*;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct SaveData {
    player_position: (f32, f32),
    score: u32,
    level: u32,
}

fn save_game(
    player_query: Query<&Transform, With<Player>>,
    score: Res<Score>,
    level: Res<Level>,
) {
    let transform = player_query.single();
    
    let save_data = SaveData {
        player_position: (transform.translation.x, transform.translation.y),
        score: score.value,
        level: level.current,
    };
    
    let json = serde_json::to_string(&save_data).unwrap();
    std::fs::write("save.json", json).unwrap();
}

fn load_game(
    mut commands: Commands,
    mut player_query: Query<&mut Transform, With<Player>>,
) {
    if let Ok(json) = std::fs::read_to_string("save.json") {
        if let Ok(save_data) = serde_json::from_str::<SaveData>(&json) {
            let mut transform = player_query.single_mut();
            transform.translation.x = save_data.player_position.0;
            transform.translation.y = save_data.player_position.1;
            
            commands.insert_resource(Score { value: save_data.score });
            commands.insert_resource(Level { current: save_data.level });
        }
    }
}
```

**Q5: 如何发布到 WebAssembly?**

```bash
# 安装 wasm 工具
rustup target add wasm32-unknown-unknown
cargo install wasm-server-runner

# 配置 .cargo/config.toml
[target.wasm32-unknown-unknown]
runner = "wasm-server-runner"

# 编译
cargo build --release --target wasm32-unknown-unknown

# 运行
cargo run --target wasm32-unknown-unknown
```

---

## 11. 参考资源

**官方文档**:

- [Bevy 官方网站](https://bevyengine.org/)
- [Bevy Book](https://bevyengine.org/learn/book/introduction/)
- [Bevy Cheat Book](https://bevy-cheatbook.github.io/)
- [Bevy Assets](https://bevyengine.org/assets/)

**游戏引擎**:

- [Bevy](https://github.com/bevyengine/bevy)
- [Godot Rust](https://github.com/godot-rust/gdext)
- [Fyrox](https://github.com/FyroxEngine/Fyrox)
- [Macroquad](https://github.com/not-fl3/macroquad)

**物理引擎**:

- [Rapier](https://rapier.rs/)
- [bevy_rapier](https://github.com/dimforge/bevy_rapier)

**学习资源**:

- [Bevy 示例集](https://github.com/bevyengine/bevy/tree/main/examples)
- [Logic Projects - Bevy 教程](https://logicprojects.org/tags/bevy/)
- [Awesome Bevy](https://github.com/bevyengine/awesome-bevy)

**社区**:

- [Bevy Discord](https://discord.gg/bevy)
- [r/bevy](https://www.reddit.com/r/bevy/)
- [Rust GameDev WG](https://gamedev.rs/)

---

**总结**:

Rust 游戏开发结合了高性能和安全性，是独立游戏开发者的绝佳选择。
通过 Bevy 引擎的 ECS 架构和现代化的工具链，您可以快速构建出高质量的游戏原型和完整项目。
虽然 Bevy 仍在快速迭代中，但其社区活跃，生态逐渐完善，是值得投入学习的游戏开发技术栈! 🎮🦀
