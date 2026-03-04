# Rust 游戏开发完整指南

> 从入门到精通：使用 Rust 构建高性能游戏

## 目录

- [Rust 游戏开发完整指南](#rust-游戏开发完整指南)
  - [目录](#目录)
  - [1. 游戏引擎概述](#1-游戏引擎概述)
    - [1.1 Bevy 引擎](#11-bevy-引擎)
      - [核心特性](#核心特性)
      - [Bevy 系统顺序](#bevy-系统顺序)
    - [1.2 Fyrox (rg3d)](#12-fyrox-rg3d)
    - [1.3 Amethyst（归档）](#13-amethyst归档)
    - [1.4 macroquad（轻量级）](#14-macroquad轻量级)
    - [1.5 引擎选择指南](#15-引擎选择指南)
  - [2. ECS 架构](#2-ecs-架构)
    - [2.1 核心概念](#21-核心概念)
    - [2.2 数据导向设计](#22-数据导向设计)
    - [2.3 查询系统](#23-查询系统)
    - [2.4 性能优化](#24-性能优化)
  - [3. 渲染系统](#3-渲染系统)
    - [3.1 WGPU 基础](#31-wgpu-基础)
    - [3.2 材质和着色器](#32-材质和着色器)
    - [3.3 2D vs 3D 渲染](#33-2d-vs-3d-渲染)
    - [3.4 粒子系统](#34-粒子系统)
  - [4. 物理引擎](#4-物理引擎)
    - [4.1 Rapier2D/3D](#41-rapier2d3d)
    - [4.2 碰撞检测](#42-碰撞检测)
    - [4.3 刚体动力学](#43-刚体动力学)
    - [4.4 射线检测](#44-射线检测)
  - [5. 资源管理](#5-资源管理)
    - [5.1 Asset Pipeline](#51-asset-pipeline)
    - [5.2 热重载](#52-热重载)
    - [5.3 内存管理](#53-内存管理)
  - [6. 音频系统](#6-音频系统)
    - [6.1 Rodio](#61-rodio)
    - [6.2 3D 空间音频](#62-3d-空间音频)
    - [6.3 音乐流媒体](#63-音乐流媒体)
  - [7. 输入处理](#7-输入处理)
    - [7.1 键盘/鼠标](#71-键盘鼠标)
    - [7.2 游戏手柄](#72-游戏手柄)
    - [7.3 触摸输入](#73-触摸输入)
  - [8. 多人游戏](#8-多人游戏)
    - [8.1 网络同步](#81-网络同步)
    - [8.2 客户端预测](#82-客户端预测)
    - [8.3 服务器权威](#83-服务器权威)
  - [9. 完整示例：简单 3D 游戏](#9-完整示例简单-3d-游戏)
    - [9.1 场景设置](#91-场景设置)
    - [9.2 玩家控制](#92-玩家控制)
    - [9.3 敌人 AI](#93-敌人-ai)
    - [9.4 UI 系统](#94-ui-系统)
    - [9.5 游戏状态管理](#95-游戏状态管理)
  - [10. 性能优化](#10-性能优化)
    - [10.1 剖析工具](#101-剖析工具)
    - [10.2 批处理](#102-批处理)
    - [10.3 LOD（细节层次）](#103-lod细节层次)
    - [10.4 其他优化技巧](#104-其他优化技巧)
  - [总结](#总结)
  - [推荐资源](#推荐资源)
  - [下一步](#下一步)

---

## 1. 游戏引擎概述

Rust 生态系统提供了多个优秀的游戏引擎选择，每个都有其独特的优势和适用场景。

### 1.1 Bevy 引擎

Bevy 是 Rust 生态中最活跃、最受欢迎的游戏引擎之一，采用现代 ECS 架构。

#### 核心特性

```rust
// Cargo.toml
// [dependencies]
// bevy = "0.13"

use bevy::prelude::*;

fn main() {
    App::new()
        // 添加默认插件（窗口、渲染、输入等）
        .add_plugins(DefaultPlugins)
        // 启动系统
        .add_systems(Startup, setup)
        // 更新系统
        .add_systems(Update, (player_movement, camera_follow))
        .run();
}

fn setup(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
) {
    // 创建相机
    commands.spawn(Camera3dBundle {
        transform: Transform::from_xyz(0.0, 5.0, 10.0).looking_at(Vec3::ZERO, Vec3::Y),
        ..default()
    });

    // 创建光源
    commands.spawn(PointLightBundle {
        point_light: PointLight {
            intensity: 1500.0,
            shadows_enabled: true,
            ..default()
        },
        transform: Transform::from_xyz(4.0, 8.0, 4.0),
        ..default()
    });

    // 创建地面
    commands.spawn(PbrBundle {
        mesh: meshes.add(Mesh::from(shape::Plane::from_size(20.0))),
        material: materials.add(Color::rgb(0.3, 0.5, 0.3).into()),
        ..default()
    });

    // 创建玩家
    commands.spawn((
        PbrBundle {
            mesh: meshes.add(Mesh::from(shape::Cube::new(1.0))),
            material: materials.add(Color::rgb(0.8, 0.2, 0.2).into()),
            transform: Transform::from_xyz(0.0, 0.5, 0.0),
            ..default()
        },
        Player { speed: 5.0 },
    ));
}

#[derive(Component)]
struct Player {
    speed: f32,
}

fn player_movement(
    time: Res<Time>,
    keyboard_input: Res<Input<KeyCode>>,
    mut query: Query<(&mut Transform, &Player)>,
) {
    for (mut transform, player) in query.iter_mut() {
        let mut direction = Vec3::ZERO;

        if keyboard_input.pressed(KeyCode::W) {
            direction.z -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::S) {
            direction.z += 1.0;
        }
        if keyboard_input.pressed(KeyCode::A) {
            direction.x -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::D) {
            direction.x += 1.0;
        }

        if direction != Vec3::ZERO {
            direction = direction.normalize();
            transform.translation += direction * player.speed * time.delta_seconds();
        }
    }
}
```

#### Bevy 系统顺序

```rust
use bevy::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        // 使用系统集合组织更新逻辑
        .add_systems(
            Update,
            (
                input_handling,
                physics_simulation.after(input_handling),
                animation_update.after(physics_simulation),
                render_preparation.after(animation_update),
            ),
        )
        // 使用系统标签
        .configure_sets(
            Update,
            (
                GameSystemSet::Input,
                GameSystemSet::Physics.after(GameSystemSet::Input),
                GameSystemSet::Rendering.after(GameSystemSet::Physics),
            ),
        )
        .run();
}

#[derive(SystemSet, Debug, Clone, PartialEq, Eq, Hash)]
enum GameSystemSet {
    Input,
    Physics,
    Rendering,
}
```

### 1.2 Fyrox (rg3d)

Fyrox 是一个功能完整的 3D 游戏引擎，具有内置的编辑器。

```rust
// Cargo.toml
// [dependencies]
// fyrox = "0.33"

use fyrox::{
    core::{algebra::Vector3, pool::Handle},
    engine::{framework::prelude::*, Engine},
    scene::{node::Node, Scene, base::BaseBuilder, camera::CameraBuilder},
    event::Event,
};

struct Game {
    scene: Handle<Scene>,
    camera: Handle<Node>,
}

impl GameState for Game {
    fn init(engine: &mut Engine) -> Self
    where
        Self: Sized,
    {
        let mut scene = Scene::new();

        // 创建相机
        let camera = CameraBuilder::new(
            BaseBuilder::new().with_local_transform(
                TransformBuilder::new()
                    .with_local_position(Vector3::new(0.0, 5.0, -10.0))
                    .build(),
            ),
        )
        .build(&mut scene.graph);

        // 添加光源
        scene.graph.add_node(Node::new(PointLightBuilder::new(
            BaseBuilder::new().with_local_transform(
                TransformBuilder::new()
                    .with_local_position(Vector3::new(5.0, 10.0, 5.0))
                    .build(),
            ),
        )));

        let scene_handle = engine.scenes.add(scene);

        Self {
            scene: scene_handle,
            camera,
        }
    }

    fn on_tick(&mut self, engine: &mut Engine, dt: f32, _control_flow: &mut ControlFlow) {
        // 游戏逻辑更新
        let scene = &mut engine.scenes[self.scene];

        // 处理输入、更新实体等
    }

    fn on_window_event(&mut self, _engine: &mut Engine, _event: Event<()>) {
        // 处理窗口事件
    }
}

fn main() {
    Framework::new().unwrap().title("My Fyrox Game").run::<Game>();
}
```

### 1.3 Amethyst（归档）

Amethyst 是一个数据导向的游戏引擎，虽然项目已归档，但其设计理念仍有学习价值。

```rust
// Amethyst 示例（历史参考）
use amethyst::{
    prelude::*,
    renderer::{DisplayConfig, DrawFlat, Pipeline, PosNormTex, RenderBundle, Stage},
    core::transform::TransformBundle,
    input::InputBundle,
};

struct GameState;

impl SimpleState for GameState {
    fn on_start(&mut self, data: StateData<'_, GameData<'_, '_>>) {
        // 初始化游戏世界
    }

    fn update(&mut self, data: &mut StateData<'_, GameData<'_, '_>>) -> SimpleTrans {
        Trans::None
    }
}

fn main() -> amethyst::Result<()> {
    let pipe = Pipeline::build().with_stage(
        Stage::with_backbuffer()
            .clear_target([0.0, 0.0, 0.0, 1.0], 1.0)
            .with_pass(DrawFlat::<PosNormTex>::new()),
    );

    let game_data = GameDataBuilder::default()
        .with_bundle(RenderBundle::new(pipe, Some(DisplayConfig::default())))?
        .with_bundle(TransformBundle::new())?
        .with_bundle(InputBundle::<StringBindings>::new())?;

    let mut game = Application::new("./", GameState, game_data)?;
    game.run();
    Ok(())
}
```

### 1.4 macroquad（轻量级）

macroquad 是一个极简的 2D 游戏框架，非常适合原型开发和小型游戏。

```rust
// Cargo.toml
// [dependencies]
// macroquad = "0.4"

use macroquad::prelude::*;

struct Player {
    pos: Vec2,
    velocity: Vec2,
    size: f32,
    color: Color,
}

impl Player {
    fn new(x: f32, y: f32) -> Self {
        Self {
            pos: vec2(x, y),
            velocity: vec2(0.0, 0.0),
            size: 32.0,
            color: GREEN,
        }
    }

    fn update(&mut self, dt: f32) {
        // 输入处理
        let speed = 200.0;
        let mut move_dir = vec2(0.0, 0.0);

        if is_key_down(KeyCode::W) {
            move_dir.y -= 1.0;
        }
        if is_key_down(KeyCode::S) {
            move_dir.y += 1.0;
        }
        if is_key_down(KeyCode::A) {
            move_dir.x -= 1.0;
        }
        if is_key_down(KeyCode::D) {
            move_dir.x += 1.0;
        }

        if move_dir != vec2(0.0, 0.0) {
            move_dir = move_dir.normalize();
            self.velocity = move_dir * speed;
        } else {
            // 摩擦力
            self.velocity *= 0.9;
        }

        // 更新位置
        self.pos += self.velocity * dt;

        // 边界检查
        self.pos.x = self.pos.x.clamp(self.size / 2.0, screen_width() - self.size / 2.0);
        self.pos.y = self.pos.y.clamp(self.size / 2.0, screen_height() - self.size / 2.0);
    }

    fn draw(&self) {
        draw_rectangle(
            self.pos.x - self.size / 2.0,
            self.pos.y - self.size / 2.0,
            self.size,
            self.size,
            self.color,
        );
    }
}

#[macroquad::main("Simple Game")]
async fn main() {
    let mut player = Player::new(screen_width() / 2.0, screen_height() / 2.0);
    let mut score = 0;
    let mut game_time = 0.0;

    loop {
        let dt = get_frame_time();
        game_time += dt;

        // 更新
        player.update(dt);

        // 渲染
        clear_background(DARKGRAY);

        player.draw();

        // UI
        draw_text(&format!("Score: {}", score), 10.0, 30.0, 30.0, WHITE);
        draw_text(&format!("Time: {:.1}", game_time), 10.0, 60.0, 20.0, GRAY);

        // 简单敌人
        let enemy_pos = vec2(
            screen_width() / 2.0 + (game_time * 2.0).sin() * 200.0,
            screen_height() / 2.0 + (game_time * 1.5).cos() * 100.0,
        );
        draw_circle(enemy_pos.x, enemy_pos.y, 20.0, RED);

        // 碰撞检测
        if player.pos.distance(enemy_pos) < (player.size / 2.0 + 20.0) {
            draw_text("COLLISION!", screen_width() / 2.0 - 50.0, screen_height() / 2.0, 40.0, YELLOW);
        }

        next_frame().await;
    }
}
```

### 1.5 引擎选择指南

| 引擎 | 适用场景 | 学习曲线 | 社区活跃度 | 特性 |
|------|----------|----------|------------|------|
| **Bevy** | 2D/3D 游戏 | 中等 | 高 | 现代 ECS、热重载、跨平台 |
| **Fyrox** | 3D 游戏 | 陡峭 | 中 | 内置编辑器、完整功能集 |
| **macroquad** | 2D 原型 | 平缓 | 中 | 轻量级、快速开发 |
| **ggez** | 2D 游戏 | 平缓 | 中 | 简单 API、适合初学者 |

---

## 2. ECS 架构

Entity-Component-System (ECS) 是现代游戏开发的核心架构模式，强调数据导向设计。

### 2.1 核心概念

```rust
use bevy::prelude::*;

// ========== Component（组件）==========
// 组件是纯数据结构，描述实体的属性

#[derive(Component)]
struct Position {
    x: f32,
    y: f32,
}

#[derive(Component)]
struct Velocity {
    x: f32,
    y: f32,
}

#[derive(Component)]
struct Health {
    current: i32,
    max: i32,
}

#[derive(Component)]
struct Player;

#[derive(Component)]
struct Enemy {
    ai_type: AiType,
}

enum AiType {
    Patrolling,
    Chasing,
    Stationary,
}

// ========== Entity（实体）==========
// 实体是组件的容器，本质上是唯一 ID

fn spawn_entities(mut commands: Commands) {
    // 创建玩家实体
    commands.spawn((
        Position { x: 0.0, y: 0.0 },
        Velocity { x: 0.0, y: 0.0 },
        Health { current: 100, max: 100 },
        Player,
    ));

    // 创建敌人实体
    commands.spawn((
        Position { x: 10.0, y: 5.0 },
        Velocity { x: 0.0, y: 0.0 },
        Health { current: 50, max: 50 },
        Enemy { ai_type: AiType::Patrolling },
    ));

    // 创建只有位置的静态物体
    commands.spawn(Position { x: 5.0, y: 5.0 });
}

// ========== System（系统）==========
// 系统是处理逻辑的功能函数，操作组件数据

// 更新位置系统
fn update_positions(
    time: Res<Time>,
    mut query: Query<(&mut Position, &Velocity)>,
) {
    for (mut position, velocity) in query.iter_mut() {
        position.x += velocity.x * time.delta_seconds();
        position.y += velocity.y * time.delta_seconds();
    }
}

// 玩家输入系统
fn player_input(
    keyboard_input: Res<Input<KeyCode>>,
    mut query: Query<&mut Velocity, With<Player>>,
) {
    for mut velocity in query.iter_mut() {
        let speed = 5.0;

        velocity.x = 0.0;
        velocity.y = 0.0;

        if keyboard_input.pressed(KeyCode::W) {
            velocity.y = speed;
        }
        if keyboard_input.pressed(KeyCode::S) {
            velocity.y = -speed;
        }
        if keyboard_input.pressed(KeyCode::A) {
            velocity.x = -speed;
        }
        if keyboard_input.pressed(KeyCode::D) {
            velocity.x = speed;
        }
    }
}

// AI 系统 - 只处理有 Enemy 组件的实体
fn enemy_ai(
    time: Res<Time>,
    mut enemies: Query<(&mut Velocity, &Position, &Enemy), Without<Player>>,
    players: Query<&Position, With<Player>>,
) {
    if let Ok(player_pos) = players.get_single() {
        for (mut velocity, enemy_pos, enemy) in enemies.iter_mut() {
            match enemy.ai_type {
                AiType::Chasing => {
                    let direction = Vec2::new(
                        player_pos.x - enemy_pos.x,
                        player_pos.y - enemy_pos.y,
                    ).normalize();

                    velocity.x = direction.x * 2.0;
                    velocity.y = direction.y * 2.0;
                }
                AiType::Patrolling => {
                    // 简单的巡逻逻辑
                    velocity.x = (time.elapsed_seconds() * 2.0).sin() * 1.0;
                    velocity.y = (time.elapsed_seconds() * 1.5).cos() * 1.0;
                }
                AiType::Stationary => {
                    velocity.x = 0.0;
                    velocity.y = 0.0;
                }
            }
        }
    }
}
```

### 2.2 数据导向设计

ECS 的核心优势在于数据局部性和缓存友好性。

```rust
use bevy::prelude::*;

// 传统 OOP 方式（不推荐）
// 每个实体都有不同的内存布局，缓存不友好
struct GameObject {
    position: Position,
    velocity: Option<Velocity>,
    health: Option<Health>,
    sprite: Option<Sprite>,
    // ... 更多可选字段
}

// ECS 方式（推荐）
// 组件按类型连续存储，CPU 缓存命中率高

#[derive(Component, Default)]
struct Position(Vec3);

#[derive(Component, Default)]
struct Velocity(Vec3);

#[derive(Component, Default)]
struct Acceleration(Vec3);

#[derive(Component)]
struct Mass(f32);

// 系统只处理需要的组件，数据局部性极佳
fn physics_simulation(
    time: Res<Time>,
    mut query: Query<(&mut Position, &mut Velocity, &Acceleration, Option<&Mass>)>,
) {
    let dt = time.delta_seconds();

    // 所有数据连续存储，CPU 可以高效预取
    for (mut pos, mut vel, acc, mass) in query.iter_mut() {
        let m = mass.map(|m| m.0).unwrap_or(1.0);

        // v = v + a * dt
        vel.0 += acc.0 * dt / m;

        // p = p + v * dt
        pos.0 += vel.0 * dt;
    }
}

// 批量处理 - SoA (Structure of Arrays) 优化
#[derive(Component)]
struct Particle {
    lifetime: f32,
    max_lifetime: f32,
}

fn update_particles(
    time: Res<Time>,
    mut commands: Commands,
    mut particles: Query<(Entity, &mut Position, &mut Particle)>,
) {
    for (entity, mut pos, mut particle) in particles.iter_mut() {
        particle.lifetime -= time.delta_seconds();

        if particle.lifetime <= 0.0 {
            // 销毁过期粒子
            commands.entity(entity).despawn();
        } else {
            // 粒子下落效果
            pos.0.y -= time.delta_seconds() * 2.0;
        }
    }
}
```

### 2.3 查询系统

Bevy 的查询系统提供了强大的组件筛选能力。

```rust
use bevy::prelude::*;

#[derive(Component)]
struct Position(Vec3);

#[derive(Component)]
struct Velocity(Vec3);

#[derive(Component)]
struct Health(f32);

#[derive(Component)]
struct Invulnerable;

#[derive(Component)]
struct Enemy;

#[derive(Component)]
struct Boss;

// 基础查询 - 获取所有有 Position 和 Velocity 的实体
fn basic_query(query: Query<(&Position, &Velocity)>) {
    for (pos, vel) in query.iter() {
        println!("Entity at {:?} moving at {:?}", pos.0, vel.0);
    }
}

// 可变查询 - 修改组件
fn mutable_query(mut query: Query<&mut Position>) {
    for mut pos in query.iter_mut() {
        pos.0.y += 1.0;
    }
}

// 使用 With - 筛选包含特定组件的实体
fn players_only(query: Query<&Position, With<Player>>) {
    for pos in query.iter() {
        println!("Player at {:?}", pos.0);
    }
}

// 使用 Without - 排除特定组件
fn damageable_entities(query: Query<(Entity, &Health), Without<Invulnerable>>) {
    for (entity, health) in query.iter() {
        if health.0 <= 0.0 {
            println!("Entity {:?} should die", entity);
        }
    }
}

// 组合过滤
fn complex_query(
    // 所有敌人，但不是 Boss
    normal_enemies: Query<&Position, (With<Enemy>, Without<Boss>)>,
    // 所有 Boss
    bosses: Query<&Position, With<Boss>>,
    // 所有可移动的实体
    movable: Query<(&Position, &Velocity)>,
) {
    // 处理普通敌人
    for pos in normal_enemies.iter() {
        println!("Normal enemy at {:?}", pos.0);
    }

    // 处理 Boss
    for pos in bosses.iter() {
        println!("Boss at {:?}", pos.0);
    }
}

// 可选组件
fn optional_components(query: Query<(&Position, Option<&Velocity>)>) {
    for (pos, maybe_vel) in query.iter() {
        match maybe_vel {
            Some(vel) => println!("Entity at {:?} moving at {:?}", pos.0, vel.0),
            None => println!("Entity at {:?} is stationary", pos.0),
        }
    }
}

// 查询单个实体
fn single_entity(query: Query<&Position, With<Player>>) {
    // 如果确定只有一个匹配实体
    if let Ok(pos) = query.get_single() {
        println!("Player at {:?}", pos.0);
    }
}

// 通过 Entity ID 查询
fn get_by_id(
    mut commands: Commands,
    entity_query: Query<Entity>,
    mut specific_query: Query<&mut Position>,
) {
    for entity in entity_query.iter() {
        // 获取特定实体的组件
        if let Ok(mut pos) = specific_query.get_mut(entity) {
            pos.0.x += 1.0;
        }

        // 添加组件
        commands.entity(entity).insert(Velocity(Vec3::ZERO));
    }
}

// 组合过滤条件
#[derive(Component)]
struct Active;

fn active_entities(query: Query<Entity, (With<Active>, Or<(With<Player>, With<Enemy>)>)>) {
    for entity in query.iter() {
        println!("Active game entity: {:?}", entity);
    }
}

// 嵌套查询
fn nested_queries(
    mut commands: Commands,
    entities: Query<Entity>,
    mut positions: Query<&mut Position>,
    velocities: Query<&Velocity>,
) {
    for entity in entities.iter() {
        // 安全地获取多个组件
        if let (Ok(mut pos), Ok(vel)) = (
            positions.get_mut(entity),
            velocities.get(entity),
        ) {
            pos.0 += vel.0;
        }
    }
}
```

### 2.4 性能优化

```rust
use bevy::prelude::*;

// ========== 并行系统 ==========
// Bevy 自动并行化不冲突的系统

fn system_a(query: Query<&Position>) {
    // 只读 Position
}

fn system_b(query: Query<&Velocity>) {
    // 只读 Velocity - 可以与 system_a 并行
}

fn system_c(query: Query<(&mut Position, &Velocity)>) {
    // 写入 Position，读取 Velocity
}

// ========== 系统配置 ==========
fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Update, (
            // 这些系统可以并行运行
            system_a,
            system_b,
            // system_c 必须等待前两个完成
            system_c.after(system_a).after(system_b),
        ))
        .run();
}

// ========== 批处理优化 ==========
#[derive(Component)]
struct BatchRenderData {
    meshes: Vec<Handle<Mesh>>,
    materials: Vec<Handle<StandardMaterial>>,
}

// 批量生成实体
fn batch_spawn(mut commands: Commands) {
    // 一次性生成大量实体
    commands.spawn_batch((0..1000).map(|i| {
        (
            Position(Vec3::new(i as f32 * 2.0, 0.0, 0.0)),
            Velocity(Vec3::new(0.0, 0.0, 0.0)),
        )
    }));
}

// 批量销毁
fn batch_despawn(
    mut commands: Commands,
    query: Query<Entity, With<Enemy>>,
) {
    // 一次性销毁所有敌人
    for entity in query.iter() {
        commands.entity(entity).despawn();
    }
}

// ========== 事件系统 ==========
#[derive(Event)]
struct DamageEvent {
    target: Entity,
    amount: f32,
}

fn send_damage_events(
    mut events: EventWriter<DamageEvent>,
    query: Query<(Entity, &Health)>,
) {
    for (entity, health) in query.iter() {
        if health.0 < 50.0 {
            events.send(DamageEvent {
                target: entity,
                amount: 10.0,
            });
        }
    }
}

fn process_damage_events(
    mut events: EventReader<DamageEvent>,
    mut query: Query<&mut Health>,
) {
    for event in events.read() {
        if let Ok(mut health) = query.get_mut(event.target) {
            health.0 -= event.amount;
        }
    }
}

// ========== 资源优化 ==========
#[derive(Resource, Default)]
struct GameState {
    score: i32,
    level: u32,
    paused: bool,
}

#[derive(Resource)]
struct GameConfig {
    player_speed: f32,
    enemy_spawn_rate: f32,
    gravity: f32,
}

impl Default for GameConfig {
    fn default() -> Self {
        Self {
            player_speed: 10.0,
            enemy_spawn_rate: 1.0,
            gravity: 9.8,
        }
    }
}

fn use_resources(
    state: Res<GameState>,
    config: Res<GameConfig>,
    mut local_state: Local<u32>,
) {
    if !state.paused {
        *local_state += 1;
        println!("Frame {} - Score: {}, Speed: {}",
            *local_state, state.score, config.player_speed);
    }
}

// ========== 状态机 ==========
#[derive(States, Default, Debug, Clone, PartialEq, Eq, Hash)]
enum AppState {
    #[default]
    Loading,
    MainMenu,
    InGame,
    Paused,
    GameOver,
}

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .init_state::<AppState>()
        // 只在 Loading 状态运行的系统
        .add_systems(OnEnter(AppState::Loading), load_assets)
        .add_systems(Update, check_loading.run_if(in_state(AppState::Loading)))
        // 只在 InGame 状态运行的系统
        .add_systems(Update, (
            player_movement,
            enemy_ai,
            physics_update,
        ).run_if(in_state(AppState::InGame)))
        // 暂停系统
        .add_systems(Update, toggle_pause.run_if(in_state(AppState::InGame)))
        .run();
}

fn toggle_pause(
    keyboard_input: Res<Input<KeyCode>>,
    mut next_state: ResMut<NextState<AppState>>,
) {
    if keyboard_input.just_pressed(KeyCode::Escape) {
        next_state.set(AppState::Paused);
    }
}
```

---

## 3. 渲染系统

### 3.1 WGPU 基础

WGPU 是 Rust 生态的现代图形 API，基于 WebGPU 标准。

```rust
// 基础 WGPU 设置
use wgpu::util::DeviceExt;

async fn setup_wgpu(window: &winit::window::Window) -> (wgpu::Device, wgpu::Queue, wgpu::Surface) {
    let instance = wgpu::Instance::new(wgpu::InstanceDescriptor {
        backends: wgpu::Backends::all(),
        ..default()
    });

    let surface = unsafe { instance.create_surface(window) }.unwrap();

    let adapter = instance
        .request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: Some(&surface),
            force_fallback_adapter: false,
        })
        .await
        .unwrap();

    let (device, queue) = adapter
        .request_device(
            &wgpu::DeviceDescriptor {
                features: wgpu::Features::empty(),
                limits: wgpu::Limits::default(),
                label: None,
            },
            None,
        )
        .await
        .unwrap();

    (device, queue, surface)
}
```

### 3.2 材质和着色器

```rust
// Bevy 中的材质系统
use bevy::prelude::*;

// 自定义材质
#[derive(Asset, TypePath, AsBindGroup, Debug, Clone)]
pub struct CustomMaterial {
    #[uniform(0)]
    pub color: Color,
    #[texture(1)]
    #[sampler(2)]
    pub base_color_texture: Option<Handle<Image>>,
    #[uniform(3)]
    pub time: f32,
}

impl Material for CustomMaterial {
    fn fragment_shader() -> ShaderRef {
        "shaders/custom.wgsl".into()
    }
}

// WGSL 着色器示例 (assets/shaders/custom.wgsl)
/*
#import bevy_pbr::mesh_functions::{get_world_from_local, mesh_position_local_to_clip}

@group(0) @binding(0) var<uniform> material: CustomMaterial;
@group(0) @binding(1) var base_color_texture: texture_2d<f32>;
@group(0) @binding(2) var base_color_sampler: sampler;
@group(0) @binding(3) var<uniform> time: f32;

struct CustomMaterial {
    color: vec4<f32>,
    time: f32,
};

struct VertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) uv: vec2<f32>,
    @location(1) world_position: vec3<f32>,
};

@vertex
fn vertex(
    @location(0) position: vec3<f32>,
    @location(1) uv: vec2<f32>,
) -> VertexOutput {
    var output: VertexOutput;

    // 简单的波浪动画
    var animated_position = position;
    animated_position.y += sin(position.x * 2.0 + time) * 0.2;

    output.clip_position = mesh_position_local_to_clip(
        get_world_from_local(0u),
        vec4<f32>(animated_position, 1.0),
    );
    output.uv = uv;
    output.world_position = animated_position;

    return output;
}

@fragment
fn fragment(input: VertexOutput) -> @location(0) vec4<f32> {
    let texture_color = textureSample(base_color_texture, base_color_sampler, input.uv);

    // 脉冲效果
    let pulse = (sin(time * 2.0) + 1.0) * 0.5;
    let glow_color = vec4<f32>(0.2, 0.5, 1.0, 1.0) * pulse;

    return texture_color * material.color + glow_color * 0.3;
}
*/

// 使用自定义材质
fn setup_custom_material(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<CustomMaterial>>,
    asset_server: Res<AssetServer>,
) {
    // 加载纹理
    let texture_handle = asset_server.load("textures/custom.png");

    // 创建自定义材质
    let material_handle = materials.add(CustomMaterial {
        color: Color::WHITE,
        base_color_texture: Some(texture_handle),
        time: 0.0,
    });

    // 应用到网格
    commands.spawn(MaterialMeshBundle {
        mesh: meshes.add(Mesh::from(shape::Cube::new(1.0))),
        material: material_handle,
        transform: Transform::from_xyz(0.0, 0.5, 0.0),
        ..default()
    });
}

// 动画材质时间
fn animate_material_time(
    time: Res<Time>,
    mut materials: ResMut<Assets<CustomMaterial>>,
) {
    for (_, material) in materials.iter_mut() {
        material.time = time.elapsed_seconds();
    }
}
```

### 3.3 2D vs 3D 渲染

```rust
use bevy::prelude::*;

// ========== 2D 渲染 ==========
fn setup_2d_scene(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
    mut texture_atlases: ResMut<Assets<TextureAtlas>>,
) {
    // 2D 相机
    commands.spawn(Camera2dBundle::default());

    // 精灵（Sprite）
    commands.spawn(SpriteBundle {
        texture: asset_server.load("sprites/player.png"),
        transform: Transform::from_xyz(100.0, 100.0, 0.0)
            .with_scale(Vec3::new(2.0, 2.0, 1.0)),
        ..default()
    });

    // 精灵图集（动画）
    let texture_handle = asset_server.load("sprites/animation.png");
    let texture_atlas = TextureAtlas::from_grid(
        texture_handle,
        Vec2::new(32.0, 32.0),
        4, // 列数
        1, // 行数
        None,
        None,
    );
    let texture_atlas_handle = texture_atlases.add(texture_atlas);

    commands.spawn((
        SpriteSheetBundle {
            texture_atlas: texture_atlas_handle,
            sprite: TextureAtlasSprite::new(0),
            transform: Transform::from_xyz(0.0, 0.0, 0.0),
            ..default()
        },
        AnimationTimer(Timer::from_seconds(0.1, TimerMode::Repeating)),
    ));
}

#[derive(Component)]
struct AnimationTimer(Timer);

fn animate_sprite(
    time: Res<Time>,
    mut query: Query<(&mut AnimationTimer, &mut TextureAtlasSprite)>,
) {
    for (mut timer, mut sprite) in query.iter_mut() {
        timer.0.tick(time.delta());
        if timer.0.just_finished() {
            sprite.index = (sprite.index + 1) % 4;
        }
    }
}

// ========== 3D 渲染 ==========
fn setup_3d_scene(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
) {
    // 3D 相机
    commands.spawn(Camera3dBundle {
        transform: Transform::from_xyz(10.0, 10.0, 10.0)
            .looking_at(Vec3::ZERO, Vec3::Y),
        ..default()
    });

    // 环境光
    commands.insert_resource(AmbientLight {
        color: Color::WHITE,
        brightness: 0.3,
    });

    // 定向光
    commands.spawn(DirectionalLightBundle {
        directional_light: DirectionalLight {
            illuminance: 10000.0,
            shadows_enabled: true,
            ..default()
        },
        transform: Transform::from_xyz(5.0, 10.0, 5.0)
            .looking_at(Vec3::ZERO, Vec3::Y),
        ..default()
    });

    // 点光源
    commands.spawn(PointLightBundle {
        point_light: PointLight {
            intensity: 1000.0,
            color: Color::ORANGE,
            shadows_enabled: true,
            ..default()
        },
        transform: Transform::from_xyz(-5.0, 5.0, -5.0),
        ..default()
    });

    // 3D 网格
    // 立方体
    commands.spawn(PbrBundle {
        mesh: meshes.add(Mesh::from(shape::Cube::new(1.0))),
        material: materials.add(StandardMaterial {
            base_color: Color::RED,
            metallic: 0.5,
            perceptual_roughness: 0.3,
            ..default()
        }),
        transform: Transform::from_xyz(0.0, 0.5, 0.0),
        ..default()
    });

    // 球体
    commands.spawn(PbrBundle {
        mesh: meshes.add(Mesh::from(shape::UVSphere {
            radius: 0.5,
            sectors: 32,
            stacks: 16,
        })),
        material: materials.add(StandardMaterial {
            base_color: Color::BLUE,
            metallic: 0.8,
            perceptual_roughness: 0.2,
            ..default()
        }),
        transform: Transform::from_xyz(2.0, 0.5, 0.0),
        ..default()
    });

    // 平面（地面）
    commands.spawn(PbrBundle {
        mesh: meshes.add(Mesh::from(shape::Plane::from_size(20.0))),
        material: materials.add(StandardMaterial {
            base_color: Color::GRAY,
            ..default()
        }),
        ..default()
    });
}

// ========== 混合 2D/3D ==========
fn setup_mixed_scene(mut commands: Commands) {
    // 先设置 3D 场景
    commands.spawn(Camera3dBundle {
        transform: Transform::from_xyz(0.0, 5.0, 10.0)
            .looking_at(Vec3::ZERO, Vec3::Y),
        ..default()
    });

    // 3D 物体
    // ...

    // UI 相机（始终在最上层）
    commands.spawn(Camera2dBundle {
        camera: Camera {
            order: 1, // 在 3D 相机之后渲染
            ..default()
        },
        ..default()
    });
}
```

### 3.4 粒子系统

```rust
use bevy::prelude::*;
use rand::Rng;

#[derive(Component)]
struct Particle {
    velocity: Vec3,
    lifetime: Timer,
    initial_size: f32,
}

#[derive(Component)]
struct ParticleEmitter {
    spawn_rate: f32,
    spawn_timer: Timer,
    particle_lifetime: f32,
    velocity_range: (Vec3, Vec3),
    color_over_lifetime: Vec<Color>,
    size_over_lifetime: Vec<f32>,
}

fn spawn_particles(
    time: Res<Time>,
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
    mut emitters: Query<(&mut ParticleEmitter, &Transform)>,
) {
    let mut rng = rand::thread_rng();

    for (mut emitter, transform) in emitters.iter_mut() {
        emitter.spawn_timer.tick(time.delta());

        while emitter.spawn_timer.just_finished() {
            // 随机速度
            let velocity = Vec3::new(
                rng.gen_range(emitter.velocity_range.0.x..emitter.velocity_range.1.x),
                rng.gen_range(emitter.velocity_range.0.y..emitter.velocity_range.1.y),
                rng.gen_range(emitter.velocity_range.0.z..emitter.velocity_range.1.z),
            );

            // 创建粒子
            commands.spawn((
                PbrBundle {
                    mesh: meshes.add(Mesh::from(shape::Cube::new(0.1))),
                    material: materials.add(StandardMaterial {
                        base_color: emitter.color_over_lifetime[0],
                        emissive: emitter.color_over_lifetime[0] * 2.0,
                        ..default()
                    }),
                    transform: Transform::from_translation(transform.translation),
                    ..default()
                },
                Particle {
                    velocity,
                    lifetime: Timer::from_seconds(emitter.particle_lifetime, TimerMode::Once),
                    initial_size: 0.1,
                },
            ));

            // 重置计时器
            emitter.spawn_timer = Timer::from_seconds(1.0 / emitter.spawn_rate, TimerMode::Once);
        }
    }
}

fn update_particles(
    time: Res<Time>,
    mut commands: Commands,
    mut particles: Query<(Entity, &mut Particle, &mut Transform, &Handle<StandardMaterial>)>,
    mut materials: ResMut<Assets<StandardMaterial>>,
) {
    for (entity, mut particle, mut transform, material_handle) in particles.iter_mut() {
        particle.lifetime.tick(time.delta());

        let life_ratio = 1.0 - particle.lifetime.fraction_remaining();

        // 更新位置
        transform.translation += particle.velocity * time.delta_seconds();

        // 重力效果
        particle.velocity.y -= 9.8 * time.delta_seconds();

        // 更新颜色（淡出）
        if let Some(material) = materials.get_mut(material_handle) {
            let alpha = 1.0 - life_ratio;
            material.base_color.set_a(alpha);
            material.emissive = material.base_color * (2.0 * (1.0 - life_ratio));
        }

        // 销毁过期粒子
        if particle.lifetime.finished() {
            commands.entity(entity).despawn();
        }
    }
}

// 预设：爆炸效果
fn create_explosion(
    commands: &mut Commands,
    meshes: &mut ResMut<Assets<Mesh>>,
    materials: &mut ResMut<Assets<StandardMaterial>>,
    position: Vec3,
) {
    let mut rng = rand::thread_rng();
    let colors = vec![
        Color::YELLOW,
        Color::ORANGE,
        Color::RED,
    ];

    for i in 0..50 {
        let angle = rng.gen_range(0.0..std::f32::consts::TAU);
        let speed = rng.gen_range(3.0..8.0);
        let velocity = Vec3::new(
            angle.cos() * speed,
            rng.gen_range(2.0..5.0),
            angle.sin() * speed,
        );

        commands.spawn((
            PbrBundle {
                mesh: meshes.add(Mesh::from(shape::Cube::new(rng.gen_range(0.05..0.15)))),
                material: materials.add(StandardMaterial {
                    base_color: colors[rng.gen_range(0..colors.len())],
                    emissive: Color::ORANGE_RED * 3.0,
                    ..default()
                }),
                transform: Transform::from_translation(position),
                ..default()
            },
            Particle {
                velocity,
                lifetime: Timer::from_seconds(rng.gen_range(0.5..1.5), TimerMode::Once),
                initial_size: 0.1,
            },
        ));
    }
}
```

---

## 4. 物理引擎

### 4.1 Rapier2D/3D

Rapier 是 Rust 的高性能物理引擎。

```rust
// Cargo.toml
// [dependencies]
// bevy = "0.13"
// bevy_rapier3d = "0.25"

use bevy::prelude::*;
use bevy_rapier3d::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_plugins(RapierPhysicsPlugin::<NoUserData>::default())
        // 启用调试渲染（开发时有用）
        .add_plugins(RapierDebugRenderPlugin::default())
        .add_systems(Startup, setup_physics)
        .add_systems(Update, (player_controller, projectile_system))
        .run();
}

fn setup_physics(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
) {
    // 重力设置
    commands.insert_resource(Gravity::from(Vec3::new(0.0, -9.81, 0.0)));

    // ========== 静态地面 ==========
    commands.spawn((
        // 视觉
        PbrBundle {
            mesh: meshes.add(Mesh::from(shape::Plane::from_size(50.0))),
            material: materials.add(Color::DARK_GREEN.into()),
            ..default()
        },
        // 物理：静态刚体
        RigidBody::Fixed,
        // 碰撞器
        Collider::cuboid(25.0, 0.1, 25.0),
        // 物理材质
        Friction::coefficient(0.7),
        Restitution::coefficient(0.1),
    ));

    // ========== 动态箱子 ==========
    for i in 0..5 {
        commands.spawn((
            PbrBundle {
                mesh: meshes.add(Mesh::from(shape::Cube::new(1.0))),
                material: materials.add(Color::rgb(0.8, 0.4, 0.2).into()),
                transform: Transform::from_xyz(i as f32 * 2.0, 5.0 + i as f32 * 2.0, 0.0),
                ..default()
            },
            // 动态刚体
            RigidBody::Dynamic,
            // 立方体碰撞器
            Collider::cuboid(0.5, 0.5, 0.5),
            // 质量属性
            ColliderMassProperties::Density(1.0),
            // 摩擦力
            Friction::coefficient(0.5),
            // 弹性
            Restitution::coefficient(0.3),
        ));
    }

    // ========== 球体 ==========
    commands.spawn((
        PbrBundle {
            mesh: meshes.add(Mesh::from(shape::UVSphere {
                radius: 0.5,
                sectors: 32,
                stacks: 16,
            })),
            material: materials.add(StandardMaterial {
                base_color: Color::BLUE,
                metallic: 0.5,
                perceptual_roughness: 0.3,
                ..default()
            }),
            transform: Transform::from_xyz(-3.0, 10.0, 0.0),
            ..default()
        },
        RigidBody::Dynamic,
        Collider::ball(0.5),
        ColliderMassProperties::Density(2.0),
        Restitution::coefficient(0.8), // 高弹性，像橡胶球
    ));

    // ========== 玩家角色 ==========
    commands.spawn((
        PbrBundle {
            mesh: meshes.add(Mesh::from(shape::Capsule {
                radius: 0.5,
                depth: 1.0,
                ..default()
            })),
            material: materials.add(Color::GOLD.into()),
            transform: Transform::from_xyz(0.0, 2.0, 0.0),
            ..default()
        },
        RigidBody::Dynamic,
        // 胶囊体碰撞器
        Collider::capsule_y(0.5, 0.5),
        // 锁定旋转（防止玩家倒下）
        LockedAxes::ROTATION_LOCKED,
        // 额外阻尼（更好的控制感）
        Damping {
            linear_damping: 2.0,
            angular_damping: 2.0,
        },
        PlayerController {
            speed: 10.0,
            jump_force: 15.0,
        },
    ));
}

#[derive(Component)]
struct PlayerController {
    speed: f32,
    jump_force: f32,
}

fn player_controller(
    keyboard_input: Res<Input<KeyCode>>,
    mut players: Query<(&mut Velocity, &PlayerController), With<PlayerController>>,
) {
    for (mut velocity, controller) in players.iter_mut() {
        let mut move_direction = Vec3::ZERO;

        if keyboard_input.pressed(KeyCode::W) {
            move_direction.z -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::S) {
            move_direction.z += 1.0;
        }
        if keyboard_input.pressed(KeyCode::A) {
            move_direction.x -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::D) {
            move_direction.x += 1.0;
        }

        // 应用移动速度
        if move_direction != Vec3::ZERO {
            move_direction = move_direction.normalize();
            velocity.linvel.x = move_direction.x * controller.speed;
            velocity.linvel.z = move_direction.z * controller.speed;
        } else {
            // 停止时减速
            velocity.linvel.x *= 0.8;
            velocity.linvel.z *= 0.8;
        }

        // 跳跃
        if keyboard_input.just_pressed(KeyCode::Space) {
            // 检查是否在地面（简化版本）
            velocity.linvel.y = controller.jump_force;
        }
    }
}
```

### 4.2 碰撞检测

```rust
use bevy::prelude::*;
use bevy_rapier3d::prelude::*;

// ========== 碰撞事件处理 ==========
fn handle_collisions(
    mut collision_events: EventReader<CollisionEvent>,
    mut contact_forces: EventReader<ContactForceEvent>,
    mut commands: Commands,
    query: Query<(Entity, &Health, Option<&Destructible>)>,
) {
    for collision_event in collision_events.read() {
        match collision_event {
            CollisionEvent::Started(entity1, entity2, flags) => {
                println!("Collision started between {:?} and {:?}", entity1, entity2);

                // 检查是否需要处理碰撞
                if let (Ok((e1, health1, dest1)), Ok((e2, health2, dest2))) =
                    (query.get(*entity1), query.get(*entity2)) {

                    // 处理伤害逻辑
                    // ...
                }
            }
            CollisionEvent::Stopped(entity1, entity2, flags) => {
                println!("Collision ended between {:?} and {:?}", entity1, entity2);
            }
        }
    }

    // 处理接触力（用于冲击力效果）
    for contact_force in contact_forces.read() {
        println!(
            "Contact force: {} between {:?} and {:?}",
            contact_force.max_force_magnitude,
            contact_force.collider1,
            contact_force.collider2
        );
    }
}

// ========== 传感器（触发器）==========
#[derive(Component)]
struct DeathZone;

#[derive(Component)]
struct Checkpoint;

fn setup_triggers(mut commands: Commands) {
    // 死亡区域
    commands.spawn((
        TransformBundle::from_transform(Transform::from_xyz(0.0, -10.0, 0.0)),
        Collider::cuboid(50.0, 1.0, 50.0),
        Sensor, // 传感器不产生物理碰撞，只检测进入/离开
        DeathZone,
        ActiveEvents::COLLISION_EVENTS,
    ));

    // 检查点
    commands.spawn((
        TransformBundle::from_transform(Transform::from_xyz(10.0, 1.0, 10.0)),
        Collider::ball(2.0),
        Sensor,
        Checkpoint,
        ActiveEvents::COLLISION_EVENTS,
    ));
}

fn handle_sensor_events(
    mut collision_events: EventReader<CollisionEvent>,
    death_zones: Query<(), With<DeathZone>>,
    checkpoints: Query<(), With<Checkpoint>>,
    players: Query<(), With<PlayerController>>,
    mut game_state: ResMut<GameState>,
) {
    for event in collision_events.read() {
        if let CollisionEvent::Started(entity1, entity2, _) = event {
            // 检查是否是玩家触发了传感器
            let player_entity = if players.get(*entity1).is_ok() {
                *entity1
            } else if players.get(*entity2).is_ok() {
                *entity2
            } else {
                continue;
            };

            let other_entity = if *entity1 == player_entity { *entity2 } else { *entity1 };

            // 检查传感器类型
            if death_zones.get(other_entity).is_ok() {
                println!("Player fell into death zone!");
                // 处理玩家死亡
            } else if checkpoints.get(other_entity).is_ok() {
                println!("Checkpoint reached!");
                // 保存检查点
            }
        }
    }
}

// ========== 连续碰撞检测（CCD）==========
fn setup_fast_objects(mut commands: Commands) {
    commands.spawn((
        RigidBody::Dynamic,
        Collider::ball(0.1),
        Ccd::enabled(), // 启用连续碰撞检测，防止高速物体穿透
        Transform::from_xyz(0.0, 10.0, 0.0),
        Velocity {
            linvel: Vec3::new(0.0, -100.0, 0.0), // 高速下落
            ..default()
        },
    ));
}
```

### 4.3 刚体动力学

```rust
use bevy::prelude::*;
use bevy_rapier3d::prelude::*;

// ========== 力和冲量 ==========
fn apply_forces(
    keyboard_input: Res<Input<KeyCode>>,
    mut query: Query<(&mut ExternalForce, &mut ExternalImpulse, &Transform), With<PlayerController>>,
) {
    for (mut force, mut impulse, transform) in query.iter_mut() {
        // 持续力（例如火箭推进）
        if keyboard_input.pressed(KeyCode::ShiftLeft) {
            let forward = transform.forward();
            force.force = forward * 50.0;
        } else {
            force.force = Vec3::ZERO;
        }

        // 冲量（瞬间的力，如爆炸冲击）
        if keyboard_input.just_pressed(KeyCode::E) {
            impulse.impulse = Vec3::new(0.0, 20.0, 0.0);
        }
    }
}

// ========== 关节 ==========
fn setup_joints(mut commands: Commands) {
    // 创建链条
    let mut previous_entity = None;

    for i in 0..5 {
        let entity = commands.spawn((
            RigidBody::Dynamic,
            Collider::ball(0.5),
            Transform::from_xyz(i as f32 * 1.5, 10.0, 0.0),
        )).id();

        if let Some(prev) = previous_entity {
            // 创建球形关节连接
            commands.spawn(
                RevoluteJointBuilder::new(prev, entity)
                    .local_anchor1(Vec3::new(0.75, 0.0, 0.0))
                    .local_anchor2(Vec3::new(-0.75, 0.0, 0.0))
                    .limits([-0.5, 0.5]) // 限制旋转角度
            );
        } else {
            // 第一个球体固定
            commands.entity(entity).insert(RigidBody::Fixed);
        }

        previous_entity = Some(entity);
    }
}

// ========== 自定义形状 ==========
fn setup_custom_shapes(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
) {
    // 复合碰撞器（多个碰撞器组合）
    commands.spawn((
        PbrBundle {
            mesh: meshes.add(Mesh::from(shape::Capsule {
                radius: 0.5,
                depth: 1.0,
                ..default()
            })),
            material: materials.add(Color::PURPLE.into()),
            transform: Transform::from_xyz(5.0, 5.0, 0.0),
            ..default()
        },
        RigidBody::Dynamic,
        // 主体碰撞器
        Collider::capsule_y(0.5, 0.5),
        // 额外的小碰撞器（如武器）
        Collider::cuboid(0.1, 0.1, 0.5)
            .with_translation(Vec3::new(0.6, 0.0, 0.0)),
    ));

    // 三角形网格碰撞器（用于复杂静态几何）
    // 注意：性能开销较大，通常用于静态物体
    let mesh_handle = meshes.add(Mesh::from(shape::Cube::new(2.0)));
    // 需要三角网格碰撞器时：
    // Collider::from_bevy_mesh(&mesh, &ComputedColliderShape::TriMesh)
}

// ========== 物理查询 ==========
fn physics_queries(
    rapier_context: Res<RapierContext>,
    mut query: Query<&mut Transform, With<PlayerController>>,
) {
    for transform in query.iter() {
        let shape = Collider::ball(0.5);
        let shape_pos = transform.translation;
        let shape_rot = Quat::default();
        let filter = QueryFilter::default()
            .exclude_sensors()
            .groups(CollisionGroups::default());

        // 形状投射（Shape Cast）- 预测碰撞
        if let Some((entity, hit)) = rapier_context.cast_shape(
            shape_pos,
            shape_rot,
            Vec3::new(1.0, 0.0, 0.0), // 投射方向
            &shape,
            5.0, // 投射距离
            true, // 包含相交物体
            filter,
        ) {
            println!("Hit entity {:?} at distance {}", entity, hit.time_of_impact);
        }

        // 检测区域内的所有碰撞器
        rapier_context.intersections_with_shape(
            shape_pos,
            shape_rot,
            &shape,
            filter,
            |entity| {
                println!("Entity {:?} is inside the shape", entity);
                true // 继续检测
            },
        );
    }
}
```

### 4.4 射线检测

```rust
use bevy::prelude::*;
use bevy_rapier3d::prelude::*;

// ========== 基础射线检测 ==========
fn raycast_from_camera(
    windows: Query<&Window>,
    cameras: Query<(&Camera, &GlobalTransform), With<PlayerCamera>>,
    rapier_context: Res<RapierContext>,
    mut gizmos: Gizmos,
) {
    let window = windows.single();
    let (camera, camera_transform) = cameras.single();

    // 获取鼠标位置
    if let Some(cursor_position) = window.cursor_position() {
        // 将屏幕坐标转换为射线
        let ray = camera.viewport_to_world(camera_transform, cursor_position);

        if let Some(ray) = ray {
            // 执行射线检测
            let filter = QueryFilter::default();

            if let Some((entity, intersection)) = rapier_context.cast_ray(
                ray.origin,
                ray.direction,
                f32::MAX,
                true, // 包含传感器
                filter,
            ) {
                let hit_point = ray.origin + ray.direction * intersection.time_of_impact;
                println!(
                    "Hit entity {:?} at {} with normal {:?}",
                    entity,
                    hit_point,
                    intersection.normal
                );

                // 可视化射线
                gizmos.line(ray.origin, hit_point, Color::RED);
                gizmos.sphere(hit_point, Quat::default(), 0.1, Color::GREEN);
            }
        }
    }
}

// ========== 射击系统 ==========
#[derive(Component)]
struct Weapon {
    damage: f32,
    range: f32,
    fire_rate: f32,
    last_fire_time: f32,
}

fn weapon_system(
    time: Res<Time>,
    mouse_input: Res<Input<MouseButton>>,
    rapier_context: Res<RapierContext>,
    mut weapons: Query<(&GlobalTransform, &mut Weapon)>,
    mut targets: Query<&mut Health>,
    mut commands: Commands,
) {
    for (transform, mut weapon) in weapons.iter_mut() {
        // 检查射击冷却
        if time.elapsed_seconds() - weapon.last_fire_time < 1.0 / weapon.fire_rate {
            continue;
        }

        if mouse_input.pressed(MouseButton::Left) {
            weapon.last_fire_time = time.elapsed_seconds();

            let origin = transform.translation();
            let direction = transform.forward();

            // 射线检测
            let filter = QueryFilter::default()
                .exclude_collider(entity); // 排除自己

            if let Some((hit_entity, intersection)) = rapier_context.cast_ray(
                origin,
                direction,
                weapon.range,
                true,
                filter,
            ) {
                let hit_point = origin + direction * intersection.time_of_impact;

                // 应用伤害
                if let Ok(mut health) = targets.get_mut(hit_entity) {
                    health.current -= weapon.damage;

                    // 产生击中效果
                    spawn_impact_effect(&mut commands, hit_point, intersection.normal);
                }

                // 在表面留下弹孔
                spawn_bullet_hole(&mut commands, hit_point, intersection.normal);
            }
        }
    }
}

fn spawn_impact_effect(commands: &mut Commands, position: Vec3, normal: Vec3) {
    // 创建粒子效果或贴花
    commands.spawn((
        Transform::from_translation(position)
            .with_rotation(Quat::from_rotation_arc(Vec3::Y, normal)),
        ImpactEffect {
            lifetime: Timer::from_seconds(2.0, TimerMode::Once),
        },
    ));
}

fn spawn_bullet_hole(commands: &mut Commands, position: Vec3, normal: Vec3) {
    commands.spawn((
        Transform::from_translation(position + normal * 0.01)
            .with_rotation(Quat::from_rotation_arc(Vec3::Z, normal)),
        Decal {
            texture: "textures/bullet_hole.png".to_string(),
            size: Vec2::new(0.1, 0.1),
        },
        Lifetime::new(30.0), // 30秒后消失
    ));
}

// ========== 多射线检测 ==========
fn shotgun_raycast(
    origin: Vec3,
    forward: Vec3,
    rapier_context: &RapierContext,
) -> Vec<(Entity, RayIntersection)> {
    let mut hits = Vec::new();
    let pellet_count = 8;
    let spread = 0.1; // 散布角度

    let mut rng = rand::thread_rng();

    for _ in 0..pellet_count {
        // 添加随机散布
        let spread_x = rng.gen_range(-spread..spread);
        let spread_y = rng.gen_range(-spread..spread);

        let direction = (forward + Vec3::new(spread_x, spread_y, 0.0)).normalize();

        if let Some(hit) = rapier_context.cast_ray(
            origin,
            direction,
            100.0,
            true,
            QueryFilter::default(),
        ) {
            hits.push(hit);
        }
    }

    hits
}

// ========== 球体投射（扫掠检测）==========
fn sphere_sweep(
    rapier_context: &RapierContext,
    origin: Vec3,
    direction: Vec3,
    radius: f32,
) -> Option<(Entity, ShapeHit)> {
    let shape = Collider::ball(radius);
    let shape_rotation = Quat::default();

    rapier_context.cast_shape(
        origin,
        shape_rotation,
        direction,
        &shape,
        10.0, // 投射距离
        true,
        QueryFilter::default(),
    )
}
```

---

## 5. 资源管理

### 5.1 Asset Pipeline

```rust
use bevy::prelude::*;
use bevy::asset::LoadState;

// ========== 资源加载 ==========
#[derive(Resource, Default)]
struct GameAssets {
    player_sprite: Handle<Image>,
    enemy_sprite: Handle<Image>,
    background_music: Handle<AudioSource>,
    explosion_sound: Handle<AudioSource>,
    // 跟踪加载状态
    loaded: bool,
}

fn load_assets(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
) {
    let assets = GameAssets {
        player_sprite: asset_server.load("sprites/player.png"),
        enemy_sprite: asset_server.load("sprites/enemy.png"),
        background_music: asset_server.load("audio/background.ogg"),
        explosion_sound: asset_server.load("audio/explosion.wav"),
        loaded: false,
    };

    commands.insert_resource(assets);
}

// ========== 资源加载状态检查 ==========
fn check_asset_loading(
    mut game_assets: ResMut<GameAssets>,
    asset_server: Res<AssetServer>,
    mut next_state: ResMut<NextState<AppState>>,
) {
    if game_assets.loaded {
        return;
    }

    // 检查所有资源是否加载完成
    let handles: Vec<HandleUntyped> = vec![
        game_assets.player_sprite.clone_untyped(),
        game_assets.enemy_sprite.clone_untyped(),
        game_assets.background_music.clone_untyped(),
        game_assets.explosion_sound.clone_untyped(),
    ];

    match asset_server.get_group_load_state(handles) {
        LoadState::Loaded => {
            println!("All assets loaded!");
            game_assets.loaded = true;
            next_state.set(AppState::MainMenu);
        }
        LoadState::Failed => {
            eprintln!("Failed to load some assets!");
            // 处理加载失败
        }
        _ => {
            // 仍在加载中
        }
    }
}

// ========== 高级资源处理 ==========
use bevy::gltf::Gltf;

#[derive(Resource)]
struct ModelAssets {
    character: Handle<Gltf>,
    environment: Handle<Gltf>,
    animations: HashMap<String, Handle<AnimationClip>>,
}

fn load_models(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
    mut assets_gltf: ResMut<Assets<Gltf>>,
) {
    let character_handle = asset_server.load("models/character.glb");

    commands.insert_resource(ModelAssets {
        character: character_handle.clone(),
        environment: asset_server.load("models/level.glb"),
        animations: HashMap::new(),
    });
}

// 当 GLTF 加载完成后提取动画
fn extract_animations(
    mut model_assets: ResMut<ModelAssets>,
    assets_gltf: Res<Assets<Gltf>>,
) {
    if let Some(gltf) = assets_gltf.get(&model_assets.character) {
        for (name, animation) in &gltf.named_animations {
            model_assets.animations.insert(name.clone(), animation.clone());
            println!("Loaded animation: {}", name);
        }
    }
}

// ========== 动态资源加载 ==========
#[derive(Event)]
struct LoadLevelEvent {
    level_name: String,
}

fn dynamic_level_loading(
    mut events: EventReader<LoadLevelEvent>,
    asset_server: Res<AssetServer>,
    mut commands: Commands,
) {
    for event in events.read() {
        let level_path = format!("levels/{}.gltf", event.level_name);
        let level_handle: Handle<Gltf> = asset_server.load(&level_path);

        // 生成一个临时实体来跟踪这个资源的加载
        commands.spawn(LevelLoading {
            handle: level_handle,
            level_name: event.level_name.clone(),
        });
    }
}

#[derive(Component)]
struct LevelLoading {
    handle: Handle<Gltf>,
    level_name: String,
}
```

### 5.2 热重载

```rust
use bevy::prelude::*;

// ========== 基本热重载 ==========
fn hot_reload_setup(app: &mut App) {
    // 在开发模式下启用自动资源重载
    app.add_plugins(DefaultPlugins.set(AssetPlugin {
        watch_for_changes: true, // 启用文件监视
        ..default()
    }));
}

// ========== 着色器热重载 ==========
fn watch_shaders(
    asset_server: Res<AssetServer>,
    mut materials: ResMut<Assets<CustomMaterial>>,
) {
    // 手动重新加载着色器
    if asset_server.is_changed(&materials).is_ok() {
        // 重新编译着色器
        println!("Shader changed, reloading...");
    }
}

// ========== 场景热重载 ==========
#[derive(Resource)]
struct SceneWatcher {
    scene_handle: Handle<DynamicScene>,
    last_modified: SystemTime,
}

fn watch_scene_files(
    mut watcher: ResMut<SceneWatcher>,
    asset_server: Res<AssetServer>,
    mut scene_spawner: ResMut<SceneSpawner>,
) {
    // 检查文件修改时间
    let metadata = std::fs::metadata("assets/scenes/game.scn.ron");

    if let Ok(meta) = metadata {
        if let Ok(modified) = meta.modified() {
            if modified > watcher.last_modified {
                println!("Scene file changed, reloading...");

                // 重新加载场景
                watcher.scene_handle = asset_server.load("scenes/game.scn.ron");
                watcher.last_modified = modified;

                // 重新生成场景
                scene_spawner.spawn(watcher.scene_handle.clone());
            }
        }
    }
}

// ========== 配置热重载 ==========
#[derive(Resource, Deserialize, Serialize, Debug, Clone)]
struct GameConfig {
    player_speed: f32,
    gravity: f32,
    enemy_spawn_rate: f32,
}

impl Default for GameConfig {
    fn default() -> Self {
        Self {
            player_speed: 10.0,
            gravity: 9.8,
            enemy_spawn_rate: 1.0,
        }
    }
}

fn reload_config(
    mut config: ResMut<GameConfig>,
    asset_server: Res<AssetServer>,
    mut config_handle: Local<Handle<GameConfig>>,
    mut config_assets: ResMut<Assets<GameConfig>>,
) {
    // 首次加载
    if config_handle.is_none() {
        *config_handle = asset_server.load("config/game_config.ron");
    }

    // 检查是否有新版本
    if let Some(new_config) = config_assets.get(config_handle.id()) {
        if new_config != &*config {
            println!("Config reloaded: {:?}", new_config);
            *config = new_config.clone();
        }
    }
}
```

### 5.3 内存管理

```rust
use bevy::prelude::*;

// ========== 资源清理策略 ==========
#[derive(Resource)]
struct AssetCleanupConfig {
    unused_asset_lifetime: Duration,
    last_cleanup: Instant,
    cleanup_interval: Duration,
}

fn cleanup_unused_assets(
    mut config: ResMut<AssetCleanupConfig>,
    asset_server: Res<AssetServer>,
    time: Res<Time>,
) {
    if time.elapsed() - config.last_cleanup < config.cleanup_interval {
        return;
    }

    config.last_cleanup = time.elapsed();

    // Bevy 的资源系统会自动清理未被引用的资源
    // 这里可以添加自定义的清理逻辑
}

// ========== 对象池模式 ==========
#[derive(Resource)]
struct BulletPool {
    available: Vec<Entity>,
    in_use: HashSet<Entity>,
    prefab: Handle<Scene>,
}

impl BulletPool {
    fn spawn(&mut self, commands: &mut Commands, position: Vec3, direction: Vec3) -> Option<Entity> {
        if let Some(entity) = self.available.pop() {
            // 重用现有实体
            commands.entity(entity).insert((
                Transform::from_translation(position),
                GlobalTransform::default(),
                Velocity::from(direction * 50.0),
                ActiveBullet { lifetime: 5.0 },
            ));
            self.in_use.insert(entity);
            Some(entity)
        } else {
            // 创建新实体
            let entity = commands.spawn((
                SceneBundle {
                    scene: self.prefab.clone(),
                    transform: Transform::from_translation(position),
                    ..default()
                },
                Velocity::from(direction * 50.0),
                ActiveBullet { lifetime: 5.0 },
            )).id();
            self.in_use.insert(entity);
            Some(entity)
        }
    }

    fn recycle(&mut self, commands: &mut Commands, entity: Entity) {
        if self.in_use.remove(&entity) {
            // 禁用实体而不是销毁
            commands.entity(entity).insert(RecycleMarker);
            commands.entity(entity).remove::<(ActiveBullet, Velocity)>();
            self.available.push(entity);
        }
    }
}

#[derive(Component)]
struct ActiveBullet {
    lifetime: f32,
}

#[derive(Component)]
struct RecycleMarker;

fn update_bullets(
    mut commands: Commands,
    time: Res<Time>,
    mut bullet_pool: ResMut<BulletPool>,
    mut bullets: Query<(Entity, &mut ActiveBullet, &mut Transform)>,
) {
    for (entity, mut bullet, mut transform) in bullets.iter_mut() {
        bullet.lifetime -= time.delta_seconds();

        // 移动子弹
        transform.translation += transform.forward() * 50.0 * time.delta_seconds();

        if bullet.lifetime <= 0.0 {
            bullet_pool.recycle(&mut commands, entity);
        }
    }
}

// ========== 纹理图集（Atlas）优化 ==========
fn create_texture_atlas(
    asset_server: Res<AssetServer>,
    mut texture_atlases: ResMut<Assets<TextureAtlas>>,
    mut images: ResMut<Assets<Image>>,
) -> Handle<TextureAtlas> {
    // 加载多个小纹理
    let textures = vec![
        asset_server.load("sprites/tile1.png"),
        asset_server.load("sprites/tile2.png"),
        asset_server.load("sprites/tile3.png"),
        asset_server.load("sprites/tile4.png"),
    ];

    // 构建图集
    let mut atlas_builder = TextureAtlasBuilder::default();

    for handle in textures {
        if let Some(texture) = images.get(&handle) {
            atlas_builder.add_texture(handle.id(), texture);
        }
    }

    let atlas = atlas_builder.finish(&mut images).unwrap();
    texture_atlases.add(atlas)
}

// ========== LOD（细节层次）系统 ==========
#[derive(Component)]
struct LodMesh {
    high: Handle<Mesh>,
    medium: Handle<Mesh>,
    low: Handle<Mesh>,
    distance_thresholds: Vec<f32>,
}

fn update_lod(
    camera_query: Query<&Transform, With<Camera>>,
    mut meshes: Query<(&Transform, &mut Handle<Mesh>, &LodMesh)>,
) {
    let camera_transform = camera_query.single();

    for (transform, mut current_mesh, lod) in meshes.iter_mut() {
        let distance = transform.translation.distance(camera_transform.translation);

        // 根据距离选择 LOD 级别
        let new_mesh = if distance < lod.distance_thresholds[0] {
            lod.high.clone()
        } else if distance < lod.distance_thresholds[1] {
            lod.medium.clone()
        } else {
            lod.low.clone()
        };

        *current_mesh = new_mesh;
    }
}
```

---

## 6. 音频系统

### 6.1 Rodio

Rodio 是 Rust 的纯 Rust 音频播放库。

```rust
use rodio::{Decoder, OutputStream, Sink, Source};
use std::fs::File;
use std::io::BufReader;

fn play_sound() {
    // 获取默认输出流
    let (_stream, stream_handle) = OutputStream::try_default().unwrap();

    // 创建音频接收器
    let sink = Sink::try_new(&stream_handle).unwrap();

    // 加载音频文件
    let file = File::open("assets/audio/music.mp3").unwrap();
    let source = Decoder::new(BufReader::new(file)).unwrap();

    // 播放
    sink.append(source);
    sink.sleep_until_end();
}

// ========== 音频管理器 ==========
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

pub struct AudioManager {
    stream: OutputStream,
    stream_handle: rodio::OutputStreamHandle,
    sinks: HashMap<String, Arc<Mutex<Sink>>>,
    sound_cache: HashMap<String, Vec<u8>>,
}

impl AudioManager {
    pub fn new() -> Result<Self, rodio::StreamError> {
        let (stream, stream_handle) = OutputStream::try_default()?;

        Ok(Self {
            stream,
            stream_handle,
            sinks: HashMap::new(),
            sound_cache: HashMap::new(),
        })
    }

    pub fn preload_sound(&mut self, name: &str, path: &str) -> Result<(), std::io::Error> {
        let data = std::fs::read(path)?;
        self.sound_cache.insert(name.to_string(), data);
        Ok(())
    }

    pub fn play_sound(&mut self, name: &str) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(data) = self.sound_cache.get(name) {
            let sink = Sink::try_new(&self.stream_handle)?;
            let cursor = std::io::Cursor::new(data.clone());
            let source = Decoder::new(cursor)?;
            sink.append(source);

            self.sinks.insert(format!("{}_{}", name, std::time::Instant::now().elapsed().as_millis()),
                Arc::new(Mutex::new(sink)));
        }
        Ok(())
    }

    pub fn play_music(&mut self, name: &str, looping: bool) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(data) = self.sound_cache.get(name) {
            // 停止现有音乐
            if let Some(sink) = self.sinks.get("music") {
                sink.lock().unwrap().stop();
            }

            let sink = Sink::try_new(&self.stream_handle)?;
            let cursor = std::io::Cursor::new(data.clone());
            let source = Decoder::new(cursor)?;

            if looping {
                sink.append(source.repeat_infinite());
            } else {
                sink.append(source);
            }

            self.sinks.insert("music".to_string(), Arc::new(Mutex::new(sink)));
        }
        Ok(())
    }

    pub fn set_volume(&self, name: &str, volume: f32) {
        if let Some(sink) = self.sinks.get(name) {
            sink.lock().unwrap().set_volume(volume);
        }
    }

    pub fn stop(&self, name: &str) {
        if let Some(sink) = self.sinks.get(name) {
            sink.lock().unwrap().stop();
        }
    }
}
```

### 6.2 3D 空间音频

```rust
use bevy::prelude::*;
use bevy_kira_audio::{Audio, AudioPlugin, AudioSource, SpatialAudio};

// ========== Bevy + Kira Audio ==========
fn setup_spatial_audio(mut commands: Commands) {
    // 创建监听器（通常是玩家相机）
    commands.spawn((
        SpatialAudioListener,
        Transform::default(),
        GlobalTransform::default(),
    ));
}

#[derive(Component)]
struct SpatialSound {
    handle: Handle<AudioSource>,
    range: f32,
    volume: f32,
}

fn update_spatial_audio(
    listener: Query<&Transform, With<SpatialAudioListener>>,
    sounds: Query<(&Transform, &SpatialSound)>,
    audio: Res<Audio>,
) {
    if let Ok(listener_transform) = listener.get_single() {
        for (sound_transform, sound) in sounds.iter() {
            let distance = listener_transform.translation
                .distance(sound_transform.translation);

            // 计算音量衰减
            if distance < sound.range {
                let volume = sound.volume * (1.0 - distance / sound.range);
                audio.set_volume(volume);

                // 计算声相（左右平衡）
                let direction = sound_transform.translation - listener_transform.translation;
                let angle = direction.x.atan2(direction.z);
                let panning = (angle.sin() + 1.0) / 2.0; // 0.0 = 左, 1.0 = 右

                audio.set_panning(panning);
            }
        }
    }
}

// ========== 环境音效区域 ==========
#[derive(Component)]
struct AmbientZone {
    sound: Handle<AudioSource>,
    inner_radius: f32,
    outer_radius: f32,
}

fn ambient_zone_system(
    player: Query<&Transform, With<Player>>,
    zones: Query<(&Transform, &AmbientZone)>,
    audio: Res<Audio>,
) {
    if let Ok(player_transform) = player.get_single() {
        for (zone_transform, zone) in zones.iter() {
            let distance = player_transform.translation.distance(zone_transform.translation);

            if distance < zone.outer_radius {
                // 计算内外半径之间的音量
                let t = ((distance - zone.inner_radius) / (zone.outer_radius - zone.inner_radius))
                    .clamp(0.0, 1.0);
                let volume = 1.0 - t;

                audio.set_volume(volume);
            }
        }
    }
}
```

### 6.3 音乐流媒体

```rust
use rodio::source::SineWave;
use std::sync::mpsc::{channel, Receiver, Sender};

// ========== 背景音乐系统 ==========
pub struct MusicSystem {
    stream_handle: rodio::OutputStreamHandle,
    current_sink: Option<Sink>,
    playlist: Vec<String>,
    current_index: usize,
    volume: f32,
}

impl MusicSystem {
    pub fn new(stream_handle: rodio::OutputStreamHandle) -> Self {
        Self {
            stream_handle,
            current_sink: None,
            playlist: Vec::new(),
            current_index: 0,
            volume: 0.5,
        }
    }

    pub fn set_playlist(&mut self, tracks: Vec<String>) {
        self.playlist = tracks;
        self.current_index = 0;
    }

    pub fn play(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        if self.playlist.is_empty() {
            return Ok(());
        }

        // 停止当前播放
        if let Some(sink) = &self.current_sink {
            sink.stop();
        }

        let track = &self.playlist[self.current_index];
        let file = File::open(track)?;
        let source = Decoder::new(BufReader::new(file))?;

        let sink = Sink::try_new(&self.stream_handle)?;
        sink.set_volume(self.volume);
        sink.append(source);

        self.current_sink = Some(sink);
        Ok(())
    }

    pub fn next_track(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.current_index = (self.current_index + 1) % self.playlist.len();
        self.play()
    }

    pub fn previous_track(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        if self.current_index == 0 {
            self.current_index = self.playlist.len() - 1;
        } else {
            self.current_index -= 1;
        }
        self.play()
    }

    pub fn set_volume(&mut self, volume: f32) {
        self.volume = volume.clamp(0.0, 1.0);
        if let Some(sink) = &self.current_sink {
            sink.set_volume(self.volume);
        }
    }

    pub fn is_playing(&self) -> bool {
        self.current_sink.as_ref().map(|s| !s.empty()).unwrap_or(false)
    }
}

// ========== 动态音乐系统（根据游戏状态切换）==========
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MusicState {
    Calm,
    Tense,
    Combat,
    Victory,
    GameOver,
}

pub struct AdaptiveMusicSystem {
    music_system: MusicSystem,
    state_tracks: HashMap<MusicState, Vec<String>>,
    current_state: MusicState,
    transition_time: f32,
}

impl AdaptiveMusicSystem {
    pub fn transition_to(&mut self, new_state: MusicState) {
        if self.current_state != new_state {
            self.current_state = new_state;

            if let Some(tracks) = self.state_tracks.get(&new_state) {
                self.music_system.set_playlist(tracks.clone());
                let _ = self.music_system.play();
            }
        }
    }

    pub fn update(&mut self, game_intensity: f32) {
        // 根据游戏强度自动切换音乐状态
        let new_state = if game_intensity > 0.8 {
            MusicState::Combat
        } else if game_intensity > 0.4 {
            MusicState::Tense
        } else {
            MusicState::Calm
        };

        self.transition_to(new_state);
    }
}
```

---

## 7. 输入处理

### 7.1 键盘/鼠标

```rust
use bevy::prelude::*;

// ========== 基础输入处理 ==========
fn keyboard_input_system(
    keyboard_input: Res<Input<KeyCode>>,
    mut player_query: Query<&mut Velocity, With<Player>>,
) {
    for mut velocity in player_query.iter_mut() {
        let mut direction = Vec3::ZERO;

        // 持续按键检测
        if keyboard_input.pressed(KeyCode::W) {
            direction.z -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::S) {
            direction.z += 1.0;
        }
        if keyboard_input.pressed(KeyCode::A) {
            direction.x -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::D) {
            direction.x += 1.0;
        }

        // 单次按键检测
        if keyboard_input.just_pressed(KeyCode::Space) {
            println!("Jump!");
        }

        // 按键释放检测
        if keyboard_input.just_released(KeyCode::ShiftLeft) {
            println!("Sprint ended");
        }

        // 组合键检测
        if keyboard_input.pressed(KeyCode::ControlLeft) && keyboard_input.just_pressed(KeyCode::S) {
            println!("Save game!");
        }

        if direction != Vec3::ZERO {
            velocity.0 = direction.normalize() * 5.0;
        } else {
            velocity.0 = Vec3::ZERO;
        }
    }
}

// ========== 鼠标输入处理 ==========
fn mouse_input_system(
    mouse_button_input: Res<Input<MouseButton>>,
    mut mouse_motion_events: EventReader<MouseMotion>,
    mut mouse_wheel_events: EventReader<MouseWheel>,
    mut camera_query: Query<&mut Transform, With<Camera>>,
) {
    // 鼠标按钮
    if mouse_button_input.just_pressed(MouseButton::Left) {
        println!("Left click!");
    }
    if mouse_button_input.pressed(MouseButton::Right) {
        println!("Right button held");
    }

    // 鼠标移动（用于视角控制）
    for event in mouse_motion_events.read() {
        let delta = event.delta;

        for mut transform in camera_query.iter_mut() {
            // 水平旋转（绕 Y 轴）
            transform.rotate_y(-delta.x * 0.002);

            // 垂直旋转（绕 X 轴）
            let (mut yaw, mut pitch, roll) = transform.rotation.to_euler(EulerRot::YXZ);
            pitch -= delta.y * 0.002;
            pitch = pitch.clamp(-1.5, 1.5); // 限制俯仰角
            transform.rotation = Quat::from_euler(EulerRot::YXZ, yaw, pitch, roll);
        }
    }

    // 鼠标滚轮（用于缩放）
    for event in mouse_wheel_events.read() {
        println!("Scroll: {}", event.y);
    }
}

// ========== 第一人称控制器 ==========
#[derive(Component)]
struct FirstPersonController {
    sensitivity: f32,
    speed: f32,
    sprint_speed: f32,
}

fn first_person_controller(
    keyboard_input: Res<Input<KeyCode>>,
    mut mouse_motion: EventReader<MouseMotion>,
    mut query: Query<(&mut Transform, &FirstPersonController), With<Camera>>,
    time: Res<Time>,
) {
    for (mut transform, controller) in query.iter_mut() {
        // 处理鼠标输入
        let mut mouse_delta = Vec2::ZERO;
        for motion in mouse_motion.read() {
            mouse_delta += motion.delta;
        }

        if mouse_delta != Vec2::ZERO {
            // 计算当前旋转
            let (yaw, pitch, roll) = transform.rotation.to_euler(EulerRot::YXZ);

            let new_yaw = yaw - mouse_delta.x * controller.sensitivity;
            let new_pitch = (pitch - mouse_delta.y * controller.sensitivity)
                .clamp(-1.5, 1.5);

            transform.rotation = Quat::from_euler(EulerRot::YXZ, new_yaw, new_pitch, roll);
        }

        // 处理键盘移动（相对于视角方向）
        let forward = transform.forward();
        let right = transform.right();
        let flat_forward = Vec3::new(forward.x, 0.0, forward.z).normalize_or_zero();
        let flat_right = Vec3::new(right.x, 0.0, right.z).normalize_or_zero();

        let mut movement = Vec3::ZERO;

        if keyboard_input.pressed(KeyCode::W) {
            movement += flat_forward;
        }
        if keyboard_input.pressed(KeyCode::S) {
            movement -= flat_forward;
        }
        if keyboard_input.pressed(KeyCode::A) {
            movement -= flat_right;
        }
        if keyboard_input.pressed(KeyCode::D) {
            movement += flat_right;
        }

        let speed = if keyboard_input.pressed(KeyCode::ShiftLeft) {
            controller.sprint_speed
        } else {
            controller.speed
        };

        if movement != Vec3::ZERO {
            movement = movement.normalize() * speed * time.delta_seconds();
            transform.translation += movement;
        }
    }
}
```

### 7.2 游戏手柄

```rust
use bevy::prelude::*;
use bevy_input::gamepad::{
    Gamepad, GamepadAxis, GamepadAxisType, GamepadButton, GamepadButtonType, GamepadEvent,
};

// ========== 游戏手柄连接检测 ==========
fn gamepad_connection(
    mut commands: Commands,
    mut gamepad_events: EventReader<GamepadEvent>,
    mut connected_gamepads: ResMut<ConnectedGamepads>,
) {
    for event in gamepad_events.read() {
        match event {
            GamepadEvent::Connected(gamepad) => {
                println!("Gamepad {:?} connected", gamepad);
                connected_gamepads.0.push(*gamepad);

                // 为游戏手柄创建玩家实体
                commands.spawn((
                    *gamepad,
                    PlayerInput::default(),
                ));
            }
            GamepadEvent::Disconnected(gamepad) => {
                println!("Gamepad {:?} disconnected", gamepad);
                connected_gamepads.0.retain(|g| g != gamepad);
            }
        }
    }
}

#[derive(Resource, Default)]
struct ConnectedGamepads(Vec<Gamepad>);

#[derive(Component, Default)]
struct PlayerInput {
    move_direction: Vec2,
    look_direction: Vec2,
    jump: bool,
    attack: bool,
}

// ========== 游戏手柄输入处理 ==========
fn gamepad_input_system(
    gamepads: Res<Gamepads>,
    axes: Res<Axis<GamepadAxis>>,
    buttons: Res<Input<GamepadButton>>,
    mut query: Query<(&Gamepad, &mut PlayerInput)>,
) {
    for (gamepad, mut input) in query.iter_mut() {
        if !gamepads.contains(*gamepad) {
            continue;
        }

        // 左摇杆 - 移动
        let left_stick_x = axes
            .get(GamepadAxis::new(*gamepad, GamepadAxisType::LeftStickX))
            .unwrap_or(0.0);
        let left_stick_y = axes
            .get(GamepadAxis::new(*gamepad, GamepadAxisType::LeftStickY))
            .unwrap_or(0.0);

        input.move_direction = Vec2::new(left_stick_x, left_stick_y);

        // 应用死区
        if input.move_direction.length() < 0.1 {
            input.move_direction = Vec2::ZERO;
        }

        // 右摇杆 - 视角
        let right_stick_x = axes
            .get(GamepadAxis::new(*gamepad, GamepadAxisType::RightStickX))
            .unwrap_or(0.0);
        let right_stick_y = axes
            .get(GamepadAxis::new(*gamepad, GamepadAxisType::RightStickY))
            .unwrap_or(0.0);

        input.look_direction = Vec2::new(right_stick_x, right_stick_y);

        // 按钮
        input.jump = buttons.just_pressed(GamepadButton::new(*gamepad, GamepadButtonType::South));
        input.attack = buttons.pressed(GamepadButton::new(*gamepad, GamepadButtonType::West));

        // 扳机键
        let left_trigger = axes
            .get(GamepadAxis::new(*gamepad, GamepadAxisType::LeftZ))
            .unwrap_or(0.0);
        let right_trigger = axes
            .get(GamepadAxis::new(*gamepad, GamepadAxisType::RightZ))
            .unwrap_or(0.0);

        // 振动反馈
        // gamepad.set_rumble(...)
    }
}

// ========== 输入抽象层 ==========
#[derive(Resource)]
struct InputMap {
    keyboard_bindings: HashMap<Action, Vec<KeyCode>>,
    gamepad_bindings: HashMap<Action, Vec<GamepadButtonType>>,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
enum Action {
    MoveForward,
    MoveBackward,
    MoveLeft,
    MoveRight,
    Jump,
    Attack,
    Interact,
    Pause,
}

impl Default for InputMap {
    fn default() -> Self {
        let mut keyboard_bindings = HashMap::new();
        keyboard_bindings.insert(Action::MoveForward, vec![KeyCode::W, KeyCode::Up]);
        keyboard_bindings.insert(Action::MoveBackward, vec![KeyCode::S, KeyCode::Down]);
        keyboard_bindings.insert(Action::MoveLeft, vec![KeyCode::A, KeyCode::Left]);
        keyboard_bindings.insert(Action::MoveRight, vec![KeyCode::D, KeyCode::Right]);
        keyboard_bindings.insert(Action::Jump, vec![KeyCode::Space]);
        keyboard_bindings.insert(Action::Attack, vec![KeyCode::MouseLeft]);
        keyboard_bindings.insert(Action::Interact, vec![KeyCode::E]);
        keyboard_bindings.insert(Action::Pause, vec![KeyCode::Escape]);

        let mut gamepad_bindings = HashMap::new();
        gamepad_bindings.insert(Action::Jump, vec![GamepadButtonType::South]);
        gamepad_bindings.insert(Action::Attack, vec![GamepadButtonType::West]);
        gamepad_bindings.insert(Action::Interact, vec![GamepadButtonType::East]);
        gamepad_bindings.insert(Action::Pause, vec![GamepadButtonType::Start]);

        Self {
            keyboard_bindings,
            gamepad_bindings,
        }
    }
}

fn unified_input_system(
    input_map: Res<InputMap>,
    keyboard_input: Res<Input<KeyCode>>,
    mouse_input: Res<Input<MouseButton>>,
    gamepads: Res<Gamepads>,
    buttons: Res<Input<GamepadButton>>,
    mut action_state: ResMut<ActionState>,
) {
    action_state.pressed.clear();
    action_state.just_pressed.clear();

    for (action, keys) in &input_map.keyboard_bindings {
        let pressed = keys.iter().any(|key| match key {
            KeyCode::MouseLeft => mouse_input.pressed(MouseButton::Left),
            KeyCode::MouseRight => mouse_input.pressed(MouseButton::Right),
            _ => keyboard_input.pressed(*key),
        });

        let just_pressed = keys.iter().any(|key| match key {
            KeyCode::MouseLeft => mouse_input.just_pressed(MouseButton::Left),
            KeyCode::MouseRight => mouse_input.just_pressed(MouseButton::Right),
            _ => keyboard_input.just_pressed(*key),
        });

        if pressed {
            action_state.pressed.insert(*action);
        }
        if just_pressed {
            action_state.just_pressed.insert(*action);
        }
    }
}

#[derive(Resource, Default)]
struct ActionState {
    pressed: HashSet<Action>,
    just_pressed: HashSet<Action>,
}
```

### 7.3 触摸输入

```rust
use bevy::prelude::*;
use bevy::input::touch::{TouchInput, TouchPhase};

// ========== 基础触摸处理 ==========
fn touch_input_system(
    mut touch_events: EventReader<TouchInput>,
    windows: Query<&Window>,
    mut touches: ResMut<Touches>,
) {
    let window = windows.single();

    for event in touch_events.read() {
        match event.phase {
            TouchPhase::Started => {
                println!("Touch started at {:?}", event.position);
                touches.active.insert(event.id, event.position);

                // 检测多指手势开始
                if touches.active.len() == 2 {
                    touches.initial_pinch_distance = Some(calculate_pinch_distance(&touches.active));
                }
            }
            TouchPhase::Moved => {
                if let Some(&previous_pos) = touches.active.get(&event.id) {
                    let delta = event.position - previous_pos;

                    // 处理移动
                    if touches.active.len() == 1 {
                        // 单指 - 拖动/视角控制
                        touches.gesture = Some(Gesture::Drag(delta));
                    } else if touches.active.len() == 2 {
                        // 双指 - 缩放
                        if let Some(initial_distance) = touches.initial_pinch_distance {
                            let current_distance = calculate_pinch_distance(&touches.active);
                            let scale = current_distance / initial_distance;
                            touches.gesture = Some(Gesture::Pinch(scale));
                        }
                    }

                    touches.active.insert(event.id, event.position);
                }
            }
            TouchPhase::Ended | TouchPhase::Cancelled => {
                println!("Touch ended");
                touches.active.remove(&event.id);

                if touches.active.len() < 2 {
                    touches.initial_pinch_distance = None;
                }

                if touches.active.is_empty() {
                    touches.gesture = None;
                }
            }
        }
    }
}

fn calculate_pinch_distance(touches: &HashMap<u64, Vec2>) -> f32 {
    let positions: Vec<Vec2> = touches.values().copied().collect();
    if positions.len() >= 2 {
        positions[0].distance(positions[1])
    } else {
        0.0
    }
}

#[derive(Resource, Default)]
struct Touches {
    active: HashMap<u64, Vec2>,
    initial_pinch_distance: Option<f32>,
    gesture: Option<Gesture>,
}

enum Gesture {
    Drag(Vec2),
    Pinch(f32),
    Rotate(f32),
}

// ========== 虚拟摇杆（移动端）==========
#[derive(Component)]
struct VirtualJoystick {
    base_position: Vec2,
    current_position: Vec2,
    max_radius: f32,
    touch_id: Option<u64>,
}

impl VirtualJoystick {
    fn value(&self) -> Vec2 {
        let delta = self.current_position - self.base_position;
        let magnitude = delta.length().min(self.max_radius) / self.max_radius;
        delta.normalize_or_zero() * magnitude
    }
}

fn virtual_joystick_system(
    mut touch_events: EventReader<TouchInput>,
    mut joysticks: Query<&mut VirtualJoystick>,
    windows: Query<&Window>,
) {
    let window = windows.single();

    for event in touch_events.read() {
        for mut joystick in joysticks.iter_mut() {
            match event.phase {
                TouchPhase::Started => {
                    // 检测触摸是否在摇杆区域内
                    let touch_pos = event.position;
                    if touch_pos.distance(joystick.base_position) < joystick.max_radius * 1.5 {
                        joystick.touch_id = Some(event.id);
                        joystick.current_position = touch_pos;
                    }
                }
                TouchPhase::Moved => {
                    if joystick.touch_id == Some(event.id) {
                        let delta = event.position - joystick.base_position;
                        joystick.current_position = joystick.base_position
                            + delta.clamp_length_max(joystick.max_radius);
                    }
                }
                TouchPhase::Ended | TouchPhase::Cancelled => {
                    if joystick.touch_id == Some(event.id) {
                        joystick.touch_id = None;
                        joystick.current_position = joystick.base_position;
                    }
                }
            }
        }
    }
}

fn draw_virtual_joysticks(
    mut gizmos: Gizmos,
    joysticks: Query<&VirtualJoystick>,
) {
    for joystick in joysticks.iter() {
        // 绘制底座
        gizmos.circle_2d(
            joystick.base_position,
            joystick.max_radius,
            Color::GRAY,
        );

        // 绘制摇杆头
        gizmos.circle_2d(
            joystick.current_position,
            joystick.max_radius * 0.4,
            if joystick.touch_id.is_some() { Color::WHITE } else { Color::DARK_GRAY },
        );
    }
}
```

---

## 8. 多人游戏

### 8.1 网络同步

```rust
use bevy::prelude::*;

// ========== 网络基础架构 ==========
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::io::{Read, Write};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
enum NetworkMessage {
    PlayerInput {
        player_id: u64,
        input: PlayerInputState,
        sequence: u32,
    },
    GameState {
        tick: u32,
        entities: Vec<EntityState>,
    },
    PlayerJoin {
        player_id: u64,
        player_name: String,
    },
    PlayerLeave {
        player_id: u64,
    },
    ChatMessage {
        player_id: u64,
        message: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PlayerInputState {
    movement: Vec2,
    look_delta: Vec2,
    jump: bool,
    attack: bool,
    timestamp: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct EntityState {
    id: u64,
    position: Vec3,
    rotation: Quat,
    velocity: Vec3,
    health: f32,
}

// ========== 服务器架构 ==========
pub struct GameServer {
    listener: TcpListener,
    clients: HashMap<u64, ClientConnection>,
    next_player_id: u64,
    game_state: ServerGameState,
}

struct ClientConnection {
    stream: TcpStream,
    player_id: u64,
    last_acknowledged_tick: u32,
    input_buffer: Vec<PlayerInputState>,
}

impl GameServer {
    pub fn new(bind_addr: SocketAddr) -> std::io::Result<Self> {
        let listener = TcpListener::bind(bind_addr)?;
        listener.set_nonblocking(true)?;

        Ok(Self {
            listener,
            clients: HashMap::new(),
            next_player_id: 1,
            game_state: ServerGameState::new(),
        })
    }

    pub fn accept_connections(&mut self) {
        while let Ok((stream, addr)) = self.listener.accept() {
            let player_id = self.next_player_id;
            self.next_player_id += 1;

            stream.set_nonblocking(true).unwrap();

            let client = ClientConnection {
                stream,
                player_id,
                last_acknowledged_tick: 0,
                input_buffer: Vec::new(),
            };

            self.clients.insert(player_id, client);

            // 通知其他玩家
            let join_msg = NetworkMessage::PlayerJoin {
                player_id,
                player_name: format!("Player {}", player_id),
            };
            self.broadcast(&join_msg, Some(player_id));

            println!("Player {} connected from {}", player_id, addr);
        }
    }

    pub fn process_input(&mut self, delta_time: f32) {
        // 处理所有客户端输入
        for (player_id, client) in &mut self.clients {
            // 读取网络数据
            let mut buffer = [0u8; 1024];
            if let Ok(bytes_read) = client.stream.read(&mut buffer) {
                if bytes_read > 0 {
                    // 解析输入消息
                    if let Ok(msg) = bincode::deserialize(&buffer[..bytes_read]) {
                        match msg {
                            NetworkMessage::PlayerInput { input, .. } => {
                                client.input_buffer.push(input);
                            }
                            _ => {}
                        }
                    }
                }
            }

            // 应用输入到游戏状态
            for input in &client.input_buffer {
                self.game_state.apply_player_input(*player_id, input, delta_time);
            }
            client.input_buffer.clear();
        }
    }

    pub fn broadcast_game_state(&mut self, tick: u32) {
        let state_msg = NetworkMessage::GameState {
            tick,
            entities: self.game_state.snapshot(),
        };

        self.broadcast(&state_msg, None);
    }

    fn broadcast(&mut self, message: &NetworkMessage, exclude: Option<u64>) {
        let data = bincode::serialize(message).unwrap();

        for (player_id, client) in &mut self.clients {
            if Some(*player_id) != exclude {
                let _ = client.stream.write_all(&data);
            }
        }
    }
}
```

### 8.2 客户端预测

```rust
use bevy::prelude::*;

// ========== 客户端预测系统 ==========
#[derive(Resource)]
struct ClientNetworkState {
    server_connection: Option<TcpStream>,
    local_player_id: u64,

    // 预测相关
    predicted_states: VecDeque<(u32, GameSnapshot)>,
    server_snapshots: VecDeque<(u32, GameSnapshot)>,
    current_input_sequence: u32,

    // 网络补偿
    latency: f32,
    jitter: f32,
    server_tick: u32,
}

#[derive(Clone)]
struct GameSnapshot {
    player_position: Vec3,
    player_velocity: Vec3,
    entities: Vec<EntitySnapshot>,
}

#[derive(Clone)]
struct EntitySnapshot {
    id: u64,
    position: Vec3,
    velocity: Vec3,
}

// 客户端输入处理（带预测）
fn client_input_system(
    mut client_state: ResMut<ClientNetworkState>,
    input: Res<InputState>,
    time: Res<Time>,
    mut player_query: Query<(&mut Transform, &mut Velocity), With<LocalPlayer>>,
) {
    // 创建输入状态
    let input_state = PlayerInputState {
        movement: input.movement,
        look_delta: input.look_delta,
        jump: input.jump_just_pressed,
        attack: input.attack_pressed,
        timestamp: time.elapsed_seconds_f64(),
    };

    // 发送输入到服务器
    let msg = NetworkMessage::PlayerInput {
        player_id: client_state.local_player_id,
        input: input_state.clone(),
        sequence: client_state.current_input_sequence,
    };

    if let Some(ref mut stream) = client_state.server_connection {
        let data = bincode::serialize(&msg).unwrap();
        let _ = stream.write_all(&data);
    }

    // 立即预测应用输入（客户端预测）
    for (mut transform, mut velocity) in player_query.iter_mut() {
        apply_input(&input_state, &mut transform, &mut velocity, time.delta_seconds());
    }

    // 保存预测状态用于之后的和解
    let snapshot = GameSnapshot {
        player_position: player_query.single().0.translation,
        player_velocity: player_query.single().1 .0,
        entities: Vec::new(),
    };

    client_state.predicted_states.push_back((
        client_state.current_input_sequence,
        snapshot,
    ));

    client_state.current_input_sequence += 1;
}

// 服务器状态和解（Reconciliation）
fn reconcile_with_server(
    mut client_state: ResMut<ClientNetworkState>,
    mut player_query: Query<(&mut Transform, &mut Velocity), With<LocalPlayer>>,
) {
    // 读取服务器快照
    if let Some(ref mut stream) = client_state.server_connection {
        let mut buffer = [0u8; 4096];
        if let Ok(bytes_read) = stream.read(&mut buffer) {
            if bytes_read > 0 {
                if let Ok(NetworkMessage::GameState { tick, entities }) =
                    bincode::deserialize(&buffer[..bytes_read]) {

                    // 找到对应的本地玩家实体状态
                    if let Some(server_player) = entities.iter()
                        .find(|e| e.id == client_state.local_player_id) {

                        // 找到服务器快照对应的预测状态
                        if let Some(index) = client_state.predicted_states
                            .iter()
                            .position(|(seq, _)| *seq == tick) {

                            let (_, predicted) = &client_state.predicted_states[index];

                            // 计算误差
                            let position_error = server_player.position.distance(predicted.player_position);

                            // 如果误差超过阈值，进行和解
                            if position_error > 0.1 {
                                println!("Reconciling: error = {}", position_error);

                                // 设置到服务器状态
                                for (mut transform, mut velocity) in player_query.iter_mut() {
                                    transform.translation = server_player.position;
                                    velocity.0 = server_player.velocity;
                                }

                                // 重放之后的所有输入
                                for (_, input_state) in &client_state.predicted_states[index + 1..] {
                                    for (mut transform, mut velocity) in player_query.iter_mut() {
                                        // 重新应用输入（简化示例）
                                        transform.translation += velocity.0 * 0.016;
                                    }
                                }
                            }

                            // 删除已确认的旧状态
                            client_state.predicted_states = client_state.predicted_states
                                .split_off(index + 1);
                        }
                    }
                }
            }
        }
    }
}

fn apply_input(
    input: &PlayerInputState,
    transform: &mut Transform,
    velocity: &mut Velocity,
    delta_time: f32,
) {
    // 应用移动输入
    let speed = 5.0;
    velocity.0.x = input.movement.x * speed;
    velocity.0.z = input.movement.y * speed;

    // 应用重力
    velocity.0.y -= 9.8 * delta_time;

    // 跳跃
    if input.jump {
        velocity.0.y = 10.0;
    }

    // 更新位置
    transform.translation += velocity.0 * delta_time;

    // 应用视角旋转
    transform.rotate_y(-input.look_delta.x * 0.002);
}
```

### 8.3 服务器权威

```rust
use bevy::prelude::*;

// ========== 服务器权威游戏逻辑 ==========
#[derive(Resource)]
struct AuthoritativeServer {
    game_state: ServerGameState,
    tick_rate: f32,
    accumulator: f32,
    current_tick: u32,
}

impl AuthoritativeServer {
    fn update(&mut self, delta_time: f32, clients: &mut HashMap<u64, ClientConnection>) {
        self.accumulator += delta_time;

        // 固定时间步长更新
        while self.accumulator >= self.tick_rate {
            self.fixed_update(clients);
            self.accumulator -= self.tick_rate;
            self.current_tick += 1;
        }
    }

    fn fixed_update(&mut self, clients: &mut HashMap<u64, ClientConnection>) {
        // 1. 收集并验证所有客户端输入
        for (player_id, client) in clients.iter_mut() {
            // 读取输入
            while let Some(input) = client.input_buffer.pop() {
                // 验证输入（防止作弊）
                if self.validate_input(&input) {
                    self.apply_player_input(*player_id, &input);
                }
            }
        }

        // 2. 更新游戏世界
        self.game_state.update_physics(self.tick_rate);
        self.game_state.update_ai(self.tick_rate);

        // 3. 处理游戏规则
        self.check_win_conditions();
        self.resolve_conflicts();

        // 4. 广播更新后的状态
        self.broadcast_state(clients);
    }

    fn validate_input(&self, input: &PlayerInputState) -> bool {
        // 检查输入是否合法
        // 1. 检查移动速度是否超过限制
        if input.movement.length() > 1.1 {
            return false;
        }

        // 2. 检查时间戳（防止回放攻击）
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs_f64();

        if (now - input.timestamp).abs() > 1.0 {
            return false; // 时间戳偏差太大
        }

        // 3. 检查玩家状态是否允许该操作
        // ...

        true
    }

    fn apply_player_input(&mut self, player_id: u64, input: &PlayerInputState) {
        if let Some(player) = self.game_state.players.get_mut(&player_id) {
            // 服务器权威地计算新状态
            let speed = if player.is_sprinting { 8.0 } else { 5.0 };

            player.velocity.x = input.movement.x * speed;
            player.velocity.z = input.movement.y * speed;

            // 服务器计算的位置是权威位置
            player.position += player.velocity * self.tick_rate;

            // 验证位置（防止穿墙等作弊）
            if !self.is_valid_position(player.position) {
                // 回退到上一次有效位置
                player.position = player.last_valid_position;
                player.velocity = Vec3::ZERO;
            } else {
                player.last_valid_position = player.position;
            }
        }
    }

    fn is_valid_position(&self, position: Vec3) -> bool {
        // 检查是否在地图边界内
        if position.y < -100.0 || position.y > 1000.0 {
            return false;
        }

        // 检查是否穿过墙壁（使用服务器端的碰撞检测）
        // ...

        true
    }

    fn resolve_conflicts(&mut self) {
        // 处理多个玩家同时互动的情况
        // 例如：两个玩家同时拾取同一个物品

        // 使用时间戳或玩家ID决定优先级
        // ...
    }

    fn broadcast_state(&self, clients: &mut HashMap<u64, ClientConnection>) {
        let state = NetworkMessage::GameState {
            tick: self.current_tick,
            entities: self.game_state.get_entity_states(),
        };

        let data = bincode::serialize(&state).unwrap();

        for client in clients.values_mut() {
            // 使用可靠的UDP或直接TCP发送
            let _ = client.stream.write_all(&data);
        }
    }
}

// ========== 延迟补偿（Lag Compensation）==========
impl AuthoritativeServer {
    fn handle_shooting(&mut self, shooter_id: u64, shoot_time: f64, target_pos: Vec3) {
        // 计算射击时刻的服务器tick
        let latency = self.get_player_latency(shooter_id);
        let shoot_tick = self.time_to_tick(shoot_time - latency as f64);

        // 回滚到那个tick的状态
        let historical_state = self.get_state_at_tick(shoot_tick);

        // 在那个历史状态下进行命中检测
        if let Some(hit_entity) = self.raycast_in_historical_state(
            shooter_id,
            target_pos,
            &historical_state
        ) {
            // 确认命中
            self.apply_damage(hit_entity, 25.0);
        }
    }

    fn get_state_at_tick(&self, tick: u32) -> ServerGameState {
        // 从历史记录中恢复状态
        self.state_history
            .get(&tick)
            .cloned()
            .unwrap_or_else(|| self.game_state.clone())
    }

    fn raycast_in_historical_state(
        &self,
        shooter_id: u64,
        target_pos: Vec3,
        state: &ServerGameState
    ) -> Option<u64> {
        // 在历史状态下进行射线检测
        // 这样即使目标玩家已经移动，只要射击时准星在目标上就算命中

        let shooter = state.players.get(&shooter_id)?;
        let ray_origin = shooter.position + Vec3::Y * 1.6; // 眼睛高度
        let ray_direction = (target_pos - ray_origin).normalize();

        // 射线检测
        for (entity_id, entity) in &state.entities {
            if *entity_id != shooter_id && self.ray_intersects_entity(ray_origin, ray_direction, entity) {
                return Some(*entity_id);
            }
        }

        None
    }
}
```

---

## 9. 完整示例：简单 3D 游戏

### 9.1 场景设置

```rust
// main.rs
use bevy::prelude::*;
use bevy_rapier3d::prelude::*;

mod player;
mod enemy;
mod ui;
mod game_state;

use player::PlayerPlugin;
use enemy::EnemyPlugin;
use ui::UiPlugin;
use game_state::GameStatePlugin;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "Rust 3D Game".into(),
                resolution: (1280.0, 720.0).into(),
                ..default()
            }),
            ..default()
        }))
        .add_plugins(RapierPhysicsPlugin::<NoUserData>::default())
        .add_plugins(RapierDebugRenderPlugin::default().disable())
        .add_plugins((PlayerPlugin, EnemyPlugin, UiPlugin, GameStatePlugin))
        .add_systems(Startup, setup_game)
        .run();
}

fn setup_game(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
) {
    // 环境光
    commands.insert_resource(AmbientLight {
        color: Color::WHITE,
        brightness: 0.2,
    });

    // 重力
    commands.insert_resource(Gravity::from(Vec3::new(0.0, -9.81, 0.0)));

    // 地面
    commands.spawn((
        PbrBundle {
            mesh: meshes.add(Mesh::from(shape::Plane::from_size(100.0))),
            material: materials.add(StandardMaterial {
                base_color: Color::rgb(0.2, 0.4, 0.2),
                ..default()
            }),
            ..default()
        },
        RigidBody::Fixed,
        Collider::cuboid(50.0, 0.1, 50.0),
    ));

    // 障碍物 - 墙壁
    for i in 0..10 {
        let x = (i as f32 - 5.0) * 5.0;
        commands.spawn((
            PbrBundle {
                mesh: meshes.add(Mesh::from(shape::Cube::new(2.0))),
                material: materials.add(Color::rgb(0.5, 0.5, 0.5).into()),
                transform: Transform::from_xyz(x, 1.0, -10.0),
                ..default()
            },
            RigidBody::Fixed,
            Collider::cuboid(1.0, 1.0, 1.0),
        ));
    }

    // 可收集物品
    for i in 0..5 {
        let angle = (i as f32 / 5.0) * std::f32::consts::TAU;
        let x = angle.cos() * 10.0;
        let z = angle.sin() * 10.0;

        commands.spawn((
            PbrBundle {
                mesh: meshes.add(Mesh::from(shape::UVSphere {
                    radius: 0.5,
                    sectors: 16,
                    stacks: 8,
                })),
                material: materials.add(StandardMaterial {
                    base_color: Color::GOLD,
                    emissive: Color::GOLD * 0.5,
                    ..default()
                }),
                transform: Transform::from_xyz(x, 1.0, z),
                ..default()
            },
            Collectible { value: 10 },
            Rotating { speed: 2.0 },
            Collider::ball(0.5),
            Sensor,
        ));
    }

    // 光源
    commands.spawn(DirectionalLightBundle {
        directional_light: DirectionalLight {
            illuminance: 10000.0,
            shadows_enabled: true,
            ..default()
        },
        transform: Transform::from_xyz(10.0, 20.0, 10.0)
            .looking_at(Vec3::ZERO, Vec3::Y),
        ..default()
    });
}

#[derive(Component)]
struct Collectible {
    value: i32,
}

#[derive(Component)]
struct Rotating {
    speed: f32,
}

fn rotate_collectibles(
    time: Res<Time>,
    mut query: Query<(&mut Transform, &Rotating)>,
) {
    for (mut transform, rotating) in query.iter_mut() {
        transform.rotate_y(rotating.speed * time.delta_seconds());
    }
}
```

### 9.2 玩家控制

```rust
// player.rs
use bevy::prelude::*;
use bevy_rapier3d::prelude::*;

pub struct PlayerPlugin;

impl Plugin for PlayerPlugin {
    fn build(&self, app: &mut App) {
        app.add_systems(Startup, spawn_player)
            .add_systems(Update, (
                player_movement,
                player_camera,
                player_shooting,
                handle_collectibles,
            ));
    }
}

#[derive(Component)]
pub struct Player {
    speed: f32,
    health: f32,
    max_health: f32,
}

#[derive(Component)]
struct PlayerCamera;

fn spawn_player(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
) {
    // 玩家实体
    let player = commands.spawn((
        PbrBundle {
            mesh: meshes.add(Mesh::from(shape::Capsule {
                radius: 0.5,
                depth: 1.0,
                ..default()
            })),
            material: materials.add(Color::BLUE.into()),
            transform: Transform::from_xyz(0.0, 2.0, 0.0),
            ..default()
        },
        Player {
            speed: 8.0,
            health: 100.0,
            max_health: 100.0,
        },
        RigidBody::Dynamic,
        Collider::capsule_y(0.5, 0.5),
        LockedAxes::ROTATION_LOCKED,
        Velocity::default(),
        ExternalImpulse::default(),
    )).id();

    // 相机（作为子实体）
    commands.spawn((
        Camera3dBundle {
            transform: Transform::from_xyz(0.0, 1.0, 0.0),
            ..default()
        },
        PlayerCamera,
    )).set_parent(player);
}

fn player_movement(
    keyboard_input: Res<Input<KeyCode>>,
    mut query: Query<(&mut Velocity, &Player)>,
) {
    for (mut velocity, player) in query.iter_mut() {
        let mut input = Vec3::ZERO;

        if keyboard_input.pressed(KeyCode::W) {
            input.z -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::S) {
            input.z += 1.0;
        }
        if keyboard_input.pressed(KeyCode::A) {
            input.x -= 1.0;
        }
        if keyboard_input.pressed(KeyCode::D) {
            input.x += 1.0;
        }

        if input != Vec3::ZERO {
            input = input.normalize() * player.speed;
            velocity.linvel.x = input.x;
            velocity.linvel.z = input.z;
        } else {
            velocity.linvel.x *= 0.8;
            velocity.linvel.z *= 0.8;
        }
    }
}

fn player_camera(
    mut mouse_motion: EventReader<MouseMotion>,
    mut query: Query<&mut Transform, With<PlayerCamera>>,
) {
    let mut delta = Vec2::ZERO;
    for motion in mouse_motion.read() {
        delta += motion.delta;
    }

    if delta == Vec2::ZERO {
        return;
    }

    for mut transform in query.iter_mut() {
        let (yaw, pitch, roll) = transform.rotation.to_euler(EulerRot::YXZ);

        let new_yaw = yaw - delta.x * 0.002;
        let new_pitch = (pitch - delta.y * 0.002).clamp(-1.5, 1.5);

        transform.rotation = Quat::from_euler(EulerRot::YXZ, new_yaw, new_pitch, roll);
    }
}

fn player_shooting(
    mouse_input: Res<Input<MouseButton>>,
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
    player_query: Query<&GlobalTransform, With<PlayerCamera>>,
    rapier_context: Res<RapierContext>,
) {
    if !mouse_input.just_pressed(MouseButton::Left) {
        return;
    }

    for transform in player_query.iter() {
        let origin = transform.translation();
        let direction = transform.forward();

        // 射线检测
        if let Some((entity, intersection)) = rapier_context.cast_ray(
            origin,
            direction,
            100.0,
            true,
            QueryFilter::default(),
        ) {
            let hit_point = origin + direction * intersection.time_of_impact;

            // 产生击中效果
            commands.spawn((
                PbrBundle {
                    mesh: meshes.add(Mesh::from(shape::UVSphere {
                        radius: 0.2,
                        sectors: 8,
                        stacks: 4,
                    })),
                    material: materials.add(StandardMaterial {
                        base_color: Color::YELLOW,
                        emissive: Color::YELLOW * 5.0,
                        ..default()
                    }),
                    transform: Transform::from_translation(hit_point),
                    ..default()
                },
                ImpactEffect {
                    lifetime: Timer::from_seconds(0.5, TimerMode::Once),
                },
            ));
        }
    }
}

#[derive(Component)]
struct ImpactEffect {
    lifetime: Timer,
}

fn update_impact_effects(
    mut commands: Commands,
    time: Res<Time>,
    mut query: Query<(Entity, &mut ImpactEffect)>,
) {
    for (entity, mut effect) in query.iter_mut() {
        effect.lifetime.tick(time.delta());
        if effect.lifetime.finished() {
            commands.entity(entity).despawn();
        }
    }
}

fn handle_collectibles(
    mut commands: Commands,
    mut collision_events: EventReader<CollisionEvent>,
    collectibles: Query<&Collectible>,
    mut score: ResMut<Score>,
) {
    for event in collision_events.read() {
        if let CollisionEvent::Started(entity1, entity2, _) = event {
            // 检查是否是玩家收集了物品
            if let Ok(collectible) = collectibles.get(*entity1) {
                score.0 += collectible.value;
                commands.entity(*entity1).despawn();
            } else if let Ok(collectible) = collectibles.get(*entity2) {
                score.0 += collectible.value;
                commands.entity(*entity2).despawn();
            }
        }
    }
}

#[derive(Resource, Default)]
struct Score(pub i32);
```

### 9.3 敌人 AI

```rust
// enemy.rs
use bevy::prelude::*;
use bevy_rapier3d::prelude::*;

pub struct EnemyPlugin;

impl Plugin for EnemyPlugin {
    fn build(&self, app: &mut App) {
        app.add_systems(Startup, spawn_enemies)
            .add_systems(Update, (enemy_ai, enemy_health_check));
    }
}

#[derive(Component)]
struct Enemy {
    detection_range: f32,
    attack_range: f32,
    speed: f32,
    health: f32,
    state: EnemyState,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum EnemyState {
    Idle,
    Chasing,
    Attacking,
    Dead,
}

fn spawn_enemies(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
) {
    for i in 0..3 {
        let x = (i as f32 - 1.0) * 15.0;

        commands.spawn((
            PbrBundle {
                mesh: meshes.add(Mesh::from(shape::Cube::new(1.5))),
                material: materials.add(Color::RED.into()),
                transform: Transform::from_xyz(x, 1.0, -20.0),
                ..default()
            },
            Enemy {
                detection_range: 20.0,
                attack_range: 2.0,
                speed: 4.0,
                health: 50.0,
                state: EnemyState::Idle,
            },
            RigidBody::Dynamic,
            Collider::cuboid(0.75, 0.75, 0.75),
            LockedAxes::ROTATION_LOCKED,
            Velocity::default(),
        ));
    }
}

fn enemy_ai(
    time: Res<Time>,
    mut enemies: Query<(Entity, &mut Transform, &mut Velocity, &mut Enemy)>,
    players: Query<&Transform, With<Player>>,
) {
    if let Ok(player_transform) = players.get_single() {
        for (entity, mut transform, mut velocity, mut enemy) in enemies.iter_mut() {
            let distance = transform.translation.distance(player_transform.translation);
            let direction = (player_transform.translation - transform.translation)
                .normalize_or_zero();

            match enemy.state {
                EnemyState::Idle => {
                    if distance < enemy.detection_range {
                        enemy.state = EnemyState::Chasing;
                    }
                }
                EnemyState::Chasing => {
                    if distance < enemy.attack_range {
                        enemy.state = EnemyState::Attacking;
                    } else if distance > enemy.detection_range * 1.5 {
                        enemy.state = EnemyState::Idle;
                        velocity.linvel = Vec3::ZERO;
                    } else {
                        // 向玩家移动
                        velocity.linvel.x = direction.x * enemy.speed;
                        velocity.linvel.z = direction.z * enemy.speed;

                        // 朝向玩家
                        let target_rotation = Quat::from_rotation_arc(
                            Vec3::Z,
                            Vec3::new(direction.x, 0.0, direction.z).normalize_or_zero(),
                        );
                        transform.rotation = transform.rotation.slerp(target_rotation, 5.0 * time.delta_seconds());
                    }
                }
                EnemyState::Attacking => {
                    if distance > enemy.attack_range * 1.5 {
                        enemy.state = EnemyState::Chasing;
                    } else {
                        // 攻击玩家
                        velocity.linvel = Vec3::ZERO;
                        // 在这里实现攻击逻辑
                    }
                }
                EnemyState::Dead => {
                    velocity.linvel = Vec3::ZERO;
                }
            }
        }
    }
}

fn enemy_health_check(
    mut commands: Commands,
    mut enemies: Query<(Entity, &mut Enemy)>,
) {
    for (entity, mut enemy) in enemies.iter_mut() {
        if enemy.health <= 0.0 && enemy.state != EnemyState::Dead {
            enemy.state = EnemyState::Dead;
            // 播放死亡动画或粒子效果
            // 一段时间后销毁实体
            commands.entity(entity).despawn();
        }
    }
}
```

### 9.4 UI 系统

```rust
// ui.rs
use bevy::prelude::*;

pub struct UiPlugin;

impl Plugin for UiPlugin {
    fn build(&self, app: &mut App) {
        app.add_systems(Startup, setup_ui)
            .add_systems(Update, update_ui);
    }
}

#[derive(Component)]
struct HealthBar;

#[derive(Component)]
struct ScoreText;

fn setup_ui(mut commands: Commands) {
    // 根节点
    commands.spawn(NodeBundle {
        style: Style {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            flex_direction: FlexDirection::Column,
            justify_content: JustifyContent::SpaceBetween,
            ..default()
        },
        ..default()
    }).with_children(|parent| {
        // 顶部分数显示
        parent.spawn((
            TextBundle::from_section(
                "Score: 0",
                TextStyle {
                    font_size: 30.0,
                    color: Color::WHITE,
                    ..default()
                },
            )
            .with_style(Style {
                margin: UiRect::all(Val::Px(20.0)),
                ..default()
            }),
            ScoreText,
        ));

        // 底部血条
        parent.spawn(NodeBundle {
            style: Style {
                width: Val::Px(300.0),
                height: Val::Px(30.0),
                margin: UiRect::all(Val::Px(20.0)),
                ..default()
            },
            background_color: Color::DARK_GRAY.into(),
            ..default()
        }).with_children(|parent| {
            parent.spawn((
                NodeBundle {
                    style: Style {
                        width: Val::Percent(100.0),
                        height: Val::Percent(100.0),
                        ..default()
                    },
                    background_color: Color::RED.into(),
                    ..default()
                },
                HealthBar,
            ));
        });
    });
}

fn update_ui(
    score: Res<Score>,
    mut score_query: Query<&mut Text, With<ScoreText>>,
    player_query: Query<&Player>,
    mut health_bar_query: Query<&mut Style, With<HealthBar>>,
) {
    // 更新分数
    for mut text in score_query.iter_mut() {
        text.sections[0].value = format!("Score: {}", score.0);
    }

    // 更新血条
    if let Ok(player) = player_query.get_single() {
        let health_percent = (player.health / player.max_health) * 100.0;
        for mut style in health_bar_query.iter_mut() {
            style.width = Val::Percent(health_percent.clamp(0.0, 100.0));
        }
    }
}
```

### 9.5 游戏状态管理

```rust
// game_state.rs
use bevy::prelude::*;

pub struct GameStatePlugin;

impl Plugin for GameStatePlugin {
    fn build(&self, app: &mut App) {
        app.init_state::<GameState>()
            .add_systems(OnEnter(GameState::Playing), start_game)
            .add_systems(OnEnter(GameState::GameOver), show_game_over)
            .add_systems(Update, check_game_over.run_if(in_state(GameState::Playing)));
    }
}

#[derive(States, Default, Debug, Clone, PartialEq, Eq, Hash)]
pub enum GameState {
    #[default]
    MainMenu,
    Playing,
    Paused,
    GameOver,
    Victory,
}

#[derive(Resource)]
struct GameTimer {
    elapsed: f32,
    max_time: f32,
}

impl Default for GameTimer {
    fn default() -> Self {
        Self {
            elapsed: 0.0,
            max_time: 300.0, // 5分钟
        }
    }
}

fn start_game(
    mut commands: Commands,
    mut next_state: ResMut<NextState<GameState>>,
) {
    commands.insert_resource(GameTimer::default());
    commands.insert_resource(Score::default());
    println!("Game started!");
}

fn check_game_over(
    time: Res<Time>,
    mut game_timer: ResMut<GameTimer>,
    player_query: Query<&Player>,
    enemies: Query<&Enemy>,
    mut next_state: ResMut<NextState<GameState>>,
) {
    // 更新时间
    game_timer.elapsed += time.delta_seconds();

    // 检查时间限制
    if game_timer.elapsed >= game_timer.max_time {
        next_state.set(GameState::GameOver);
        return;
    }

    // 检查玩家死亡
    if let Ok(player) = player_query.get_single() {
        if player.health <= 0.0 {
            next_state.set(GameState::GameOver);
            return;
        }
    }

    // 检查胜利条件（消灭所有敌人）
    if enemies.is_empty() {
        next_state.set(GameState::Victory);
    }
}

fn show_game_over(
    score: Res<Score>,
    game_timer: Res<GameTimer>,
) {
    println!("Game Over!");
    println!("Final Score: {}", score.0);
    println!("Time Survived: {:.1}s", game_timer.elapsed);
}

// 暂停功能
fn toggle_pause(
    keyboard_input: Res<Input<KeyCode>>,
    current_state: Res<State<GameState>>,
    mut next_state: ResMut<NextState<GameState>>,
) {
    if keyboard_input.just_pressed(KeyCode::Escape) {
        match current_state.get() {
            GameState::Playing => next_state.set(GameState::Paused),
            GameState::Paused => next_state.set(GameState::Playing),
            _ => {}
        }
    }
}
```

---

## 10. 性能优化

### 10.1 剖析工具

```rust
use bevy::prelude::*;
use bevy::diagnostic::{FrameTimeDiagnosticsPlugin, LogDiagnosticsPlugin};

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        // 添加性能诊断插件
        .add_plugins(FrameTimeDiagnosticsPlugin)
        .add_plugins(LogDiagnosticsPlugin::default())
        // 启用 Tracy 性能分析（需要 feature = "bevy/trace_tracy"）
        // .add_plugins(bevy::log::LogPlugin::default())
        .run();
}

// ========== 自定义性能计数器 ==========
#[derive(Resource, Default)]
struct PerformanceMetrics {
    entity_count: usize,
    draw_calls: usize,
    physics_time: Duration,
    render_time: Duration,
}

fn update_performance_metrics(
    mut metrics: ResMut<PerformanceMetrics>,
    query: Query<Entity>,
) {
    metrics.entity_count = query.iter().count();
}

fn display_performance_ui(
    metrics: Res<PerformanceMetrics>,
    diagnostics: Res<DiagnosticsStore>,
) {
    // 获取 FPS
    if let Some(fps) = diagnostics.get(&FrameTimeDiagnosticsPlugin::FPS) {
        if let Some(value) = fps.smoothed() {
            println!("FPS: {:.1}", value);
        }
    }

    // 获取帧时间
    if let Some(frame_time) = diagnostics.get(&FrameTimeDiagnosticsPlugin::FRAME_TIME) {
        if let Some(value) = frame_time.smoothed() {
            println!("Frame Time: {:.2}ms", value);
        }
    }

    println!("Entities: {}", metrics.entity_count);
}

// ========== 系统耗时分析 ==========
fn expensive_system(
    query: Query<&Transform>,
) {
    // 使用 tracing 进行性能标记
    let _span = info_span!("expensive_system").entered();

    for transform in query.iter() {
        // 执行一些计算
        let _ = transform.translation.length();
    }
}

// ========== 内存分析 ==========
#[cfg(debug_assertions)]
fn print_memory_usage() {
    use std::alloc::{GlobalAlloc, Layout, System};

    // 注意：这只是一个示例，实际使用需要更复杂的实现
    println!("Memory usage tracking enabled in debug mode");
}
```

### 10.2 批处理

```rust
use bevy::prelude::*;

// ========== 绘制调用批处理 ==========
// Bevy 自动进行网格批处理，但可以通过以下方式优化：

#[derive(Component)]
struct BatchedMesh {
    // 使用纹理图集减少材质切换
    atlas_handle: Handle<TextureAtlas>,
}

// 手动批处理：合并相似网格
fn batch_similar_meshes(
    mut commands: Commands,
    query: Query<(Entity, &Transform, &Handle<Mesh>, &Handle<StandardMaterial>)>,
) {
    // 按材质和网格分组
    let mut batches: HashMap<(Handle<Mesh>, Handle<StandardMaterial>), Vec<(Entity, Transform)>> = HashMap::new();

    for (entity, transform, mesh, material) in query.iter() {
        batches
            .entry((mesh.clone(), material.clone()))
            .or_default()
            .push((entity, *transform));
    }

    // 处理大批量实体
    for ((mesh, material), instances) in batches {
        if instances.len() > 100 {
            // 使用 GPU Instancing 或合并网格
            // 这需要更复杂的实现
        }
    }
}

// ========== ECS 批处理 ==========
fn batch_spawn_system(mut commands: Commands) {
    // 批量生成实体
    commands.spawn_batch((0..1000).map(|i| {
        (
            Transform::from_xyz(i as f32, 0.0, 0.0),
            GlobalTransform::default(),
            Visibility::default(),
        )
    }));
}

fn batch_despawn_system(
    mut commands: Commands,
    query: Query<Entity, With<ShouldDespawn>>,
) {
    // 批量销毁实体
    for entity in query.iter() {
        commands.entity(entity).despawn();
    }
}

#[derive(Component)]
struct ShouldDespawn;

// ========== 遮挡剔除 ==========
#[derive(Component)]
struct Occluder;

fn occlusion_culling(
    camera: Query<&Transform, With<Camera>>,
    mut query: Query<(&Transform, &mut Visibility), Without<Occluder>>,
) {
    if let Ok(camera_transform) = camera.get_single() {
        for (transform, mut visibility) in query.iter_mut() {
            let distance = transform.translation.distance(camera_transform.translation);

            // 简单距离剔除
            if distance > 100.0 {
                *visibility = Visibility::Hidden;
            } else {
                *visibility = Visibility::Visible;
            }
        }
    }
}
```

### 10.3 LOD（细节层次）

```rust
use bevy::prelude::*;

// ========== 基于距离的 LOD ==========
#[derive(Component)]
struct LodGroup {
    levels: Vec<LodLevel>,
}

struct LodLevel {
    mesh: Handle<Mesh>,
    distance: f32,
}

fn update_lod_system(
    camera: Query<&Transform, With<Camera>>,
    mut query: Query<(&Transform, &mut Handle<Mesh>, &LodGroup)>,
) {
    if let Ok(camera_transform) = camera.get_single() {
        for (transform, mut current_mesh, lod_group) in query.iter_mut() {
            let distance = transform.translation.distance(camera_transform.translation);

            // 选择适当的 LOD 级别
            for level in &lod_group.levels {
                if distance < level.distance {
                    *current_mesh = level.mesh.clone();
                    break;
                }
            }
        }
    }
}

// ========== 自动生成 LOD ==========
use bevy::render::mesh::Indices;

fn generate_lod_meshes(
    mut meshes: ResMut<Assets<Mesh>>,
    original_mesh: &Mesh,
) -> Vec<Handle<Mesh>> {
    let mut lod_handles = Vec::new();

    // 原始模型
    lod_handles.push(meshes.add(original_mesh.clone()));

    // 简化版本（这里应该使用实际的网格简化算法）
    // 例如：meshoptimizer 库

    lod_handles
}

// ========== 静态合批 ==========
#[derive(Component)]
struct StaticBatch;

fn static_batching_system(
    mut commands: Commands,
    query: Query<(Entity, &Transform, &Handle<Mesh>, &Handle<StandardMaterial>), With<StaticBatch>>,
    mut meshes: ResMut<Assets<Mesh>>,
) {
    // 收集所有静态网格
    let mut batches: HashMap<(Handle<Mesh>, Handle<StandardMaterial>), Vec<Mat4>> = HashMap::new();

    for (entity, transform, mesh, material) in query.iter() {
        batches
            .entry((mesh.clone(), material.clone()))
            .or_default()
            .push(transform.compute_matrix());

        // 移除原始实体
        commands.entity(entity).despawn();
    }

    // 创建合并后的网格（简化示例）
    for ((mesh_handle, material), transforms) in batches {
        // 这里应该实际合并网格顶点数据
        // 使用 mesh.merge() 或第三方库
    }
}
```

### 10.4 其他优化技巧

```rust
use bevy::prelude::*;

// ========== 固定时间步长 ==========
fn fixed_update_system(
    time: Res<Time>,
    mut accumulator: Local<f32>,
    fixed_timestep: Local<f32>,
) {
    *accumulator += time.delta_seconds();

    while *accumulator >= *fixed_timestep {
        // 执行物理更新等固定频率逻辑
        *accumulator -= *fixed_timestep;
    }
}

// ========== 对象池 ==========
#[derive(Resource)]
struct ObjectPool<T> {
    available: Vec<T>,
    in_use: Vec<T>,
}

impl<T> ObjectPool<T> {
    fn acquire(&mut self) -> Option<T> {
        self.available.pop()
    }

    fn release(&mut self, item: T) {
        self.available.push(item);
    }
}

// ========== 延迟加载 ==========
#[derive(Component)]
struct LazyLoad {
    load_distance: f32,
    loaded: bool,
}

fn lazy_load_system(
    camera: Query<&Transform, With<Camera>>,
    mut query: Query<(Entity, &Transform, &mut LazyLoad, &mut Visibility)>,
) {
    if let Ok(camera_transform) = camera.get_single() {
        for (entity, transform, mut lazy_load, mut visibility) in query.iter_mut() {
            let distance = transform.translation.distance(camera_transform.translation);

            if !lazy_load.loaded && distance < lazy_load.load_distance {
                // 加载资源
                lazy_load.loaded = true;
                *visibility = Visibility::Visible;
            } else if lazy_load.loaded && distance > lazy_load.load_distance * 2.0 {
                // 卸载资源
                lazy_load.loaded = false;
                *visibility = Visibility::Hidden;
            }
        }
    }
}

// ========== 异步资源加载 ==========
use bevy::asset::LoadState;

fn async_asset_loading(
    asset_server: Res<AssetServer>,
    mut loading_assets: ResMut<LoadingAssets>,
) {
    // 检查加载状态
    for handle in &loading_assets.handles {
        match asset_server.get_load_state(handle) {
            LoadState::Loaded => {
                // 资源已加载
            }
            LoadState::Failed => {
                // 加载失败
            }
            _ => {}
        }
    }
}

#[derive(Resource)]
struct LoadingAssets {
    handles: Vec<HandleUntyped>,
}

// ========== 内存管理 ==========
fn cleanup_system(
    mut commands: Commands,
    query: Query<(Entity, &Transform), Without<Player>>,
    camera: Query<&Transform, With<Camera>>,
) {
    if let Ok(camera_transform) = camera.get_single() {
        for (entity, transform) in query.iter() {
            // 清理远离相机的实体
            if transform.translation.distance(camera_transform.translation) > 500.0 {
                commands.entity(entity).despawn();
            }
        }
    }
}
```

---

## 总结

本指南涵盖了 Rust 游戏开发的完整知识体系：

1. **游戏引擎选择**：根据项目需求选择合适的引擎
2. **ECS 架构**：掌握数据导向设计的核心思想
3. **渲染系统**：理解现代图形编程基础
4. **物理引擎**：实现真实的游戏物理效果
5. **资源管理**：高效加载和管理游戏资源
6. **音频系统**：创建沉浸式的声音体验
7. **输入处理**：支持多种输入设备
8. **多人游戏**：构建联网游戏体验
9. **完整示例**：通过实践项目巩固知识
10. **性能优化**：确保游戏流畅运行

## 推荐资源

- [Bevy 官方文档](https://bevyengine.org/learn/)
- [Bevy Cheat Book](https://bevy-cheatbook.github.io/)
- [Rapier 物理引擎文档](https://rapier.rs/docs/)
- [Rust GameDev Working Group](https://gamedev.rs/)
- [Awesome Bevy](https://github.com/bevyengine/awesome-bevy)

## 下一步

1. 完成 [Bevy 官方示例](https://github.com/bevyengine/bevy/tree/main/examples)
2. 尝试修改本指南中的示例代码
3. 参与开源游戏项目
4. 在 [itch.io](https://itch.io/) 上发布你的游戏

祝你的 Rust 游戏开发之旅顺利！
