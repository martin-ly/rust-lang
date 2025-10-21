# Game Development - 游戏开发

## 📋 目录

- [Game Development - 游戏开发](#game-development---游戏开发)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [Bevy](#bevy)
    - [基础示例](#基础示例)
    - [ECS 系统](#ecs-系统)
  - [ggez](#ggez)
    - [基础游戏循环](#基础游戏循环)
  - [macroquad](#macroquad)
    - [简单游戏](#简单游戏)
  - [实战示例](#实战示例)
    - [简单的 Pong 游戏](#简单的-pong-游戏)
  - [参考资源](#参考资源)

---

## 概述

Rust 游戏开发生态日趋成熟，提供高性能和内存安全的游戏引擎。

### 核心依赖

```toml
[dependencies]
# Bevy - ECS 游戏引擎
bevy = "0.12"

# ggez - 2D 游戏框架
ggez = "0.9"

# macroquad - 简单的跨平台游戏库
macroquad = "0.4"
```

---

## Bevy

### 基础示例

```rust
use bevy::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        .add_systems(Update, move_player)
        .run();
}

#[derive(Component)]
struct Player;

fn setup(mut commands: Commands) {
    // 相机
    commands.spawn(Camera2dBundle::default());
    
    // 玩家
    commands.spawn((
        SpriteBundle {
            sprite: Sprite {
                color: Color::rgb(0.0, 0.5, 1.0),
                custom_size: Some(Vec2::new(50.0, 50.0)),
                ..default()
            },
            ..default()
        },
        Player,
    ));
}

fn move_player(
    keyboard_input: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut Transform, With<Player>>,
    time: Res<Time>,
) {
    let mut transform = query.single_mut();
    let speed = 200.0;
    
    if keyboard_input.pressed(KeyCode::ArrowLeft) {
        transform.translation.x -= speed * time.delta_seconds();
    }
    if keyboard_input.pressed(KeyCode::ArrowRight) {
        transform.translation.x += speed * time.delta_seconds();
    }
}
```

### ECS 系统

```rust
use bevy::prelude::*;

#[derive(Component)]
struct Health {
    current: i32,
    max: i32,
}

#[derive(Component)]
struct Enemy;

fn spawn_enemies(mut commands: Commands) {
    for i in 0..5 {
        commands.spawn((
            Enemy,
            Health { current: 100, max: 100 },
            TransformBundle::from_transform(
                Transform::from_xyz(i as f32 * 100.0, 0.0, 0.0)
            ),
        ));
    }
}

fn damage_system(mut query: Query<&mut Health, With<Enemy>>) {
    for mut health in query.iter_mut() {
        health.current -= 10;
        if health.current <= 0 {
            println!("敌人死亡！");
        }
    }
}
```

---

## ggez

### 基础游戏循环

```rust
use ggez::*;

struct GameState {
    pos_x: f32,
}

impl event::EventHandler for GameState {
    fn update(&mut self, ctx: &mut Context) -> GameResult {
        self.pos_x += 1.0;
        if self.pos_x > 800.0 {
            self.pos_x = 0.0;
        }
        Ok(())
    }
    
    fn draw(&mut self, ctx: &mut Context) -> GameResult {
        let mut canvas = graphics::Canvas::from_frame(
            ctx,
            graphics::Color::from_rgb(0, 0, 0),
        );
        
        // 绘制圆形
        let circle = graphics::Mesh::new_circle(
            ctx,
            graphics::DrawMode::fill(),
            [self.pos_x, 300.0],
            50.0,
            0.1,
            graphics::Color::WHITE,
        )?;
        
        canvas.draw(&circle, graphics::DrawParam::default());
        canvas.finish(ctx)?;
        
        Ok(())
    }
}

fn main() -> GameResult {
    let (ctx, event_loop) = ContextBuilder::new("my_game", "author")
        .build()?;
    
    let state = GameState { pos_x: 0.0 };
    event::run(ctx, event_loop, state)
}
```

---

## macroquad

### 简单游戏

```rust
use macroquad::prelude::*;

#[macroquad::main("BasicShapes")]
async fn main() {
    let mut x = screen_width() / 2.0;
    let mut y = screen_height() / 2.0;
    
    loop {
        clear_background(BLACK);
        
        // 移动
        if is_key_down(KeyCode::Right) {
            x += 2.0;
        }
        if is_key_down(KeyCode::Left) {
            x -= 2.0;
        }
        if is_key_down(KeyCode::Down) {
            y += 2.0;
        }
        if is_key_down(KeyCode::Up) {
            y -= 2.0;
        }
        
        // 绘制
        draw_circle(x, y, 15.0, YELLOW);
        
        draw_text("移动圆形！", 20.0, 20.0, 30.0, WHITE);
        
        next_frame().await
    }
}
```

---

## 实战示例

### 简单的 Pong 游戏

```rust
use macroquad::prelude::*;

struct Ball {
    x: f32,
    y: f32,
    vx: f32,
    vy: f32,
}

struct Paddle {
    x: f32,
    y: f32,
}

#[macroquad::main("Pong")]
async fn main() {
    let mut ball = Ball {
        x: screen_width() / 2.0,
        y: screen_height() / 2.0,
        vx: 5.0,
        vy: 5.0,
    };
    
    let mut paddle = Paddle {
        x: screen_width() / 2.0,
        y: screen_height() - 50.0,
    };
    
    loop {
        clear_background(BLACK);
        
        // 移动球
        ball.x += ball.vx;
        ball.y += ball.vy;
        
        // 边界检测
        if ball.x < 0.0 || ball.x > screen_width() {
            ball.vx *= -1.0;
        }
        if ball.y < 0.0 {
            ball.vy *= -1.0;
        }
        
        // 碰撞检测
        if ball.y + 10.0 > paddle.y 
            && ball.x > paddle.x 
            && ball.x < paddle.x + 100.0 
        {
            ball.vy *= -1.0;
        }
        
        // 游戏结束
        if ball.y > screen_height() {
            ball.x = screen_width() / 2.0;
            ball.y = screen_height() / 2.0;
        }
        
        // 移动挡板
        if is_key_down(KeyCode::Left) && paddle.x > 0.0 {
            paddle.x -= 5.0;
        }
        if is_key_down(KeyCode::Right) && paddle.x < screen_width() - 100.0 {
            paddle.x += 5.0;
        }
        
        // 绘制
        draw_circle(ball.x, ball.y, 10.0, YELLOW);
        draw_rectangle(paddle.x, paddle.y, 100.0, 20.0, WHITE);
        
        next_frame().await
    }
}
```

---

## 参考资源

- [Bevy 官网](https://bevyengine.org/)
- [ggez GitHub](https://github.com/ggez/ggez)
- [macroquad 文档](https://docs.rs/macroquad/)
