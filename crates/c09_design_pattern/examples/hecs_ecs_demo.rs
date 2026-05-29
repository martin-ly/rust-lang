//! HECS ECS 生态系统演示
//!
//! 使用 `hecs` crate 演示实体组件系统的核心概念：
//! - World: 实体容器
//! - Entity: 唯一标识符
//! - Component: 纯数据（Position, Velocity, Health, Name）
//! - System: 查询 + 逻辑（移动、碰撞、渲染）
//! - Query: 按组件类型筛选实体
//!
//! 运行: cargo run --example hecs_ecs_demo -p c09_design_pattern

use hecs::{Entity, World};

// ============================================================
// 组件定义 (纯数据)
// ============================================================

#[derive(Clone, Copy, Debug, PartialEq)]
struct Position {
    x: f32,
    y: f32,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Velocity {
    dx: f32,
    dy: f32,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Health {
    current: i32,
    max: i32,
}

#[derive(Clone, Debug, PartialEq)]
struct Name(String);

#[derive(Clone, Copy, Debug, PartialEq)]
struct Player; // 标签组件 (zero-sized)

#[derive(Clone, Copy, Debug, PartialEq)]
struct Enemy; // 标签组件

// ============================================================
// System: 移动系统
// ============================================================

fn movement_system(world: &mut World, dt: f32) {
    for (pos, vel) in world.query_mut::<(&mut Position, &Velocity)>() {
        pos.x += vel.dx * dt;
        pos.y += vel.dy * dt;
    }
}

// ============================================================
// System: 碰撞检测系统
// ============================================================

fn collision_system(world: &mut World) {
    // 收集所有带 Position + Health 的实体位置
    let entities: Vec<(Entity, Position, i32)> = world
        .query_mut::<(Entity, &Position, &Health)>()
        .into_iter()
        .map(|(e, pos, health)| (e, *pos, health.current))
        .collect();

    for (e1, pos1, _hp1) in &entities {
        for (e2, pos2, hp2) in &entities {
            if e1 == e2 {
                continue;
            }
            let dx = pos1.x - pos2.x;
            let dy = pos1.y - pos2.y;
            let dist_sq = dx * dx + dy * dy;
            if dist_sq < 1.0 {
                // 碰撞：对 e2 造成伤害
                if let Ok(mut health) = world.get::<&mut Health>(*e2) {
                    health.current = (*hp2 - 10).max(0);
                }
            }
        }
    }
}

// ============================================================
// System: 渲染/状态打印系统
// ============================================================

fn render_system(world: &World) {
    println!("--- 实体状态 ---");
    for (id, name, pos, health) in world.query::<(Entity, &Name, &Position, &Health)>().iter() {
        let tag = if world.satisfies::<&Player>(id) {
            "[玩家]"
        } else if world.satisfies::<&Enemy>(id) {
            "[敌人]"
        } else {
            "[中立]"
        };
        println!(
            "  {} {}: pos=({:.1}, {:.1}), hp={}/{}",
            tag, name.0, pos.x, pos.y, health.current, health.max
        );
    }
}

// ============================================================
// 游戏模拟
// ============================================================

fn demo_basic_ecs() {
    println!("=== HECS ECS 基础演示 ===\n");

    let mut world = World::new();

    // 生成玩家实体
    let player = world.spawn((
        Player,
        Name("勇者".to_string()),
        Position { x: 0.0, y: 0.0 },
        Velocity { dx: 1.0, dy: 0.5 },
        Health {
            current: 100,
            max: 100,
        },
    ));

    // 生成敌人实体
    let _enemy1 = world.spawn((
        Enemy,
        Name("史莱姆".to_string()),
        Position { x: 5.0, y: 5.0 },
        Velocity { dx: -0.5, dy: -0.2 },
        Health {
            current: 30,
            max: 30,
        },
    ));

    let _enemy2 = world.spawn((
        Enemy,
        Name("哥布林".to_string()),
        Position { x: 2.0, y: 1.0 }, // 靠近玩家，会发生碰撞
        Velocity { dx: 0.0, dy: 0.0 },
        Health {
            current: 50,
            max: 50,
        },
    ));

    // 生成一个没有 Velocity 的静态实体（如宝箱）
    let _chest = world.spawn((
        Name("宝箱".to_string()),
        Position { x: 10.0, y: 10.0 },
        Health { current: 1, max: 1 },
    ));

    println!("初始状态:");
    render_system(&world);

    // 模拟 3 帧
    for frame in 1..=3 {
        println!("\n--- 第 {} 帧 ---", frame);
        movement_system(&mut world, 1.0);
        collision_system(&mut world);
        render_system(&world);
    }

    // 演示动态添加/移除组件
    println!("\n--- 动态组件操作 ---");
    world
        .insert(player, (Velocity { dx: 2.0, dy: 2.0 },))
        .unwrap();
    println!("给玩家添加了新的 Velocity 组件");
    movement_system(&mut world, 1.0);
    render_system(&world);

    // 演示实体销毁
    println!("\n--- 销毁史莱姆 ---");
    let to_remove: Vec<Entity> = world
        .query::<(Entity, &Name)>()
        .iter()
        .filter(|(_, name)| name.0 == "史莱姆")
        .map(|(e, _)| e)
        .collect();
    for e in to_remove {
        world.despawn(e).unwrap();
    }
    render_system(&world);

    println!("\n✅ HECS ECS 演示完成\n");
}

// ============================================================
// 高级查询演示
// ============================================================

fn demo_advanced_queries() {
    println!("=== 高级查询演示 ===\n");

    let mut world = World::new();

    for i in 0..5 {
        world.spawn((
            Name(format!("单位{}", i)),
            Position {
                x: i as f32,
                y: i as f32,
            },
            Velocity {
                dx: 0.1 * i as f32,
                dy: -0.1 * i as f32,
            },
            Health {
                current: 10 + i * 5,
                max: 20 + i * 5,
            },
        ));
    }

    // 查询所有带 Velocity 的实体数量
    let moving_count = world.query::<&Velocity>().iter().count();
    println!("移动中的实体数量: {}", moving_count);

    // 查询 Health < 50% 的实体
    println!("\n低生命值实体:");
    for (name, health) in world.query::<(&Name, &Health)>().iter() {
        if health.current * 2 < health.max {
            println!(
                "  {}: {}/{} ({}%)",
                name.0,
                health.current,
                health.max,
                health.current * 100 / health.max
            );
        }
    }

    // 批量查询并修改
    println!("\n批量治疗所有实体 (+5 HP):");
    for health in world.query_mut::<&mut Health>() {
        health.current = (health.current + 5).min(health.max);
    }
    for (name, health) in world.query::<(&Name, &Health)>().iter() {
        println!("  {}: {}/{}", name.0, health.current, health.max);
    }

    println!("\n✅ 高级查询演示完成\n");
}

fn main() {
    demo_basic_ecs();
    demo_advanced_queries();
    println!("🎉 全部 ECS 演示通过！");
}
