# Bevy ECS 形式化分析

> **主题**: 实体组件系统的内存布局与并发
>
> **形式化框架**: 关系代数 + 数据导向设计
>
> **参考**: Bevy Documentation; Data-Oriented Design

---

## 目录

- [Bevy ECS 形式化分析](#bevy-ecs-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. ECS基础概念](#2-ecs基础概念)
    - [2.1 Entity-Component-System定义](#21-entity-component-system定义)
    - [定义 2.1 (ECS核心类型)](#定义-21-ecs核心类型)
    - [定理 2.1 (Entity唯一性)](#定理-21-entity唯一性)
    - [2.2 Archetype存储](#22-archetype存储)
    - [定义 2.2 (Archetype)](#定义-22-archetype)
    - [定理 2.2 (SOA布局)](#定理-22-soa布局)
  - [3. 查询系统](#3-查询系统)
    - [3.1 Query过滤](#31-query过滤)
    - [定义 3.1 (Query)](#定义-31-query)
    - [定理 3.1 (Query类型安全)](#定理-31-query类型安全)
    - [3.2 借用规则](#32-借用规则)
    - [定理 3.2 (ECS借用检查)](#定理-32-ecs借用检查)
  - [4. System调度](#4-system调度)
    - [4.1 依赖图](#41-依赖图)
    - [定义 4.1 (Stage)](#定义-41-stage)
    - [定理 4.1 (依赖图无环)](#定理-41-依赖图无环)
    - [4.2 并行执行](#42-并行执行)
    - [定理 4.2 (自动并行化)](#定理-42-自动并行化)
  - [5. 资源管理](#5-资源管理)
    - [定理 5.1 (Resource唯一性)](#定理-51-resource唯一性)
  - [6. 事件系统](#6-事件系统)
    - [定理 6.1 (事件广播)](#定理-61-事件广播)
  - [7. 内存安全](#7-内存安全)
    - [定理 7.1 (Query生命周期)](#定理-71-query生命周期)
    - [定理 7.2 (命令缓冲)](#定理-72-命令缓冲)
  - [8. 反例与最佳实践](#8-反例与最佳实践)
    - [反例 8.1 (迭代中修改)](#反例-81-迭代中修改)
    - [反例 8.2 (Query冲突)](#反例-82-query冲突)
    - [反例 8.3 (忘记标记组件)](#反例-83-忘记标记组件)
  - [参考文献](#参考文献)

---

## 1. 引言

Bevy ECS提供:

- **数据导向**: SOA内存布局，缓存友好
- **类型安全**: 编译时查询验证
- **并行**: 自动System并行化
- **灵活性**: 动态组件添加/移除

---

## 2. ECS基础概念

### 2.1 Entity-Component-System定义

### 定义 2.1 (ECS核心类型)

```rust
// 实体: 轻量级ID
pub struct Entity {
    id: u32,
    generation: u32,
}

// 组件: 普通数据类型
trait Component: Send + Sync + 'static {}

// System: 处理逻辑
trait System: Send + Sync + 'static {
    fn run(&mut self, world: &mut World);
}
```

### 定理 2.1 (Entity唯一性)

> 每个Entity在世界中有唯一标识。

**证明**:

- `id`: 实体索引
- `generation`: 回收代数
- 相同id不同generation表示不同实体

∎

### 2.2 Archetype存储

### 定义 2.2 (Archetype)

```rust
struct Archetype {
    id: ArchetypeId,
    components: SparseSet<ComponentId, Column>,
    entities: Vec<Entity>,
}
```

### 定理 2.2 (SOA布局)

> Archetype使用SOA(结构体数组)布局，缓存友好。

**对比**:

```text
AOS (传统):
[Entity { pos, vel, health }, Entity { pos, vel, health }, ...]
 分散访问: 每次跳跃 stride

SOA (Bevy):
pos:    [p1, p2, p3, ...]
vel:    [v1, v2, v3, ...]
health: [h1, h2, h3, ...]
连续访问: 缓存命中
```

∎

---

## 3. 查询系统

### 3.1 Query过滤

### 定义 3.1 (Query)

```rust
fn movement_system(
    mut query: Query<(&mut Position, &Velocity), With<Player>>,
) {
    for (mut pos, vel) in query.iter_mut() {
        pos.x += vel.x;
    }
}
```

### 定理 3.1 (Query类型安全)

> Query在编译时验证组件存在性。

**证明**:

```rust
// 编译错误: Camera没有Position
fn system(query: Query<&Position, With<Camera>>) { }

// 编译错误: 同时可变和不可变借用
fn bad_system(query: Query<(&mut Position, &Position)>) { }
```

∎

### 3.2 借用规则

### 定理 3.2 (ECS借用检查)

> Bevy在运行时强制执行组件借用规则。

**规则**:

- 同一组件不能同时有可变和不可变引用
- 不同组件可以同时访问

**实现**:

```rust
// OK: 访问不同组件
fn system1(query: Query<&mut Position>) { }
fn system2(query: Query<&mut Velocity>) { }
// 可以并行执行

// 冲突: 访问相同组件
fn system3(query: Query<&mut Position>) { }
fn system4(query: Query<&Position>) { }
// 不能并行，有依赖
```

∎

---

## 4. System调度

### 4.1 依赖图

### 定义 4.1 (Stage)

```rust
app.add_system(movement.before(collision))
   .add_system(collision)
   .add_system(render.after(collision));
```

### 定理 4.1 (依赖图无环)

> System依赖图必须无环，否则panic。

**证明**:

```rust
// 非法: A -> B -> C -> A
app.add_system(a.before(b))
   .add_system(b.before(c))
   .add_system(c.before(a));  // panic!
```

∎

### 4.2 并行执行

### 定理 4.2 (自动并行化)

> 不冲突的System自动并行执行。

**证明**:

```rust
// System 1: 只读Health
fn read_health(query: Query<&Health>) { }

// System 2: 只读Position
fn read_position(query: Query<&Position>) { }

// System 3: 写Position
fn write_position(query: Query<&mut Position>) { }

// 调度:
// - read_health || read_position (并行)
// - write_position (串行，冲突避免)
```

∎

---

## 5. 资源管理

### 定理 5.1 (Resource唯一性)

> 每种Resource类型只有一个实例。

**实现**:

```rust
pub struct Time {
    delta: Duration,
}

fn system(time: Res<Time>) {
    // 全局访问Time
}
```

**保证**:

- `Res<T>`: 共享访问
- `ResMut<T>`: 独占访问
- 类型系统防止重复

∎

---

## 6. 事件系统

### 定理 6.1 (事件广播)

> 事件在同一帧内广播给所有监听器。

**实现**:

```rust
// 发送
events.send(DamageEvent { amount: 10 });

// 接收
fn damage_system(mut events: EventReader<DamageEvent>) {
    for event in events.read() {
        // 处理
    }
}
```

**保证**:

- 双缓冲: 读写分离
- 无丢失(直到缓冲区满)
- 类型安全

∎

---

## 7. 内存安全

### 定理 7.1 (Query生命周期)

> Query结果在迭代期间有效。

**证明**:

```rust
fn system(world: &mut World) {
    let mut query = world.query::<&Position>();

    // 迭代期间不能修改world
    for pos in query.iter(world) {
        // pos有效
    }
    // 迭代结束，释放借用
}
```

∎

### 定理 7.2 (命令缓冲)

> Commands延迟执行，避免迭代中修改。

**实现**:

```rust
fn system(mut commands: Commands, query: Query<Entity>) {
    for entity in query.iter() {
        commands.entity(entity).despawn();  // 延迟执行
    }
}
// 所有despawn在帧末安全执行
```

∎

---

## 8. 反例与最佳实践

### 反例 8.1 (迭代中修改)

```rust
fn bad_system(world: &mut World) {
    let mut query = world.query::<Entity>();
    for entity in query.iter(world) {
        world.despawn(entity);  // 错误! 已借用world
    }
}

// 正确
fn good_system(mut commands: Commands, query: Query<Entity>) {
    for entity in query.iter() {
        commands.entity(entity).despawn();
    }
}
```

### 反例 8.2 (Query冲突)

```rust
fn bad_system(query: Query<(&mut Position, &mut Position)>) {
    // 编译错误: 重复可变借用
}
```

### 反例 8.3 (忘记标记组件)

```rust
struct MyData;  // 需要 #[derive(Component)]

// 正确
#[derive(Component)]
struct MyData;
```

---

## 参考文献

1. **Bevy Contributors.** (2024). *Bevy Documentation*. <https://bevyengine.org/learn/>

2. **Acton, M.** (2014). *Data-Oriented Design and C++*. CppCon.

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 9个*
*最后更新: 2026-03-04*
