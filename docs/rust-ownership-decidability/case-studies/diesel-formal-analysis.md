# Diesel ORM形式化分析

> **主题**: 编译时SQL检查的ORM
> **形式化框架**: 类型安全查询 + 编译时验证 + 连接管理
> **参考**: Diesel Documentation (https://diesel.rs)

---

## 目录

1. [引言](#1-引言)
2. [DSL类型系统](#2-dsl类型系统)
3. [查询构建](#3-查询构建)
4. [Schema推理](#4-schema推理)
5. [迁移系统](#5-迁移系统)
6. [连接管理](#6-连接管理)
7. [定理与证明](#7-定理与证明)
8. [代码示例](#8-代码示例)

---

## 1. 引言

Diesel是Rust的编译时SQL检查ORM：
- 零成本抽象
- 编译时SQL验证
- 类型安全查询DSL
- 多后端支持(PostgreSQL, MySQL, SQLite)

---

## 2. DSL类型系统

### 定义 DSL-1 ( 查询DSL )

```rust
users.filter(name.eq("Alice")).limit(10).load::<User>(conn)
```

**形式化**:

$$
\text{Query} = \text{Source} \times \text{Filter}^* \times \text{Limit}^? \times \text{Select}^?
$$

### 定义 DSL-2 ( 表达式类型 )

| 表达式 | 类型 | 返回 |
| :--- | :--- | :--- |
| `col.eq(val)` | `Eq<Column, Value>` | `Bool` |
| `col.gt(val)` | `Gt<Column, Value>` | `Bool` |
| `col.like(pattern)` | `Like<Column, Pattern>` | `Bool` |
| `col.desc()` | `Desc<Column>` | `Order` |

### 定理 DSL-T1 ( 类型一致 )

比较操作要求类型兼容。

$$
\forall c : \text{Column}<T>, v : V.\ T = V \lor \text{compile\_error}
$$

---

## 3. 查询构建

### 定义 QUERY-1 ( Select查询 )

```rust
let query = users.select((id, name));
```

$$
\text{Select} : \text{Table} \times \text{Columns} \to \text{Query}<\text{ReturnType}>
$$

### 定义 QUERY-2 ( 类型推断 )

```rust
let results: Vec<User> = users.load(conn)?;
```

$$
\text{load} : \text{Query}<T> \to \text{Result}<\text{Vec}<T>, \text{Error}>
$$

### 定理 QUERY-T1 ( 返回类型安全 )

查询返回类型在编译时确定。

$$
\text{select}((\text{id}, \text{name})) : \text{Query}<(i32, String)>
$$

---

## 4. Schema推理

### 定义 SCHEMA-1 ( Table定义 )

diesel.toml + migrations → schema.rs

```rust
table! {
    users (id) {
        id -> Int4,
        name -> Varchar,
        email -> Varchar,
    }
}
```

### 定义 SCHEMA-2 ( 关联类型 )

```rust
#[derive(Associations)]
#[diesel(belongs_to(User))]
struct Post { ... }
```

$$
\text{Association} : \text{Child} \times \text{Parent} \times \text{ForeignKey}
$$

---

## 5. 迁移系统

### 定义 MIGRATION-1 ( 迁移结构 )

```rust
// up.sql
CREATE TABLE users (
    id SERIAL PRIMARY KEY,
    name VARCHAR NOT NULL
);

// down.sql
DROP TABLE users;
```

### 定理 MIGRATION-T1 ( 幂等性 )

迁移可重复执行。

$$
\text{run}(m) \circ \text{run}(m) = \text{run}(m)
$$

---

## 6. 连接管理

### 定义 CONN-1 ( 连接池 )

```rust
let manager = ConnectionManager::<PgConnection>::new(database_url);
let pool = Pool::builder().build(manager)?;
```

### 定理 CONN-T1 ( 线程安全 )

连接池自动管理并发。

$$
\text{Pool} : \text{Send} + \text{Sync}
$$

---

## 7. 定理与证明

### 定理 DIESEL-T1 ( 编译时SQL验证 )

无效SQL在编译时捕获。

$$
\text{invalid\_query} \to \text{compile\_error}
$$

**证明**: DSL将查询编码为类型，类型检查即SQL验证。$\square$

### 定理 DIESEL-T2 ( 零成本抽象 )

生成SQL无运行时开销。

$$
\text{DSL\_to\_SQL} = \text{compile\_time}
$$

---

## 8. 代码示例

### 示例1: CRUD操作

```rust
use diesel::prelude::*;
use schema::users;

// Create
let new_user = NewUser { name: "Alice" };
diesel::insert_into(users::table)
    .values(&new_user)
    .execute(conn)?;

// Read
let user = users::table
    .filter(users::name.eq("Alice"))
    .first::<User>(conn)?;

// Update
diesel::update(users::table.find(user.id))
    .set(users::name.eq("Bob"))
    .execute(conn)?;

// Delete
diesel::delete(users::table.find(user.id))
    .execute(conn)?;
```

### 示例2: 关联查询

```rust
#[derive(Queryable, Identifiable)]
struct User { id: i32, name: String }

#[derive(Queryable, Associations)]
#[diesel(belongs_to(User))]
struct Post { id: i32, user_id: i32, title: String }

// 加载用户及其文章
let users_with_posts = User::table
    .limit(10)
    .load::<User>(conn)?
    .into_iter()
    .map(|user| {
        let posts = Post::belonging_to(&user)
            .load::<Post>(conn)?;
        Ok((user, posts))
    })
    .collect::<Result<Vec<_>, diesel::result::Error>>()?;
```

### 示例3: 复杂查询

```rust
use diesel::dsl::*;

// 聚合查询
let count = users::table
    .filter(users::active.eq(true))
    .count()
    .get_result::<i64>(conn)?;

// 分组统计
let stats = posts::table
    .group_by(posts::user_id)
    .select((posts::user_id, count_star()))
    .load::<(i32, i64)>(conn)?;

// 自定义SQL类型
#[derive(SqlType)]
#[diesel(postgres_type(name = "status"))]
struct Status;
```

---

**维护者**: Rust Database Formal Methods Team
**创建日期**: 2026-03-05
**Diesel版本**: 2.x
**状态**: ✅ 已对齐
