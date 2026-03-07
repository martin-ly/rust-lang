# 分层架构 (Layered Architecture)

> **模式类型**: 架构模式
> **难度**: 🟡 中等
> **应用场景**: 企业应用、Web 后端

---

## 目录

- [分层架构 (Layered Architecture)](#分层架构-layered-architecture)
  - [目录](#目录)
  - [概念](#概念)
  - [Rust 实现](#rust-实现)
    - [项目结构](#项目结构)
    - [核心代码](#核心代码)
  - [依赖规则](#依赖规则)
  - [优缺点](#优缺点)
  - [变体](#变体)
    - [三层架构](#三层架构)
    - [清洁架构 (Clean Architecture)](#清洁架构-clean-architecture)

## 概念

分层架构将系统组织为水平层，每层有明确职责，只与相邻层交互。

```
┌─────────────────────────────────────┐
│           表示层 (Presentation)      │  ← HTTP/Web
├─────────────────────────────────────┤
│           应用层 (Application)       │  ← 用例、编排
├─────────────────────────────────────┤
│           领域层 (Domain)            │  ← 业务逻辑、实体
├─────────────────────────────────────┤
│           数据层 (Data)              │  ← 数据库、存储
└─────────────────────────────────────┘
```

---

## Rust 实现

### 项目结构

```
src/
├── main.rs              # 入口、DI 配置
├── presentation/        # 表示层
│   ├── mod.rs
│   ├── handlers.rs      # HTTP 处理器
│   └── dto.rs           # 数据传输对象
├── application/         # 应用层
│   ├── mod.rs
│   ├── services.rs      # 应用服务
│   └── traits.rs        # 端口 (接口)
├── domain/              # 领域层
│   ├── mod.rs
│   ├── entities.rs      # 实体
│   ├── value_objects.rs # 值对象
│   └── errors.rs        # 领域错误
└── infrastructure/      # 基础设施层
    ├── mod.rs
    ├── persistence.rs   # 存储实现
    └── http.rs          # HTTP 客户端
```

### 核心代码

```rust
// domain/entities.rs - 领域实体
pub struct User {
    id: UserId,
    name: String,
    email: Email,
}

impl User {
    pub fn new(id: UserId, name: String, email: Email) -> Result<Self, DomainError> {
        // 验证逻辑
        Ok(Self { id, name, email })
    }

    pub fn update_email(&mut self, email: Email) {
        self.email = email;
    }
}

// application/traits.rs - 端口 (接口)
#[async_trait]
pub trait UserRepository: Send + Sync {
    async fn find_by_id(&self, id: &UserId) -> Result<Option<User>, Error>;
    async fn save(&self, user: &User) -> Result<(), Error>;
}

// application/services.rs - 应用服务
pub struct UserService<R: UserRepository> {
    repo: R,
}

impl<R: UserRepository> UserService<R> {
    pub async fn register_user(&self, cmd: RegisterUserCmd) -> Result<User, Error> {
        // 编排逻辑
        let user = User::new(cmd.id, cmd.name, cmd.email)?;
        self.repo.save(&user).await?;
        Ok(user)
    }
}

// presentation/handlers.rs - HTTP 处理器
pub async fn create_user<R: UserRepository>(
    service: web::Data<UserService<R>>,
    dto: web::Json<CreateUserDto>,
) -> impl Responder {
    match service.register_user(dto.into()).await {
        Ok(user) => HttpResponse::Ok().json(UserDto::from(user)),
        Err(e) => HttpResponse::BadRequest().body(e.to_string()),
    }
}
```

---

## 依赖规则

```
依赖方向:

表示层 → 应用层 → 领域层 ↘
                         数据层
              基础设施层 ↗

禁止:
- 领域层依赖应用层
- 应用层依赖表示层
- 层跳跃 (表示层直接访问数据层)
```

---

## 优缺点

| 优点 | 缺点 |
|-----|------|
| 关注点分离 | 性能开销 (层间转换) |
| 可测试性 | 过度抽象风险 |
| 可维护性 | 小型项目可能过度设计 |
| 团队并行开发 | 层数过多导致复杂 |

---

## 变体

### 三层架构

简化版，合并应用层和领域层。

### 清洁架构 (Clean Architecture)

依赖指向领域层，基础设施在外围。

---

*文档版本: 1.0.0*
