# Rust 全栈项目实战：构建现代化 Web 应用 (2025版)

> **项目**: 完整的博客系统 (Blog Platform)  
> **技术栈**: Axum + PostgreSQL + React  
> **难度**: 中高级  
> **预计学习时间**: 20-30 小时  
> **更新日期**: 2025-10-20

---

## 📊 目录

- [Rust 全栈项目实战：构建现代化 Web 应用 (2025版)](#rust-全栈项目实战构建现代化-web-应用-2025版)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [项目概览](#项目概览)
    - [功能特性](#功能特性)
    - [技术架构](#技术架构)
    - [项目结构](#项目结构)
  - [环境准备](#环境准备)
    - [开发工具](#开发工具)
    - [数据库设置](#数据库设置)
  - [后端实现](#后端实现)
    - [1. 项目初始化](#1-项目初始化)
    - [2. 数据模型](#2-数据模型)
    - [3. API 路由](#3-api-路由)
    - [4. 认证系统](#4-认证系统)
    - [5. 文章管理](#5-文章管理)
  - [前端实现](#前端实现)
    - [项目设置](#项目设置)
    - [API 客户端](#api-客户端)
    - [页面组件](#页面组件)
  - [高级功能](#高级功能)
    - [1. 图片上传](#1-图片上传)
    - [2. Markdown 渲染](#2-markdown-渲染)
    - [3. 评论系统](#3-评论系统)
    - [4. 搜索功能](#4-搜索功能)
  - [部署上线](#部署上线)
    - [Docker 部署](#docker-部署)
    - [K8s 部署](#k8s-部署)
    - [CI/CD 配置](#cicd-配置)
  - [测试](#测试)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
    - [E2E 测试](#e2e-测试)
  - [性能优化](#性能优化)
  - [安全加固](#安全加固)
  - [监控与日志](#监控与日志)
  - [最佳实践总结](#最佳实践总结)
  - [常见问题](#常见问题)
  - [扩展方向](#扩展方向)
  - [参考资源](#参考资源)

## 📋 目录

- [Rust 全栈项目实战：构建现代化 Web 应用 (2025版)](#rust-全栈项目实战构建现代化-web-应用-2025版)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [项目概览](#项目概览)
    - [功能特性](#功能特性)
    - [技术架构](#技术架构)
    - [项目结构](#项目结构)
  - [环境准备](#环境准备)
    - [开发工具](#开发工具)
    - [数据库设置](#数据库设置)
  - [后端实现](#后端实现)
    - [1. 项目初始化](#1-项目初始化)
    - [2. 数据模型](#2-数据模型)
    - [3. API 路由](#3-api-路由)
    - [4. 认证系统](#4-认证系统)
    - [5. 文章管理](#5-文章管理)
  - [前端实现](#前端实现)
    - [项目设置](#项目设置)
    - [API 客户端](#api-客户端)
    - [页面组件](#页面组件)
  - [高级功能](#高级功能)
    - [1. 图片上传](#1-图片上传)
    - [2. Markdown 渲染](#2-markdown-渲染)
    - [3. 评论系统](#3-评论系统)
    - [4. 搜索功能](#4-搜索功能)
  - [部署上线](#部署上线)
    - [Docker 部署](#docker-部署)
    - [K8s 部署](#k8s-部署)
    - [CI/CD 配置](#cicd-配置)
  - [测试](#测试)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
    - [E2E 测试](#e2e-测试)
  - [性能优化](#性能优化)
  - [安全加固](#安全加固)
  - [监控与日志](#监控与日志)
  - [最佳实践总结](#最佳实践总结)
  - [常见问题](#常见问题)
  - [扩展方向](#扩展方向)
  - [参考资源](#参考资源)

---

## 项目概览

### 功能特性

**核心功能**:

- ✅ 用户注册/登录 (JWT 认证)
- ✅ 文章 CRUD (创建、读取、更新、删除)
- ✅ Markdown 编辑器
- ✅ 评论系统
- ✅ 标签分类
- ✅ 文章搜索
- ✅ 图片上传

**高级功能**:

- ✅ 实时预览
- ✅ 代码高亮
- ✅ SEO 优化
- ✅ RSS 订阅
- ✅ 文章统计

### 技术架构

```text
┌─────────────────────────────────────────────────────────────────┐
│                         前端 (React)                             │
│  • React 18                                                     │
│  • TypeScript                                                   │
│  • TanStack Query                                               │
│  • Tailwind CSS                                                 │
└───────────────────────┬─────────────────────────────────────────┘
                        │ REST API
┌───────────────────────▼─────────────────────────────────────────┐
│                      后端 (Rust)                                 │
│  • Axum (Web 框架)                                              │
│  • SQLx (数据库)                                                │
│  • JWT (认证)                                                    │
│  • Tower (中间件)                                               │
└───────────────────────┬─────────────────────────────────────────┘
                        │
┌───────────────────────▼─────────────────────────────────────────┐
│                    PostgreSQL                                    │
│  • 用户表 (users)                                               │
│  • 文章表 (posts)                                               │
│  • 评论表 (comments)                                            │
└─────────────────────────────────────────────────────────────────┘
```

### 项目结构

```text
blog-platform/
├── backend/                    # Rust 后端
│   ├── Cargo.toml
│   ├── migrations/             # 数据库迁移
│   │   └── 20250120000000_init.sql
│   ├── src/
│   │   ├── main.rs
│   │   ├── config.rs           # 配置
│   │   ├── models/             # 数据模型
│   │   │   ├── mod.rs
│   │   │   ├── user.rs
│   │   │   ├── post.rs
│   │   │   └── comment.rs
│   │   ├── handlers/           # API 处理器
│   │   │   ├── mod.rs
│   │   │   ├── auth.rs
│   │   │   ├── posts.rs
│   │   │   └── comments.rs
│   │   ├── services/           # 业务逻辑
│   │   │   ├── mod.rs
│   │   │   ├── auth_service.rs
│   │   │   └── post_service.rs
│   │   ├── middleware/         # 中间件
│   │   │   ├── mod.rs
│   │   │   └── auth.rs
│   │   └── utils/              # 工具函数
│   │       ├── mod.rs
│   │       └── jwt.rs
│   └── tests/                  # 测试
│       └── integration_test.rs
├── frontend/                   # React 前端
│   ├── package.json
│   ├── src/
│   │   ├── App.tsx
│   │   ├── components/
│   │   ├── pages/
│   │   ├── api/
│   │   └── hooks/
│   └── public/
├── docker-compose.yml          # 本地开发
├── Dockerfile                  # 生产部署
└── README.md
```

---

## 环境准备

### 开发工具

```bash
# 安装 Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 安装 sqlx-cli
cargo install sqlx-cli --no-default-features --features postgres

# 安装 Node.js (v20+)
# 访问 https://nodejs.org/

# 安装 Docker & Docker Compose
# 访问 https://www.docker.com/
```

### 数据库设置

**docker-compose.yml**:

```yaml
version: '3.8'

services:
  postgres:
    image: postgres:16
    environment:
      POSTGRES_DB: blog
      POSTGRES_USER: blog_user
      POSTGRES_PASSWORD: blog_password
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

volumes:
  postgres_data:
```

```bash
# 启动数据库
docker-compose up -d

# 创建数据库
sqlx database create

# 运行迁移
sqlx migrate run
```

**migrations/20250120000000_init.sql**:

```sql
-- 用户表
CREATE TABLE users (
    id SERIAL PRIMARY KEY,
    username VARCHAR(50) UNIQUE NOT NULL,
    email VARCHAR(255) UNIQUE NOT NULL,
    password_hash VARCHAR(255) NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 文章表
CREATE TABLE posts (
    id SERIAL PRIMARY KEY,
    title VARCHAR(255) NOT NULL,
    slug VARCHAR(255) UNIQUE NOT NULL,
    content TEXT NOT NULL,
    excerpt TEXT,
    author_id INTEGER REFERENCES users(id) ON DELETE CASCADE,
    published BOOLEAN DEFAULT FALSE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 标签表
CREATE TABLE tags (
    id SERIAL PRIMARY KEY,
    name VARCHAR(50) UNIQUE NOT NULL
);

-- 文章标签关联表
CREATE TABLE post_tags (
    post_id INTEGER REFERENCES posts(id) ON DELETE CASCADE,
    tag_id INTEGER REFERENCES tags(id) ON DELETE CASCADE,
    PRIMARY KEY (post_id, tag_id)
);

-- 评论表
CREATE TABLE comments (
    id SERIAL PRIMARY KEY,
    post_id INTEGER REFERENCES posts(id) ON DELETE CASCADE,
    author_id INTEGER REFERENCES users(id) ON DELETE CASCADE,
    content TEXT NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 全文搜索索引
CREATE INDEX posts_title_content_idx ON posts USING gin(to_tsvector('english', title || ' ' || content));
```

---

## 后端实现

### 1. 项目初始化

**Cargo.toml**:

```toml
[package]
name = "blog-backend"
version = "0.1.0"
edition = "2021"

[dependencies]
# Web 框架
axum = { version = "0.7", features = ["macros"] }
tower = { version = "0.4", features = ["full"] }
tower-http = { version = "0.5", features = ["cors", "fs"] }

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 数据库
sqlx = { version = "0.7", features = ["runtime-tokio", "postgres", "macros", "chrono"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 认证
jsonwebtoken = "9"
bcrypt = "0.15"

# 配置
config = "0.14"
dotenvy = "0.15"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 时间
chrono = { version = "0.4", features = ["serde"] }

# 其他
uuid = { version = "1.0", features = ["v4", "serde"] }
```

### 2. 数据模型

**src/models/user.rs**:

```rust
use serde::{Serialize, Deserialize};
use sqlx::FromRow;

#[derive(Debug, Serialize, Deserialize, FromRow)]
pub struct User {
    pub id: i32,
    pub username: String,
    pub email: String,
    #[serde(skip_serializing)]
    pub password_hash: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Deserialize)]
pub struct RegisterRequest {
    pub username: String,
    pub email: String,
    pub password: String,
}

#[derive(Debug, Deserialize)]
pub struct LoginRequest {
    pub email: String,
    pub password: String,
}

#[derive(Debug, Serialize)]
pub struct AuthResponse {
    pub token: String,
    pub user: UserInfo,
}

#[derive(Debug, Serialize)]
pub struct UserInfo {
    pub id: i32,
    pub username: String,
    pub email: String,
}
```

**src/models/post.rs**:

```rust
#[derive(Debug, Serialize, Deserialize, FromRow)]
pub struct Post {
    pub id: i32,
    pub title: String,
    pub slug: String,
    pub content: String,
    pub excerpt: Option<String>,
    pub author_id: i32,
    pub published: bool,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub updated_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Deserialize)]
pub struct CreatePostRequest {
    pub title: String,
    pub content: String,
    pub excerpt: Option<String>,
    pub tags: Vec<String>,
    pub published: bool,
}

#[derive(Debug, Deserialize)]
pub struct UpdatePostRequest {
    pub title: Option<String>,
    pub content: Option<String>,
    pub excerpt: Option<String>,
    pub published: Option<bool>,
}

#[derive(Debug, Serialize)]
pub struct PostWithAuthor {
    #[serde(flatten)]
    pub post: Post,
    pub author: String,
    pub tags: Vec<String>,
}
```

### 3. API 路由

**src/main.rs**:

```rust
use axum::{Router, routing::{get, post, put, delete}};
use tower_http::cors::{CorsLayer, Any};
use sqlx::postgres::PgPoolOptions;
use std::sync::Arc;

mod models;
mod handlers;
mod services;
mod middleware;
mod utils;

#[derive(Clone)]
pub struct AppState {
    pub db: sqlx::PgPool,
}

#[tokio::main]
async fn main() {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    // 加载环境变量
    dotenvy::dotenv().ok();
    
    // 数据库连接池
    let database_url = std::env::var("DATABASE_URL")
        .expect("DATABASE_URL must be set");
    
    let pool = PgPoolOptions::new()
        .max_connections(5)
        .connect(&database_url)
        .await
        .expect("Failed to connect to database");
    
    let state = Arc::new(AppState { db: pool });
    
    // 构建路由
    let app = Router::new()
        // 认证路由
        .route("/api/auth/register", post(handlers::auth::register))
        .route("/api/auth/login", post(handlers::auth::login))
        
        // 文章路由
        .route("/api/posts", get(handlers::posts::list_posts))
        .route("/api/posts", post(handlers::posts::create_post))
        .route("/api/posts/:id", get(handlers::posts::get_post))
        .route("/api/posts/:id", put(handlers::posts::update_post))
        .route("/api/posts/:id", delete(handlers::posts::delete_post))
        
        // 评论路由
        .route("/api/posts/:id/comments", get(handlers::comments::list_comments))
        .route("/api/posts/:id/comments", post(handlers::comments::create_comment))
        
        // 中间件
        .layer(CorsLayer::new().allow_origin(Any).allow_methods(Any).allow_headers(Any))
        .with_state(state);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    println!("🚀 Server running on http://0.0.0.0:3000");
    
    axum::serve(listener, app).await.unwrap();
}
```

### 4. 认证系统

**src/utils/jwt.rs**:

```rust
use jsonwebtoken::{encode, decode, Header, Validation, EncodingKey, DecodingKey};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: i32,  // 用户 ID
    pub exp: usize,  // 过期时间
}

pub fn generate_token(user_id: i32) -> Result<String, jsonwebtoken::errors::Error> {
    let secret = std::env::var("JWT_SECRET").expect("JWT_SECRET must be set");
    let expiration = chrono::Utc::now()
        .checked_add_signed(chrono::Duration::days(7))
        .expect("valid timestamp")
        .timestamp() as usize;
    
    let claims = Claims {
        sub: user_id,
        exp: expiration,
    };
    
    encode(
        &Header::default(),
        &claims,
        &EncodingKey::from_secret(secret.as_ref())
    )
}

pub fn verify_token(token: &str) -> Result<Claims, jsonwebtoken::errors::Error> {
    let secret = std::env::var("JWT_SECRET").expect("JWT_SECRET must be set");
    
    decode::<Claims>(
        token,
        &DecodingKey::from_secret(secret.as_ref()),
        &Validation::default()
    ).map(|data| data.claims)
}
```

**src/handlers/auth.rs**:

```rust
use axum::{Json, extract::State, http::StatusCode};
use std::sync::Arc;
use crate::models::user::*;
use crate::AppState;
use crate::utils::jwt;

pub async fn register(
    State(state): State<Arc<AppState>>,
    Json(req): Json<RegisterRequest>,
) -> Result<(StatusCode, Json<AuthResponse>), (StatusCode, String)> {
    // 验证输入
    if req.username.is_empty() || req.email.is_empty() || req.password.is_empty() {
        return Err((StatusCode::BAD_REQUEST, "All fields are required".to_string()));
    }
    
    // 检查用户是否已存在
    let exists = sqlx::query!("SELECT id FROM users WHERE email = $1", req.email)
        .fetch_optional(&state.db)
        .await
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    if exists.is_some() {
        return Err((StatusCode::CONFLICT, "Email already exists".to_string()));
    }
    
    // 哈希密码
    let password_hash = bcrypt::hash(&req.password, bcrypt::DEFAULT_COST)
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    // 创建用户
    let user = sqlx::query_as!(
        User,
        "INSERT INTO users (username, email, password_hash) VALUES ($1, $2, $3) RETURNING *",
        req.username,
        req.email,
        password_hash
    )
    .fetch_one(&state.db)
    .await
    .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    // 生成 JWT
    let token = jwt::generate_token(user.id)
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    Ok((StatusCode::CREATED, Json(AuthResponse {
        token,
        user: UserInfo {
            id: user.id,
            username: user.username,
            email: user.email,
        },
    })))
}

pub async fn login(
    State(state): State<Arc<AppState>>,
    Json(req): Json<LoginRequest>,
) -> Result<Json<AuthResponse>, (StatusCode, String)> {
    // 查找用户
    let user = sqlx::query_as!(
        User,
        "SELECT * FROM users WHERE email = $1",
        req.email
    )
    .fetch_optional(&state.db)
    .await
    .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?
    .ok_or((StatusCode::UNAUTHORIZED, "Invalid credentials".to_string()))?;
    
    // 验证密码
    let valid = bcrypt::verify(&req.password, &user.password_hash)
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    if !valid {
        return Err((StatusCode::UNAUTHORIZED, "Invalid credentials".to_string()));
    }
    
    // 生成 JWT
    let token = jwt::generate_token(user.id)
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    Ok(Json(AuthResponse {
        token,
        user: UserInfo {
            id: user.id,
            username: user.username,
            email: user.email,
        },
    }))
}
```

### 5. 文章管理

**src/handlers/posts.rs**:

```rust
use axum::{Json, extract::{Path, State, Query}, http::StatusCode};
use std::sync::Arc;
use crate::models::post::*;
use crate::AppState;
use serde::Deserialize;

#[derive(Deserialize)]
pub struct ListQuery {
    page: Option<i64>,
    limit: Option<i64>,
    tag: Option<String>,
}

pub async fn list_posts(
    State(state): State<Arc<AppState>>,
    Query(query): Query<ListQuery>,
) -> Result<Json<Vec<PostWithAuthor>>, (StatusCode, String)> {
    let page = query.page.unwrap_or(1);
    let limit = query.limit.unwrap_or(10);
    let offset = (page - 1) * limit;
    
    let posts = sqlx::query!(
        r#"
        SELECT p.*, u.username as author
        FROM posts p
        JOIN users u ON p.author_id = u.id
        WHERE p.published = true
        ORDER BY p.created_at DESC
        LIMIT $1 OFFSET $2
        "#,
        limit,
        offset
    )
    .fetch_all(&state.db)
    .await
    .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    // 转换为 PostWithAuthor
    let posts_with_author = posts.into_iter().map(|row| {
        PostWithAuthor {
            post: Post {
                id: row.id,
                title: row.title,
                slug: row.slug,
                content: row.content,
                excerpt: row.excerpt,
                author_id: row.author_id,
                published: row.published,
                created_at: row.created_at,
                updated_at: row.updated_at,
            },
            author: row.author.unwrap(),
            tags: vec![],  // TODO: 加载标签
        }
    }).collect();
    
    Ok(Json(posts_with_author))
}

pub async fn create_post(
    State(state): State<Arc<AppState>>,
    Json(req): Json<CreatePostRequest>,
    // TODO: 从中间件获取当前用户
) -> Result<(StatusCode, Json<Post>), (StatusCode, String)> {
    // 生成 slug
    let slug = req.title.to_lowercase().replace(" ", "-");
    
    let author_id = 1;  // TODO: 从认证中获取
    
    let post = sqlx::query_as!(
        Post,
        r#"
        INSERT INTO posts (title, slug, content, excerpt, author_id, published)
        VALUES ($1, $2, $3, $4, $5, $6)
        RETURNING *
        "#,
        req.title,
        slug,
        req.content,
        req.excerpt,
        author_id,
        req.published
    )
    .fetch_one(&state.db)
    .await
    .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    Ok((StatusCode::CREATED, Json(post)))
}
```

---

## 前端实现

### 项目设置

```bash
# 创建 React 项目
npx create-react-app frontend --template typescript
cd frontend

# 安装依赖
npm install @tanstack/react-query axios react-router-dom
npm install -D tailwindcss postcss autoprefixer
npx tailwindcss init -p
```

### API 客户端

**src/api/client.ts**:

```typescript
import axios from 'axios';

const API_BASE_URL = process.env.REACT_APP_API_URL || 'http://localhost:3000/api';

export const apiClient = axios.create({
  baseURL: API_BASE_URL,
  headers: {
    'Content-Type': 'application/json',
  },
});

// 请求拦截器：添加 token
apiClient.interceptors.request.use((config) => {
  const token = localStorage.getItem('token');
  if (token) {
    config.headers.Authorization = `Bearer ${token}`;
  }
  return config;
});

// 响应拦截器：处理错误
apiClient.interceptors.response.use(
  (response) => response,
  (error) => {
    if (error.response?.status === 401) {
      localStorage.removeItem('token');
      window.location.href = '/login';
    }
    return Promise.reject(error);
  }
);
```

**src/api/auth.ts**:

```typescript
import { apiClient } from './client';

export interface RegisterRequest {
  username: string;
  email: string;
  password: string;
}

export interface LoginRequest {
  email: string;
  password: string;
}

export interface AuthResponse {
  token: string;
  user: {
    id: number;
    username: string;
    email: string;
  };
}

export const authApi = {
  register: async (data: RegisterRequest): Promise<AuthResponse> => {
    const response = await apiClient.post('/auth/register', data);
    return response.data;
  },
  
  login: async (data: LoginRequest): Promise<AuthResponse> => {
    const response = await apiClient.post('/auth/login', data);
    return response.data;
  },
};
```

### 页面组件

**src/pages/LoginPage.tsx**:

```typescript
import React, { useState } from 'react';
import { useMutation } from '@tanstack/react-query';
import { useNavigate } from 'react-router-dom';
import { authApi } from '../api/auth';

export const LoginPage: React.FC = () => {
  const [email, setEmail] = useState('');
  const [password, setPassword] = useState('');
  const navigate = useNavigate();
  
  const loginMutation = useMutation({
    mutationFn: authApi.login,
    onSuccess: (data) => {
      localStorage.setItem('token', data.token);
      navigate('/');
    },
  });
  
  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    loginMutation.mutate({ email, password });
  };
  
  return (
    <div className="min-h-screen flex items-center justify-center bg-gray-50">
      <div className="max-w-md w-full space-y-8 p-8 bg-white rounded-lg shadow">
        <h2 className="text-3xl font-bold text-center">登录</h2>
        <form onSubmit={handleSubmit} className="space-y-6">
          <div>
            <label className="block text-sm font-medium text-gray-700">
              邮箱
            </label>
            <input
              type="email"
              value={email}
              onChange={(e) => setEmail(e.target.value)}
              className="mt-1 block w-full px-3 py-2 border border-gray-300 rounded-md"
              required
            />
          </div>
          <div>
            <label className="block text-sm font-medium text-gray-700">
              密码
            </label>
            <input
              type="password"
              value={password}
              onChange={(e) => setPassword(e.target.value)}
              className="mt-1 block w-full px-3 py-2 border border-gray-300 rounded-md"
              required
            />
          </div>
          <button
            type="submit"
            disabled={loginMutation.isPending}
            className="w-full flex justify-center py-2 px-4 border border-transparent rounded-md shadow-sm text-sm font-medium text-white bg-blue-600 hover:bg-blue-700"
          >
            {loginMutation.isPending ? '登录中...' : '登录'}
          </button>
        </form>
      </div>
    </div>
  );
};
```

---

## 高级功能

### 1. 图片上传

**后端**:

```rust
use axum::extract::Multipart;
use tokio::fs;
use uuid::Uuid;

pub async fn upload_image(
    mut multipart: Multipart,
) -> Result<Json<serde_json::Value>, (StatusCode, String)> {
    while let Some(field) = multipart.next_field().await.unwrap() {
        let name = field.name().unwrap().to_string();
        let data = field.bytes().await.unwrap();
        
        // 生成唯一文件名
        let file_name = format!("{}.jpg", Uuid::new_v4());
        let file_path = format!("uploads/{}", file_name);
        
        // 保存文件
        fs::write(&file_path, &data).await
            .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
        
        return Ok(Json(serde_json::json!({
            "url": format!("/static/{}", file_name)
        })));
    }
    
    Err((StatusCode::BAD_REQUEST, "No file provided".to_string()))
}
```

### 2. Markdown 渲染

**前端**:

```bash
npm install react-markdown remark-gfm
```

```typescript
import ReactMarkdown from 'react-markdown';
import remarkGfm from 'remark-gfm';

export const PostContent: React.FC<{ content: string }> = ({ content }) => {
  return (
    <ReactMarkdown
      remarkPlugins={[remarkGfm]}
      className="prose prose-lg max-w-none"
    >
      {content}
    </ReactMarkdown>
  );
};
```

### 3. 评论系统

**后端**:

```rust
#[derive(Debug, Serialize, FromRow)]
pub struct Comment {
    pub id: i32,
    pub post_id: i32,
    pub author_id: i32,
    pub content: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

pub async fn create_comment(
    Path(post_id): Path<i32>,
    State(state): State<Arc<AppState>>,
    Json(req): Json<CreateCommentRequest>,
) -> Result<(StatusCode, Json<Comment>), (StatusCode, String)> {
    let author_id = 1;  // TODO: 从认证获取
    
    let comment = sqlx::query_as!(
        Comment,
        "INSERT INTO comments (post_id, author_id, content) VALUES ($1, $2, $3) RETURNING *",
        post_id,
        author_id,
        req.content
    )
    .fetch_one(&state.db)
    .await
    .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    Ok((StatusCode::CREATED, Json(comment)))
}
```

### 4. 搜索功能

**后端**:

```rust
pub async fn search_posts(
    State(state): State<Arc<AppState>>,
    Query(query): Query<SearchQuery>,
) -> Result<Json<Vec<Post>>, (StatusCode, String)> {
    let posts = sqlx::query_as!(
        Post,
        r#"
        SELECT *
        FROM posts
        WHERE to_tsvector('english', title || ' ' || content) @@ plainto_tsquery('english', $1)
        AND published = true
        ORDER BY ts_rank(to_tsvector('english', title || ' ' || content), plainto_tsquery('english', $1)) DESC
        LIMIT 20
        "#,
        query.q
    )
    .fetch_all(&state.db)
    .await
    .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    Ok(Json(posts))
}
```

---

## 部署上线

### Docker 部署

**Dockerfile**:

```dockerfile
# 构建阶段
FROM rust:1.75 as builder

WORKDIR /app
COPY . .

RUN cargo build --release

# 运行阶段
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    libpq5 \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY --from=builder /app/target/release/blog-backend /app/blog-backend

EXPOSE 3000

CMD ["./blog-backend"]
```

**docker-compose.yml (生产)**:

```yaml
version: '3.8'

services:
  backend:
    build: ./backend
    ports:
      - "3000:3000"
    environment:
      DATABASE_URL: postgres://user:password@postgres:5432/blog
      JWT_SECRET: your-secret-key
    depends_on:
      - postgres
  
  frontend:
    build: ./frontend
    ports:
      - "80:80"
  
  postgres:
    image: postgres:16
    volumes:
      - postgres_data:/var/lib/postgresql/data
    environment:
      POSTGRES_DB: blog
      POSTGRES_USER: user
      POSTGRES_PASSWORD: password

volumes:
  postgres_data:
```

### K8s 部署

**k8s/deployment.yaml**:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: blog-backend
spec:
  replicas: 3
  selector:
    matchLabels:
      app: blog-backend
  template:
    metadata:
      labels:
        app: blog-backend
    spec:
      containers:
      - name: backend
        image: blog-backend:latest
        ports:
        - containerPort: 3000
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: blog-secret
              key: database-url
```

### CI/CD 配置

**.github/workflows/deploy.yml**:

```yaml
name: Deploy

on:
  push:
    branches: [ main ]

jobs:
  build-and-deploy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Build Docker image
        run: docker build -t blog-backend:${{ github.sha }} ./backend
      
      - name: Push to Registry
        run: docker push blog-backend:${{ github.sha }}
      
      - name: Deploy to Kubernetes
        run: kubectl apply -f k8s/
```

---

## 测试

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_create_user() {
        // 测试逻辑
    }
}
```

### 集成测试

```rust
#[tokio::test]
async fn test_login_flow() {
    let pool = setup_test_db().await;
    
    // 注册用户
    let register_req = RegisterRequest {
        username: "test".to_string(),
        email: "test@example.com".to_string(),
        password: "password123".to_string(),
    };
    
    // 登录
    let login_req = LoginRequest {
        email: "test@example.com".to_string(),
        password: "password123".to_string(),
    };
    
    // 断言
    assert!(response.is_ok());
}
```

### E2E 测试

**使用 Playwright**:

```typescript
import { test, expect } from '@playwright/test';

test('user can create a post', async ({ page }) => {
  await page.goto('http://localhost:3000');
  await page.click('text=Login');
  await page.fill('input[name="email"]', 'test@example.com');
  await page.fill('input[name="password"]', 'password');
  await page.click('button[type="submit"]');
  
  await page.click('text=New Post');
  await page.fill('input[name="title"]', 'Test Post');
  await page.fill('textarea[name="content"]', 'This is a test post');
  await page.click('button:has-text("Publish")');
  
  await expect(page.locator('text=Test Post')).toBeVisible();
});
```

---

## 性能优化

**1. 数据库索引**:

```sql
CREATE INDEX idx_posts_published ON posts(published, created_at DESC);
CREATE INDEX idx_comments_post_id ON comments(post_id);
```

**2. 响应缓存**:

```rust
use tower_http::compression::CompressionLayer;

let app = Router::new()
    .route("/api/posts", get(list_posts))
    .layer(CompressionLayer::new());
```

**3. 连接池优化**:

```rust
let pool = PgPoolOptions::new()
    .max_connections(20)
    .min_connections(5)
    .connect(&database_url)
    .await?;
```

---

## 安全加固

**1. HTTPS**:

```bash
# 使用 Let's Encrypt
certbot --nginx -d blog.example.com
```

**2. CSRF 防护**:

```rust
use tower_http::csrf::CsrfLayer;

let app = Router::new()
    .route("/api/posts", post(create_post))
    .layer(CsrfLayer::new());
```

**3. SQL 注入防护**: 使用参数化查询 (SQLx 自动防护)

**4. XSS 防护**: React 自动转义

---

## 监控与日志

**1. 日志**:

```rust
use tracing::{info, error};

#[tracing::instrument]
async fn create_post(...) {
    info!("Creating post");
    // ...
    error!("Failed to create post: {}", e);
}
```

**2. 指标**:

```rust
use prometheus::{Counter, Registry};

lazy_static! {
    static ref HTTP_REQUESTS: Counter = Counter::new(
        "http_requests_total",
        "Total HTTP requests"
    ).unwrap();
}
```

---

## 最佳实践总结

**1. 代码组织**: 按功能模块划分
**2. 错误处理**: 使用 `Result` + 自定义错误类型
**3. 数据验证**: 在输入端验证
**4. 安全性**: JWT + HTTPS + 参数化查询
**5. 性能**: 索引 + 缓存 + 连接池
**6. 测试**: 单元测试 + 集成测试 + E2E
**7. 文档**: API 文档 + 代码注释

---

## 常见问题

**Q: 如何处理文件上传？**
A: 使用 `Multipart` + 文件系统/S3

**Q: 如何实现实时通知？**
A: 使用 WebSocket

**Q: 如何优化数据库查询？**
A: 添加索引 + 使用连接池 + 批量操作

---

## 扩展方向

- ✅ 添加 WebSocket 实时评论
- ✅ 集成 Elasticsearch 全文搜索
- ✅ 添加 Redis 缓存
- ✅ 支持多语言 (i18n)
- ✅ 添加邮件通知
- ✅ 实现 SSR/SSG (Next.js)

---

## 参考资源

**官方文档**:

- **Axum**: <https://docs.rs/axum/>
- **SQLx**: <https://docs.rs/sqlx/>
- **React**: <https://react.dev/>

**示例项目**:

- **Realworld**: <https://github.com/gothinkster/realworld>

---

**项目完整代码**: `https://github.com/example/blog-platform-rust`

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20  
**贡献者**: Rust 学习社区

**下一步**: [微服务架构](./RUST_MICROSERVICES_ARCHITECTURE_2025.md) | [性能优化](./RUST_PERFORMANCE_OPTIMIZATION_2025.md)
