# Web UI 管理界面

c19_ai 提供了一个现代化的Web管理界面，用于管理AI模型、用户、配置和监控系统状态。

## 功能特性

### 🏠 仪表板

- 系统概览和关键指标
- 实时性能监控
- 资源使用情况
- 最近活动日志

### 🤖 模型管理

- 模型列表和搜索
- 模型创建和编辑
- 模型部署和监控
- 性能指标查看
- 模型版本管理

### 👥 用户管理

- 用户账户管理
- 角色和权限控制
- 用户活动监控
- 权限分配

### ⚙️ 配置管理

- 系统配置查看和编辑
- 配置分类管理
- 配置验证和保存
- 配置历史记录

## 技术栈

- **前端**: HTML5, CSS3, JavaScript (ES6+)
- **UI框架**: Bootstrap 5
- **图标**: Bootstrap Icons
- **图表**: Chart.js
- **后端**: Rust + Axum
- **响应式设计**: 支持移动端和桌面端

## 快速开始

### 1. 启动Web UI服务器

```bash
# 运行Web UI示例
cargo run --example web_ui_server

# 或者使用完整功能
cargo run --features "api-server" --example web_ui_server
```

### 2. 访问管理界面

打开浏览器访问: <http://localhost:8080>

### 3. 默认登录

- 用户名: `admin`
- 密码: `admin123`

## 页面结构

```text
/
├── /dashboard          # 仪表板
├── /models            # 模型管理
│   ├── /new           # 新建模型
│   └── /:id           # 模型详情
├── /users             # 用户管理
│   ├── /new           # 新建用户
│   └── /:id           # 用户详情
└── /config            # 配置管理
```

## API端点

### 模型管理API

- `GET /api/models` - 获取模型列表
- `POST /api/models` - 创建模型
- `GET /api/models/:id` - 获取模型详情
- `PUT /api/models/:id` - 更新模型
- `DELETE /api/models/:id` - 删除模型

### 用户管理API

- `GET /api/users` - 获取用户列表
- `POST /api/users` - 创建用户
- `GET /api/users/:id` - 获取用户详情
- `PUT /api/users/:id` - 更新用户
- `DELETE /api/users/:id` - 删除用户
- `GET /api/users/:id/permissions` - 获取用户权限
- `PUT /api/users/:id/permissions` - 更新用户权限

### 配置管理API

- `GET /api/configs` - 获取配置列表
- `POST /api/configs` - 创建配置
- `GET /api/configs/:id` - 获取配置详情
- `PUT /api/configs/:id` - 更新配置
- `DELETE /api/configs/:id` - 删除配置
- `POST /api/configs/save` - 保存所有配置
- `POST /api/configs/reset` - 重置配置

## 自定义配置

### 修改主题

Web UI使用Bootstrap 5，可以通过CSS变量自定义主题：

```css
:root {
  --bs-primary: #your-color;
  --bs-secondary: #your-color;
  --bs-success: #your-color;
  --bs-info: #your-color;
  --bs-warning: #your-color;
  --bs-danger: #your-color;
}
```

### 添加自定义页面

1. 在 `src/web_ui/` 目录下创建新的模块
2. 在 `mod.rs` 中注册模块
3. 添加路由配置
4. 实现页面处理函数

示例：

```rust
// src/web_ui/custom_page.rs
use super::{base_html, WebUIState};
use axum::{extract::State, response::Html};

pub async fn custom_page(State(state): State<WebUIState>) -> Html<String> {
    let content = r#"
        <div class="container">
            <h1>自定义页面</h1>
            <p>这是自定义页面内容</p>
        </div>
    "#;
    
    Html(base_html("自定义页面", content, &state))
}
```

## 安全考虑

### 认证和授权

- 所有API端点都需要认证
- 基于JWT的会话管理
- 角色基础的访问控制(RBAC)

### 输入验证

- 所有用户输入都经过验证
- SQL注入防护
- XSS攻击防护

### HTTPS支持

- 生产环境建议使用HTTPS
- 支持SSL/TLS证书配置

## 性能优化

### 前端优化

- 静态资源压缩
- 图片懒加载
- 代码分割
- 缓存策略

### 后端优化

- 数据库连接池
- 查询优化
- 缓存机制
- 异步处理

## 部署

### Docker部署

```dockerfile
FROM rust:1.70 as builder
WORKDIR /app
COPY . .
RUN cargo build --release

FROM nginx:alpine
COPY --from=builder /app/target/release/c19_ai /usr/local/bin/
COPY nginx.conf /etc/nginx/nginx.conf
EXPOSE 80
CMD ["c19_ai"]
```

### 环境变量

```bash
# 数据库配置
DATABASE_URL=postgresql://user:password@localhost/c19_ai

# Redis配置
REDIS_URL=redis://localhost:6379

# JWT密钥
JWT_SECRET=your-secret-key

# 服务器配置
SERVER_HOST=0.0.0.0
SERVER_PORT=8080
```

## 故障排除

### 常见问题

1. **页面无法加载**
   - 检查服务器是否启动
   - 确认端口是否被占用
   - 查看浏览器控制台错误

2. **API请求失败**
   - 检查网络连接
   - 确认API端点是否正确
   - 查看服务器日志

3. **认证失败**
   - 检查JWT密钥配置
   - 确认用户凭据
   - 查看认证日志

### 日志查看

```bash
# 查看应用日志
tail -f logs/app.log

# 查看错误日志
tail -f logs/error.log

# 查看访问日志
tail -f logs/access.log
```

## 贡献指南

1. Fork项目
2. 创建功能分支
3. 提交更改
4. 推送到分支
5. 创建Pull Request

## 许可证

本项目采用MIT许可证。详见 [LICENSE](LICENSE) 文件。

## 支持

如有问题或建议，请：

1. 查看 [FAQ](FAQ.md)
2. 搜索 [Issues](https://github.com/your-repo/issues)
3. 创建新的Issue
4. 联系维护者

---

**注意**: 这是一个示例文档，实际使用时请根据项目需求进行调整。
