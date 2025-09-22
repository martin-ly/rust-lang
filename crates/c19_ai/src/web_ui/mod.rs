//! Web管理界面模块
//! 
//! 提供基于Web的管理界面，用于管理AI模型、监控系统状态等

pub mod dashboard;
pub mod model_manager;
pub mod user_manager;
pub mod config_manager;

use axum::{
    extract::State,
    response::{Html, Response},
    routing::{get, post, put, delete},
    Router,
};
use std::sync::Arc;

/// Web UI状态
#[derive(Clone)]
pub struct WebUIState {
    pub api_base_url: String,
    pub version: String,
    pub build_time: String,
}

/// 创建Web UI路由
pub fn create_web_ui_routes(state: WebUIState) -> Router {
    Router::new()
        // 主页面
        .route("/", get(dashboard::dashboard_page))
        .route("/dashboard", get(dashboard::dashboard_page))
        
        // 模型管理
        .route("/models", get(model_manager::models_page))
        .route("/models/new", get(model_manager::new_model_page))
        .route("/models/:id", get(model_manager::model_detail_page))
        .route("/api/models", get(model_manager::get_models_api))
        .route("/api/models", post(model_manager::create_model_api))
        .route("/api/models/:id", put(model_manager::update_model_api))
        .route("/api/models/:id", get(model_manager::get_model_api))
        .route("/api/models/:id", delete(model_manager::delete_model_api))
        
        // 用户管理
        .route("/users", get(user_manager::users_page))
        .route("/users/new", get(user_manager::new_user_page))
        .route("/users/:id", get(user_manager::user_detail_page))
        .route("/api/users", get(user_manager::get_users_api))
        .route("/api/users", post(user_manager::create_user_api))
        .route("/api/users/:id", put(user_manager::update_user_api))
        .route("/api/users/:id", get(user_manager::get_user_api))
        .route("/api/users/:id", delete(user_manager::delete_user_api))
        .route("/api/users/:id/permissions", get(user_manager::get_user_permissions_api))
        .route("/api/users/:id/permissions", put(user_manager::update_user_permissions_api))
        
        // 配置管理
        .route("/config", get(config_manager::config_page))
        .route("/api/configs", get(config_manager::get_configs_api))
        .route("/api/configs", post(config_manager::create_config_api))
        .route("/api/configs/:id", get(config_manager::get_config_api))
        .route("/api/configs/:id", put(config_manager::update_config_api))
        .route("/api/configs/:id", delete(config_manager::delete_config_api))
        .route("/api/configs/save", post(config_manager::save_all_configs_api))
        .route("/api/configs/reset", post(config_manager::reset_configs_api))
        
        .with_state(state)
}

/// 基础HTML模板
pub fn base_html(title: &str, content: &str, state: &WebUIState) -> String {
    format!(r#"
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{} - c19_ai 管理界面</title>
    <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.1.3/dist/css/bootstrap.min.css" rel="stylesheet">
    <link href="https://cdn.jsdelivr.net/npm/bootstrap-icons@1.7.2/font/bootstrap-icons.css" rel="stylesheet">
    <link href="/static/css/admin.css" rel="stylesheet">
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
</head>
<body>
    <nav class="navbar navbar-expand-lg navbar-dark bg-dark">
        <div class="container-fluid">
            <a class="navbar-brand" href="/">
                <i class="bi bi-cpu"></i> c19_ai
            </a>
            <button class="navbar-toggler" type="button" data-bs-toggle="collapse" data-bs-target="#navbarNav">
                <span class="navbar-toggler-icon"></span>
            </button>
            <div class="collapse navbar-collapse" id="navbarNav">
                <ul class="navbar-nav me-auto">
                    <li class="nav-item">
                        <a class="nav-link" href="/dashboard">
                            <i class="bi bi-speedometer2"></i> 仪表板
                        </a>
                    </li>
                    <li class="nav-item">
                        <a class="nav-link" href="/models">
                            <i class="bi bi-diagram-3"></i> 模型管理
                        </a>
                    </li>
                    <li class="nav-item">
                        <a class="nav-link" href="/monitor">
                            <i class="bi bi-graph-up"></i> 系统监控
                        </a>
                    </li>
                    <li class="nav-item">
                        <a class="nav-link" href="/users">
                            <i class="bi bi-people"></i> 用户管理
                        </a>
                    </li>
                    <li class="nav-item">
                        <a class="nav-link" href="/config">
                            <i class="bi bi-gear"></i> 配置管理
                        </a>
                    </li>
                </ul>
                <ul class="navbar-nav">
                    <li class="nav-item dropdown">
                        <a class="nav-link dropdown-toggle" href="#" id="navbarDropdown" role="button" data-bs-toggle="dropdown">
                            <i class="bi bi-person-circle"></i> 管理员
                        </a>
                        <ul class="dropdown-menu">
                            <li><a class="dropdown-item" href="/profile">个人资料</a></li>
                            <li><a class="dropdown-item" href="/settings">设置</a></li>
                            <li><hr class="dropdown-divider"></li>
                            <li><a class="dropdown-item" href="/logout">退出登录</a></li>
                        </ul>
                    </li>
                </ul>
            </div>
        </div>
    </nav>

    <div class="container-fluid">
        <div class="row">
            <nav class="col-md-3 col-lg-2 d-md-block bg-light sidebar">
                <div class="position-sticky pt-3">
                    <ul class="nav flex-column">
                        <li class="nav-item">
                            <a class="nav-link" href="/dashboard">
                                <i class="bi bi-speedometer2"></i> 仪表板
                            </a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" href="/models">
                                <i class="bi bi-diagram-3"></i> 模型管理
                            </a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" href="/monitor">
                                <i class="bi bi-graph-up"></i> 系统监控
                            </a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" href="/users">
                                <i class="bi bi-people"></i> 用户管理
                            </a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" href="/config">
                                <i class="bi bi-gear"></i> 配置管理
                            </a>
                        </li>
                    </ul>
                </div>
            </nav>

            <main class="col-md-9 ms-sm-auto col-lg-10 px-md-4">
                <div class="d-flex justify-content-between flex-wrap flex-md-nowrap align-items-center pt-3 pb-2 mb-3 border-bottom">
                    <h1 class="h2">{}</h1>
                    <div class="btn-toolbar mb-2 mb-md-0">
                        <div class="btn-group me-2">
                            <button type="button" class="btn btn-sm btn-outline-secondary">导出</button>
                            <button type="button" class="btn btn-sm btn-outline-secondary">分享</button>
                        </div>
                        <button type="button" class="btn btn-sm btn-primary">
                            <i class="bi bi-plus"></i> 新建
                        </button>
                    </div>
                </div>

                {}
            </main>
        </div>
    </div>

    <footer class="footer mt-auto py-3 bg-light">
        <div class="container">
            <div class="row">
                <div class="col-md-6">
                    <span class="text-muted">© 2024 c19_ai v{}</span>
                </div>
                <div class="col-md-6 text-end">
                    <span class="text-muted">构建时间: {}</span>
                </div>
            </div>
        </div>
    </footer>

    <script src="https://cdn.jsdelivr.net/npm/bootstrap@5.1.3/dist/js/bootstrap.bundle.min.js"></script>
    <script src="/static/js/admin.js"></script>
</body>
</html>
"#, title, title, content, state.version, state.build_time)
}

/// 错误页面
pub fn error_page(title: &str, message: &str, state: &WebUIState) -> String {
    let content = format!(r#"
        <div class="alert alert-danger" role="alert">
            <h4 class="alert-heading">错误</h4>
            <p>{}</p>
            <hr>
            <p class="mb-0">
                <a href="/dashboard" class="btn btn-primary">返回仪表板</a>
            </p>
        </div>
    "#, message);
    
    base_html(title, &content, state)
}

/// 成功页面
pub fn success_page(title: &str, message: &str, state: &WebUIState) -> String {
    let content = format!(r#"
        <div class="alert alert-success" role="alert">
            <h4 class="alert-heading">成功</h4>
            <p>{}</p>
            <hr>
            <p class="mb-0">
                <a href="/dashboard" class="btn btn-primary">返回仪表板</a>
            </p>
        </div>
    "#, message);
    
    base_html(title, &content, state)
}

/// 加载页面
pub fn loading_page(title: &str, message: &str, state: &WebUIState) -> String {
    let content = format!(r#"
        <div class="text-center">
            <div class="spinner-border text-primary" role="status">
                <span class="visually-hidden">加载中...</span>
            </div>
            <p class="mt-3">{}</p>
        </div>
    "#, message);
    
    base_html(title, &content, state)
}
