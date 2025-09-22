//! 配置管理页面
//! 
//! 提供系统配置的查看、编辑和管理功能

use super::{base_html, WebUIState};
use axum::{
    extract::{Path, State},
    response::Html,
    Json,
};
use serde_json::{json, Value};

/// 配置管理页面
pub async fn config_page(State(state): State<WebUIState>) -> Html<String> {
    let content = r#"
        <div class="d-flex justify-content-between align-items-center mb-4">
            <h2>配置管理</h2>
            <div class="btn-group">
                <button class="btn btn-success" onclick="saveAllConfigs()">
                    <i class="bi bi-save"></i> 保存所有配置
                </button>
                <button class="btn btn-warning" onclick="resetConfigs()">
                    <i class="bi bi-arrow-clockwise"></i> 重置配置
                </button>
                <button class="btn btn-primary" onclick="showNewConfigModal()">
                    <i class="bi bi-plus"></i> 新建配置
                </button>
            </div>
        </div>

        <div class="row">
            <div class="col-md-3">
                <div class="card">
                    <div class="card-header">
                        <h6 class="mb-0">配置分类</h6>
                    </div>
                    <div class="card-body p-0">
                        <div class="list-group list-group-flush">
                            <a href="#" class="list-group-item list-group-item-action active" onclick="showConfigCategory('system')">
                                <i class="bi bi-gear"></i> 系统配置
                            </a>
                            <a href="#" class="list-group-item list-group-item-action" onclick="showConfigCategory('database')">
                                <i class="bi bi-database"></i> 数据库配置
                            </a>
                            <a href="#" class="list-group-item list-group-item-action" onclick="showConfigCategory('cache')">
                                <i class="bi bi-speedometer2"></i> 缓存配置
                            </a>
                            <a href="#" class="list-group-item list-group-item-action" onclick="showConfigCategory('storage')">
                                <i class="bi bi-hdd"></i> 存储配置
                            </a>
                            <a href="#" class="list-group-item list-group-item-action" onclick="showConfigCategory('api')">
                                <i class="bi bi-cloud"></i> API配置
                            </a>
                            <a href="#" class="list-group-item list-group-item-action" onclick="showConfigCategory('security')">
                                <i class="bi bi-shield-check"></i> 安全配置
                            </a>
                        </div>
                    </div>
                </div>
            </div>
            <div class="col-md-9">
                <div class="card">
                    <div class="card-header">
                        <div class="row">
                            <div class="col-md-6">
                                <h5 class="mb-0" id="config-category-title">系统配置</h5>
                            </div>
                            <div class="col-md-6">
                                <div class="input-group">
                                    <input type="text" class="form-control" placeholder="搜索配置..." id="config-search">
                                    <button class="btn btn-outline-secondary" type="button" onclick="searchConfigs()">
                                        <i class="bi bi-search"></i>
                                    </button>
                                </div>
                            </div>
                        </div>
                    </div>
                    <div class="card-body">
                        <div id="config-list">
                            <div class="text-center">
                                <div class="spinner-border" role="status">
                                    <span class="visually-hidden">加载中...</span>
                                </div>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        </div>

        <!-- 新建配置模态框 -->
        <div class="modal fade" id="newConfigModal" tabindex="-1">
            <div class="modal-dialog modal-lg">
                <div class="modal-content">
                    <div class="modal-header">
                        <h5 class="modal-title">新建配置</h5>
                        <button type="button" class="btn-close" data-bs-dismiss="modal"></button>
                    </div>
                    <div class="modal-body">
                        <form id="new-config-form">
                            <div class="row">
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="config-key" class="form-label">配置键</label>
                                        <input type="text" class="form-control" id="config-key" required>
                                    </div>
                                </div>
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="config-category" class="form-label">分类</label>
                                        <select class="form-select" id="config-category" required>
                                            <option value="">请选择分类</option>
                                            <option value="system">系统配置</option>
                                            <option value="database">数据库配置</option>
                                            <option value="cache">缓存配置</option>
                                            <option value="storage">存储配置</option>
                                            <option value="api">API配置</option>
                                            <option value="security">安全配置</option>
                                        </select>
                                    </div>
                                </div>
                            </div>
                            <div class="mb-3">
                                <label for="config-value" class="form-label">配置值</label>
                                <textarea class="form-control" id="config-value" rows="3" required></textarea>
                            </div>
                            <div class="mb-3">
                                <label for="config-description" class="form-label">描述</label>
                                <textarea class="form-control" id="config-description" rows="2"></textarea>
                            </div>
                            <div class="mb-3">
                                <div class="form-check">
                                    <input class="form-check-input" type="checkbox" id="config-encrypted">
                                    <label class="form-check-label" for="config-encrypted">
                                        加密存储
                                    </label>
                                </div>
                            </div>
                        </form>
                    </div>
                    <div class="modal-footer">
                        <button type="button" class="btn btn-secondary" data-bs-dismiss="modal">取消</button>
                        <button type="button" class="btn btn-primary" onclick="createConfig()">创建配置</button>
                    </div>
                </div>
            </div>
        </div>

        <!-- 编辑配置模态框 -->
        <div class="modal fade" id="editConfigModal" tabindex="-1">
            <div class="modal-dialog modal-lg">
                <div class="modal-content">
                    <div class="modal-header">
                        <h5 class="modal-title">编辑配置</h5>
                        <button type="button" class="btn-close" data-bs-dismiss="modal"></button>
                    </div>
                    <div class="modal-body">
                        <form id="edit-config-form">
                            <input type="hidden" id="edit-config-id">
                            <div class="row">
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="edit-config-key" class="form-label">配置键</label>
                                        <input type="text" class="form-control" id="edit-config-key" readonly>
                                    </div>
                                </div>
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="edit-config-category" class="form-label">分类</label>
                                        <input type="text" class="form-control" id="edit-config-category" readonly>
                                    </div>
                                </div>
                            </div>
                            <div class="mb-3">
                                <label for="edit-config-value" class="form-label">配置值</label>
                                <textarea class="form-control" id="edit-config-value" rows="3" required></textarea>
                            </div>
                            <div class="mb-3">
                                <label for="edit-config-description" class="form-label">描述</label>
                                <textarea class="form-control" id="edit-config-description" rows="2"></textarea>
                            </div>
                        </form>
                    </div>
                    <div class="modal-footer">
                        <button type="button" class="btn btn-secondary" data-bs-dismiss="modal">取消</button>
                        <button type="button" class="btn btn-primary" onclick="updateConfig()">更新配置</button>
                    </div>
                </div>
            </div>
        </div>

        <script>
            let currentCategory = 'system';
            let allConfigs = {};

            // 页面加载时初始化
            document.addEventListener('DOMContentLoaded', function() {
                loadConfigs();
            });

            // 加载所有配置
            async function loadConfigs() {
                try {
                    const response = await fetch('/api/configs');
                    allConfigs = await response.json();
                    showConfigCategory(currentCategory);
                } catch (error) {
                    console.error('加载配置失败:', error);
                    showError('加载配置失败');
                }
            }

            // 显示配置分类
            function showConfigCategory(category) {
                currentCategory = category;
                
                // 更新导航状态
                document.querySelectorAll('.list-group-item').forEach(item => {
                    item.classList.remove('active');
                });
                event.target.classList.add('active');
                
                // 更新标题
                const titles = {
                    'system': '系统配置',
                    'database': '数据库配置',
                    'cache': '缓存配置',
                    'storage': '存储配置',
                    'api': 'API配置',
                    'security': '安全配置'
                };
                document.getElementById('config-category-title').textContent = titles[category];
                
                // 显示配置列表
                displayConfigs(category);
            }

            // 显示配置列表
            function displayConfigs(category) {
                const configList = document.getElementById('config-list');
                const categoryConfigs = allConfigs[category] || [];
                
                if (categoryConfigs.length === 0) {
                    configList.innerHTML = '<div class="text-center text-muted">暂无配置</div>';
                    return;
                }

                configList.innerHTML = categoryConfigs.map(config => `
                    <div class="config-item border rounded p-3 mb-3">
                        <div class="row">
                            <div class="col-md-8">
                                <h6 class="mb-1">${config.key}</h6>
                                <p class="text-muted mb-2">${config.description || '无描述'}</p>
                                <div class="config-value">
                                    <code>${config.value}</code>
                                </div>
                            </div>
                            <div class="col-md-4 text-end">
                                <div class="btn-group btn-group-sm">
                                    <button class="btn btn-outline-primary" onclick="editConfig('${config.id}')" title="编辑">
                                        <i class="bi bi-pencil"></i>
                                    </button>
                                    <button class="btn btn-outline-danger" onclick="deleteConfig('${config.id}')" title="删除">
                                        <i class="bi bi-trash"></i>
                                    </button>
                                </div>
                                <div class="mt-2">
                                    <small class="text-muted">
                                        更新于 ${formatDate(config.updated_at)}
                                    </small>
                                </div>
                            </div>
                        </div>
                    </div>
                `).join('');
            }

            // 显示新建配置模态框
            function showNewConfigModal() {
                const modal = new bootstrap.Modal(document.getElementById('newConfigModal'));
                modal.show();
            }

            // 创建配置
            async function createConfig() {
                const form = document.getElementById('new-config-form');
                const configData = {
                    key: document.getElementById('config-key').value,
                    category: document.getElementById('config-category').value,
                    value: document.getElementById('config-value').value,
                    description: document.getElementById('config-description').value,
                    encrypted: document.getElementById('config-encrypted').checked
                };

                try {
                    const response = await fetch('/api/configs', {
                        method: 'POST',
                        headers: {
                            'Content-Type': 'application/json'
                        },
                        body: JSON.stringify(configData)
                    });

                    if (response.ok) {
                        showSuccess('配置创建成功');
                        bootstrap.Modal.getInstance(document.getElementById('newConfigModal')).hide();
                        form.reset();
                        loadConfigs();
                    } else {
                        const error = await response.json();
                        showError(error.message || '创建配置失败');
                    }
                } catch (error) {
                    console.error('创建配置失败:', error);
                    showError('创建配置失败');
                }
            }

            // 编辑配置
            function editConfig(configId) {
                const config = findConfigById(configId);
                if (!config) {
                    showError('配置不存在');
                    return;
                }

                document.getElementById('edit-config-id').value = config.id;
                document.getElementById('edit-config-key').value = config.key;
                document.getElementById('edit-config-category').value = config.category;
                document.getElementById('edit-config-value').value = config.value;
                document.getElementById('edit-config-description').value = config.description || '';

                const modal = new bootstrap.Modal(document.getElementById('editConfigModal'));
                modal.show();
            }

            // 更新配置
            async function updateConfig() {
                const configId = document.getElementById('edit-config-id').value;
                const configData = {
                    value: document.getElementById('edit-config-value').value,
                    description: document.getElementById('edit-config-description').value
                };

                try {
                    const response = await fetch(`/api/configs/${configId}`, {
                        method: 'PUT',
                        headers: {
                            'Content-Type': 'application/json'
                        },
                        body: JSON.stringify(configData)
                    });

                    if (response.ok) {
                        showSuccess('配置更新成功');
                        bootstrap.Modal.getInstance(document.getElementById('editConfigModal')).hide();
                        loadConfigs();
                    } else {
                        const error = await response.json();
                        showError(error.message || '更新配置失败');
                    }
                } catch (error) {
                    console.error('更新配置失败:', error);
                    showError('更新配置失败');
                }
            }

            // 删除配置
            async function deleteConfig(configId) {
                if (!confirm('确定要删除这个配置吗？此操作不可恢复。')) {
                    return;
                }

                try {
                    const response = await fetch(`/api/configs/${configId}`, {
                        method: 'DELETE'
                    });

                    if (response.ok) {
                        showSuccess('配置删除成功');
                        loadConfigs();
                    } else {
                        const error = await response.json();
                        showError(error.message || '删除配置失败');
                    }
                } catch (error) {
                    console.error('删除配置失败:', error);
                    showError('删除配置失败');
                }
            }

            // 保存所有配置
            async function saveAllConfigs() {
                if (!confirm('确定要保存所有配置吗？')) {
                    return;
                }

                try {
                    const response = await fetch('/api/configs/save', {
                        method: 'POST'
                    });

                    if (response.ok) {
                        showSuccess('所有配置保存成功');
                    } else {
                        const error = await response.json();
                        showError(error.message || '保存配置失败');
                    }
                } catch (error) {
                    console.error('保存配置失败:', error);
                    showError('保存配置失败');
                }
            }

            // 重置配置
            async function resetConfigs() {
                if (!confirm('确定要重置所有配置吗？此操作将恢复默认配置。')) {
                    return;
                }

                try {
                    const response = await fetch('/api/configs/reset', {
                        method: 'POST'
                    });

                    if (response.ok) {
                        showSuccess('配置重置成功');
                        loadConfigs();
                    } else {
                        const error = await response.json();
                        showError(error.message || '重置配置失败');
                    }
                } catch (error) {
                    console.error('重置配置失败:', error);
                    showError('重置配置失败');
                }
            }

            // 搜索配置
            function searchConfigs() {
                const searchTerm = document.getElementById('config-search').value.toLowerCase();
                const configItems = document.querySelectorAll('.config-item');
                
                configItems.forEach(item => {
                    const text = item.textContent.toLowerCase();
                    item.style.display = text.includes(searchTerm) ? '' : 'none';
                });
            }

            // 辅助函数
            function findConfigById(configId) {
                for (const category in allConfigs) {
                    const config = allConfigs[category].find(c => c.id === configId);
                    if (config) return config;
                }
                return null;
            }

            function formatDate(dateString) {
                return new Date(dateString).toLocaleString('zh-CN');
            }

            function showSuccess(message) {
                const alert = document.createElement('div');
                alert.className = 'alert alert-success alert-dismissible fade show';
                alert.innerHTML = `
                    ${message}
                    <button type="button" class="btn-close" data-bs-dismiss="alert"></button>
                `;
                document.body.insertBefore(alert, document.body.firstChild);
                setTimeout(() => alert.remove(), 3000);
            }

            function showError(message) {
                const alert = document.createElement('div');
                alert.className = 'alert alert-danger alert-dismissible fade show';
                alert.innerHTML = `
                    ${message}
                    <button type="button" class="btn-close" data-bs-dismiss="alert"></button>
                `;
                document.body.insertBefore(alert, document.body.firstChild);
                setTimeout(() => alert.remove(), 5000);
            }
        </script>
    "#;

    Html(base_html("配置管理", content, &state))
}

/// 获取配置列表API
pub async fn get_configs_api() -> Json<Value> {
    // TODO: 从数据库获取配置列表
    let configs = json!({
        "system": [
            {
                "id": "config_1",
                "key": "app_name",
                "value": "C19 AI Platform",
                "description": "应用程序名称",
                "category": "system",
                "updated_at": "2024-01-01T00:00:00Z"
            },
            {
                "id": "config_2",
                "key": "app_version",
                "value": "1.0.0",
                "description": "应用程序版本",
                "category": "system",
                "updated_at": "2024-01-01T00:00:00Z"
            }
        ],
        "database": [
            {
                "id": "config_3",
                "key": "db_host",
                "value": "localhost",
                "description": "数据库主机地址",
                "category": "database",
                "updated_at": "2024-01-01T00:00:00Z"
            },
            {
                "id": "config_4",
                "key": "db_port",
                "value": "5432",
                "description": "数据库端口",
                "category": "database",
                "updated_at": "2024-01-01T00:00:00Z"
            }
        ],
        "cache": [
            {
                "id": "config_5",
                "key": "cache_ttl",
                "value": "3600",
                "description": "缓存生存时间（秒）",
                "category": "cache",
                "updated_at": "2024-01-01T00:00:00Z"
            }
        ],
        "storage": [],
        "api": [],
        "security": []
    });
    
    Json(configs)
}

/// 创建配置API
pub async fn create_config_api() -> Json<Value> {
    // TODO: 实现配置创建逻辑
    Json(json!({"success": true, "message": "配置创建成功"}))
}

/// 获取单个配置API
pub async fn get_config_api(Path(config_id): Path<String>) -> Json<Value> {
    // TODO: 从数据库获取配置详情
    let config = json!({
        "id": config_id,
        "key": "app_name",
        "value": "C19 AI Platform",
        "description": "应用程序名称",
        "category": "system",
        "updated_at": "2024-01-01T00:00:00Z"
    });
    
    Json(config)
}

/// 更新配置API
pub async fn update_config_api(Path(config_id): Path<String>) -> Json<Value> {
    // TODO: 实现配置更新逻辑
    Json(json!({"success": true, "message": "配置更新成功"}))
}

/// 删除配置API
pub async fn delete_config_api(Path(config_id): Path<String>) -> Json<Value> {
    // TODO: 实现配置删除逻辑
    Json(json!({"success": true, "message": "配置删除成功"}))
}

/// 保存所有配置API
pub async fn save_all_configs_api() -> Json<Value> {
    // TODO: 实现保存所有配置逻辑
    Json(json!({"success": true, "message": "所有配置保存成功"}))
}

/// 重置配置API
pub async fn reset_configs_api() -> Json<Value> {
    // TODO: 实现配置重置逻辑
    Json(json!({"success": true, "message": "配置重置成功"}))
}
