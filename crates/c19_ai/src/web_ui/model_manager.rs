//! 模型管理页面
//! 
//! 提供AI模型的创建、编辑、删除和监控功能

use super::{base_html, WebUIState};
use axum::{
    extract::{Path, State},
    response::Html,
    Json,
};
use serde_json::{json, Value};

/// 模型列表页面
pub async fn models_page(State(state): State<WebUIState>) -> Html<String> {
    let content = r#"
        <div class="d-flex justify-content-between align-items-center mb-4">
            <h2>模型管理</h2>
            <button class="btn btn-primary" onclick="showNewModelModal()">
                <i class="bi bi-plus"></i> 新建模型
            </button>
        </div>

        <div class="card">
            <div class="card-header">
                <div class="row">
                    <div class="col-md-6">
                        <h5 class="mb-0">模型列表</h5>
                    </div>
                    <div class="col-md-6">
                        <div class="input-group">
                            <input type="text" class="form-control" placeholder="搜索模型..." id="model-search">
                            <button class="btn btn-outline-secondary" type="button" onclick="searchModels()">
                                <i class="bi bi-search"></i>
                            </button>
                        </div>
                    </div>
                </div>
            </div>
            <div class="card-body">
                <div class="table-responsive">
                    <table class="table table-hover">
                        <thead>
                            <tr>
                                <th>模型名称</th>
                                <th>类型</th>
                                <th>框架</th>
                                <th>版本</th>
                                <th>状态</th>
                                <th>创建时间</th>
                                <th>操作</th>
                            </tr>
                        </thead>
                        <tbody id="models-table">
                            <tr>
                                <td colspan="7" class="text-center">加载中...</td>
                            </tr>
                        </tbody>
                    </table>
                </div>
            </div>
        </div>

        <!-- 新建模型模态框 -->
        <div class="modal fade" id="newModelModal" tabindex="-1">
            <div class="modal-dialog modal-lg">
                <div class="modal-content">
                    <div class="modal-header">
                        <h5 class="modal-title">新建模型</h5>
                        <button type="button" class="btn-close" data-bs-dismiss="modal"></button>
                    </div>
                    <div class="modal-body">
                        <form id="new-model-form">
                            <div class="row">
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="model-name" class="form-label">模型名称</label>
                                        <input type="text" class="form-control" id="model-name" required>
                                    </div>
                                </div>
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="model-version" class="form-label">版本</label>
                                        <input type="text" class="form-control" id="model-version" value="1.0.0" required>
                                    </div>
                                </div>
                            </div>
                            <div class="row">
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="model-type" class="form-label">模型类型</label>
                                        <select class="form-select" id="model-type" required>
                                            <option value="">请选择类型</option>
                                            <option value="machine_learning">机器学习</option>
                                            <option value="deep_learning">深度学习</option>
                                            <option value="nlp">自然语言处理</option>
                                            <option value="computer_vision">计算机视觉</option>
                                            <option value="recommendation">推荐系统</option>
                                        </select>
                                    </div>
                                </div>
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="model-framework" class="form-label">框架</label>
                                        <select class="form-select" id="model-framework" required>
                                            <option value="">请选择框架</option>
                                            <option value="pytorch">PyTorch</option>
                                            <option value="tensorflow">TensorFlow</option>
                                            <option value="scikit-learn">Scikit-learn</option>
                                            <option value="xgboost">XGBoost</option>
                                            <option value="lightgbm">LightGBM</option>
                                        </select>
                                    </div>
                                </div>
                            </div>
                            <div class="mb-3">
                                <label for="model-description" class="form-label">描述</label>
                                <textarea class="form-control" id="model-description" rows="3"></textarea>
                            </div>
                            <div class="mb-3">
                                <label for="model-file" class="form-label">模型文件</label>
                                <input type="file" class="form-control" id="model-file" accept=".pkl,.pth,.h5,.onnx,.joblib">
                            </div>
                        </form>
                    </div>
                    <div class="modal-footer">
                        <button type="button" class="btn btn-secondary" data-bs-dismiss="modal">取消</button>
                        <button type="button" class="btn btn-primary" onclick="createModel()">创建模型</button>
                    </div>
                </div>
            </div>
        </div>

        <!-- 模型详情模态框 -->
        <div class="modal fade" id="modelDetailModal" tabindex="-1">
            <div class="modal-dialog modal-xl">
                <div class="modal-content">
                    <div class="modal-header">
                        <h5 class="modal-title">模型详情</h5>
                        <button type="button" class="btn-close" data-bs-dismiss="modal"></button>
                    </div>
                    <div class="modal-body">
                        <div id="model-detail-content">
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

        <script>
            // 页面加载时初始化
            document.addEventListener('DOMContentLoaded', function() {
                loadModels();
            });

            // 加载模型列表
            async function loadModels() {
                try {
                    const response = await fetch('/api/models');
                    const models = await response.json();
                    updateModelsTable(models);
                } catch (error) {
                    console.error('加载模型列表失败:', error);
                    showError('加载模型列表失败');
                }
            }

            // 更新模型表格
            function updateModelsTable(models) {
                const tbody = document.getElementById('models-table');
                
                if (!models || models.length === 0) {
                    tbody.innerHTML = '<tr><td colspan="7" class="text-center">暂无模型</td></tr>';
                    return;
                }

                tbody.innerHTML = models.map(model => `
                    <tr>
                        <td>
                            <strong>${model.name}</strong>
                            <br>
                            <small class="text-muted">${model.description || '无描述'}</small>
                        </td>
                        <td>
                            <span class="badge bg-primary">${getModelTypeLabel(model.model_type)}</span>
                        </td>
                        <td>${model.framework || '未知'}</td>
                        <td>${model.version}</td>
                        <td>
                            <span class="badge ${getStatusBadgeClass(model.status)}">${getStatusLabel(model.status)}</span>
                        </td>
                        <td>${formatDate(model.created_at)}</td>
                        <td>
                            <div class="btn-group btn-group-sm">
                                <button class="btn btn-outline-primary" onclick="viewModel('${model.id}')" title="查看详情">
                                    <i class="bi bi-eye"></i>
                                </button>
                                <button class="btn btn-outline-success" onclick="deployModel('${model.id}')" title="部署">
                                    <i class="bi bi-play"></i>
                                </button>
                                <button class="btn btn-outline-warning" onclick="editModel('${model.id}')" title="编辑">
                                    <i class="bi bi-pencil"></i>
                                </button>
                                <button class="btn btn-outline-danger" onclick="deleteModel('${model.id}')" title="删除">
                                    <i class="bi bi-trash"></i>
                                </button>
                            </div>
                        </td>
                    </tr>
                `).join('');
            }

            // 显示新建模型模态框
            function showNewModelModal() {
                const modal = new bootstrap.Modal(document.getElementById('newModelModal'));
                modal.show();
            }

            // 创建模型
            async function createModel() {
                const form = document.getElementById('new-model-form');
                const formData = new FormData();
                
                formData.append('name', document.getElementById('model-name').value);
                formData.append('version', document.getElementById('model-version').value);
                formData.append('model_type', document.getElementById('model-type').value);
                formData.append('framework', document.getElementById('model-framework').value);
                formData.append('description', document.getElementById('model-description').value);
                
                const fileInput = document.getElementById('model-file');
                if (fileInput.files[0]) {
                    formData.append('file', fileInput.files[0]);
                }

                try {
                    const response = await fetch('/api/models', {
                        method: 'POST',
                        body: formData
                    });

                    if (response.ok) {
                        showSuccess('模型创建成功');
                        bootstrap.Modal.getInstance(document.getElementById('newModelModal')).hide();
                        form.reset();
                        loadModels();
                    } else {
                        const error = await response.json();
                        showError(error.message || '创建模型失败');
                    }
                } catch (error) {
                    console.error('创建模型失败:', error);
                    showError('创建模型失败');
                }
            }

            // 查看模型详情
            async function viewModel(modelId) {
                try {
                    const response = await fetch(`/api/models/${modelId}`);
                    const model = await response.json();
                    showModelDetail(model);
                } catch (error) {
                    console.error('加载模型详情失败:', error);
                    showError('加载模型详情失败');
                }
            }

            // 显示模型详情
            function showModelDetail(model) {
                const content = `
                    <div class="row">
                        <div class="col-md-6">
                            <h6>基本信息</h6>
                            <table class="table table-sm">
                                <tr><td>名称</td><td>${model.name}</td></tr>
                                <tr><td>版本</td><td>${model.version}</td></tr>
                                <tr><td>类型</td><td>${getModelTypeLabel(model.model_type)}</td></tr>
                                <tr><td>框架</td><td>${model.framework || '未知'}</td></tr>
                                <tr><td>状态</td><td><span class="badge ${getStatusBadgeClass(model.status)}">${getStatusLabel(model.status)}</span></td></tr>
                                <tr><td>创建时间</td><td>${formatDate(model.created_at)}</td></tr>
                                <tr><td>更新时间</td><td>${formatDate(model.updated_at)}</td></tr>
                            </table>
                        </div>
                        <div class="col-md-6">
                            <h6>性能指标</h6>
                            <div class="row">
                                <div class="col-6">
                                    <div class="card text-center">
                                        <div class="card-body">
                                            <h5 class="card-title">${model.metrics?.total_requests || 0}</h5>
                                            <p class="card-text">总请求数</p>
                                        </div>
                                    </div>
                                </div>
                                <div class="col-6">
                                    <div class="card text-center">
                                        <div class="card-body">
                                            <h5 class="card-title">${model.metrics?.avg_response_time || 0}ms</h5>
                                            <p class="card-text">平均响应时间</p>
                                        </div>
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>
                    <div class="row mt-3">
                        <div class="col-12">
                            <h6>描述</h6>
                            <p>${model.description || '无描述'}</p>
                        </div>
                    </div>
                `;
                
                document.getElementById('model-detail-content').innerHTML = content;
                const modal = new bootstrap.Modal(document.getElementById('modelDetailModal'));
                modal.show();
            }

            // 部署模型
            async function deployModel(modelId) {
                if (!confirm('确定要部署这个模型吗？')) {
                    return;
                }

                try {
                    const response = await fetch(`/api/models/${modelId}/deploy`, {
                        method: 'POST'
                    });

                    if (response.ok) {
                        showSuccess('模型部署成功');
                        loadModels();
                    } else {
                        const error = await response.json();
                        showError(error.message || '部署模型失败');
                    }
                } catch (error) {
                    console.error('部署模型失败:', error);
                    showError('部署模型失败');
                }
            }

            // 删除模型
            async function deleteModel(modelId) {
                if (!confirm('确定要删除这个模型吗？此操作不可恢复。')) {
                    return;
                }

                try {
                    const response = await fetch(`/api/models/${modelId}`, {
                        method: 'DELETE'
                    });

                    if (response.ok) {
                        showSuccess('模型删除成功');
                        loadModels();
                    } else {
                        const error = await response.json();
                        showError(error.message || '删除模型失败');
                    }
                } catch (error) {
                    console.error('删除模型失败:', error);
                    showError('删除模型失败');
                }
            }

            // 搜索模型
            function searchModels() {
                const searchTerm = document.getElementById('model-search').value.toLowerCase();
                const rows = document.querySelectorAll('#models-table tr');
                
                rows.forEach(row => {
                    const text = row.textContent.toLowerCase();
                    row.style.display = text.includes(searchTerm) ? '' : 'none';
                });
            }

            // 辅助函数
            function getModelTypeLabel(type) {
                const labels = {
                    'machine_learning': '机器学习',
                    'deep_learning': '深度学习',
                    'nlp': '自然语言处理',
                    'computer_vision': '计算机视觉',
                    'recommendation': '推荐系统'
                };
                return labels[type] || type;
            }

            function getStatusLabel(status) {
                const labels = {
                    'active': '活跃',
                    'inactive': '非活跃',
                    'training': '训练中',
                    'deploying': '部署中',
                    'error': '错误'
                };
                return labels[status] || status;
            }

            function getStatusBadgeClass(status) {
                const classes = {
                    'active': 'bg-success',
                    'inactive': 'bg-secondary',
                    'training': 'bg-warning',
                    'deploying': 'bg-info',
                    'error': 'bg-danger'
                };
                return classes[status] || 'bg-secondary';
            }

            function formatDate(dateString) {
                return new Date(dateString).toLocaleString('zh-CN');
            }

            function showSuccess(message) {
                // 显示成功消息
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
                // 显示错误消息
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

    Html(base_html("模型管理", content, &state))
}

/// 新建模型页面
pub async fn new_model_page(State(state): State<WebUIState>) -> Html<String> {
    let content = r#"
        <div class="row justify-content-center">
            <div class="col-md-8">
                <div class="card">
                    <div class="card-header">
                        <h5 class="mb-0">新建模型</h5>
                    </div>
                    <div class="card-body">
                        <form id="new-model-form">
                            <div class="mb-3">
                                <label for="model-name" class="form-label">模型名称 *</label>
                                <input type="text" class="form-control" id="model-name" required>
                            </div>
                            <div class="row">
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="model-version" class="form-label">版本 *</label>
                                        <input type="text" class="form-control" id="model-version" value="1.0.0" required>
                                    </div>
                                </div>
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="model-type" class="form-label">模型类型 *</label>
                                        <select class="form-select" id="model-type" required>
                                            <option value="">请选择类型</option>
                                            <option value="machine_learning">机器学习</option>
                                            <option value="deep_learning">深度学习</option>
                                            <option value="nlp">自然语言处理</option>
                                            <option value="computer_vision">计算机视觉</option>
                                            <option value="recommendation">推荐系统</option>
                                        </select>
                                    </div>
                                </div>
                            </div>
                            <div class="row">
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="model-framework" class="form-label">框架 *</label>
                                        <select class="form-select" id="model-framework" required>
                                            <option value="">请选择框架</option>
                                            <option value="pytorch">PyTorch</option>
                                            <option value="tensorflow">TensorFlow</option>
                                            <option value="scikit-learn">Scikit-learn</option>
                                            <option value="xgboost">XGBoost</option>
                                            <option value="lightgbm">LightGBM</option>
                                        </select>
                                    </div>
                                </div>
                                <div class="col-md-6">
                                    <div class="mb-3">
                                        <label for="model-device" class="form-label">设备</label>
                                        <select class="form-select" id="model-device">
                                            <option value="cpu">CPU</option>
                                            <option value="cuda">CUDA</option>
                                            <option value="mps">MPS (Apple Silicon)</option>
                                        </select>
                                    </div>
                                </div>
                            </div>
                            <div class="mb-3">
                                <label for="model-description" class="form-label">描述</label>
                                <textarea class="form-control" id="model-description" rows="3"></textarea>
                            </div>
                            <div class="mb-3">
                                <label for="model-file" class="form-label">模型文件 *</label>
                                <input type="file" class="form-control" id="model-file" accept=".pkl,.pth,.h5,.onnx,.joblib" required>
                                <div class="form-text">支持 .pkl, .pth, .h5, .onnx, .joblib 格式</div>
                            </div>
                            <div class="d-grid gap-2 d-md-flex justify-content-md-end">
                                <a href="/models" class="btn btn-secondary me-md-2">取消</a>
                                <button type="button" class="btn btn-primary" onclick="createModel()">创建模型</button>
                            </div>
                        </form>
                    </div>
                </div>
            </div>
        </div>

        <script>
            async function createModel() {
                const form = document.getElementById('new-model-form');
                if (!form.checkValidity()) {
                    form.reportValidity();
                    return;
                }

                const formData = new FormData();
                formData.append('name', document.getElementById('model-name').value);
                formData.append('version', document.getElementById('model-version').value);
                formData.append('model_type', document.getElementById('model-type').value);
                formData.append('framework', document.getElementById('model-framework').value);
                formData.append('device', document.getElementById('model-device').value);
                formData.append('description', document.getElementById('model-description').value);
                formData.append('file', document.getElementById('model-file').files[0]);

                try {
                    const response = await fetch('/api/models', {
                        method: 'POST',
                        body: formData
                    });

                    if (response.ok) {
                        alert('模型创建成功！');
                        window.location.href = '/models';
                    } else {
                        const error = await response.json();
                        alert('创建模型失败: ' + (error.message || '未知错误'));
                    }
                } catch (error) {
                    console.error('创建模型失败:', error);
                    alert('创建模型失败');
                }
            }
        </script>
    "#;

    Html(base_html("新建模型", content, &state))
}

/// 模型详情页面
pub async fn model_detail_page(Path(model_id): Path<String>, State(state): State<WebUIState>) -> Html<String> {
    let content = format!(r#"
        <div id="model-detail-container">
            <div class="text-center">
                <div class="spinner-border" role="status">
                    <span class="visually-hidden">加载中...</span>
                </div>
            </div>
        </div>

        <script>
            document.addEventListener('DOMContentLoaded', function() {{
                loadModelDetail('{}');
            }});

            async function loadModelDetail(modelId) {{
                try {{
                    const response = await fetch(`/api/models/${{modelId}}`);
                    const model = await response.json();
                    displayModelDetail(model);
                }} catch (error) {{
                    console.error('加载模型详情失败:', error);
                    document.getElementById('model-detail-container').innerHTML = 
                        '<div class="alert alert-danger">加载模型详情失败</div>';
                }}
            }}

            function displayModelDetail(model) {{
                const container = document.getElementById('model-detail-container');
                container.innerHTML = `
                    <div class="d-flex justify-content-between align-items-center mb-4">
                        <h2>${{model.name}}</h2>
                        <div class="btn-group">
                            <button class="btn btn-success" onclick="deployModel('${{model.id}}')">
                                <i class="bi bi-play"></i> 部署
                            </button>
                            <button class="btn btn-warning" onclick="editModel('${{model.id}}')">
                                <i class="bi bi-pencil"></i> 编辑
                            </button>
                            <button class="btn btn-danger" onclick="deleteModel('${{model.id}}')">
                                <i class="bi bi-trash"></i> 删除
                            </button>
                        </div>
                    </div>

                    <div class="row">
                        <div class="col-md-8">
                            <div class="card">
                                <div class="card-header">
                                    <h5 class="mb-0">基本信息</h5>
                                </div>
                                <div class="card-body">
                                    <table class="table">
                                        <tr><td>名称</td><td>${{model.name}}</td></tr>
                                        <tr><td>版本</td><td>${{model.version}}</td></tr>
                                        <tr><td>类型</td><td>${{model.model_type}}</td></tr>
                                        <tr><td>框架</td><td>${{model.framework || '未知'}}</td></tr>
                                        <tr><td>设备</td><td>${{model.device || 'CPU'}}</td></tr>
                                        <tr><td>状态</td><td><span class="badge bg-success">${{model.status}}</span></td></tr>
                                        <tr><td>创建时间</td><td>${{new Date(model.created_at).toLocaleString()}}</td></tr>
                                        <tr><td>更新时间</td><td>${{new Date(model.updated_at).toLocaleString()}}</td></tr>
                                    </table>
                                </div>
                            </div>
                        </div>
                        <div class="col-md-4">
                            <div class="card">
                                <div class="card-header">
                                    <h5 class="mb-0">性能指标</h5>
                                </div>
                                <div class="card-body">
                                    <div class="row text-center">
                                        <div class="col-6">
                                            <h4>${{model.metrics?.total_requests || 0}}</h4>
                                            <small>总请求数</small>
                                        </div>
                                        <div class="col-6">
                                            <h4>${{model.metrics?.avg_response_time || 0}}ms</h4>
                                            <small>平均响应时间</small>
                                        </div>
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>
                `;
            }}
        </script>
    "#, model_id);

    Html(base_html("模型详情", &content, &state))
}

/// 获取模型列表API
pub async fn get_models_api() -> Json<Value> {
    // TODO: 从数据库获取模型列表
    let models = json!([
        {
            "id": "model_1",
            "name": "BERT Base",
            "version": "1.0.0",
            "model_type": "nlp",
            "framework": "pytorch",
            "status": "active",
            "description": "BERT基础模型用于文本分类",
            "created_at": "2024-01-01T00:00:00Z",
            "updated_at": "2024-01-01T00:00:00Z",
            "metrics": {
                "total_requests": 1000,
                "avg_response_time": 150
            }
        }
    ]);
    
    Json(models)
}

/// 创建模型API
pub async fn create_model_api() -> Json<Value> {
    // TODO: 实现模型创建逻辑
    Json(json!({"success": true, "message": "模型创建成功"}))
}

/// 获取单个模型API
pub async fn get_model_api(Path(model_id): Path<String>) -> Json<Value> {
    // TODO: 从数据库获取模型详情
    let model = json!({
        "id": model_id,
        "name": "BERT Base",
        "version": "1.0.0",
        "model_type": "nlp",
        "framework": "pytorch",
        "device": "cpu",
        "status": "active",
        "description": "BERT基础模型用于文本分类",
        "created_at": "2024-01-01T00:00:00Z",
        "updated_at": "2024-01-01T00:00:00Z",
        "metrics": {
            "total_requests": 1000,
            "avg_response_time": 150
        }
    });
    
    Json(model)
}

/// 更新模型API
pub async fn update_model_api(Path(model_id): Path<String>) -> Json<Value> {
    // TODO: 实现模型更新逻辑
    Json(json!({"success": true, "message": "模型更新成功"}))
}

/// 删除模型API
pub async fn delete_model_api(Path(model_id): Path<String>) -> Json<Value> {
    // TODO: 实现模型删除逻辑
    Json(json!({"success": true, "message": "模型删除成功"}))
}
