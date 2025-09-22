//! 仪表板页面
//! 
//! 提供系统概览和关键指标展示

use super::{base_html, WebUIState};
use axum::{
    extract::State,
    response::Html,
};
use serde_json::json;

/// 仪表板主页面
pub async fn dashboard_page(State(state): State<WebUIState>) -> Html<String> {
    let content = r#"
        <div class="row">
            <div class="col-xl-3 col-md-6 mb-4">
                <div class="card border-left-primary shadow h-100 py-2">
                    <div class="card-body">
                        <div class="row no-gutters align-items-center">
                            <div class="col mr-2">
                                <div class="text-xs font-weight-bold text-primary text-uppercase mb-1">
                                    活跃模型
                                </div>
                                <div class="h5 mb-0 font-weight-bold text-gray-800" id="active-models">
                                    加载中...
                                </div>
                            </div>
                            <div class="col-auto">
                                <i class="bi bi-diagram-3 fa-2x text-gray-300"></i>
                            </div>
                        </div>
                    </div>
                </div>
            </div>

            <div class="col-xl-3 col-md-6 mb-4">
                <div class="card border-left-success shadow h-100 py-2">
                    <div class="card-body">
                        <div class="row no-gutters align-items-center">
                            <div class="col mr-2">
                                <div class="text-xs font-weight-bold text-success text-uppercase mb-1">
                                    今日推理请求
                                </div>
                                <div class="h5 mb-0 font-weight-bold text-gray-800" id="today-inferences">
                                    加载中...
                                </div>
                            </div>
                            <div class="col-auto">
                                <i class="bi bi-lightning-charge fa-2x text-gray-300"></i>
                            </div>
                        </div>
                    </div>
                </div>
            </div>

            <div class="col-xl-3 col-md-6 mb-4">
                <div class="card border-left-info shadow h-100 py-2">
                    <div class="card-body">
                        <div class="row no-gutters align-items-center">
                            <div class="col mr-2">
                                <div class="text-xs font-weight-bold text-info text-uppercase mb-1">
                                    系统状态
                                </div>
                                <div class="h5 mb-0 font-weight-bold text-gray-800" id="system-status">
                                    加载中...
                                </div>
                            </div>
                            <div class="col-auto">
                                <i class="bi bi-heart-pulse fa-2x text-gray-300"></i>
                            </div>
                        </div>
                    </div>
                </div>
            </div>

            <div class="col-xl-3 col-md-6 mb-4">
                <div class="card border-left-warning shadow h-100 py-2">
                    <div class="card-body">
                        <div class="row no-gutters align-items-center">
                            <div class="col mr-2">
                                <div class="text-xs font-weight-bold text-warning text-uppercase mb-1">
                                    活跃用户
                                </div>
                                <div class="h5 mb-0 font-weight-bold text-gray-800" id="active-users">
                                    加载中...
                                </div>
                            </div>
                            <div class="col-auto">
                                <i class="bi bi-people fa-2x text-gray-300"></i>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        </div>

        <div class="row">
            <div class="col-lg-8">
                <div class="card shadow mb-4">
                    <div class="card-header py-3 d-flex flex-row align-items-center justify-content-between">
                        <h6 class="m-0 font-weight-bold text-primary">推理请求趋势</h6>
                        <div class="dropdown no-arrow">
                            <a class="dropdown-toggle" href="#" role="button" id="dropdownMenuLink" data-bs-toggle="dropdown">
                                <i class="bi bi-three-dots-vertical fa-sm fa-fw text-gray-400"></i>
                            </a>
                            <div class="dropdown-menu dropdown-menu-right shadow">
                                <a class="dropdown-item" href="#" onclick="refreshChart()">刷新图表</a>
                                <a class="dropdown-item" href="#" onclick="exportChart()">导出数据</a>
                            </div>
                        </div>
                    </div>
                    <div class="card-body">
                        <div class="chart-area">
                            <canvas id="inferenceChart"></canvas>
                        </div>
                    </div>
                </div>
            </div>

            <div class="col-lg-4">
                <div class="card shadow mb-4">
                    <div class="card-header py-3 d-flex flex-row align-items-center justify-content-between">
                        <h6 class="m-0 font-weight-bold text-primary">系统资源使用率</h6>
                    </div>
                    <div class="card-body">
                        <div class="mb-3">
                            <div class="d-flex justify-content-between">
                                <span>CPU使用率</span>
                                <span id="cpu-usage">0%</span>
                            </div>
                            <div class="progress">
                                <div class="progress-bar" role="progressbar" id="cpu-progress" style="width: 0%"></div>
                            </div>
                        </div>
                        <div class="mb-3">
                            <div class="d-flex justify-content-between">
                                <span>内存使用率</span>
                                <span id="memory-usage">0%</span>
                            </div>
                            <div class="progress">
                                <div class="progress-bar bg-success" role="progressbar" id="memory-progress" style="width: 0%"></div>
                            </div>
                        </div>
                        <div class="mb-3">
                            <div class="d-flex justify-content-between">
                                <span>磁盘使用率</span>
                                <span id="disk-usage">0%</span>
                            </div>
                            <div class="progress">
                                <div class="progress-bar bg-warning" role="progressbar" id="disk-progress" style="width: 0%"></div>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        </div>

        <div class="row">
            <div class="col-lg-6">
                <div class="card shadow mb-4">
                    <div class="card-header py-3">
                        <h6 class="m-0 font-weight-bold text-primary">最近活动</h6>
                    </div>
                    <div class="card-body">
                        <div class="list-group" id="recent-activities">
                            <div class="list-group-item">
                                <div class="d-flex w-100 justify-content-between">
                                    <h6 class="mb-1">系统启动</h6>
                                    <small>刚刚</small>
                                </div>
                                <p class="mb-1">c19_ai 系统已成功启动</p>
                            </div>
                        </div>
                    </div>
                </div>
            </div>

            <div class="col-lg-6">
                <div class="card shadow mb-4">
                    <div class="card-header py-3">
                        <h6 class="m-0 font-weight-bold text-primary">模型性能排行</h6>
                    </div>
                    <div class="card-body">
                        <div class="table-responsive">
                            <table class="table table-sm">
                                <thead>
                                    <tr>
                                        <th>模型名称</th>
                                        <th>请求数</th>
                                        <th>平均响应时间</th>
                                        <th>成功率</th>
                                    </tr>
                                </thead>
                                <tbody id="model-performance">
                                    <tr>
                                        <td colspan="4" class="text-center">加载中...</td>
                                    </tr>
                                </tbody>
                            </table>
                        </div>
                    </div>
                </div>
            </div>
        </div>

        <script>
            // 初始化仪表板
            document.addEventListener('DOMContentLoaded', function() {
                loadDashboardData();
                initializeCharts();
                startAutoRefresh();
            });

            // 加载仪表板数据
            async function loadDashboardData() {
                try {
                    // 加载统计数据
                    const statsResponse = await fetch('/api/monitor/stats');
                    const stats = await statsResponse.json();
                    
                    document.getElementById('active-models').textContent = stats.active_models || 0;
                    document.getElementById('today-inferences').textContent = stats.today_inferences || 0;
                    document.getElementById('system-status').textContent = stats.system_status || '未知';
                    document.getElementById('active-users').textContent = stats.active_users || 0;

                    // 加载系统资源使用率
                    const resourcesResponse = await fetch('/api/monitor/resources');
                    const resources = await resourcesResponse.json();
                    
                    updateResourceUsage('cpu', resources.cpu_usage || 0);
                    updateResourceUsage('memory', resources.memory_usage || 0);
                    updateResourceUsage('disk', resources.disk_usage || 0);

                    // 加载模型性能数据
                    const performanceResponse = await fetch('/api/monitor/performance');
                    const performance = await performanceResponse.json();
                    updateModelPerformance(performance);

                } catch (error) {
                    console.error('加载仪表板数据失败:', error);
                }
            }

            // 更新资源使用率
            function updateResourceUsage(type, usage) {
                const percentage = Math.round(usage * 100);
                document.getElementById(`${type}-usage`).textContent = `${percentage}%`;
                const progressBar = document.getElementById(`${type}-progress`);
                progressBar.style.width = `${percentage}%`;
                
                // 根据使用率设置颜色
                progressBar.className = 'progress-bar';
                if (percentage > 80) {
                    progressBar.classList.add('bg-danger');
                } else if (percentage > 60) {
                    progressBar.classList.add('bg-warning');
                } else {
                    progressBar.classList.add('bg-success');
                }
            }

            // 更新模型性能表格
            function updateModelPerformance(performance) {
                const tbody = document.getElementById('model-performance');
                if (!performance || performance.length === 0) {
                    tbody.innerHTML = '<tr><td colspan="4" class="text-center">暂无数据</td></tr>';
                    return;
                }

                tbody.innerHTML = performance.map(model => `
                    <tr>
                        <td>${model.name}</td>
                        <td>${model.request_count}</td>
                        <td>${model.avg_response_time}ms</td>
                        <td>
                            <span class="badge ${model.success_rate > 95 ? 'bg-success' : model.success_rate > 90 ? 'bg-warning' : 'bg-danger'}">
                                ${model.success_rate}%
                            </span>
                        </td>
                    </tr>
                `).join('');
            }

            // 初始化图表
            function initializeCharts() {
                const ctx = document.getElementById('inferenceChart').getContext('2d');
                window.inferenceChart = new Chart(ctx, {
                    type: 'line',
                    data: {
                        labels: [],
                        datasets: [{
                            label: '推理请求数',
                            data: [],
                            borderColor: 'rgb(75, 192, 192)',
                            backgroundColor: 'rgba(75, 192, 192, 0.2)',
                            tension: 0.1
                        }]
                    },
                    options: {
                        responsive: true,
                        scales: {
                            y: {
                                beginAtZero: true
                            }
                        }
                    }
                });

                loadChartData();
            }

            // 加载图表数据
            async function loadChartData() {
                try {
                    const response = await fetch('/api/monitor/inference-trend');
                    const data = await response.json();
                    
                    window.inferenceChart.data.labels = data.labels;
                    window.inferenceChart.data.datasets[0].data = data.values;
                    window.inferenceChart.update();
                } catch (error) {
                    console.error('加载图表数据失败:', error);
                }
            }

            // 自动刷新
            function startAutoRefresh() {
                setInterval(() => {
                    loadDashboardData();
                    loadChartData();
                }, 30000); // 每30秒刷新一次
            }

            // 刷新图表
            function refreshChart() {
                loadChartData();
            }

            // 导出图表
            function exportChart() {
                const link = document.createElement('a');
                link.download = 'inference-trend.png';
                link.href = window.inferenceChart.toBase64Image();
                link.click();
            }
        </script>
    "#;

    Html(base_html("仪表板", content, &state))
}
