//! 监控仪表板
//! 
//! 提供监控数据的可视化和仪表板功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use uuid::Uuid;
use chrono::{DateTime, Utc};

use super::collector::{MonitoringCollector, SystemHealth, PerformanceMetrics, MonitoringStats};
use super::metrics::Metric;
use super::logging::LogEntry;
use super::collector::{MonitoringEvent, Alert};

/// 监控仪表板
#[derive(Debug)]
pub struct MonitoringDashboard {
    collector: Arc<MonitoringCollector>,
    widgets: Arc<RwLock<HashMap<String, DashboardWidget>>>,
    layouts: Arc<RwLock<HashMap<String, DashboardLayout>>>,
    config: DashboardConfig,
}

/// 仪表板配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardConfig {
    pub refresh_interval: std::time::Duration,
    pub max_widgets: usize,
    pub default_layout: String,
    pub theme: DashboardTheme,
    pub auto_refresh: bool,
}

/// 仪表板主题
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DashboardTheme {
    Light,
    Dark,
    Auto,
}

impl Default for DashboardConfig {
    fn default() -> Self {
        Self {
            refresh_interval: std::time::Duration::from_secs(30),
            max_widgets: 50,
            default_layout: "default".to_string(),
            theme: DashboardTheme::Auto,
            auto_refresh: true,
        }
    }
}

/// 仪表板小部件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardWidget {
    pub id: Uuid,
    pub name: String,
    pub widget_type: WidgetType,
    pub title: String,
    pub description: Option<String>,
    pub position: WidgetPosition,
    pub size: WidgetSize,
    pub config: WidgetConfig,
    pub data_source: String,
    pub refresh_interval: std::time::Duration,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 小部件类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WidgetType {
    MetricChart,
    LogViewer,
    EventTimeline,
    AlertList,
    SystemHealth,
    PerformanceChart,
    Custom(String),
}

/// 小部件位置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WidgetPosition {
    pub x: i32,
    pub y: i32,
    pub z: i32,
}

/// 小部件大小
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WidgetSize {
    pub width: u32,
    pub height: u32,
}

/// 小部件配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WidgetConfig {
    pub chart_type: Option<ChartType>,
    pub time_range: Option<TimeRange>,
    pub filters: HashMap<String, String>,
    pub display_options: HashMap<String, serde_json::Value>,
}

/// 图表类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ChartType {
    Line,
    Bar,
    Pie,
    Area,
    Scatter,
    Heatmap,
    Gauge,
    Table,
}

/// 时间范围
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeRange {
    pub start: DateTime<Utc>,
    pub end: DateTime<Utc>,
}

/// 仪表板布局
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardLayout {
    pub id: Uuid,
    pub name: String,
    pub description: Option<String>,
    pub widget_ids: Vec<Uuid>,
    pub grid_config: GridConfig,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 网格配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GridConfig {
    pub columns: u32,
    pub rows: u32,
    pub cell_width: u32,
    pub cell_height: u32,
    pub gap: u32,
}

/// 仪表板数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardData {
    pub widgets: Vec<WidgetData>,
    pub system_health: SystemHealth,
    pub performance_metrics: PerformanceMetrics,
    pub monitoring_stats: MonitoringStats,
    pub last_updated: DateTime<Utc>,
}

/// 小部件数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WidgetData {
    pub widget_id: Uuid,
    pub data: serde_json::Value,
    pub last_updated: DateTime<Utc>,
}

/// 预定义小部件模板
pub struct WidgetTemplates;

impl WidgetTemplates {
    /// 获取所有预定义小部件模板
    pub fn get_all() -> Vec<DashboardWidget> {
        vec![
            // 系统健康小部件
            DashboardWidget {
                id: Uuid::new_v4(),
                name: "system_health".to_string(),
                widget_type: WidgetType::SystemHealth,
                title: "系统健康状态".to_string(),
                description: Some("显示系统各组件的健康状态".to_string()),
                position: WidgetPosition { x: 0, y: 0, z: 0 },
                size: WidgetSize { width: 400, height: 300 },
                config: WidgetConfig {
                    chart_type: None,
                    time_range: None,
                    filters: HashMap::new(),
                    display_options: HashMap::new(),
                },
                data_source: "system_health".to_string(),
                refresh_interval: std::time::Duration::from_secs(30),
                created_at: Utc::now(),
                updated_at: Utc::now(),
            },

            // CPU使用率图表
            DashboardWidget {
                id: Uuid::new_v4(),
                name: "cpu_usage".to_string(),
                widget_type: WidgetType::MetricChart,
                title: "CPU使用率".to_string(),
                description: Some("显示CPU使用率趋势".to_string()),
                position: WidgetPosition { x: 400, y: 0, z: 0 },
                size: WidgetSize { width: 400, height: 300 },
                config: WidgetConfig {
                    chart_type: Some(ChartType::Line),
                    time_range: Some(TimeRange {
                        start: Utc::now() - chrono::Duration::hours(1),
                        end: Utc::now(),
                    }),
                    filters: HashMap::new(),
                    display_options: HashMap::new(),
                },
                data_source: "cpu_usage".to_string(),
                refresh_interval: std::time::Duration::from_secs(60),
                created_at: Utc::now(),
                updated_at: Utc::now(),
            },

            // 内存使用率图表
            DashboardWidget {
                id: Uuid::new_v4(),
                name: "memory_usage".to_string(),
                widget_type: WidgetType::MetricChart,
                title: "内存使用率".to_string(),
                description: Some("显示内存使用率趋势".to_string()),
                position: WidgetPosition { x: 0, y: 300, z: 0 },
                size: WidgetSize { width: 400, height: 300 },
                config: WidgetConfig {
                    chart_type: Some(ChartType::Area),
                    time_range: Some(TimeRange {
                        start: Utc::now() - chrono::Duration::hours(1),
                        end: Utc::now(),
                    }),
                    filters: HashMap::new(),
                    display_options: HashMap::new(),
                },
                data_source: "memory_usage".to_string(),
                refresh_interval: std::time::Duration::from_secs(60),
                created_at: Utc::now(),
                updated_at: Utc::now(),
            },

            // 告警列表
            DashboardWidget {
                id: Uuid::new_v4(),
                name: "alerts".to_string(),
                widget_type: WidgetType::AlertList,
                title: "活跃告警".to_string(),
                description: Some("显示当前活跃的告警".to_string()),
                position: WidgetPosition { x: 400, y: 300, z: 0 },
                size: WidgetSize { width: 400, height: 300 },
                config: WidgetConfig {
                    chart_type: Some(ChartType::Table),
                    time_range: None,
                    filters: HashMap::new(),
                    display_options: HashMap::new(),
                },
                data_source: "alerts".to_string(),
                refresh_interval: std::time::Duration::from_secs(30),
                created_at: Utc::now(),
                updated_at: Utc::now(),
            },

            // 日志查看器
            DashboardWidget {
                id: Uuid::new_v4(),
                name: "logs".to_string(),
                widget_type: WidgetType::LogViewer,
                title: "系统日志".to_string(),
                description: Some("显示最近的系统日志".to_string()),
                position: WidgetPosition { x: 0, y: 600, z: 0 },
                size: WidgetSize { width: 800, height: 300 },
                config: WidgetConfig {
                    chart_type: Some(ChartType::Table),
                    time_range: Some(TimeRange {
                        start: Utc::now() - chrono::Duration::hours(1),
                        end: Utc::now(),
                    }),
                    filters: HashMap::new(),
                    display_options: HashMap::new(),
                },
                data_source: "logs".to_string(),
                refresh_interval: std::time::Duration::from_secs(10),
                created_at: Utc::now(),
                updated_at: Utc::now(),
            },

            // 事件时间线
            DashboardWidget {
                id: Uuid::new_v4(),
                name: "events".to_string(),
                widget_type: WidgetType::EventTimeline,
                title: "事件时间线".to_string(),
                description: Some("显示系统事件的时间线".to_string()),
                position: WidgetPosition { x: 0, y: 900, z: 0 },
                size: WidgetSize { width: 800, height: 300 },
                config: WidgetConfig {
                    chart_type: Some(ChartType::Line),
                    time_range: Some(TimeRange {
                        start: Utc::now() - chrono::Duration::hours(24),
                        end: Utc::now(),
                    }),
                    filters: HashMap::new(),
                    display_options: HashMap::new(),
                },
                data_source: "events".to_string(),
                refresh_interval: std::time::Duration::from_secs(60),
                created_at: Utc::now(),
                updated_at: Utc::now(),
            },
        ]
    }

    /// 根据类型获取小部件模板
    pub fn get_by_type(widget_type: &WidgetType) -> Vec<DashboardWidget> {
        Self::get_all()
            .into_iter()
            .filter(|widget| std::mem::discriminant(&widget.widget_type) == std::mem::discriminant(widget_type))
            .collect()
    }
}

impl MonitoringDashboard {
    /// 创建新的监控仪表板
    pub fn new(collector: Arc<MonitoringCollector>, config: DashboardConfig) -> Self {
        Self {
            collector,
            widgets: Arc::new(RwLock::new(HashMap::new())),
            layouts: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    /// 初始化默认仪表板
    pub async fn initialize_default(&self) -> Result<()> {
        // 创建默认布局
        let default_layout = DashboardLayout {
            id: Uuid::new_v4(),
            name: "default".to_string(),
            description: Some("默认仪表板布局".to_string()),
            widget_ids: Vec::new(),
            grid_config: GridConfig {
                columns: 4,
                rows: 6,
                cell_width: 200,
                cell_height: 150,
                gap: 10,
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        {
            let mut layouts = self.layouts.write().await;
            layouts.insert("default".to_string(), default_layout);
        }

        // 添加预定义小部件
        for widget in WidgetTemplates::get_all() {
            self.add_widget(widget).await?;
        }

        Ok(())
    }

    /// 添加小部件
    pub async fn add_widget(&self, widget: DashboardWidget) -> Result<()> {
        {
            let mut widgets = self.widgets.write().await;
            if widgets.len() >= self.config.max_widgets {
                return Err(anyhow::anyhow!("Maximum number of widgets reached"));
            }
            widgets.insert(widget.id.to_string(), widget);
        }

        // 更新默认布局
        {
            let mut layouts = self.layouts.write().await;
            if let Some(layout) = layouts.get_mut("default") {
                layout.widget_ids.push(widget.id);
                layout.updated_at = Utc::now();
            }
        }

        Ok(())
    }

    /// 移除小部件
    pub async fn remove_widget(&self, widget_id: &Uuid) -> Result<()> {
        {
            let mut widgets = self.widgets.write().await;
            widgets.remove(&widget_id.to_string());
        }

        // 从所有布局中移除小部件
        {
            let mut layouts = self.layouts.write().await;
            for layout in layouts.values_mut() {
                layout.widget_ids.retain(|id| id != widget_id);
                layout.updated_at = Utc::now();
            }
        }

        Ok(())
    }

    /// 更新小部件
    pub async fn update_widget(&self, widget_id: &Uuid, updates: WidgetUpdate) -> Result<()> {
        {
            let mut widgets = self.widgets.write().await;
            if let Some(widget) = widgets.get_mut(&widget_id.to_string()) {
                if let Some(name) = updates.name {
                    widget.name = name;
                }
                if let Some(title) = updates.title {
                    widget.title = title;
                }
                if let Some(description) = updates.description {
                    widget.description = Some(description);
                }
                if let Some(position) = updates.position {
                    widget.position = position;
                }
                if let Some(size) = updates.size {
                    widget.size = size;
                }
                if let Some(config) = updates.config {
                    widget.config = config;
                }
                widget.updated_at = Utc::now();
            }
        }

        Ok(())
    }

    /// 获取小部件
    pub async fn get_widget(&self, widget_id: &Uuid) -> Option<DashboardWidget> {
        let widgets = self.widgets.read().await;
        widgets.get(&widget_id.to_string()).cloned()
    }

    /// 获取所有小部件
    pub async fn get_all_widgets(&self) -> Vec<DashboardWidget> {
        let widgets = self.widgets.read().await;
        widgets.values().cloned().collect()
    }

    /// 获取仪表板数据
    pub async fn get_dashboard_data(&self, layout_name: Option<&str>) -> Result<DashboardData> {
        let layout_name = layout_name.unwrap_or(&self.config.default_layout);
        
        // 获取布局
        let layout = {
            let layouts = self.layouts.read().await;
            layouts.get(layout_name).cloned()
        };

        let widget_ids = if let Some(layout) = layout {
            layout.widget_ids
        } else {
            // 如果没有找到布局，返回所有小部件
            let widgets = self.widgets.read().await;
            widgets.keys()
                .filter_map(|id| Uuid::parse_str(id).ok())
                .collect()
        };

        // 获取小部件数据
        let mut widget_data = Vec::new();
        for widget_id in widget_ids {
            if let Some(widget) = self.get_widget(&widget_id).await {
                let data = self.get_widget_data(&widget).await?;
                widget_data.push(WidgetData {
                    widget_id,
                    data,
                    last_updated: Utc::now(),
                });
            }
        }

        // 获取系统数据
        let system_health = self.collector.get_system_health().await;
        let performance_metrics = self.collector.get_performance_metrics().await;
        let monitoring_stats = self.collector.get_monitoring_stats().await;

        Ok(DashboardData {
            widgets: widget_data,
            system_health,
            performance_metrics,
            monitoring_stats,
            last_updated: Utc::now(),
        })
    }

    /// 获取小部件数据
    async fn get_widget_data(&self, widget: &DashboardWidget) -> Result<serde_json::Value> {
        match widget.widget_type {
            WidgetType::SystemHealth => {
                let health = self.collector.get_system_health().await;
                Ok(serde_json::to_value(health)?)
            }
            WidgetType::MetricChart => {
                let metric = self.collector.get_metric(&widget.data_source).await;
                Ok(serde_json::to_value(metric)?)
            }
            WidgetType::LogViewer => {
                let logs = self.collector.get_logs(None, Some(100)).await;
                Ok(serde_json::to_value(logs)?)
            }
            WidgetType::EventTimeline => {
                let events = self.collector.get_events(None, Some(100)).await;
                Ok(serde_json::to_value(events)?)
            }
            WidgetType::AlertList => {
                let alerts = self.collector.get_alerts(Some(super::collector::AlertStatus::Active), Some(50)).await;
                Ok(serde_json::to_value(alerts)?)
            }
            WidgetType::PerformanceChart => {
                let metrics = self.collector.get_performance_metrics().await;
                Ok(serde_json::to_value(metrics)?)
            }
            WidgetType::Custom(_) => {
                // 自定义小部件的数据获取逻辑
                Ok(serde_json::Value::Null)
            }
        }
    }

    /// 创建布局
    pub async fn create_layout(&self, name: String, description: Option<String>, widget_ids: Vec<Uuid>) -> Result<DashboardLayout> {
        let layout = DashboardLayout {
            id: Uuid::new_v4(),
            name: name.clone(),
            description,
            widget_ids,
            grid_config: GridConfig {
                columns: 4,
                rows: 6,
                cell_width: 200,
                cell_height: 150,
                gap: 10,
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        {
            let mut layouts = self.layouts.write().await;
            layouts.insert(name, layout.clone());
        }

        Ok(layout)
    }

    /// 获取布局
    pub async fn get_layout(&self, name: &str) -> Option<DashboardLayout> {
        let layouts = self.layouts.read().await;
        layouts.get(name).cloned()
    }

    /// 获取所有布局
    pub async fn get_all_layouts(&self) -> Vec<DashboardLayout> {
        let layouts = self.layouts.read().await;
        layouts.values().cloned().collect()
    }
}

/// 小部件更新
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WidgetUpdate {
    pub name: Option<String>,
    pub title: Option<String>,
    pub description: Option<String>,
    pub position: Option<WidgetPosition>,
    pub size: Option<WidgetSize>,
    pub config: Option<WidgetConfig>,
}
