//! 可视化支持
//! 
//! 本模块提供了数据可视化的基础功能，包括图表生成、数据导出等。
//! 使用Rust的类型安全特性确保可视化数据的正确性。

//use std::collections::HashMap;
//use std::fmt;

/// 图表类型
#[derive(Debug, Clone)]
pub enum ChartType {
    /// 折线图
    Line,
    /// 柱状图
    Bar,
    /// 散点图
    Scatter,
    /// 饼图
    Pie,
    /// 直方图
    Histogram,
    /// 热力图
    Heatmap,
}

/// 图表数据点
#[derive(Debug, Clone)]
pub struct DataPoint {
    /// X坐标
    pub x: f64,
    /// Y坐标
    pub y: f64,
    /// 标签（可选）
    pub label: Option<String>,
    /// 颜色（可选）
    pub color: Option<String>,
}

/// 图表数据集
#[derive(Debug, Clone)]
pub struct Dataset {
    /// 数据集名称
    pub name: String,
    /// 数据点
    pub data: Vec<DataPoint>,
    /// 颜色
    pub color: String,
    /// 是否显示线条
    pub show_line: bool,
    /// 是否显示点
    pub show_points: bool,
}

/// 图表配置
#[derive(Debug, Clone)]
pub struct ChartConfig {
    /// 图表标题
    pub title: String,
    /// X轴标签
    pub x_label: String,
    /// Y轴标签
    pub y_label: String,
    /// 图表宽度
    pub width: u32,
    /// 图表高度
    pub height: u32,
    /// 是否显示网格
    pub show_grid: bool,
    /// 是否显示图例
    pub show_legend: bool,
}

impl Default for ChartConfig {
    fn default() -> Self {
        Self {
            title: "Chart".to_string(),
            x_label: "X".to_string(),
            y_label: "Y".to_string(),
            width: 800,
            height: 600,
            show_grid: true,
            show_legend: true,
        }
    }
}

/// 图表
#[derive(Debug, Clone)]
pub struct Chart {
    /// 图表类型
    pub chart_type: ChartType,
    /// 图表配置
    pub config: ChartConfig,
    /// 数据集
    pub datasets: Vec<Dataset>,
}

impl Chart {
    /// 创建新图表
    pub fn new(chart_type: ChartType, config: ChartConfig) -> Self {
        Self {
            chart_type,
            config,
            datasets: Vec::new(),
        }
    }

    /// 添加数据集
    pub fn add_dataset(&mut self, dataset: Dataset) {
        self.datasets.push(dataset);
    }

    /// 生成SVG格式的图表
    pub fn to_svg(&self) -> String {
        let mut svg = String::new();
        
        // SVG头部
        svg.push_str(&format!(
            r#"<svg width="{}" height="{}" xmlns="http://www.w3.org/2000/svg">"#,
            self.config.width, self.config.height
        ));
        
        // 背景
        svg.push_str(r#"<rect width="100%" height="100%" fill="white"/>"#);
        
        // 标题
        svg.push_str(&format!(
            r#"<text x="{}" y="30" text-anchor="middle" font-size="16" font-weight="bold">{}</text>"#,
            self.config.width / 2, self.config.title
        ));
        
        // 计算绘图区域
        let margin = 80;
        let plot_width = self.config.width - 2 * margin;
        let plot_height = self.config.height - 2 * margin;
        let plot_x = margin;
        let plot_y = margin;
        
        // 绘制网格
        if self.config.show_grid {
            self.draw_grid(&mut svg, plot_x, plot_y, plot_width, plot_height);
        }
        
        // 绘制数据
        self.draw_data(&mut svg, plot_x, plot_y, plot_width, plot_height);
        
        // 绘制坐标轴
        self.draw_axes(&mut svg, plot_x, plot_y, plot_width, plot_height);
        
        // 绘制图例
        if self.config.show_legend {
            self.draw_legend(&mut svg);
        }
        
        svg.push_str("</svg>");
        svg
    }

    /// 绘制网格
    fn draw_grid(&self, svg: &mut String, x: u32, y: u32, width: u32, height: u32) {
        let grid_color = "#e0e0e0";
        
        // 垂直网格线
        for i in 0..=10 {
            let grid_x = x + (i * width / 10);
            svg.push_str(&format!(
                r#"<line x1="{}" y1="{}" x2="{}" y2="{}" stroke="{}" stroke-width="1"/>"#,
                grid_x, y, grid_x, y + height, grid_color
            ));
        }
        
        // 水平网格线
        for i in 0..=10 {
            let grid_y = y + (i * height / 10);
            svg.push_str(&format!(
                r#"<line x1="{}" y1="{}" x2="{}" y2="{}" stroke="{}" stroke-width="1"/>"#,
                x, grid_y, x + width, grid_y, grid_color
            ));
        }
    }

    /// 绘制数据
    fn draw_data(&self, svg: &mut String, x: u32, y: u32, width: u32, height: u32) {
        for dataset in &self.datasets {
            if dataset.data.is_empty() {
                continue;
            }
            
            // 计算数据范围
            let x_min = dataset.data.iter().map(|p| p.x).fold(f64::INFINITY, f64::min);
            let x_max = dataset.data.iter().map(|p| p.x).fold(f64::NEG_INFINITY, f64::max);
            let y_min = dataset.data.iter().map(|p| p.y).fold(f64::INFINITY, f64::min);
            let y_max = dataset.data.iter().map(|p| p.y).fold(f64::NEG_INFINITY, f64::max);
            
            let x_range = x_max - x_min;
            let y_range = y_max - y_min;
            
            if x_range == 0.0 || y_range == 0.0 {
                continue;
            }
            
            // 绘制线条
            if dataset.show_line && dataset.data.len() > 1 {
                let mut path = String::new();
                for (i, point) in dataset.data.iter().enumerate() {
                    let svg_x = x as f64 + ((point.x - x_min) / x_range) * width as f64;
                    let svg_y = (y + height) as f64 - ((point.y - y_min) / y_range) * height as f64;
                    
                    if i == 0 {
                        path.push_str(&format!("M {} {}", svg_x, svg_y));
                    } else {
                        path.push_str(&format!(" L {} {}", svg_x, svg_y));
                    }
                }
                
                svg.push_str(&format!(
                    r#"<path d="{}" stroke="{}" stroke-width="2" fill="none"/>"#,
                    path, dataset.color
                ));
            }
            
            // 绘制点
            if dataset.show_points {
                for point in &dataset.data {
                    let svg_x = x as f64 + ((point.x - x_min) / x_range) * width as f64;
                    let svg_y = (y + height) as f64 - ((point.y - y_min) / y_range) * height as f64;
                    
                    svg.push_str(&format!(
                        r#"<circle cx="{}" cy="{}" r="3" fill="{}"/>"#,
                        svg_x, svg_y, dataset.color
                    ));
                }
            }
        }
    }

    /// 绘制坐标轴
    fn draw_axes(&self, svg: &mut String, x: u32, y: u32, width: u32, height: u32) {
        // X轴
        svg.push_str(&format!(
            r#"<line x1="{}" y1="{}" x2="{}" y2="{}" stroke="black" stroke-width="2"/>"#,
            x, y + height, x + width, y + height
        ));
        
        // Y轴
        svg.push_str(&format!(
            r#"<line x1="{}" y1="{}" x2="{}" y2="{}" stroke="black" stroke-width="2"/>"#,
            x, y, x, y + height
        ));
        
        // X轴标签
        svg.push_str(&format!(
            r#"<text x="{}" y="{}" text-anchor="middle" font-size="12">{}</text>"#,
            x + width / 2, y + height + 30, self.config.x_label
        ));
        
        // Y轴标签
        svg.push_str(&format!(
            r#"<text x="{}" y="{}" text-anchor="middle" font-size="12" transform="rotate(-90, {}, {})">{}</text>"#,
            20, y + height / 2, 20, y + height / 2, self.config.y_label
        ));
    }

    /// 绘制图例
    fn draw_legend(&self, svg: &mut String) {
        let legend_x = self.config.width - 150;
        let legend_y = 50;
        
        for (i, dataset) in self.datasets.iter().enumerate() {
            let y_pos = legend_y + i as u32 * 25;
            
            // 图例颜色块
            svg.push_str(&format!(
                r#"<rect x="{}" y="{}" width="15" height="15" fill="{}"/>"#,
                legend_x, y_pos, dataset.color
            ));
            
            // 图例文本
            svg.push_str(&format!(
                r#"<text x="{}" y="{}" font-size="12">{}</text>"#,
                legend_x + 20, y_pos + 12, dataset.name
            ));
        }
    }

    /// 导出为CSV格式
    pub fn to_csv(&self) -> String {
        let mut csv = String::new();
        
        // CSV头部
        csv.push_str("Dataset,X,Y,Label\n");
        
        // 数据行
        for dataset in &self.datasets {
            for point in &dataset.data {
                csv.push_str(&format!(
                    "{},{},{},{}\n",
                    dataset.name,
                    point.x,
                    point.y,
                    point.label.as_deref().unwrap_or("")
                ));
            }
        }
        
        csv
    }

    /// 导出为JSON格式
    pub fn to_json(&self) -> String {
        // 简化实现：手动构建JSON
        let mut json = String::from("{\n");
        json.push_str(&format!("  \"title\": \"{}\",\n", self.config.title));
        json.push_str(&format!("  \"x_label\": \"{}\",\n", self.config.x_label));
        json.push_str(&format!("  \"y_label\": \"{}\",\n", self.config.y_label));
        json.push_str(&format!("  \"width\": {},\n", self.config.width));
        json.push_str(&format!("  \"height\": {},\n", self.config.height));
        json.push_str("  \"datasets\": [\n");
        
        for (i, dataset) in self.datasets.iter().enumerate() {
            json.push_str("    {\n");
            json.push_str(&format!("      \"name\": \"{}\",\n", dataset.name));
            json.push_str(&format!("      \"color\": \"{}\",\n", dataset.color));
            json.push_str(&format!("      \"data_points\": {}\n", dataset.data.len()));
            json.push_str("    }");
            if i < self.datasets.len() - 1 {
                json.push(',');
            }
            json.push('\n');
        }
        
        json.push_str("  ]\n");
        json.push('}');
        json
    }
}

/// 图表构建器
pub struct ChartBuilder {
    chart: Chart,
}

impl ChartBuilder {
    /// 创建新的图表构建器
    pub fn new(chart_type: ChartType) -> Self {
        Self {
            chart: Chart::new(chart_type, ChartConfig::default()),
        }
    }

    /// 设置标题
    pub fn title(mut self, title: &str) -> Self {
        self.chart.config.title = title.to_string();
        self
    }

    /// 设置X轴标签
    pub fn x_label(mut self, label: &str) -> Self {
        self.chart.config.x_label = label.to_string();
        self
    }

    /// 设置Y轴标签
    pub fn y_label(mut self, label: &str) -> Self {
        self.chart.config.y_label = label.to_string();
        self
    }

    /// 设置尺寸
    pub fn size(mut self, width: u32, height: u32) -> Self {
        self.chart.config.width = width;
        self.chart.config.height = height;
        self
    }

    /// 添加数据集
    pub fn add_dataset(mut self, name: &str, data: Vec<(f64, f64)>, color: &str) -> Self {
        let dataset = Dataset {
            name: name.to_string(),
            data: data.into_iter()
                .map(|(x, y)| DataPoint { x, y, label: None, color: None })
                .collect(),
            color: color.to_string(),
            show_line: true,
            show_points: true,
        };
        self.chart.add_dataset(dataset);
        self
    }

    /// 构建图表
    pub fn build(self) -> Chart {
        self.chart
    }
}

/// 数据可视化工具
pub struct VisualizationUtils;

impl VisualizationUtils {
    /// 创建折线图
    pub fn create_line_chart(title: &str, x_label: &str, y_label: &str) -> ChartBuilder {
        ChartBuilder::new(ChartType::Line)
            .title(title)
            .x_label(x_label)
            .y_label(y_label)
    }

    /// 创建柱状图
    pub fn create_bar_chart(title: &str, x_label: &str, y_label: &str) -> ChartBuilder {
        ChartBuilder::new(ChartType::Bar)
            .title(title)
            .x_label(x_label)
            .y_label(y_label)
    }

    /// 创建散点图
    pub fn create_scatter_plot(title: &str, x_label: &str, y_label: &str) -> ChartBuilder {
        ChartBuilder::new(ChartType::Scatter)
            .title(title)
            .x_label(x_label)
            .y_label(y_label)
    }

    /// 创建直方图
    pub fn create_histogram(title: &str, x_label: &str, y_label: &str) -> ChartBuilder {
        ChartBuilder::new(ChartType::Histogram)
            .title(title)
            .x_label(x_label)
            .y_label(y_label)
    }

    /// 生成性能对比图
    pub fn create_performance_comparison(
        algorithms: &[String],
        metrics: &[String],
        data: &[Vec<f64>]
    ) -> Chart {
        let mut chart = Chart::new(
            ChartType::Bar,
            ChartConfig {
                title: "性能对比".to_string(),
                x_label: "算法".to_string(),
                y_label: "性能指标".to_string(),
                width: 800,
                height: 600,
                show_grid: true,
                show_legend: true,
            }
        );

        let colors = vec!["#FF6B6B", "#4ECDC4", "#45B7D1", "#96CEB4", "#FFEAA7"];
        
        for (i, metric) in metrics.iter().enumerate() {
            let color = colors[i % colors.len()];
            let mut dataset_data = Vec::new();
            
            for (j, _algorithm) in algorithms.iter().enumerate() {
                if j < data.len() && i < data[j].len() {
                    dataset_data.push((j as f64, data[j][i]));
                }
            }
            
            let dataset = Dataset {
                name: metric.clone(),
                data: dataset_data.into_iter()
                    .map(|(x, y)| DataPoint { x, y, label: None, color: None })
                    .collect(),
                color: color.to_string(),
                show_line: false,
                show_points: true,
            };
            
            chart.add_dataset(dataset);
        }
        
        chart
    }

    /// 生成趋势图
    pub fn create_trend_chart(
        title: &str,
        time_series: &[f64],
        values: &[f64]
    ) -> Chart {
        let mut chart = Chart::new(
            ChartType::Line,
            ChartConfig {
                title: title.to_string(),
                x_label: "时间".to_string(),
                y_label: "值".to_string(),
                width: 800,
                height: 600,
                show_grid: true,
                show_legend: true,
            }
        );

        let dataset = Dataset {
            name: "趋势".to_string(),
            data: time_series.iter().zip(values.iter())
                .map(|(&x, &y)| DataPoint { x, y, label: None, color: None })
                .collect(),
            color: "#4ECDC4".to_string(),
            show_line: true,
            show_points: true,
        };
        
        chart.add_dataset(dataset);
        chart
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chart_creation() {
        let chart = ChartBuilder::new(ChartType::Line)
            .title("测试图表")
            .x_label("X轴")
            .y_label("Y轴")
            .add_dataset("数据集1", vec![(1.0, 2.0), (2.0, 4.0), (3.0, 6.0)], "#FF6B6B")
            .build();
        
        assert_eq!(chart.config.title, "测试图表");
        assert_eq!(chart.datasets.len(), 1);
    }

    #[test]
    fn test_svg_generation() {
        let chart = ChartBuilder::new(ChartType::Line)
            .title("测试图表")
            .add_dataset("数据集1", vec![(1.0, 2.0), (2.0, 4.0)], "#FF6B6B")
            .build();
        
        let svg = chart.to_svg();
        assert!(svg.contains("<svg"));
        assert!(svg.contains("测试图表"));
    }

    #[test]
    fn test_csv_export() {
        let chart = ChartBuilder::new(ChartType::Line)
            .add_dataset("数据集1", vec![(1.0, 2.0), (2.0, 4.0)], "#FF6B6B")
            .build();
        
        let csv = chart.to_csv();
        assert!(csv.contains("Dataset,X,Y,Label"));
        assert!(csv.contains("数据集1,1,2,"));
    }

    #[test]
    fn test_visualization_utils() {
        let chart = VisualizationUtils::create_line_chart("测试", "X", "Y")
            .add_dataset("数据", vec![(1.0, 2.0)], "#FF6B6B")
            .build();
        
        assert_eq!(chart.config.title, "测试");
        assert_eq!(chart.config.x_label, "X");
        assert_eq!(chart.config.y_label, "Y");
    }
}
