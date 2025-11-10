# 🦀 性能监控配置


## 📊 目录

- [🦀 性能监控配置](#-性能监控配置)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [🎯 性能监控概述](#-性能监控概述)
    - [监控目标](#监控目标)
  - [📊 指标监控](#-指标监控)
    - [Prometheus性能指标](#prometheus性能指标)
    - [性能指标收集](#性能指标收集)
  - [🔍 性能分析](#-性能分析)
    - [性能分析工具](#性能分析工具)
    - [性能分析脚本](#性能分析脚本)
  - [📈 基准测试](#-基准测试)
    - [基准测试配置](#基准测试配置)
    - [基准测试脚本](#基准测试脚本)
  - [🚨 性能告警](#-性能告警)
    - [性能告警规则](#性能告警规则)
    - [性能告警脚本](#性能告警脚本)
  - [📝 最佳实践](#-最佳实践)
    - [性能监控原则](#性能监控原则)
    - [监控检查清单](#监控检查清单)
    - [维护建议](#维护建议)


**创建时间**: 2025年9月25日
**版本**: 1.0.0

---

## 📋 目录

- [🦀 性能监控配置](#-性能监控配置)
  - [� 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [🎯 性能监控概述](#-性能监控概述)
    - [监控目标](#监控目标)
  - [📊 指标监控](#-指标监控)
    - [Prometheus性能指标](#prometheus性能指标)
    - [性能指标收集](#性能指标收集)
  - [🔍 性能分析](#-性能分析)
    - [性能分析工具](#性能分析工具)
    - [性能分析脚本](#性能分析脚本)
  - [📈 基准测试](#-基准测试)
    - [基准测试配置](#基准测试配置)
    - [基准测试脚本](#基准测试脚本)
  - [🚨 性能告警](#-性能告警)
    - [性能告警规则](#性能告警规则)
    - [性能告警脚本](#性能告警脚本)
  - [📝 最佳实践](#-最佳实践)
    - [性能监控原则](#性能监控原则)
    - [监控检查清单](#监控检查清单)
    - [维护建议](#维护建议)

---

## 🎯 性能监控概述

### 监控目标

1. **系统性能**: 监控系统整体性能
2. **应用性能**: 监控应用程序性能
3. **资源使用**: 监控资源使用情况
4. **性能趋势**: 分析性能变化趋势

---

## 📊 指标监控

### Prometheus性能指标

```yaml
# monitoring/performance.yml
global:
  scrape_interval: 15s

scrape_configs:
  - job_name: 'rust-app-performance'
    static_configs:
      - targets: ['localhost:8080']
    metrics_path: '/metrics'
    scrape_interval: 5s

  - job_name: 'system-performance'
    static_configs:
      - targets: ['localhost:9100']
```

### 性能指标收集

```rust
// src/metrics.rs
use prometheus::{Counter, Histogram, Gauge, Registry, Encoder, TextEncoder};
use std::time::Instant;

lazy_static! {
    // 请求指标
    static ref HTTP_REQUESTS_TOTAL: Counter = Counter::new(
        "http_requests_total",
        "Total number of HTTP requests"
    ).unwrap();

    static ref HTTP_REQUEST_DURATION: Histogram = Histogram::new(
        "http_request_duration_seconds",
        "HTTP request duration in seconds"
    ).unwrap();

    // 内存指标
    static ref MEMORY_USAGE_BYTES: Gauge = Gauge::new(
        "memory_usage_bytes",
        "Current memory usage in bytes"
    ).unwrap();

    static ref HEAP_SIZE_BYTES: Gauge = Gauge::new(
        "heap_size_bytes",
        "Current heap size in bytes"
    ).unwrap();

    // CPU指标
    static ref CPU_USAGE_PERCENT: Gauge = Gauge::new(
        "cpu_usage_percent",
        "Current CPU usage percentage"
    ).unwrap();

    // 并发指标
    static ref ACTIVE_CONNECTIONS: Gauge = Gauge::new(
        "active_connections",
        "Number of active connections"
    ).unwrap();

    static ref CONCURRENT_REQUESTS: Gauge = Gauge::new(
        "concurrent_requests",
        "Number of concurrent requests"
    ).unwrap();
}

pub struct PerformanceMetrics {
    registry: Registry,
    request_timer: Histogram,
    memory_profiler: MemoryProfiler,
}

impl PerformanceMetrics {
    pub fn new() -> Self {
        let registry = Registry::new();

        // 注册指标
        registry.register(Box::new(HTTP_REQUESTS_TOTAL.clone())).unwrap();
        registry.register(Box::new(HTTP_REQUEST_DURATION.clone())).unwrap();
        registry.register(Box::new(MEMORY_USAGE_BYTES.clone())).unwrap();
        registry.register(Box::new(HEAP_SIZE_BYTES.clone())).unwrap();
        registry.register(Box::new(CPU_USAGE_PERCENT.clone())).unwrap();
        registry.register(Box::new(ACTIVE_CONNECTIONS.clone())).unwrap();
        registry.register(Box::new(CONCURRENT_REQUESTS.clone())).unwrap();

        let request_timer = Histogram::new(
            "request_processing_time_seconds",
            "Request processing time in seconds"
        ).unwrap();

        registry.register(Box::new(request_timer.clone())).unwrap();

        Self {
            registry,
            request_timer,
            memory_profiler: MemoryProfiler::new(),
        }
    }

    pub fn record_request(&self, duration: f64) {
        HTTP_REQUESTS_TOTAL.inc();
        HTTP_REQUEST_DURATION.observe(duration);
    }

    pub fn update_memory_usage(&self) {
        let usage = self.memory_profiler.current_usage();
        MEMORY_USAGE_BYTES.set(usage as f64);

        let heap_size = self.memory_profiler.heap_size();
        HEAP_SIZE_BYTES.set(heap_size as f64);
    }

    pub fn update_cpu_usage(&self, usage: f64) {
        CPU_USAGE_PERCENT.set(usage);
    }

    pub fn update_connections(&self, count: i64) {
        ACTIVE_CONNECTIONS.set(count);
    }

    pub fn update_concurrent_requests(&self, count: i64) {
        CONCURRENT_REQUESTS.set(count);
    }

    pub fn get_metrics(&self) -> String {
        let mut buffer = Vec::new();
        let encoder = TextEncoder::new();
        let metric_families = self.registry.gather();
        encoder.encode(&metric_families, &mut buffer).unwrap();
        String::from_utf8(buffer).unwrap()
    }
}

// 内存分析器
struct MemoryProfiler {
    allocated: std::sync::atomic::AtomicUsize,
    peak_allocated: std::sync::atomic::AtomicUsize,
}

impl MemoryProfiler {
    fn new() -> Self {
        Self {
            allocated: std::sync::atomic::AtomicUsize::new(0),
            peak_allocated: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    fn current_usage(&self) -> usize {
        self.allocated.load(std::sync::atomic::Ordering::SeqCst)
    }

    fn heap_size(&self) -> usize {
        // 简化的堆大小计算
        self.peak_allocated.load(std::sync::atomic::Ordering::SeqCst)
    }
}
```

---

## 🔍 性能分析

### 性能分析工具

```bash
#!/bin/bash
# scripts/performance-analysis.sh

set -e

echo "Starting performance analysis..."

# 安装性能分析工具
install_profiling_tools() {
    echo "Installing profiling tools..."

    # 安装perf工具
    if ! command -v perf &> /dev/null; then
        echo "Installing perf..."
        sudo apt-get update
        sudo apt-get install -y linux-tools-common linux-tools-generic
    fi

    # 安装flamegraph工具
    if ! command -v flamegraph &> /dev/null; then
        echo "Installing flamegraph..."
        cargo install flamegraph
    fi

    echo "Profiling tools installed"
}

# CPU性能分析
analyze_cpu_performance() {
    echo "Analyzing CPU performance..."

    # 使用perf进行CPU分析
    if command -v perf &> /dev/null; then
        perf record -g -- sleep 10
        perf report --stdio > reports/performance/cpu-analysis.txt

        # 生成火焰图
        perf script | flamegraph > reports/performance/cpu-flamegraph.svg
    fi

    echo "CPU performance analysis completed"
}

# 内存性能分析
analyze_memory_performance() {
    echo "Analyzing memory performance..."

    # 使用valgrind进行内存分析
    if command -v valgrind &> /dev/null; then
        valgrind --tool=massif --massif-out-file=reports/performance/memory-massif.out \
            --heap=yes --stacks=yes ./target/release/my-app &

        sleep 30
        kill %1

        # 生成内存报告
        ms_print reports/performance/memory-massif.out > reports/performance/memory-analysis.txt
    fi

    echo "Memory performance analysis completed"
}

# 缓存性能分析
analyze_cache_performance() {
    echo "Analyzing cache performance..."

    # 使用perf进行缓存分析
    if command -v perf &> /dev/null; then
        perf stat -e cache-references,cache-misses,L1-dcache-loads,L1-dcache-load-misses \
            -e L1-icache-loads,L1-icache-load-misses,LLC-loads,LLC-load-misses \
            ./target/release/my-app > reports/performance/cache-analysis.txt 2>&1
    fi

    echo "Cache performance analysis completed"
}

# 主函数
main() {
    install_profiling_tools
    analyze_cpu_performance
    analyze_memory_performance
    analyze_cache_performance

    echo "Performance analysis completed!"
}

main "$@"
```

### 性能分析脚本

```rust
// src/performance_analysis.rs
use std::time::{Duration, Instant};
use std::collections::HashMap;

// 性能分析器
pub struct PerformanceAnalyzer {
    measurements: HashMap<String, Vec<Duration>>,
    start_times: HashMap<String, Instant>,
}

impl PerformanceAnalyzer {
    pub fn new() -> Self {
        Self {
            measurements: HashMap::new(),
            start_times: HashMap::new(),
        }
    }

    pub fn start_timer(&mut self, name: &str) {
        self.start_times.insert(name.to_string(), Instant::now());
    }

    pub fn stop_timer(&mut self, name: &str) -> Duration {
        if let Some(start_time) = self.start_times.remove(name) {
            let duration = start_time.elapsed();
            self.measurements.entry(name.to_string())
                .or_insert_with(Vec::new)
                .push(duration);
            duration
        } else {
            Duration::from_nanos(0)
        }
    }

    pub fn get_statistics(&self, name: &str) -> Option<PerformanceStats> {
        self.measurements.get(name).map(|measurements| {
            let mut durations = measurements.clone();
            durations.sort();

            let min = durations[0];
            let max = durations[durations.len() - 1];
            let avg = durations.iter().sum::<Duration>() / durations.len() as u32;
            let median = durations[durations.len() / 2];

            PerformanceStats {
                min,
                max,
                avg,
                median,
                count: durations.len(),
            }
        })
    }

    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("Performance Analysis Report\n");
        report.push_str("==========================\n\n");

        for (name, measurements) in &self.measurements {
            if let Some(stats) = self.get_statistics(name) {
                report.push_str(&format!("{}:\n", name));
                report.push_str(&format!("  Count: {}\n", stats.count));
                report.push_str(&format!("  Min: {:?}\n", stats.min));
                report.push_str(&format!("  Max: {:?}\n", stats.max));
                report.push_str(&format!("  Avg: {:?}\n", stats.avg));
                report.push_str(&format!("  Median: {:?}\n", stats.median));
                report.push_str("\n");
            }
        }

        report
    }
}

#[derive(Debug, Clone)]
pub struct PerformanceStats {
    pub min: Duration,
    pub max: Duration,
    pub avg: Duration,
    pub median: Duration,
    pub count: usize,
}

// 性能分析宏
#[macro_export]
macro_rules! profile_function {
    ($analyzer:expr, $name:expr, $code:block) => {{
        $analyzer.start_timer($name);
        let result = $code;
        $analyzer.stop_timer($name);
        result
    }};
}

#[macro_export]
macro_rules! profile_async_function {
    ($analyzer:expr, $name:expr, $future:expr) => {{
        $analyzer.start_timer($name);
        let result = $future.await;
        $analyzer.stop_timer($name);
        result
    }};
}
```

---

## 📈 基准测试

### 基准测试配置

```toml
# Cargo.toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }
tokio = { version = "1.0", features = ["full"] }

[[bench]]
name = "performance_benchmarks"
harness = false
```

### 基准测试脚本

```bash
#!/bin/bash
# scripts/run-benchmarks.sh

set -e

echo "Running performance benchmarks..."

# 运行基准测试
run_benchmarks() {
    echo "Running Criterion benchmarks..."

    cargo bench --bench performance_benchmarks

    # 生成HTML报告
    if [ -d "target/criterion" ]; then
        cp -r target/criterion reports/performance/
        echo "Benchmark reports saved to reports/performance/criterion/"
    fi
}

# 运行自定义基准测试
run_custom_benchmarks() {
    echo "Running custom benchmarks..."

    # 内存分配基准测试
    echo "Testing memory allocation performance..."
    cargo run --release --bin memory_benchmark > reports/performance/memory-benchmark.txt 2>&1

    # 并发性能基准测试
    echo "Testing concurrent performance..."
    cargo run --release --bin concurrent_benchmark > reports/performance/concurrent-benchmark.txt 2>&1

    # 算法性能基准测试
    echo "Testing algorithm performance..."
    cargo run --release --bin algorithm_benchmark > reports/performance/algorithm-benchmark.txt 2>&1
}

# 生成基准测试报告
generate_benchmark_report() {
    echo "Generating benchmark report..."

    cat > reports/performance/benchmark-summary.md << EOF
# 基准测试报告

**生成时间**: $(date)
**项目**: $(basename $(pwd))

## 测试概述

本报告包含了项目的全面性能基准测试结果。

## Criterion基准测试

\`\`\`
$(find reports/performance/criterion -name "*.html" | head -5)
\`\`\`

## 自定义基准测试

### 内存分配性能

\`\`\`
$(head -20 reports/performance/memory-benchmark.txt)
\`\`\`

### 并发性能

\`\`\`
$(head -20 reports/performance/concurrent-benchmark.txt)
\`\`\`

### 算法性能

\`\`\`
$(head -20 reports/performance/algorithm-benchmark.txt)
\`\`\`

## 建议

基于基准测试结果，建议：

1. 优化内存分配策略
2. 改进并发处理性能
3. 优化算法实现
4. 定期运行基准测试

EOF

    echo "Benchmark report generated"
}

# 主函数
main() {
    run_benchmarks
    run_custom_benchmarks
    generate_benchmark_report

    echo "Benchmark testing completed!"
}

main "$@"
```

---

## 🚨 性能告警

### 性能告警规则

```yaml
# monitoring/performance-alerts.yml
groups:
  - name: performance_alerts
    rules:
      - alert: HighResponseTime
        expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 1.0
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High response time detected"
          description: "95th percentile response time is {{ $value }}s"

      - alert: HighMemoryUsage
        expr: memory_usage_bytes / (1024 * 1024 * 1024) > 1.0
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High memory usage detected"
          description: "Memory usage is {{ $value }}GB"

      - alert: HighCPUUsage
        expr: cpu_usage_percent > 80
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High CPU usage detected"
          description: "CPU usage is {{ $value }}%"

      - alert: TooManyConnections
        expr: active_connections > 1000
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Too many active connections"
          description: "Active connections: {{ $value }}"
```

### 性能告警脚本

```bash
#!/bin/bash
# scripts/performance-alerts.sh

set -e

echo "Setting up performance alerts..."

# 配置告警规则
setup_alert_rules() {
    echo "Setting up alert rules..."

    # 复制告警规则到Prometheus配置目录
    if [ -f "monitoring/performance-alerts.yml" ]; then
        cp monitoring/performance-alerts.yml /etc/prometheus/rules/
        echo "Alert rules configured"
    fi
}

# 启动告警管理器
start_alertmanager() {
    echo "Starting Alertmanager..."

    docker run -d \
        --name alertmanager \
        -p 9093:9093 \
        -v $(pwd)/monitoring/alertmanager.yml:/etc/alertmanager/alertmanager.yml \
        prom/alertmanager

    echo "Alertmanager started"
}

# 配置告警通知
configure_alert_notifications() {
    echo "Configuring alert notifications..."

    cat > monitoring/alertmanager.yml << EOF
global:
  smtp_smarthost: 'localhost:587'
  smtp_from: 'alerts@example.com'

route:
  group_by: ['alertname']
  group_wait: 10s
  group_interval: 10s
  repeat_interval: 1h
  receiver: 'performance-alerts'

receivers:
  - name: 'performance-alerts'
    email_configs:
      - to: 'admin@example.com'
        subject: 'Performance Alert: {{ .GroupLabels.alertname }}'
        body: |
          {{ range .Alerts }}
          Alert: {{ .Annotations.summary }}
          Description: {{ .Annotations.description }}
          {{ end }}
EOF

    echo "Alert notifications configured"
}

# 主函数
main() {
    setup_alert_rules
    start_alertmanager
    configure_alert_notifications

    echo "Performance alerts setup completed!"
}

main "$@"
```

---

## 📝 最佳实践

### 性能监控原则

1. **全面监控**: 监控所有关键性能指标
2. **实时监控**: 提供实时性能数据
3. **趋势分析**: 分析性能变化趋势
4. **告警及时**: 及时发出性能告警

### 监控检查清单

- [ ] 系统性能指标监控
- [ ] 应用性能指标监控
- [ ] 资源使用监控
- [ ] 性能分析工具配置
- [ ] 基准测试覆盖
- [ ] 性能告警配置
- [ ] 监控数据存储
- [ ] 性能报告生成

### 维护建议

1. **定期监控**: 定期检查监控系统
2. **优化配置**: 优化监控配置
3. **更新规则**: 更新告警规则
4. **备份数据**: 备份监控数据
5. **团队培训**: 培训团队使用监控系统

---

-**遵循这些性能监控配置，您将能够建立全面、有效的性能监控体系！🦀**-
