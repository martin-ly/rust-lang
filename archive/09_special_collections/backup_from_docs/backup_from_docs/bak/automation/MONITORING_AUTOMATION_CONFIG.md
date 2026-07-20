# 🦀 项目监控自动化配置

**创建时间**: 2025年9月25日
**版本**: 1.0.0

---

## 📋 目录

- [🦀 项目监控自动化配置](#-项目监控自动化配置)
  - [📋 目录](#-目录)
  - [🎯 监控概述](#-监控概述)
  - [📊 指标监控](#-指标监控)
  - [🔔 告警配置](#-告警配置)
  - [📈 性能监控](#-性能监控)
  - [🔍 日志监控](#-日志监控)
  - [📝 最佳实践](#-最佳实践)

---

## 🎯 监控概述

### 监控目标

1. **系统健康**: 监控系统运行状态
2. **性能指标**: 监控性能指标
3. **错误检测**: 检测和告警错误
4. **容量规划**: 监控资源使用情况

---

## 📊 指标监控

### Prometheus配置

```yaml
# monitoring/prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - "alerts.yml"

scrape_configs:
  - job_name: 'my-app'
    static_configs:
      - targets: ['localhost:8080']
    metrics_path: '/metrics'
    scrape_interval: 5s

  - job_name: 'node-exporter'
    static_configs:
      - targets: ['localhost:9100']

  - job_name: 'cadvisor'
    static_configs:
      - targets: ['localhost:8080']
```

### 应用指标

```rust
// src/metrics.rs
use prometheus::{Counter, Histogram, Registry, Encoder, TextEncoder};

lazy_static! {
    static ref HTTP_REQUESTS_TOTAL: Counter = Counter::new(
        "http_requests_total",
        "Total number of HTTP requests"
    ).unwrap();

    static ref HTTP_REQUEST_DURATION: Histogram = Histogram::new(
        "http_request_duration_seconds",
        "HTTP request duration in seconds"
    ).unwrap();
}

pub fn init_metrics() -> Registry {
    let registry = Registry::new();
    registry.register(Box::new(HTTP_REQUESTS_TOTAL.clone())).unwrap();
    registry.register(Box::new(HTTP_REQUEST_DURATION.clone())).unwrap();
    registry
}

pub fn record_request(duration: f64) {
    HTTP_REQUESTS_TOTAL.inc();
    HTTP_REQUEST_DURATION.observe(duration);
}
```

---

## 🔔 告警配置

### 告警规则

```yaml
# monitoring/alerts.yml
groups:
  - name: my-app
    rules:
      - alert: HighErrorRate
        expr: rate(http_requests_total{status=~"5.."}[5m]) > 0.1
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value }} errors per second"

      - alert: HighMemoryUsage
        expr: (node_memory_MemTotal_bytes - node_memory_MemAvailable_bytes) / node_memory_MemTotal_bytes > 0.8
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High memory usage detected"
          description: "Memory usage is {{ $value }}%"

      - alert: HighCPUUsage
        expr: 100 - (avg by (instance) (rate(node_cpu_seconds_total{mode="idle"}[5m])) * 100) > 80
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High CPU usage detected"
          description: "CPU usage is {{ $value }}%"

      - alert: DiskSpaceLow
        expr: (node_filesystem_avail_bytes / node_filesystem_size_bytes) * 100 < 10
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Low disk space"
          description: "Disk space is {{ $value }}%"
```

### Alertmanager配置

```yaml
# monitoring/alertmanager.yml
global:
  smtp_smarthost: 'localhost:587'
  smtp_from: 'alerts@example.com'

route:
  group_by: ['alertname']
  group_wait: 10s
  group_interval: 10s
  repeat_interval: 1h
  receiver: 'web.hook'

receivers:
  - name: 'web.hook'
    webhook_configs:
      - url: 'http://localhost:5001/'

  - name: 'email'
    email_configs:
      - to: 'admin@example.com'
        subject: 'Alert: {{ .GroupLabels.alertname }}'
        body: |
          {{ range .Alerts }}
          Alert: {{ .Annotations.summary }}
          Description: {{ .Annotations.description }}
          {{ end }}
```

---

## 📈 性能监控

### 性能指标收集

```rust
// src/performance.rs
use std::time::{Duration, Instant};
use prometheus::{Counter, Histogram, Gauge};

lazy_static! {
    static ref REQUEST_COUNT: Counter = Counter::new(
        "requests_total",
        "Total number of requests"
    ).unwrap();

    static ref REQUEST_DURATION: Histogram = Histogram::new(
        "request_duration_seconds",
        "Request duration in seconds"
    ).unwrap();

    static ref ACTIVE_CONNECTIONS: Gauge = Gauge::new(
        "active_connections",
        "Number of active connections"
    ).unwrap();
}

pub fn record_request_start() -> Instant {
    REQUEST_COUNT.inc();
    Instant::now()
}

pub fn record_request_end(start: Instant) {
    let duration = start.elapsed();
    REQUEST_DURATION.observe(duration.as_secs_f64());
}

pub fn update_active_connections(count: i64) {
    ACTIVE_CONNECTIONS.set(count);
}
```

### 性能监控脚本

```bash
#!/bin/bash
# scripts/performance-monitor.sh

set -e

echo "Starting performance monitoring..."

# 启动Prometheus
start_prometheus() {
    echo "Starting Prometheus..."
    docker run -d \
        --name prometheus \
        -p 9090:9090 \
        -v $(pwd)/monitoring/prometheus.yml:/etc/prometheus/prometheus.yml \
        prom/prometheus
    echo "Prometheus started"
}

# 启动Grafana
start_grafana() {
    echo "Starting Grafana..."
    docker run -d \
        --name grafana \
        -p 3000:3000 \
        -e GF_SECURITY_ADMIN_PASSWORD=admin \
        grafana/grafana
    echo "Grafana started"
}

# 启动Node Exporter
start_node_exporter() {
    echo "Starting Node Exporter..."
    docker run -d \
        --name node-exporter \
        -p 9100:9100 \
        prom/node-exporter
    echo "Node Exporter started"
}

# 启动Alertmanager
start_alertmanager() {
    echo "Starting Alertmanager..."
    docker run -d \
        --name alertmanager \
        -p 9093:9093 \
        -v $(pwd)/monitoring/alertmanager.yml:/etc/alertmanager/alertmanager.yml \
        prom/alertmanager
    echo "Alertmanager started"
}

# 主函数
main() {
    start_prometheus
    start_grafana
    start_node_exporter
    start_alertmanager

    echo "Performance monitoring setup completed!"
}

main "$@"
```

---

## 🔍 日志监控

### 日志配置

```yaml
# monitoring/fluentd.yml
apiVersion: v1
kind: ConfigMap
metadata:
  name: fluentd-config
data:
  fluent.conf: |
    <source>
      @type tail
      path /var/log/my-app/*.log
      pos_file /var/log/fluentd/my-app.log.pos
      tag my-app
      format json
    </source>

    <match my-app>
      @type elasticsearch
      host elasticsearch.logging.svc.cluster.local
      port 9200
      index_name my-app
      type_name _doc
    </match>
```

### 日志分析脚本

```bash
#!/bin/bash
# scripts/log-analysis.sh

set -e

echo "Starting log analysis..."

# 分析错误日志
analyze_errors() {
    echo "Analyzing error logs..."

    # 统计错误数量
    error_count=$(grep -c "ERROR" /var/log/my-app/*.log)
    echo "Total errors: $error_count"

    # 分析错误类型
    echo "Error types:"
    grep "ERROR" /var/log/my-app/*.log | \
        awk '{print $4}' | sort | uniq -c | sort -nr

    echo "Error analysis completed"
}

# 分析性能日志
analyze_performance() {
    echo "Analyzing performance logs..."

    # 分析响应时间
    echo "Response time analysis:"
    grep "response_time" /var/log/my-app/*.log | \
        awk '{print $NF}' | sort -n | \
        awk '{sum+=$1; count++} END {print "Average:", sum/count}'

    echo "Performance analysis completed"
}

# 生成日志报告
generate_report() {
    echo "Generating log report..."

    cat > /tmp/log-report.txt << EOF
Log Analysis Report - $(date)
================================

Error Analysis:
$(analyze_errors)

Performance Analysis:
$(analyze_performance)

EOF

    echo "Report generated: /tmp/log-report.txt"
}

# 主函数
main() {
    analyze_errors
    analyze_performance
    generate_report

    echo "Log analysis completed!"
}

main "$@"
```

---

## 📝 最佳实践

### 监控原则

1. **全面性**: 监控所有关键指标
2. **实时性**: 提供实时监控数据
3. **准确性**: 确保监控数据准确
4. **可操作性**: 提供可操作的告警

### 监控检查清单

- [ ] 系统指标监控配置
- [ ] 应用指标监控配置
- [ ] 告警规则配置
- [ ] 性能监控配置
- [ ] 日志监控配置
- [ ] 监控数据存储
- [ ] 告警通知配置
- [ ] 监控仪表板配置

### 维护建议

1. **定期检查**: 定期检查监控系统
2. **优化配置**: 优化监控配置
3. **更新规则**: 更新告警规则
4. **备份数据**: 备份监控数据
5. **培训团队**: 培训团队使用监控系统

---

-**遵循这些监控自动化配置，您将能够建立全面、有效的项目监控体系！🦀**-
