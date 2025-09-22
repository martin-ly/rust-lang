# WebAssembly 云原生项目

## 项目概述

WebAssembly 在云原生环境中的应用，包括容器化、微服务、服务网格等场景。

## 核心特性

### 1. 容器化支持

- 轻量级容器镜像
- 快速启动时间
- 低资源消耗

### 2. 微服务架构

- 服务发现与注册
- 负载均衡
- 熔断与限流

### 3. 服务网格集成

- Istio 集成
- Envoy 代理
- 流量管理

## 技术栈

### 运行时

- **wasmtime**: 高性能 WebAssembly 运行时
- **wasmcloud**: 云原生 WebAssembly 平台
- **Krustlet**: Kubernetes WebAssembly 节点

### 容器化

- **Docker**: 容器化部署
- **containerd**: 容器运行时
- **CRI-O**: Kubernetes 容器运行时

### 编排

- **Kubernetes**: 容器编排
- **Helm**: 包管理
- **Operator**: 自定义控制器

## 实现示例

### 1. WebAssembly 微服务

```rust
use wasm_bindgen::prelude::*;
use serde::{Serialize, Deserialize};

/// WebAssembly 微服务示例
#[wasm_bindgen]
pub struct Microservice {
    service_name: String,
    version: String,
    endpoints: Vec<Endpoint>,
    health_status: HealthStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Endpoint {
    pub path: String,
    pub method: String,
    pub handler: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Degraded,
}

#[wasm_bindgen]
impl Microservice {
    #[wasm_bindgen(constructor)]
    pub fn new(name: &str, version: &str) -> Microservice {
        Microservice {
            service_name: name.to_string(),
            version: version.to_string(),
            endpoints: Vec::new(),
            health_status: HealthStatus::Healthy,
        }
    }
    
    /// 添加端点
    #[wasm_bindgen]
    pub fn add_endpoint(&mut self, path: &str, method: &str, handler: &str) {
        self.endpoints.push(Endpoint {
            path: path.to_string(),
            method: method.to_string(),
            handler: handler.to_string(),
        });
    }
    
    /// 处理请求
    #[wasm_bindgen]
    pub fn handle_request(&self, path: &str, method: &str, body: &str) -> Result<JsValue, JsValue> {
        let endpoint = self.endpoints.iter()
            .find(|ep| ep.path == path && ep.method == method);
        
        match endpoint {
            Some(ep) => {
                let response = ServiceResponse {
                    status: 200,
                    body: format!("Handler: {}, Body: {}", ep.handler, body),
                    headers: std::collections::HashMap::new(),
                };
                Ok(JsValue::from_serde(&response).unwrap())
            }
            None => {
                let response = ServiceResponse {
                    status: 404,
                    body: "Not Found".to_string(),
                    headers: std::collections::HashMap::new(),
                };
                Ok(JsValue::from_serde(&response).unwrap())
            }
        }
    }
    
    /// 健康检查
    #[wasm_bindgen]
    pub fn health_check(&self) -> JsValue {
        JsValue::from_serde(&self.health_status).unwrap()
    }
    
    /// 获取服务信息
    #[wasm_bindgen]
    pub fn get_service_info(&self) -> JsValue {
        let info = ServiceInfo {
            name: self.service_name.clone(),
            version: self.version.clone(),
            endpoint_count: self.endpoints.len(),
            status: self.health_status.clone(),
        };
        JsValue::from_serde(&info).unwrap()
    }
}

#[derive(Serialize, Deserialize)]
struct ServiceResponse {
    status: u16,
    body: String,
    headers: std::collections::HashMap<String, String>,
}

#[derive(Serialize, Deserialize)]
struct ServiceInfo {
    name: String,
    version: String,
    endpoint_count: usize,
    status: HealthStatus,
}
```

### 2. 服务发现与注册

```rust
use wasm_bindgen::prelude::*;
use std::collections::HashMap;

/// 服务注册中心
#[wasm_bindgen]
pub struct ServiceRegistry {
    services: HashMap<String, ServiceInstance>,
    health_checker: HealthChecker,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub name: String,
    pub address: String,
    pub port: u16,
    pub version: String,
    pub tags: Vec<String>,
    pub health_status: HealthStatus,
    pub last_heartbeat: u64,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

#[wasm_bindgen]
impl ServiceRegistry {
    #[wasm_bindgen(constructor)]
    pub fn new() -> ServiceRegistry {
        ServiceRegistry {
            services: HashMap::new(),
            health_checker: HealthChecker::new(),
        }
    }
    
    /// 注册服务
    #[wasm_bindgen]
    pub fn register_service(&mut self, instance: JsValue) -> Result<(), JsValue> {
        let service_instance: ServiceInstance = instance.into_serde()
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        
        self.services.insert(service_instance.id.clone(), service_instance);
        Ok(())
    }
    
    /// 注销服务
    #[wasm_bindgen]
    pub fn deregister_service(&mut self, service_id: &str) -> Result<(), JsValue> {
        self.services.remove(service_id);
        Ok(())
    }
    
    /// 发现服务
    #[wasm_bindgen]
    pub fn discover_service(&self, service_name: &str) -> Result<JsValue, JsValue> {
        let instances: Vec<&ServiceInstance> = self.services.values()
            .filter(|instance| instance.name == service_name && instance.health_status == HealthStatus::Healthy)
            .collect();
        
        Ok(JsValue::from_serde(&instances).unwrap())
    }
    
    /// 健康检查
    #[wasm_bindgen]
    pub fn health_check(&mut self, service_id: &str) -> Result<JsValue, JsValue> {
        if let Some(instance) = self.services.get_mut(service_id) {
            let health_status = self.health_checker.check_health(instance);
            instance.health_status = health_status.clone();
            instance.last_heartbeat = js_sys::Date::now() as u64;
            
            Ok(JsValue::from_serde(&health_status).unwrap())
        } else {
            Err(JsValue::from_str("Service not found"))
        }
    }
    
    /// 获取所有服务
    #[wasm_bindgen]
    pub fn get_all_services(&self) -> JsValue {
        JsValue::from_serde(&self.services).unwrap()
    }
}

struct HealthChecker;

impl HealthChecker {
    fn new() -> Self {
        Self
    }
    
    fn check_health(&self, instance: &ServiceInstance) -> HealthStatus {
        // 模拟健康检查逻辑
        // 在实际应用中，这里会发送HTTP请求到服务的健康检查端点
        if instance.last_heartbeat > 0 {
            let current_time = js_sys::Date::now() as u64;
            if current_time - instance.last_heartbeat < 30000 { // 30秒超时
                HealthStatus::Healthy
            } else {
                HealthStatus::Unhealthy
            }
        } else {
            HealthStatus::Unknown
        }
    }
}
```

### 3. 负载均衡器

```rust
use wasm_bindgen::prelude::*;
use std::collections::HashMap;

/// 负载均衡器
#[wasm_bindgen]
pub struct LoadBalancer {
    services: HashMap<String, Vec<ServiceInstance>>,
    algorithms: HashMap<String, LoadBalanceAlgorithm>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub address: String,
    pub port: u16,
    pub weight: u32,
    pub current_connections: u32,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum LoadBalanceAlgorithm {
    RoundRobin,
    WeightedRoundRobin,
    LeastConnections,
    Random,
}

#[wasm_bindgen]
impl LoadBalancer {
    #[wasm_bindgen(constructor)]
    pub fn new() -> LoadBalancer {
        LoadBalancer {
            services: HashMap::new(),
            algorithms: HashMap::new(),
        }
    }
    
    /// 添加服务实例
    #[wasm_bindgen]
    pub fn add_service_instance(&mut self, service_name: &str, instance: JsValue) -> Result<(), JsValue> {
        let service_instance: ServiceInstance = instance.into_serde()
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        
        self.services.entry(service_name.to_string())
            .or_insert_with(Vec::new)
            .push(service_instance);
        
        Ok(())
    }
    
    /// 设置负载均衡算法
    #[wasm_bindgen]
    pub fn set_algorithm(&mut self, service_name: &str, algorithm: JsValue) -> Result<(), JsValue> {
        let algo: LoadBalanceAlgorithm = algorithm.into_serde()
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        
        self.algorithms.insert(service_name.to_string(), algo);
        Ok(())
    }
    
    /// 选择服务实例
    #[wasm_bindgen]
    pub fn select_instance(&mut self, service_name: &str) -> Result<JsValue, JsValue> {
        if let Some(instances) = self.services.get_mut(service_name) {
            if instances.is_empty() {
                return Err(JsValue::from_str("No instances available"));
            }
            
            let algorithm = self.algorithms.get(service_name)
                .cloned()
                .unwrap_or(LoadBalanceAlgorithm::RoundRobin);
            
            let selected_instance = match algorithm {
                LoadBalanceAlgorithm::RoundRobin => self.round_robin(instances),
                LoadBalanceAlgorithm::WeightedRoundRobin => self.weighted_round_robin(instances),
                LoadBalanceAlgorithm::LeastConnections => self.least_connections(instances),
                LoadBalanceAlgorithm::Random => self.random(instances),
            };
            
            // 增加连接数
            if let Some(instance) = instances.get_mut(selected_instance) {
                instance.current_connections += 1;
            }
            
            Ok(JsValue::from_serde(&instances[selected_instance]).unwrap())
        } else {
            Err(JsValue::from_str("Service not found"))
        }
    }
    
    /// 释放连接
    #[wasm_bindgen]
    pub fn release_connection(&mut self, service_name: &str, instance_id: &str) -> Result<(), JsValue> {
        if let Some(instances) = self.services.get_mut(service_name) {
            if let Some(instance) = instances.iter_mut().find(|i| i.id == instance_id) {
                if instance.current_connections > 0 {
                    instance.current_connections -= 1;
                }
            }
        }
        Ok(())
    }
    
    fn round_robin(&self, instances: &[ServiceInstance]) -> usize {
        // 简单的轮询算法
        js_sys::Math::random() as usize % instances.len()
    }
    
    fn weighted_round_robin(&self, instances: &[ServiceInstance]) -> usize {
        let total_weight: u32 = instances.iter().map(|i| i.weight).sum();
        let random_weight = (js_sys::Math::random() * total_weight as f64) as u32;
        
        let mut current_weight = 0;
        for (index, instance) in instances.iter().enumerate() {
            current_weight += instance.weight;
            if random_weight <= current_weight {
                return index;
            }
        }
        
        0
    }
    
    fn least_connections(&self, instances: &[ServiceInstance]) -> usize {
        instances.iter()
            .enumerate()
            .min_by_key(|(_, instance)| instance.current_connections)
            .map(|(index, _)| index)
            .unwrap_or(0)
    }
    
    fn random(&self, instances: &[ServiceInstance]) -> usize {
        (js_sys::Math::random() * instances.len() as f64) as usize
    }
}
```

## 部署配置

### 1. Dockerfile

```dockerfile
# 多阶段构建
FROM rust:1.90 as builder

WORKDIR /app
COPY . .

# 安装 wasm-pack
RUN curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 构建 WebAssembly 模块
RUN wasm-pack build --target web --release

# 运行时镜像
FROM nginx:alpine

# 复制 WebAssembly 文件
COPY --from=builder /app/pkg/*.wasm /usr/share/nginx/html/
COPY --from=builder /app/pkg/*.js /usr/share/nginx/html/

# 配置 nginx
COPY nginx.conf /etc/nginx/nginx.conf

EXPOSE 80

CMD ["nginx", "-g", "daemon off;"]
```

### 2. Kubernetes 部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: wasm-microservice
  labels:
    app: wasm-microservice
spec:
  replicas: 3
  selector:
    matchLabels:
      app: wasm-microservice
  template:
    metadata:
      labels:
        app: wasm-microservice
    spec:
      containers:
      - name: wasm-microservice
        image: wasm-microservice:latest
        ports:
        - containerPort: 80
        resources:
          requests:
            memory: "64Mi"
            cpu: "100m"
          limits:
            memory: "128Mi"
            cpu: "200m"
        livenessProbe:
          httpGet:
            path: /health
            port: 80
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 80
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: wasm-microservice-service
spec:
  selector:
    app: wasm-microservice
  ports:
  - protocol: TCP
    port: 80
    targetPort: 80
  type: ClusterIP
```

### 3. Helm Chart

```yaml
# values.yaml
replicaCount: 3

image:
  repository: wasm-microservice
  tag: latest
  pullPolicy: IfNotPresent

service:
  type: ClusterIP
  port: 80

resources:
  limits:
    cpu: 200m
    memory: 128Mi
  requests:
    cpu: 100m
    memory: 64Mi

autoscaling:
  enabled: false
  minReplicas: 1
  maxReplicas: 100
  targetCPUUtilizationPercentage: 80

ingress:
  enabled: false
  annotations: {}
  hosts:
    - host: wasm-microservice.local
      paths: ["/"]
  tls: []
```

## 监控与观测

### 1. 指标收集

```rust
use wasm_bindgen::prelude::*;
use std::collections::HashMap;

/// 指标收集器
#[wasm_bindgen]
pub struct MetricsCollector {
    counters: HashMap<String, u64>,
    gauges: HashMap<String, f64>,
    histograms: HashMap<String, Vec<f64>>,
}

#[wasm_bindgen]
impl MetricsCollector {
    #[wasm_bindgen(constructor)]
    pub fn new() -> MetricsCollector {
        MetricsCollector {
            counters: HashMap::new(),
            gauges: HashMap::new(),
            histograms: HashMap::new(),
        }
    }
    
    /// 增加计数器
    #[wasm_bindgen]
    pub fn increment_counter(&mut self, name: &str, value: u64) {
        *self.counters.entry(name.to_string()).or_insert(0) += value;
    }
    
    /// 设置仪表盘值
    #[wasm_bindgen]
    pub fn set_gauge(&mut self, name: &str, value: f64) {
        self.gauges.insert(name.to_string(), value);
    }
    
    /// 记录直方图值
    #[wasm_bindgen]
    pub fn record_histogram(&mut self, name: &str, value: f64) {
        self.histograms.entry(name.to_string())
            .or_insert_with(Vec::new)
            .push(value);
    }
    
    /// 获取所有指标
    #[wasm_bindgen]
    pub fn get_metrics(&self) -> JsValue {
        let metrics = Metrics {
            counters: self.counters.clone(),
            gauges: self.gauges.clone(),
            histograms: self.histograms.clone(),
        };
        JsValue::from_serde(&metrics).unwrap()
    }
}

#[derive(serde::Serialize)]
struct Metrics {
    counters: HashMap<String, u64>,
    gauges: HashMap<String, f64>,
    histograms: HashMap<String, Vec<f64>>,
}
```

### 2. 日志记录

```rust
use wasm_bindgen::prelude::*;
use serde::{Serialize, Deserialize};

/// 日志记录器
#[wasm_bindgen]
pub struct Logger {
    logs: Vec<LogEntry>,
    max_logs: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub timestamp: u64,
    pub level: LogLevel,
    pub message: String,
    pub fields: std::collections::HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

#[wasm_bindgen]
impl Logger {
    #[wasm_bindgen(constructor)]
    pub fn new(max_logs: usize) -> Logger {
        Logger {
            logs: Vec::new(),
            max_logs,
        }
    }
    
    /// 记录日志
    #[wasm_bindgen]
    pub fn log(&mut self, level: JsValue, message: &str, fields: JsValue) -> Result<(), JsValue> {
        let log_level: LogLevel = level.into_serde()
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        
        let log_fields: std::collections::HashMap<String, String> = fields.into_serde()
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        
        let entry = LogEntry {
            timestamp: js_sys::Date::now() as u64,
            level: log_level,
            message: message.to_string(),
            fields: log_fields,
        };
        
        self.logs.push(entry);
        
        // 限制日志数量
        if self.logs.len() > self.max_logs {
            self.logs.remove(0);
        }
        
        Ok(())
    }
    
    /// 获取日志
    #[wasm_bindgen]
    pub fn get_logs(&self) -> JsValue {
        JsValue::from_serde(&self.logs).unwrap()
    }
    
    /// 清空日志
    #[wasm_bindgen]
    pub fn clear_logs(&mut self) {
        self.logs.clear();
    }
}
```

## 最佳实践

### 1. 资源管理

- 合理设置内存限制
- 监控CPU使用率
- 优化启动时间

### 2. 安全考虑

- 使用安全沙箱
- 限制系统调用
- 实施访问控制

### 3. 性能优化

- 使用SIMD指令
- 优化内存访问
- 减少函数调用开销

### 4. 可观测性

- 收集关键指标
- 记录结构化日志
- 实施分布式追踪

## 总结

WebAssembly 在云原生环境中的应用提供了轻量级、高性能的解决方案。通过合理的设计和实现，可以构建可扩展、可维护的云原生应用。
