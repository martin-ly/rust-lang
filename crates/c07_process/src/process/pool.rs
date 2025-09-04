use crate::types::{ProcessConfig, ProcessInfo, ProcessStatus};
use crate::error::{ProcessResult, ProcessError};
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime};
use std::thread;

/// 进程池配置
#[derive(Debug, Clone)]
pub struct ProcessPoolConfig {
    /// 最小进程数量
    pub min_processes: usize,
    /// 最大进程数量
    pub max_processes: usize,
    /// 初始进程数量
    pub initial_processes: usize,
    /// 进程空闲超时时间
    pub idle_timeout: Duration,
    /// 健康检查间隔
    pub health_check_interval: Duration,
    /// 负载均衡策略
    pub load_balancing_strategy: LoadBalancingStrategy,
    /// 自动扩展策略
    pub auto_scaling: AutoScalingConfig,
}

/// 负载均衡策略
#[derive(Debug, Clone)]
pub enum LoadBalancingStrategy {
    /// 轮询
    RoundRobin,
    /// 最少连接
    LeastConnections,
    /// 加权轮询
    WeightedRoundRobin(Vec<f64>),
    /// 随机
    Random,
}

/// 自动扩展配置
#[derive(Debug, Clone)]
pub struct AutoScalingConfig {
    /// 启用自动扩展
    pub enabled: bool,
    /// CPU使用率阈值
    pub cpu_threshold: f64,
    /// 内存使用率阈值
    pub memory_threshold: f64,
    /// 扩展检查间隔
    pub check_interval: Duration,
    /// 扩展冷却时间
    pub cooldown_period: Duration,
}

/// 进程池
pub struct ProcessPool {
    config: ProcessPoolConfig,
    processes: Arc<Mutex<HashMap<u32, PooledProcess>>>,
    available_processes: Arc<Mutex<VecDeque<u32>>>,
    busy_processes: Arc<Mutex<HashMap<u32, SystemTime>>>,
    next_process_id: Arc<Mutex<u32>>,
    last_scale_check: Arc<Mutex<SystemTime>>,
    base_config: ProcessConfig,
}

/// 池化进程
struct PooledProcess {
    info: ProcessInfo,
    created_at: SystemTime,
    last_used: SystemTime,
    total_requests: u64,
    current_requests: u32,
    health_status: HealthStatus,
}

/// 进程健康状态
#[derive(Debug, Clone, PartialEq)]
enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

impl ProcessPool {
    /// 创建新的进程池
    pub fn new(config: ProcessPoolConfig, base_config: ProcessConfig) -> ProcessResult<Self> {
        let pool = Self {
            config,
            processes: Arc::new(Mutex::new(HashMap::new())),
            available_processes: Arc::new(Mutex::new(VecDeque::new())),
            busy_processes: Arc::new(Mutex::new(HashMap::new())),
            next_process_id: Arc::new(Mutex::new(1000)),
            last_scale_check: Arc::new(Mutex::new(SystemTime::now())),
            base_config,
        };
        
        // 初始化进程池
        pool.initialize_pool()?;
        
        Ok(pool)
    }
    
    /// 初始化进程池
    fn initialize_pool(&self) -> ProcessResult<()> {
        for _ in 0..self.config.initial_processes {
            self.spawn_process()?;
        }
        Ok(())
    }
    
    /// 生成新的进程ID
    fn generate_process_id(&self) -> u32 {
        let mut next_id = self.next_process_id.lock().unwrap();
        *next_id += 1;
        *next_id
    }
    
    /// 生成新进程
    fn spawn_process(&self) -> ProcessResult<u32> {
        let mut config = self.base_config.clone();
        let pid = self.generate_process_id();
        
        // 这里应该实际启动进程，简化实现
        let info = ProcessInfo {
            pid,
            name: config.program.clone(),
            status: ProcessStatus::Running,
            memory_usage: 0,
            cpu_usage: 0.0,
            created_at: SystemTime::now(),
            parent_pid: None,
            children_pids: Vec::new(),
        };
        
        let pooled_process = PooledProcess {
            info,
            created_at: SystemTime::now(),
            last_used: SystemTime::now(),
            total_requests: 0,
            current_requests: 0,
            health_status: HealthStatus::Healthy,
        };
        
        // 添加到进程池
        self.processes.lock().unwrap().insert(pid, pooled_process);
        self.available_processes.lock().unwrap().push_back(pid);
        
        Ok(pid)
    }
    
    /// 获取可用进程
    pub fn get_process(&self) -> ProcessResult<u32> {
        // 检查是否需要自动扩展
        self.check_auto_scaling()?;
        
        let mut available = self.available_processes.lock().unwrap();
        
        if let Some(pid) = available.pop_front() {
            // 标记进程为忙碌状态
            self.busy_processes.lock().unwrap().insert(pid, SystemTime::now());
            
            // 更新进程使用统计
            if let Some(process) = self.processes.lock().unwrap().get_mut(&pid) {
                process.current_requests += 1;
                process.total_requests += 1;
                process.last_used = SystemTime::now();
            }
            
            Ok(pid)
        } else {
            // 没有可用进程，尝试创建新进程
            if self.can_spawn_more_processes() {
                let new_pid = self.spawn_process()?;
                self.busy_processes.lock().unwrap().insert(new_pid, SystemTime::now());
                Ok(new_pid)
            } else {
                Err(ProcessError::ResourceExhausted("No available processes in pool".to_string()))
            }
        }
    }
    
    /// 释放进程回池
    pub fn release_process(&self, pid: u32) -> ProcessResult<()> {
        // 从忙碌状态移除
        self.busy_processes.lock().unwrap().remove(&pid);
        
        // 更新进程状态
        if let Some(process) = self.processes.lock().unwrap().get_mut(&pid) {
            process.current_requests = process.current_requests.saturating_sub(1);
        }
        
        // 检查进程是否仍然健康
        if self.is_process_healthy(pid)? {
            // 重新加入可用队列
            self.available_processes.lock().unwrap().push_back(pid);
        } else {
            // 标记为不健康，稍后清理
            self.mark_process_unhealthy(pid)?;
        }
        
        Ok(())
    }
    
    /// 检查进程健康状态
    fn is_process_healthy(&self, pid: u32) -> ProcessResult<bool> {
        // 简化实现，实际应该检查进程是否响应
        let processes = self.processes.lock().unwrap();
        if let Some(process) = processes.get(&pid) {
            Ok(process.health_status == HealthStatus::Healthy)
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }
    
    /// 标记进程为不健康
    fn mark_process_unhealthy(&self, pid: u32) -> ProcessResult<()> {
        if let Some(process) = self.processes.lock().unwrap().get_mut(&pid) {
            process.health_status = HealthStatus::Unhealthy;
        }
        Ok(())
    }
    
    /// 检查是否可以生成更多进程
    fn can_spawn_more_processes(&self) -> bool {
        let current_count = self.processes.lock().unwrap().len();
        current_count < self.config.max_processes
    }
    
    /// 检查自动扩展
    fn check_auto_scaling(&self) -> ProcessResult<()> {
        if !self.config.auto_scaling.enabled {
            return Ok(());
        }
        
        let mut last_check = self.last_scale_check.lock().unwrap();
        let now = SystemTime::now();
        
        if now.duration_since(*last_check).unwrap_or(Duration::ZERO) < self.config.auto_scaling.check_interval {
            return Ok(());
        }
        
        *last_check = now;
        
        // 获取系统资源使用情况
        let cpu_usage = self.get_average_cpu_usage();
        let memory_usage = self.get_average_memory_usage();
        
        // 检查是否需要扩展
        if cpu_usage > self.config.auto_scaling.cpu_threshold 
            || memory_usage > self.config.auto_scaling.memory_threshold {
            self.scale_up()?;
        } else if cpu_usage < self.config.auto_scaling.cpu_threshold * 0.5 
            && memory_usage < self.config.auto_scaling.memory_threshold * 0.5 {
            self.scale_down()?;
        }
        
        Ok(())
    }
    
    /// 扩展进程池
    fn scale_up(&self) -> ProcessResult<()> {
        let current_count = self.processes.lock().unwrap().len();
        if current_count < self.config.max_processes {
            self.spawn_process()?;
        }
        Ok(())
    }
    
    /// 收缩进程池
    fn scale_down(&self) -> ProcessResult<()> {
        let current_count = self.processes.lock().unwrap().len();
        if current_count > self.config.min_processes {
            // 移除最不活跃的进程
            self.remove_least_active_process()?;
        }
        Ok(())
    }
    
    /// 移除最不活跃的进程
    fn remove_least_active_process(&self) -> ProcessResult<()> {
        let mut processes = self.processes.lock().unwrap();
        let mut available = self.available_processes.lock().unwrap();
        
        if let Some((&pid, _)) = processes.iter()
            .filter(|(pid, _)| available.contains(pid))
            .min_by_key(|(_, process)| process.last_used) {
            
            processes.remove(&pid);
            available.retain(|&p| p != pid);
        }
        
        Ok(())
    }
    
    /// 获取平均CPU使用率
    fn get_average_cpu_usage(&self) -> f64 {
        let processes = self.processes.lock().unwrap();
        if processes.is_empty() {
            return 0.0;
        }
        
        let total: f64 = processes.values().map(|p| p.info.cpu_usage).sum();
        total / processes.len() as f64
    }
    
    /// 获取平均内存使用率
    fn get_average_memory_usage(&self) -> f64 {
        let processes = self.processes.lock().unwrap();
        if processes.is_empty() {
            return 0.0;
        }
        
        let total: u64 = processes.values().map(|p| p.info.memory_usage).sum();
        (total / processes.len() as u64) as f64
    }
    
    /// 获取进程池统计信息
    pub fn get_stats(&self) -> ProcessPoolStats {
        let processes = self.processes.lock().unwrap();
        let available = self.available_processes.lock().unwrap();
        let busy = self.busy_processes.lock().unwrap();
        
        ProcessPoolStats {
            total_processes: processes.len(),
            available_processes: available.len(),
            busy_processes: busy.len(),
            min_processes: self.config.min_processes,
            max_processes: self.config.max_processes,
            average_cpu_usage: self.get_average_cpu_usage(),
            average_memory_usage: self.get_average_memory_usage(),
            timestamp: SystemTime::now(),
        }
    }
    
    /// 清理不健康的进程
    pub fn cleanup_unhealthy_processes(&self) -> ProcessResult<usize> {
        let mut removed_count = 0;
        let mut processes = self.processes.lock().unwrap();
        let mut available = self.available_processes.lock().unwrap();
        let mut busy = self.busy_processes.lock().unwrap();
        
        let unhealthy_pids: Vec<u32> = processes.iter()
            .filter(|(_, process)| process.health_status == HealthStatus::Unhealthy)
            .map(|(&pid, _)| pid)
            .collect();
        
        for pid in unhealthy_pids {
            processes.remove(&pid);
            available.retain(|&p| p != pid);
            busy.remove(&pid);
            removed_count += 1;
        }
        
        Ok(removed_count)
    }
}

/// 进程池统计信息
#[derive(Debug, Clone)]
pub struct ProcessPoolStats {
    pub total_processes: usize,
    pub available_processes: usize,
    pub busy_processes: usize,
    pub min_processes: usize,
    pub max_processes: usize,
    pub average_cpu_usage: f64,
    pub average_memory_usage: f64,
    pub timestamp: SystemTime,
}

impl Default for ProcessPoolConfig {
    fn default() -> Self {
        Self {
            min_processes: 2,
            max_processes: 10,
            initial_processes: 3,
            idle_timeout: Duration::from_secs(300),
            health_check_interval: Duration::from_secs(30),
            load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
            auto_scaling: AutoScalingConfig::default(),
        }
    }
}

impl Default for AutoScalingConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            cpu_threshold: 80.0,
            memory_threshold: 80.0,
            check_interval: Duration::from_secs(60),
            cooldown_period: Duration::from_secs(300),
        }
    }
}
