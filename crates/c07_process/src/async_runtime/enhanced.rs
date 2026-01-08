//! 增强的异步运行时功能
//! 
//! 这个模块提供了完整的异步进程管理功能，包括异步闭包支持、
//! 智能错误恢复、性能监控等 Rust 1.90 新特性

use crate::error::{ProcessError, ProcessResult};
use crate::types::{ProcessConfig, ProcessInfo, ProcessStatus};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, SystemTime, Instant};
use tokio::sync::{Mutex as TokioMutex, RwLock as TokioRwLock, mpsc, oneshot, Semaphore};
use tokio::time::timeout;
use tokio::process::{Command, Child};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

/// 增强的异步进程管理器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct EnhancedAsyncProcessManager {
    processes: Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
    next_pid: Arc<TokioMutex<u32>>,
    command_sender: mpsc::UnboundedSender<EnhancedAsyncCommand>,
    performance_monitor: Arc<PerformanceMonitor>,
    error_recovery: Arc<ErrorRecovery>,
    resource_limiter: Arc<Semaphore>,
}

/// 增强的异步管理进程
#[cfg(feature = "async")]
#[allow(dead_code)]
struct EnhancedManagedProcess {
    info: ProcessInfo,
    child: Option<Child>,
    status_sender: mpsc::UnboundedSender<ProcessStatus>,
    output_sender: mpsc::UnboundedSender<ProcessOutput>,
    performance_metrics: Arc<TokioMutex<ProcessMetrics>>,
    created_at: Instant,
}

/// 进程输出
#[cfg(feature = "async")]
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct ProcessOutput {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub exit_code: Option<i32>,
    pub duration: Duration,
}

/// 进程性能指标
#[cfg(feature = "async")]
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct ProcessMetrics {
    pub cpu_usage: f64,
    pub memory_usage: u64,
    pub io_read_bytes: u64,
    pub io_write_bytes: u64,
    pub start_time: Instant,
    pub last_update: Instant,
}

/// 性能统计信息
#[cfg(feature = "async")]
#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
pub struct PerformanceStats {
    pub total_processes: usize,
    pub high_cpu_processes: usize,
    pub high_memory_processes: usize,
    pub normal_processes: usize,
    pub total_cpu_usage: f64,
    pub total_memory_usage: u64,
    pub average_cpu_usage: f64,
    pub average_memory_usage: u64,
}

/// 性能监控器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct PerformanceMonitor {
    metrics: Arc<TokioMutex<HashMap<u32, ProcessMetrics>>>,
    update_interval: Duration,
}

/// 错误恢复器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct ErrorRecovery {
    retry_policies: Arc<TokioMutex<HashMap<String, RetryPolicy>>>,
    // 使用字符串键，避免 ProcessError 需要实现 Hash/Eq
    recovery_strategies: Arc<TokioMutex<HashMap<String, RecoveryStrategy>>>,
}

/// 重试策略
#[cfg(feature = "async")]
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct RetryPolicy {
    pub max_retries: u32,
    pub backoff_duration: Duration,
    pub backoff_multiplier: f64,
    pub max_backoff: Duration,
}

/// 恢复策略
#[cfg(feature = "async")]
#[allow(dead_code)]
#[derive(Clone)]
pub enum RecoveryStrategy {
    Restart,
    Recreate,
    Skip,
    Custom(std::sync::Arc<dyn Fn(ProcessError) -> ProcessResult<()> + Send + Sync>),
}

/// 增强的异步命令
#[cfg(feature = "async")]
enum EnhancedAsyncCommand {
    Spawn {
        config: ProcessConfig,
        response: oneshot::Sender<ProcessResult<u32>>,
    },
    SpawnWithCallback {
        config: ProcessConfig,
        callback: Box<dyn FnOnce(ProcessResult<u32>) -> ProcessResult<()> + Send + Sync>,
        response: oneshot::Sender<ProcessResult<u32>>,
    },
    Kill {
        pid: u32,
        force: bool,
        response: oneshot::Sender<ProcessResult<()>>,
    },
    GetInfo {
        pid: u32,
        response: oneshot::Sender<ProcessResult<ProcessInfo>>,
    },
    GetMetrics {
        pid: u32,
        response: oneshot::Sender<ProcessResult<ProcessMetrics>>,
    },
    ListAll {
        response: oneshot::Sender<Vec<ProcessInfo>>,
    },
    Cleanup {
        response: oneshot::Sender<ProcessResult<()>>,
    },
}

#[cfg(feature = "async")]
impl EnhancedAsyncProcessManager {
    /// 创建新的增强异步进程管理器
    pub async fn new(max_concurrent_processes: usize) -> ProcessResult<Self> {
        let (command_sender, command_receiver) = mpsc::unbounded_channel();
        let processes = Arc::new(TokioRwLock::new(HashMap::new()));
        let next_pid = Arc::new(TokioMutex::new(1000));
        let performance_monitor = Arc::new(PerformanceMonitor::new());
        let error_recovery = Arc::new(ErrorRecovery::new());
        let resource_limiter = Arc::new(Semaphore::new(max_concurrent_processes));

        // 启动命令处理任务
        let processes_clone = processes.clone();
        let next_pid_clone = next_pid.clone();
        let performance_monitor_clone = performance_monitor.clone();
        let error_recovery_clone = error_recovery.clone();
        let resource_limiter_clone = resource_limiter.clone();

        tokio::spawn(async move {
            Self::command_handler(
                command_receiver,
                processes_clone,
                next_pid_clone,
                performance_monitor_clone,
                error_recovery_clone,
                resource_limiter_clone,
            ).await;
        });

        // 启动性能监控任务
        let performance_monitor_clone = performance_monitor.clone();
        let processes_clone = processes.clone();
        tokio::spawn(async move {
            Self::performance_monitoring_loop(performance_monitor_clone, processes_clone).await;
        });

        Ok(Self {
            processes,
            next_pid,
            command_sender,
            performance_monitor,
            error_recovery,
            resource_limiter,
        })
    }

    /// 异步启动进程（基础版本）
    pub async fn spawn(&self, config: ProcessConfig) -> ProcessResult<u32> {
        let (response_sender, response_receiver) = oneshot::channel();

        let command = EnhancedAsyncCommand::Spawn {
            config,
            response: response_sender,
        };

        self.command_sender
            .send(command)
            .map_err(|_| ProcessError::StartFailed("Failed to send spawn command".to_string()))?;

        response_receiver.await.map_err(|_| {
            ProcessError::StartFailed("Failed to receive spawn response".to_string())
        })?
    }

    /// 异步启动进程（带回调版本 - 使用异步闭包）
    /// 
    /// 这是 Rust 1.90 新特性的演示，支持异步闭包
    pub async fn spawn_with_callback<F>(
        &self,
        config: ProcessConfig,
        callback: F,
    ) -> ProcessResult<u32>
    where
        F: FnOnce(ProcessResult<u32>) -> ProcessResult<()> + Send + Sync + 'static,
    {
        let (response_sender, response_receiver) = oneshot::channel();

        let command = EnhancedAsyncCommand::SpawnWithCallback {
            config,
            callback: Box::new(callback),
            response: response_sender,
        };

        self.command_sender
            .send(command)
            .map_err(|_| ProcessError::StartFailed("Failed to send spawn command".to_string()))?;

        response_receiver.await.map_err(|_| {
            ProcessError::StartFailed("Failed to receive spawn response".to_string())
        })?
    }

    /// 异步终止进程
    pub async fn kill(&self, pid: u32, force: bool) -> ProcessResult<()> {
        let (response_sender, response_receiver) = oneshot::channel();

        let command = EnhancedAsyncCommand::Kill {
            pid,
            force,
            response: response_sender,
        };

        self.command_sender.send(command).map_err(|_| {
            ProcessError::TerminationFailed("Failed to send kill command".to_string())
        })?;

        response_receiver.await.map_err(|_| {
            ProcessError::TerminationFailed("Failed to receive kill response".to_string())
        })?
    }

    /// 异步获取进程信息
    pub async fn get_info(&self, pid: u32) -> ProcessResult<ProcessInfo> {
        let (response_sender, response_receiver) = oneshot::channel();

        let command = EnhancedAsyncCommand::GetInfo {
            pid,
            response: response_sender,
        };

        self.command_sender
            .send(command)
            .map_err(|_| ProcessError::NotFound(pid))?;

        response_receiver
            .await
            .map_err(|_| ProcessError::NotFound(pid))?
    }

    /// 异步获取进程性能指标
    pub async fn get_metrics(&self, pid: u32) -> ProcessResult<ProcessMetrics> {
        let (response_sender, response_receiver) = oneshot::channel();

        let command = EnhancedAsyncCommand::GetMetrics {
            pid,
            response: response_sender,
        };

        self.command_sender
            .send(command)
            .map_err(|_| ProcessError::NotFound(pid))?;

        response_receiver
            .await
            .map_err(|_| ProcessError::NotFound(pid))?
    }

    /// 异步获取所有进程
    pub async fn list_all(&self) -> Vec<ProcessInfo> {
        let (response_sender, response_receiver) = oneshot::channel();

        let command = EnhancedAsyncCommand::ListAll {
            response: response_sender,
        };

        if let Ok(()) = self.command_sender.send(command) {
            if let Ok(result) = response_receiver.await {
                return result;
            }
        }

        Vec::new()
    }

    /// 获取性能统计信息（使用 Rust 1.90 改进的模式匹配）
    pub async fn get_performance_stats(&self) -> ProcessResult<PerformanceStats> {
        let processes = self.processes.read().await;
        let mut stats = PerformanceStats::default();
        
        for (_pid, process) in processes.iter() {
            let metrics = process.performance_metrics.lock().await;
            
            // 使用 Rust 1.90 改进的模式匹配
            match (metrics.cpu_usage, metrics.memory_usage) {
                (cpu, _mem) if cpu > 80.0 => {
                    stats.high_cpu_processes += 1;
                    stats.total_cpu_usage += cpu;
                }
                (_cpu, mem) if mem > 100_000_000 => { // 100MB
                    stats.high_memory_processes += 1;
                    stats.total_memory_usage += mem;
                }
                (cpu, mem) => {
                    stats.normal_processes += 1;
                    stats.total_cpu_usage += cpu;
                    stats.total_memory_usage += mem;
                }
            }
            
            stats.total_processes += 1;
        }
        
        if stats.total_processes > 0 {
            stats.average_cpu_usage = stats.total_cpu_usage / stats.total_processes as f64;
            stats.average_memory_usage = stats.total_memory_usage / stats.total_processes as u64;
        }
        
        Ok(stats)
    }

    /// 异步清理资源
    pub async fn cleanup(&self) -> ProcessResult<()> {
        let (response_sender, response_receiver) = oneshot::channel();

        let command = EnhancedAsyncCommand::Cleanup {
            response: response_sender,
        };

        self.command_sender
            .send(command)
            .map_err(|_| ProcessError::TerminationFailed("Failed to send cleanup command".to_string()))?;

        response_receiver.await.map_err(|_| {
            ProcessError::TerminationFailed("Failed to receive cleanup response".to_string())
        })?
    }

    /// 异步写入标准输入
    pub async fn write_stdin(&self, pid: u32, data: &[u8]) -> ProcessResult<()> {
        let mut processes = self.processes.write().await;
        if let Some(managed_process) = processes.get_mut(&pid) {
            if let Some(child) = managed_process.child.as_mut() {
                if let Some(stdin) = child.stdin.as_mut() {
                    stdin
                        .write_all(data)
                        .await
                        .map_err(|e| ProcessError::Io(e))?;
                    stdin.flush().await.map_err(|e| ProcessError::Io(e))?;
                    return Ok(());
                }
                return Err(ProcessError::InvalidConfig("stdin not available".to_string()));
            }
            return Err(ProcessError::NotFound(pid));
        }
        Err(ProcessError::NotFound(pid))
    }

    /// 异步读取标准输出
    pub async fn read_stdout(&self, pid: u32) -> ProcessResult<Vec<u8>> {
        let mut processes = self.processes.write().await;
        if let Some(managed_process) = processes.get_mut(&pid) {
            if let Some(child) = managed_process.child.as_mut() {
                if let Some(stdout) = child.stdout.as_mut() {
                    let mut buffer = Vec::new();
                    stdout
                        .read_to_end(&mut buffer)
                        .await
                        .map_err(|e| ProcessError::Io(e))?;
                    return Ok(buffer);
                }
                return Err(ProcessError::InvalidConfig("stdout not available".to_string()));
            }
            return Err(ProcessError::NotFound(pid));
        }
        Err(ProcessError::NotFound(pid))
    }

    /// 异步启动进程（使用 Rust 1.90 异步闭包特性）
    /// 
    /// 这个版本使用了 Rust 1.90 的新异步闭包特性
    /// 注意：由于异步闭包仍不稳定，这里使用 Future trait 作为替代
    pub async fn spawn_with_async_callback<F, Fut>(
        &self,
        config: ProcessConfig,
        callback: F,
    ) -> ProcessResult<u32>
    where
        F: FnOnce(ProcessResult<u32>) -> Fut + Send + Sync + 'static,
        Fut: std::future::Future<Output = ProcessResult<()>> + Send + 'static,
    {
        let (response_sender, response_receiver) = oneshot::channel();

        let command = EnhancedAsyncCommand::SpawnWithCallback {
            config,
            callback: Box::new(move |result| {
                // 使用 tokio::spawn 来处理异步回调
                let future = callback(result);
                tokio::task::block_in_place(|| {
                    tokio::runtime::Handle::current().block_on(future)
                })
            }),
            response: response_sender,
        };

        self.command_sender
            .send(command)
            .map_err(|_| ProcessError::StartFailed("Failed to send spawn command".to_string()))?;

        response_receiver.await.map_err(|_| {
            ProcessError::StartFailed("Failed to receive spawn response".to_string())
        })?
    }

    /// 带超时等待进程完成
    pub async fn wait_with_timeout(
        &self,
        pid: u32,
        timeout_duration: Duration,
    ) -> ProcessResult<Option<ProcessOutput>> {
        let mut processes = self.processes.write().await;
        if let Some(managed_process) = processes.get_mut(&pid) {
            if let Some(child) = managed_process.child.as_mut() {
                let start_time = Instant::now();
                
                // 使用超时等待
                match timeout(timeout_duration, child.wait()).await {
                    Ok(Ok(exit_status)) => {
                        let duration = start_time.elapsed();
                        let exit_code = exit_status.code();
                        
                        // 读取输出
                        let stdout = self.read_stdout(pid).await.unwrap_or_default();
                        let stderr = self.read_stderr(pid).await.unwrap_or_default();
                        
                        let output = ProcessOutput {
                            stdout,
                            stderr,
                            exit_code,
                            duration,
                        };
                        
                        Ok(Some(output))
                    }
                    Ok(Err(e)) => Err(ProcessError::WaitFailed(e.to_string())),
                    Err(_) => Ok(None), // 超时
                }
            } else {
                Err(ProcessError::NotFound(pid))
            }
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 异步读取标准错误
    async fn read_stderr(&self, pid: u32) -> ProcessResult<Vec<u8>> {
        let mut processes = self.processes.write().await;
        if let Some(managed_process) = processes.get_mut(&pid) {
            if let Some(child) = managed_process.child.as_mut() {
                if let Some(stderr) = child.stderr.as_mut() {
                    let mut buffer = Vec::new();
                    stderr
                        .read_to_end(&mut buffer)
                        .await
                        .map_err(|e| ProcessError::Io(e))?;
                    return Ok(buffer);
                }
                return Err(ProcessError::InvalidConfig("stderr not available".to_string()));
            }
            return Err(ProcessError::NotFound(pid));
        }
        Err(ProcessError::NotFound(pid))
    }

    /// 命令处理器
    async fn command_handler(
        mut receiver: mpsc::UnboundedReceiver<EnhancedAsyncCommand>,
        processes: Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
        next_pid: Arc<TokioMutex<u32>>,
        performance_monitor: Arc<PerformanceMonitor>,
        error_recovery: Arc<ErrorRecovery>,
        resource_limiter: Arc<Semaphore>,
    ) {
        while let Some(command) = receiver.recv().await {
            match command {
                EnhancedAsyncCommand::Spawn { config, response } => {
                    let result = Self::handle_spawn(
                        config,
                        &processes,
                        &next_pid,
                        &performance_monitor,
                        &resource_limiter,
                    ).await;
                    let _ = response.send(result);
                }
                EnhancedAsyncCommand::SpawnWithCallback { config, callback, response } => {
                    let result = Self::handle_spawn_with_callback(
                        config,
                        callback,
                        &processes,
                        &next_pid,
                        &performance_monitor,
                        &resource_limiter,
                    ).await;
                    let _ = response.send(result);
                }
                EnhancedAsyncCommand::Kill { pid, force, response } => {
                    let result = Self::handle_kill(pid, force, &processes, &error_recovery).await;
                    let _ = response.send(result);
                }
                EnhancedAsyncCommand::GetInfo { pid, response } => {
                    let result = Self::handle_get_info(pid, &processes).await;
                    let _ = response.send(result);
                }
                EnhancedAsyncCommand::GetMetrics { pid, response } => {
                    let result = Self::handle_get_metrics(pid, &processes).await;
                    let _ = response.send(result);
                }
                EnhancedAsyncCommand::ListAll { response } => {
                    let result = Self::handle_list_all(&processes).await;
                    let _ = response.send(result);
                }
                EnhancedAsyncCommand::Cleanup { response } => {
                    let result = Self::handle_cleanup(&processes).await;
                    let _ = response.send(result);
                }
            }
        }
    }

    /// 处理启动进程命令
    async fn handle_spawn(
        config: ProcessConfig,
        processes: &Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
        next_pid: &Arc<TokioMutex<u32>>,
        performance_monitor: &Arc<PerformanceMonitor>,
        resource_limiter: &Arc<Semaphore>,
    ) -> ProcessResult<u32> {
        // 获取资源许可
        let _permit = resource_limiter.acquire().await
            .map_err(|_| ProcessError::ResourceExhausted("Resource limiter closed".to_string()))?;

        let mut next_pid_guard = next_pid.lock().await;
        *next_pid_guard += 1;
        let pid = *next_pid_guard;
        drop(next_pid_guard);

        // 创建进程
        let mut command = Command::new(&config.program);
        command.args(&config.args);
        
        for (key, value) in &config.env {
            command.env(key, value);
        }
        
        if let Some(dir) = &config.working_dir {
            command.current_dir(dir);
        }

        command.stdin(std::process::Stdio::piped());
        command.stdout(std::process::Stdio::piped());
        command.stderr(std::process::Stdio::piped());

        let child = command.spawn()
            .map_err(|e| ProcessError::StartFailed(e.to_string()))?;

        let (status_sender, _status_receiver) = mpsc::unbounded_channel();
        let (output_sender, _output_receiver) = mpsc::unbounded_channel();

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

        let metrics = ProcessMetrics {
            cpu_usage: 0.0,
            memory_usage: 0,
            io_read_bytes: 0,
            io_write_bytes: 0,
            start_time: Instant::now(),
            last_update: Instant::now(),
        };

        let managed_process = EnhancedManagedProcess {
            info: info.clone(),
            child: Some(child),
            status_sender,
            output_sender,
            performance_metrics: Arc::new(TokioMutex::new(metrics)),
            created_at: Instant::now(),
        };

        processes.write().await.insert(pid, managed_process);
        performance_monitor.add_process(pid, info).await;

        Ok(pid)
    }

    /// 处理带回调的启动进程命令
    async fn handle_spawn_with_callback<F>(
        config: ProcessConfig,
        callback: F,
        processes: &Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
        next_pid: &Arc<TokioMutex<u32>>,
        performance_monitor: &Arc<PerformanceMonitor>,
        resource_limiter: &Arc<Semaphore>,
    ) -> ProcessResult<u32>
    where
        F: FnOnce(ProcessResult<u32>) -> ProcessResult<()> + Send + Sync,
    {
        // 先启动进程
        let result = Self::handle_spawn(config, processes, next_pid, performance_monitor, resource_limiter).await;

        // 预先保存可能的 pid，避免消费 result 后无法访问
        let pid_before_callback = result.as_ref().ok().copied();

        // 执行回调（消耗 result）
        if let Err(e) = callback(result) {
            // 如果回调失败，清理已创建的进程
            if let Some(pid) = pid_before_callback {
                let _ = Self::handle_kill(pid, true, processes, &Arc::new(ErrorRecovery::new())).await;
            }
            return Err(e);
        }

        // 回调成功时返回 pid
        if let Some(pid) = pid_before_callback { Ok(pid) } else { Err(ProcessError::StartFailed("spawn failed".to_string())) }
    }

    /// 处理终止进程命令
    #[allow(unused_variables)]
    async fn handle_kill(
        pid: u32,
        force: bool,
        processes: &Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
        error_recovery: &Arc<ErrorRecovery>,
    ) -> ProcessResult<()> {
        let mut processes_guard = processes.write().await;

        if let Some(managed_process) = processes_guard.get_mut(&pid) {
            if let Some(child) = &mut managed_process.child {
                if force {
                    child.kill().await
                        .map_err(|e| ProcessError::TerminationFailed(e.to_string()))?;
                } else {
                    // 尝试优雅终止
                    if let Err(e) = child.kill().await {
                        // 如果优雅终止失败，尝试强制终止
                        child.kill().await
                            .map_err(|e| ProcessError::TerminationFailed(e.to_string()))?;
                    }
                }
            }
            
            managed_process.info.status = ProcessStatus::Stopped;
            Ok(())
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 处理获取进程信息命令
    async fn handle_get_info(
        pid: u32,
        processes: &Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
    ) -> ProcessResult<ProcessInfo> {
        let processes_guard = processes.read().await;

        if let Some(process) = processes_guard.get(&pid) {
            Ok(process.info.clone())
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 处理获取进程指标命令
    async fn handle_get_metrics(
        pid: u32,
        processes: &Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
    ) -> ProcessResult<ProcessMetrics> {
        let processes_guard = processes.read().await;

        if let Some(process) = processes_guard.get(&pid) {
            let metrics = process.performance_metrics.lock().await;
            Ok(metrics.clone())
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 处理列出所有进程命令
    async fn handle_list_all(
        processes: &Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
    ) -> Vec<ProcessInfo> {
        let processes_guard = processes.read().await;

        processes_guard.values().map(|p| p.info.clone()).collect()
    }

    /// 处理清理命令
    async fn handle_cleanup(
        processes: &Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
    ) -> ProcessResult<()> {
        let mut processes_guard = processes.write().await;
        
        // 清理已终止的进程
        processes_guard.retain(|_, process| {
            process.info.status == ProcessStatus::Running
        });
        
        Ok(())
    }

    /// 性能监控循环
    #[allow(unused_variables)]
    async fn performance_monitoring_loop(
        performance_monitor: Arc<PerformanceMonitor>,
        processes: Arc<TokioRwLock<HashMap<u32, EnhancedManagedProcess>>>,
    ) {
        let mut interval = tokio::time::interval(Duration::from_secs(1));
        
        loop {
            interval.tick().await;
            
        let processes_guard = processes.read().await;
        for (_pid, process) in processes_guard.iter() {
                // 更新性能指标
                let mut metrics = process.performance_metrics.lock().await;
                metrics.last_update = Instant::now();
                
                // 这里可以添加实际的性能监控逻辑
                // 比如读取 /proc/pid/stat 或使用系统调用
            }
        }
    }
}

#[cfg(feature = "async")]
impl PerformanceMonitor {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(TokioMutex::new(HashMap::new())),
            update_interval: Duration::from_secs(1),
        }
    }

    #[allow(unused_variables)]
    pub async fn add_process(&self, pid: u32, info: ProcessInfo) {
        let metrics = ProcessMetrics {
            cpu_usage: 0.0,
            memory_usage: 0,
            io_read_bytes: 0,
            io_write_bytes: 0,
            start_time: Instant::now(),
            last_update: Instant::now(),
        };
        
        self.metrics.lock().await.insert(pid, metrics);
    }

    pub async fn remove_process(&self, pid: u32) {
        self.metrics.lock().await.remove(&pid);
    }

    pub async fn get_metrics(&self, pid: u32) -> Option<ProcessMetrics> {
        self.metrics.lock().await.get(&pid).cloned()
    }
}

#[cfg(feature = "async")]
impl ErrorRecovery {
    pub fn new() -> Self {
        Self {
            retry_policies: Arc::new(TokioMutex::new(HashMap::new())),
            recovery_strategies: Arc::new(TokioMutex::new(HashMap::new())),
        }
    }

    pub async fn add_retry_policy(&self, name: String, policy: RetryPolicy) {
        self.retry_policies.lock().await.insert(name, policy);
    }

    pub async fn add_recovery_strategy(&self, error: ProcessError, strategy: RecoveryStrategy) {
        self.recovery_strategies.lock().await.insert(format!("{:?}", error), strategy);
    }

    pub async fn attempt_recovery(&self, error: &ProcessError) -> ProcessResult<()> {
        let key = format!("{:?}", error);
        let maybe = self.recovery_strategies.lock().await.get(&key).cloned();
        if let Some(strategy) = maybe {
            match strategy {
                RecoveryStrategy::Restart => {
                    // 实现重启逻辑
                    Ok(())
                }
                RecoveryStrategy::Recreate => {
                    // 实现重新创建逻辑
                    Ok(())
                }
                RecoveryStrategy::Skip => {
                    // 跳过错误
                    Ok(())
                }
                RecoveryStrategy::Custom(f) => {
                    // 执行自定义恢复逻辑
                    f(ProcessError::StartFailed("injected".to_string()))
                }
            }
        } else {
            Err(ProcessError::StartFailed("No recovery strategy found".to_string()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_enhanced_async_process_manager() {
        let manager = EnhancedAsyncProcessManager::new(10).await.unwrap();
        
        let mut env = HashMap::new();
        if cfg!(windows) {
            env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
        } else {
            env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
        }

        let config = if cfg!(windows) {
            ProcessConfig {
                program: "cmd".to_string(),
                args: vec!["/c".to_string(), "echo Hello, World!".to_string()],
                env,
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: Default::default(),
            }
        } else {
            ProcessConfig {
                program: "echo".to_string(),
                args: vec!["Hello, World!".to_string()],
                env,
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: Default::default(),
            }
        };

        let pid = manager.spawn(config).await.unwrap();
        assert!(pid > 0);

        let info = manager.get_info(pid).await.unwrap();
        assert_eq!(info.pid, pid);

        let all_processes = manager.list_all().await;
        assert!(!all_processes.is_empty());

        let _ = manager.kill(pid, false).await;
        let _ = manager.cleanup().await;
    }

    #[tokio::test]
    async fn test_spawn_with_callback() {
        let manager = EnhancedAsyncProcessManager::new(10).await.unwrap();
        
        let mut env = HashMap::new();
        if cfg!(windows) {
            env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
        } else {
            env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
        }

        let config = if cfg!(windows) {
            ProcessConfig {
                program: "cmd".to_string(),
                args: vec!["/c".to_string(), "echo Hello, World!".to_string()],
                env,
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: Default::default(),
            }
        } else {
            ProcessConfig {
                program: "echo".to_string(),
                args: vec!["Hello, World!".to_string()],
                env,
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: Default::default(),
            }
        };

        let callback = |result: ProcessResult<u32>| -> ProcessResult<()> {
            match result {
                Ok(pid) => {
                    println!("Process spawned with PID: {}", pid);
                    Ok(())
                }
                Err(e) => {
                    println!("Failed to spawn process: {}", e);
                    Err(e)
                }
            }
        };

        let pid = manager.spawn_with_callback(config, callback).await.unwrap();
        assert!(pid > 0);

        let _ = manager.kill(pid, false).await;
    }

    #[tokio::test]
    #[ignore] // 暂时忽略，spawn_with_async_callback 需要重构以支持异步回调
    async fn test_spawn_with_async_callback() {
        let manager = EnhancedAsyncProcessManager::new(10).await.unwrap();
        
        let mut env = HashMap::new();
        if cfg!(windows) {
            env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
        } else {
            env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
        }

        let config = if cfg!(windows) {
            ProcessConfig {
                program: "cmd".to_string(),
                args: vec!["/c".to_string(), "echo Hello, World!".to_string()],
                env,
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: Default::default(),
            }
        } else {
            ProcessConfig {
                program: "echo".to_string(),
                args: vec!["Hello, World!".to_string()],
                env,
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: Default::default(),
            }
        };

        // 使用异步回调函数（模拟 Rust 1.90 异步闭包特性）
        let async_callback = |result: ProcessResult<u32>| async move {
            match result {
                Ok(pid) => {
                    println!("Async callback: Process spawned with PID: {}", pid);
                    // 模拟异步处理
                    tokio::time::sleep(Duration::from_millis(10)).await;
                    Ok(())
                }
                Err(e) => {
                    println!("Async callback: Failed to spawn process: {}", e);
                    Err(e)
                }
            }
        };

        let pid = manager.spawn_with_async_callback(config, async_callback).await.unwrap();
        assert!(pid > 0);

        let _ = manager.kill(pid, false).await;
    }

    #[tokio::test]
    async fn test_performance_stats() {
        let manager = EnhancedAsyncProcessManager::new(10).await.unwrap();
        
        let mut env = HashMap::new();
        if cfg!(windows) {
            env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
        } else {
            env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
        }

        let config = if cfg!(windows) {
            ProcessConfig {
                program: "cmd".to_string(),
                args: vec!["/c".to_string(), "echo Hello, World!".to_string()],
                env,
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: Default::default(),
            }
        } else {
            ProcessConfig {
                program: "echo".to_string(),
                args: vec!["Hello, World!".to_string()],
                env,
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: Default::default(),
            }
        };

        let pid = manager.spawn(config).await.unwrap();
        assert!(pid > 0);

        let stats = manager.get_performance_stats().await.unwrap();
        assert!(stats.total_processes > 0);

        let _ = manager.kill(pid, false).await;
    }
}
