//! 操作系统设计模式应用
//!
//! 本模块展示了在操作系统开发中应用各种设计模式的实践案例，
//! 包括Singleton、Factory、Strategy等经典模式。

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

// ============================================================================
// Singleton 模式
// ============================================================================

/// 系统资源管理器（单例模式）
#[derive(Clone)]
pub struct SystemResourceManager {
    memory_pool: HashMap<String, Vec<u8>>,
    file_handles: HashMap<String, u32>,
    process_count: u32,
}

impl SystemResourceManager {
    fn new() -> Self {
        Self {
            memory_pool: HashMap::new(),
            file_handles: HashMap::new(),
            process_count: 0,
        }
    }

    pub fn allocate_memory(&mut self, name: String, size: usize) -> Result<(), String> {
        if self.memory_pool.contains_key(&name) {
            return Err("内存块已存在".to_string());
        }

        let memory = vec![0u8; size];
        self.memory_pool.insert(name, memory);
        println!("分配内存: {} 字节", size);
        Ok(())
    }

    pub fn deallocate_memory(&mut self, name: &str) -> Result<(), String> {
        if let Some(memory) = self.memory_pool.remove(name) {
            println!("释放内存: {} 字节", memory.len());
            Ok(())
        } else {
            Err("内存块不存在".to_string())
        }
    }

    pub fn open_file(&mut self, path: String) -> Result<u32, String> {
        let handle = self.file_handles.len() as u32;
        self.file_handles.insert(path, handle);
        println!("打开文件: 句柄 {}", handle);
        Ok(handle)
    }

    pub fn close_file(&mut self, handle: u32) -> Result<(), String> {
        let path = self
            .file_handles
            .iter()
            .find(|(_, h)| **h == handle)
            .map(|(p, _)| p.clone());

        if let Some(path) = path {
            self.file_handles.remove(&path);
            println!("关闭文件: 句柄 {}", handle);
            Ok(())
        } else {
            Err("文件句柄不存在".to_string())
        }
    }

    pub fn create_process(&mut self) -> u32 {
        self.process_count += 1;
        println!("创建进程: PID {}", self.process_count);
        self.process_count
    }

    pub fn get_memory_usage(&self) -> usize {
        self.memory_pool.values().map(|m| m.len()).sum()
    }

    pub fn get_file_handle_count(&self) -> usize {
        self.file_handles.len()
    }

    pub fn get_process_count(&self) -> u32 {
        self.process_count
    }
}

/// 线程安全的单例实现
pub struct SystemResourceManagerSingleton {
    instance: OnceLock<Arc<Mutex<SystemResourceManager>>>,
}

impl SystemResourceManagerSingleton {
    pub fn new() -> Self {
        Self {
            instance: OnceLock::new(),
        }
    }

    pub fn get_instance(&self) -> Arc<Mutex<SystemResourceManager>> {
        self.instance
            .get_or_init(|| Arc::new(Mutex::new(SystemResourceManager::new())))
            .clone()
    }
}

// ============================================================================
// Factory 模式
// ============================================================================

/// 设备类型枚举
#[derive(Debug, Clone, PartialEq)]
pub enum DeviceType {
    CPU,
    Memory,
    Disk,
    Network,
    GPU,
}

/// 设备接口
pub trait Device {
    fn get_id(&self) -> String;
    fn get_type(&self) -> DeviceType;
    fn initialize(&mut self) -> Result<(), String>;
    fn shutdown(&mut self) -> Result<(), String>;
    fn get_status(&self) -> DeviceStatus;
}

/// 设备状态
#[derive(Debug, Clone)]
pub struct DeviceStatus {
    pub is_online: bool,
    pub utilization: f32,
    pub error_count: u32,
}

/// CPU设备
pub struct CPUDevice {
    id: String,
    cores: u32,
    frequency: f32,
    status: DeviceStatus,
}

impl CPUDevice {
    pub fn new(id: String, cores: u32, frequency: f32) -> Self {
        Self {
            id,
            cores,
            frequency,
            status: DeviceStatus {
                is_online: false,
                utilization: 0.0,
                error_count: 0,
            },
        }
    }
}

impl Device for CPUDevice {
    fn get_id(&self) -> String {
        self.id.clone()
    }

    fn get_type(&self) -> DeviceType {
        DeviceType::CPU
    }

    fn initialize(&mut self) -> Result<(), String> {
        self.status.is_online = true;
        println!(
            "CPU设备 {} 初始化完成 ({} 核, {:.1} GHz)",
            self.id, self.cores, self.frequency
        );
        Ok(())
    }

    fn shutdown(&mut self) -> Result<(), String> {
        self.status.is_online = false;
        println!("CPU设备 {} 已关闭", self.id);
        Ok(())
    }

    fn get_status(&self) -> DeviceStatus {
        self.status.clone()
    }
}

/// 内存设备
pub struct MemoryDevice {
    id: String,
    capacity: usize,
    status: DeviceStatus,
}

impl MemoryDevice {
    pub fn new(id: String, capacity: usize) -> Self {
        Self {
            id,
            capacity,
            status: DeviceStatus {
                is_online: false,
                utilization: 0.0,
                error_count: 0,
            },
        }
    }
}

impl Device for MemoryDevice {
    fn get_id(&self) -> String {
        self.id.clone()
    }

    fn get_type(&self) -> DeviceType {
        DeviceType::Memory
    }

    fn initialize(&mut self) -> Result<(), String> {
        self.status.is_online = true;
        println!(
            "内存设备 {} 初始化完成 ({} MB)",
            self.id,
            self.capacity / 1024 / 1024
        );
        Ok(())
    }

    fn shutdown(&mut self) -> Result<(), String> {
        self.status.is_online = false;
        println!("内存设备 {} 已关闭", self.id);
        Ok(())
    }

    fn get_status(&self) -> DeviceStatus {
        self.status.clone()
    }
}

/// 磁盘设备
pub struct DiskDevice {
    id: String,
    capacity: usize,
    status: DeviceStatus,
}

impl DiskDevice {
    pub fn new(id: String, capacity: usize) -> Self {
        Self {
            id,
            capacity,
            status: DeviceStatus {
                is_online: false,
                utilization: 0.0,
                error_count: 0,
            },
        }
    }
}

impl Device for DiskDevice {
    fn get_id(&self) -> String {
        self.id.clone()
    }

    fn get_type(&self) -> DeviceType {
        DeviceType::Disk
    }

    fn initialize(&mut self) -> Result<(), String> {
        self.status.is_online = true;
        println!(
            "磁盘设备 {} 初始化完成 ({} GB)",
            self.id,
            self.capacity / 1024 / 1024 / 1024
        );
        Ok(())
    }

    fn shutdown(&mut self) -> Result<(), String> {
        self.status.is_online = false;
        println!("磁盘设备 {} 已关闭", self.id);
        Ok(())
    }

    fn get_status(&self) -> DeviceStatus {
        self.status.clone()
    }
}

/// 设备工厂接口
pub trait DeviceFactory {
    fn create_device(
        &self,
        device_type: DeviceType,
        id: String,
        params: HashMap<String, String>,
    ) -> Box<dyn Device>;
}

/// 设备工厂实现
pub struct OSDeviceFactory;

impl DeviceFactory for OSDeviceFactory {
    fn create_device(
        &self,
        device_type: DeviceType,
        id: String,
        params: HashMap<String, String>,
    ) -> Box<dyn Device> {
        match device_type {
            DeviceType::CPU => {
                let cores = params
                    .get("cores")
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(4);
                let frequency = params
                    .get("frequency")
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(2.4);
                Box::new(CPUDevice::new(id, cores, frequency))
            }
            DeviceType::Memory => {
                let capacity = params
                    .get("capacity")
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(8 * 1024 * 1024 * 1024);
                Box::new(MemoryDevice::new(id, capacity))
            }
            DeviceType::Disk => {
                let capacity = params
                    .get("capacity")
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(500 * 1024 * 1024 * 1024);
                Box::new(DiskDevice::new(id, capacity))
            }
            _ => {
                // 默认返回CPU设备
                Box::new(CPUDevice::new(id, 4, 2.4))
            }
        }
    }
}

// ============================================================================
// Strategy 模式
// ============================================================================

/// 进程调度策略接口
pub trait SchedulingStrategy {
    fn select_next_process(&self, processes: &[Process]) -> Option<usize>;
    fn get_name(&self) -> &str;
}

/// 进程结构
#[derive(Debug, Clone)]
pub struct Process {
    pub id: u32,
    pub name: String,
    pub priority: u32,
    pub burst_time: u32,
    pub arrival_time: u32,
    pub remaining_time: u32,
}

/// 先来先服务调度策略
pub struct FirstComeFirstServeStrategy;

impl SchedulingStrategy for FirstComeFirstServeStrategy {
    fn select_next_process(&self, processes: &[Process]) -> Option<usize> {
        processes
            .iter()
            .enumerate()
            .filter(|(_, p)| p.remaining_time > 0)
            .min_by_key(|(_, p)| p.arrival_time)
            .map(|(i, _)| i)
    }

    fn get_name(&self) -> &str {
        "先来先服务 (FCFS)"
    }
}

/// 最短作业优先调度策略
pub struct ShortestJobFirstStrategy;

impl SchedulingStrategy for ShortestJobFirstStrategy {
    fn select_next_process(&self, processes: &[Process]) -> Option<usize> {
        processes
            .iter()
            .enumerate()
            .filter(|(_, p)| p.remaining_time > 0)
            .min_by_key(|(_, p)| p.remaining_time)
            .map(|(i, _)| i)
    }

    fn get_name(&self) -> &str {
        "最短作业优先 (SJF)"
    }
}

/// 优先级调度策略
pub struct PrioritySchedulingStrategy;

impl SchedulingStrategy for PrioritySchedulingStrategy {
    fn select_next_process(&self, processes: &[Process]) -> Option<usize> {
        processes
            .iter()
            .enumerate()
            .filter(|(_, p)| p.remaining_time > 0)
            .max_by_key(|(_, p)| p.priority)
            .map(|(i, _)| i)
    }

    fn get_name(&self) -> &str {
        "优先级调度"
    }
}

/// 轮转调度策略
pub struct RoundRobinStrategy {
    _time_quantum: u32,
    current_index: usize,
}

impl RoundRobinStrategy {
    pub fn new(time_quantum: u32) -> Self {
        Self {
            _time_quantum: time_quantum,
            current_index: 0,
        }
    }
}

impl SchedulingStrategy for RoundRobinStrategy {
    fn select_next_process(&self, processes: &[Process]) -> Option<usize> {
        if processes.is_empty() {
            return None;
        }

        let mut index = self.current_index;
        let start_index = index;

        loop {
            if processes[index].remaining_time > 0 {
                return Some(index);
            }

            index = (index + 1) % processes.len();
            if index == start_index {
                break;
            }
        }

        None
    }

    fn get_name(&self) -> &str {
        "轮转调度 (RR)"
    }
}

/// 进程调度器
pub struct ProcessScheduler {
    strategy: Box<dyn SchedulingStrategy>,
    processes: Vec<Process>,
    current_time: u32,
}

impl ProcessScheduler {
    pub fn new(strategy: Box<dyn SchedulingStrategy>) -> Self {
        Self {
            strategy,
            processes: Vec::new(),
            current_time: 0,
        }
    }

    pub fn add_process(&mut self, process: Process) {
        self.processes.push(process);
    }

    pub fn set_strategy(&mut self, strategy: Box<dyn SchedulingStrategy>) {
        self.strategy = strategy;
    }

    pub fn run_simulation(&mut self, time_steps: u32) {
        println!("开始进程调度模拟，使用策略: {}", self.strategy.get_name());

        for _step in 0..time_steps {
            if let Some(process_index) = self.strategy.select_next_process(&self.processes) {
                let process = &mut self.processes[process_index];

                if process.remaining_time > 0 {
                    let execution_time = std::cmp::min(process.remaining_time, 1);
                    process.remaining_time -= execution_time;

                    println!(
                        "时间 {}: 执行进程 {} (剩余时间: {})",
                        self.current_time, process.name, process.remaining_time
                    );

                    if process.remaining_time == 0 {
                        println!("进程 {} 执行完成！", process.name);
                    }
                }
            }

            self.current_time += 1;
        }

        println!("调度模拟完成");
    }

    pub fn get_completion_times(&self) -> Vec<(String, u32)> {
        self.processes
            .iter()
            .map(|p| (p.name.clone(), self.current_time))
            .collect()
    }
}

// ============================================================================
// Command 模式
// ============================================================================

/// 系统命令接口
pub trait SystemCommand {
    fn execute(&self) -> Result<String, String>;
    fn undo(&self) -> Result<String, String>;
    fn get_description(&self) -> String;
}

/// 创建文件命令
pub struct CreateFileCommand {
    path: String,
    content: String,
}

impl CreateFileCommand {
    pub fn new(path: String, content: String) -> Self {
        Self { path, content }
    }
}

impl SystemCommand for CreateFileCommand {
    fn execute(&self) -> Result<String, String> {
        // 模拟使用 content，避免未读字段告警
        println!(
            "创建文件: {} (内容大小: {} 字节)",
            self.path,
            self.content.len()
        );
        Ok(format!("文件 {} 创建成功", self.path))
    }

    fn undo(&self) -> Result<String, String> {
        println!("删除文件: {}", self.path);
        Ok(format!("文件 {} 删除成功", self.path))
    }

    fn get_description(&self) -> String {
        format!("创建文件: {}", self.path)
    }
}

/// 创建目录命令
pub struct CreateDirectoryCommand {
    path: String,
}

impl CreateDirectoryCommand {
    pub fn new(path: String) -> Self {
        Self { path }
    }
}

impl SystemCommand for CreateDirectoryCommand {
    fn execute(&self) -> Result<String, String> {
        println!("创建目录: {}", self.path);
        Ok(format!("目录 {} 创建成功", self.path))
    }

    fn undo(&self) -> Result<String, String> {
        println!("删除目录: {}", self.path);
        Ok(format!("目录 {} 删除成功", self.path))
    }

    fn get_description(&self) -> String {
        format!("创建目录: {}", self.path)
    }
}

/// 系统命令管理器
pub struct SystemCommandManager {
    commands: Vec<Box<dyn SystemCommand>>,
    history: Vec<Box<dyn SystemCommand>>,
}

impl SystemCommandManager {
    pub fn new() -> Self {
        Self {
            commands: Vec::new(),
            history: Vec::new(),
        }
    }

    pub fn add_command(&mut self, command: Box<dyn SystemCommand>) {
        self.commands.push(command);
    }

    pub fn execute_all(&mut self) -> Vec<Result<String, String>> {
        let mut results = Vec::new();

        for command in &self.commands {
            match command.execute() {
                Ok(result) => {
                    results.push(Ok(result));
                    // 添加到历史记录
                    // 注意：这里简化了实现，实际应该克隆命令
                }
                Err(error) => {
                    results.push(Err(error));
                }
            }
        }

        results
    }

    pub fn undo_last(&mut self) -> Result<String, String> {
        if let Some(command) = self.history.pop() {
            command.undo()
        } else {
            Err("没有可撤销的命令".to_string())
        }
    }

    pub fn list_commands(&self) -> Vec<String> {
        self.commands
            .iter()
            .map(|cmd| cmd.get_description())
            .collect()
    }
}

// ============================================================================
// 单元测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_singleton_pattern() {
        let singleton = SystemResourceManagerSingleton::new();
        let manager = singleton.get_instance();

        {
            let mut mgr = manager.lock().unwrap();
            mgr.allocate_memory("test_memory".to_string(), 1024)
                .unwrap();
            mgr.create_process();

            assert_eq!(mgr.get_memory_usage(), 1024);
            assert_eq!(mgr.get_process_count(), 1);
        }
    }

    #[test]
    fn test_factory_pattern() {
        let factory = OSDeviceFactory;
        let mut params = HashMap::new();
        params.insert("cores".to_string(), "8".to_string());
        params.insert("frequency".to_string(), "3.2".to_string());

        let device = factory.create_device(DeviceType::CPU, "cpu0".to_string(), params);
        assert_eq!(device.get_type(), DeviceType::CPU);
        assert_eq!(device.get_id(), "cpu0");

        let mut device = device;
        device.initialize().unwrap();
        let status = device.get_status();
        assert!(status.is_online);
    }

    #[test]
    fn test_strategy_pattern() {
        let processes = vec![
            Process {
                id: 1,
                name: "Process A".to_string(),
                priority: 1,
                burst_time: 5,
                arrival_time: 0,
                remaining_time: 5,
            },
            Process {
                id: 2,
                name: "Process B".to_string(),
                priority: 2,
                burst_time: 3,
                arrival_time: 1,
                remaining_time: 3,
            },
        ];

        let fcfs_strategy = FirstComeFirstServeStrategy;
        let sjf_strategy = ShortestJobFirstStrategy;

        let next_fcfs = fcfs_strategy.select_next_process(&processes);
        let next_sjf = sjf_strategy.select_next_process(&processes);

        assert_eq!(next_fcfs, Some(0)); // FCFS选择第一个到达的
        assert_eq!(next_sjf, Some(1)); // SJF选择剩余时间最短的
    }

    #[test]
    fn test_command_pattern() {
        let mut command_manager = SystemCommandManager::new();

        let create_file_cmd =
            CreateFileCommand::new("/tmp/test.txt".to_string(), "Hello, World!".to_string());

        let create_dir_cmd = CreateDirectoryCommand::new("/tmp/test_dir".to_string());

        command_manager.add_command(Box::new(create_file_cmd));
        command_manager.add_command(Box::new(create_dir_cmd));

        let results = command_manager.execute_all();
        assert_eq!(results.len(), 2);

        let commands = command_manager.list_commands();
        assert_eq!(commands.len(), 2);
        assert!(commands[0].contains("创建文件"));
        assert!(commands[1].contains("创建目录"));
    }
}
