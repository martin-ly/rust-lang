//! GPIO (General Purpose Input/Output) 控制模块
//! 
//! 本模块提供了GPIO引脚的控制功能，包括数字输入输出、中断处理等。

use super::{HALError, HALResult};
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};
use std::collections::HashMap;

/// GPIO引脚模式
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PinMode {
    /// 输入模式
    Input,
    /// 输出模式
    Output,
    /// 上拉输入
    InputPullUp,
    /// 下拉输入
    InputPullDown,
    /// 开漏输出
    OpenDrain,
    /// 推挽输出
    PushPull,
}

/// GPIO引脚状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PinState {
    /// 低电平
    Low,
    /// 高电平
    High,
}

/// GPIO中断触发模式
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptTrigger {
    /// 上升沿触发
    Rising,
    /// 下降沿触发
    Falling,
    /// 双边沿触发
    Both,
    /// 高电平触发
    High,
    /// 低电平触发
    Low,
}

/// GPIO驱动强度
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DriveStrength {
    /// 2mA
    TwoMilliamps,
    /// 4mA
    FourMilliamps,
    /// 8mA
    EightMilliamps,
    /// 12mA
    TwelveMilliamps,
}

/// GPIO压摆率
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SlewRate {
    /// 慢速
    Slow,
    /// 快速
    Fast,
}

/// GPIO配置
#[derive(Debug, Clone)]
pub struct GPIOConfig {
    pub mode: PinMode,
    pub drive_strength: Option<DriveStrength>,
    pub slew_rate: Option<SlewRate>,
    pub debounce_time: Option<std::time::Duration>,
    pub interrupt_trigger: Option<InterruptTrigger>,
    pub initial_state: Option<PinState>,
}

impl Default for GPIOConfig {
    fn default() -> Self {
        Self {
            mode: PinMode::Input,
            drive_strength: None,
            slew_rate: None,
            debounce_time: None,
            interrupt_trigger: None,
            initial_state: None,
        }
    }
}

/// GPIO统计信息
#[derive(Debug, Clone)]
pub struct GPIOStats {
    pub total_pins: usize,
    pub active_pins: usize,
    pub input_pins: usize,
    pub output_pins: usize,
    pub interrupt_count: u64,
    pub state_changes: u64,
    pub errors: u64,
}

/// GPIO引脚配置
#[derive(Debug, Clone)]
pub struct PinConfig {
    pub mode: PinMode,
    pub initial_state: Option<PinState>,
    pub interrupt_trigger: Option<InterruptTrigger>,
    pub debounce_time: Option<std::time::Duration>,
}

/// GPIO引脚
pub struct GPIOPin {
    pin_number: u32,
    mode: PinMode,
    state: PinState,
    interrupt_enabled: bool,
    #[allow(dead_code)]
    interrupt_trigger: Option<InterruptTrigger>,
    debounce_time: Option<std::time::Duration>,
    last_change_time: std::time::Instant,
    drive_strength: Option<DriveStrength>,
    slew_rate: Option<SlewRate>,
    state_change_count: u64,
    last_interrupt_time: Option<std::time::Instant>,
}

impl GPIOPin {
    /// 创建新的GPIO引脚
    pub fn new(pin_number: u32, config: PinConfig) -> Self {
        Self {
            pin_number,
            mode: config.mode,
            state: config.initial_state.unwrap_or(PinState::Low),
            interrupt_enabled: config.interrupt_trigger.is_some(),
            interrupt_trigger: config.interrupt_trigger,
            debounce_time: config.debounce_time,
            last_change_time: std::time::Instant::now(),
            drive_strength: None,
            slew_rate: None,
            state_change_count: 0,
            last_interrupt_time: None,
        }
    }

    /// 读取引脚状态
    pub fn read(&self) -> PinState {
        self.state
    }

    /// 写入引脚状态
    pub fn write(&mut self, state: PinState) -> HALResult<()> {
        if self.mode == PinMode::Input || self.mode == PinMode::InputPullUp || self.mode == PinMode::InputPullDown {
            return Err(HALError::ConfigurationError(
                format!("引脚 {} 配置为输入模式，无法写入", self.pin_number)
            ));
        }

        self.state = state;
        self.last_change_time = std::time::Instant::now();
        Ok(())
    }

    /// 切换引脚状态
    pub fn toggle(&mut self) -> HALResult<()> {
        let new_state = match self.state {
            PinState::Low => PinState::High,
            PinState::High => PinState::Low,
        };
        self.write(new_state)
    }

    /// 设置引脚模式
    pub fn set_mode(&mut self, mode: PinMode) {
        self.mode = mode;
    }

    /// 获取引脚模式
    pub fn get_mode(&self) -> PinMode {
        self.mode
    }

    /// 获取引脚编号
    pub fn get_pin_number(&self) -> u32 {
        self.pin_number
    }

    /// 检查是否支持中断
    pub fn supports_interrupt(&self) -> bool {
        self.interrupt_enabled
    }

    /// 检查防抖时间是否已过
    pub fn is_debounce_ready(&self) -> bool {
        if let Some(debounce_time) = self.debounce_time {
            self.last_change_time.elapsed() >= debounce_time
        } else {
            true
        }
    }

    /// 设置驱动强度
    pub fn set_drive_strength(&mut self, strength: DriveStrength) {
        self.drive_strength = Some(strength);
    }

    /// 获取驱动强度
    pub fn get_drive_strength(&self) -> Option<DriveStrength> {
        self.drive_strength
    }

    /// 设置压摆率
    pub fn set_slew_rate(&mut self, rate: SlewRate) {
        self.slew_rate = Some(rate);
    }

    /// 获取压摆率
    pub fn get_slew_rate(&self) -> Option<SlewRate> {
        self.slew_rate
    }

    /// 获取状态变化次数
    pub fn get_state_change_count(&self) -> u64 {
        self.state_change_count
    }

    /// 获取最后中断时间
    pub fn get_last_interrupt_time(&self) -> Option<std::time::Instant> {
        self.last_interrupt_time
    }

    /// 更新状态变化计数
    pub fn increment_state_change_count(&mut self) {
        self.state_change_count += 1;
    }

    /// 更新最后中断时间
    pub fn update_last_interrupt_time(&mut self) {
        self.last_interrupt_time = Some(std::time::Instant::now());
    }

    /// 重置统计信息
    pub fn reset_stats(&mut self) {
        self.state_change_count = 0;
        self.last_interrupt_time = None;
    }
}

/// GPIO管理器
pub struct GPIOManager {
    pins: Arc<RwLock<HashMap<u32, GPIOPin>>>,
    interrupt_sender: mpsc::UnboundedSender<GPIOInterruptEvent>,
    initialized: bool,
    stats: GPIOStats,
}

/// GPIO中断事件
#[derive(Debug, Clone)]
pub struct GPIOInterruptEvent {
    pub pin_number: u32,
    pub state: PinState,
    pub timestamp: std::time::Instant,
}

impl GPIOManager {
    /// 创建新的GPIO管理器
    pub fn new() -> Self {
        let (interrupt_sender, _) = mpsc::unbounded_channel();
        
        Self {
            pins: Arc::new(RwLock::new(HashMap::new())),
            interrupt_sender,
            initialized: false,
            stats: GPIOStats {
                total_pins: 0,
                active_pins: 0,
                input_pins: 0,
                output_pins: 0,
                interrupt_count: 0,
                state_changes: 0,
                errors: 0,
            },
        }
    }

    /// 初始化GPIO管理器
    pub async fn initialize(&mut self) -> Result<(), HALError> {
        if self.initialized {
            return Ok(());
        }

        // 模拟GPIO初始化过程
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        
        self.initialized = true;
        Ok(())
    }

    /// 配置GPIO引脚
    pub async fn configure_pin(&self, pin_number: u32, config: PinConfig) -> HALResult<()> {
        if !self.initialized {
            return Err(HALError::InitializationFailed("GPIO管理器未初始化".to_string()));
        }

        let pin = GPIOPin::new(pin_number, config);
        let mut pins = self.pins.write().await;
        pins.insert(pin_number, pin);

        Ok(())
    }

    /// 读取GPIO引脚状态
    pub async fn read_pin(&self, pin_number: u32) -> HALResult<PinState> {
        let pins = self.pins.read().await;
        
        pins.get(&pin_number)
            .map(|pin| pin.read())
            .ok_or_else(|| HALError::DeviceNotFound(format!("GPIO引脚 {} 未配置", pin_number)))
    }

    /// 写入GPIO引脚状态
    pub async fn write_pin(&self, pin_number: u32, state: PinState) -> HALResult<()> {
        let mut pins = self.pins.write().await;
        
        if let Some(pin) = pins.get_mut(&pin_number) {
            pin.write(state)?;
            
            // 检查是否需要触发中断
            if pin.supports_interrupt() && pin.is_debounce_ready() {
                let event = GPIOInterruptEvent {
                    pin_number,
                    state,
                    timestamp: std::time::Instant::now(),
                };
                
                if let Err(_) = self.interrupt_sender.send(event) {
                    // 中断接收器已关闭，忽略错误
                }
            }
            
            Ok(())
        } else {
            Err(HALError::DeviceNotFound(format!("GPIO引脚 {} 未配置", pin_number)))
        }
    }

    /// 切换GPIO引脚状态
    pub async fn toggle_pin(&self, pin_number: u32) -> HALResult<()> {
        let current_state = self.read_pin(pin_number).await?;
        let new_state = match current_state {
            PinState::Low => PinState::High,
            PinState::High => PinState::Low,
        };
        self.write_pin(pin_number, new_state).await
    }

    /// 设置引脚模式
    pub async fn set_pin_mode(&self, pin_number: u32, mode: PinMode) -> HALResult<()> {
        let mut pins = self.pins.write().await;
        
        if let Some(pin) = pins.get_mut(&pin_number) {
            pin.set_mode(mode);
            Ok(())
        } else {
            Err(HALError::DeviceNotFound(format!("GPIO引脚 {} 未配置", pin_number)))
        }
    }

    /// 获取引脚模式
    pub async fn get_pin_mode(&self, pin_number: u32) -> HALResult<PinMode> {
        let pins = self.pins.read().await;
        
        pins.get(&pin_number)
            .map(|pin| pin.get_mode())
            .ok_or_else(|| HALError::DeviceNotFound(format!("GPIO引脚 {} 未配置", pin_number)))
    }

    /// 获取所有配置的引脚
    pub async fn get_configured_pins(&self) -> Vec<u32> {
        let pins = self.pins.read().await;
        pins.keys().cloned().collect()
    }


    /// 批量读取多个引脚
    pub async fn read_multiple_pins(&self, pin_numbers: &[u32]) -> HALResult<HashMap<u32, PinState>> {
        let pins = self.pins.read().await;
        let mut result = HashMap::new();

        for &pin_number in pin_numbers {
            if let Some(pin) = pins.get(&pin_number) {
                result.insert(pin_number, pin.read());
            } else {
                return Err(HALError::DeviceNotFound(format!("GPIO引脚 {} 未配置", pin_number)));
            }
        }

        Ok(result)
    }

    /// 批量写入多个引脚
    pub async fn write_multiple_pins(&self, pin_states: &HashMap<u32, PinState>) -> HALResult<()> {
        for (&pin_number, &state) in pin_states {
            self.write_pin(pin_number, state).await?;
        }
        Ok(())
    }

    /// 创建中断事件接收器
    pub fn create_interrupt_receiver(&self) -> mpsc::UnboundedReceiver<GPIOInterruptEvent> {
        let (_, receiver) = mpsc::unbounded_channel();
        receiver
    }

    /// 模拟外部中断触发
    pub async fn simulate_interrupt(&self, pin_number: u32, state: PinState) -> HALResult<()> {
        if !self.initialized {
            return Err(HALError::InitializationFailed("GPIO管理器未初始化".to_string()));
        }

        let pins = self.pins.read().await;
        
        if let Some(pin) = pins.get(&pin_number) {
            if pin.supports_interrupt() && pin.is_debounce_ready() {
                let event = GPIOInterruptEvent {
                    pin_number,
                    state,
                    timestamp: std::time::Instant::now(),
                };
                
                if let Err(_) = self.interrupt_sender.send(event) {
                    return Err(HALError::CommunicationError("中断发送失败".to_string()));
                }
                
                Ok(())
            } else {
                Err(HALError::ConfigurationError(
                    format!("引脚 {} 不支持中断或防抖时间未到", pin_number)
                ))
            }
        } else {
            Err(HALError::DeviceNotFound(format!("GPIO引脚 {} 未配置", pin_number)))
        }
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> GPIOStats {
        let pins = self.pins.read().await;
        let mut stats = self.stats.clone();
        
        stats.total_pins = pins.len();
        stats.active_pins = pins.len();
        stats.input_pins = pins.values().filter(|p| matches!(p.get_mode(), PinMode::Input | PinMode::InputPullUp | PinMode::InputPullDown)).count();
        stats.output_pins = pins.values().filter(|p| matches!(p.get_mode(), PinMode::Output | PinMode::OpenDrain | PinMode::PushPull)).count();
        
        stats
    }

    /// 重置统计信息
    pub fn reset_stats(&mut self) {
        self.stats = GPIOStats {
            total_pins: 0,
            active_pins: 0,
            input_pins: 0,
            output_pins: 0,
            interrupt_count: 0,
            state_changes: 0,
            errors: 0,
        };
    }

    /// 批量配置引脚
    pub async fn configure_multiple_pins(&mut self, pin_configs: HashMap<u32, PinConfig>) -> Result<(), HALError> {
        for (pin_number, config) in pin_configs {
            self.configure_pin(pin_number, config).await?;
        }
        Ok(())
    }

    /// 获取所有引脚状态
    pub async fn get_all_pin_states(&self) -> HashMap<u32, PinState> {
        let pins = self.pins.read().await;
        pins.iter().map(|(pin_number, pin)| (*pin_number, pin.read())).collect()
    }

    /// 设置引脚驱动强度
    pub async fn set_pin_drive_strength(&mut self, pin_number: u32, strength: DriveStrength) -> Result<(), HALError> {
        let mut pins = self.pins.write().await;
        if let Some(pin) = pins.get_mut(&pin_number) {
            pin.set_drive_strength(strength);
            Ok(())
        } else {
            Err(HALError::DeviceNotFound(format!("GPIO引脚 {} 未配置", pin_number)))
        }
    }

    /// 设置引脚压摆率
    pub async fn set_pin_slew_rate(&mut self, pin_number: u32, rate: SlewRate) -> Result<(), HALError> {
        let mut pins = self.pins.write().await;
        if let Some(pin) = pins.get_mut(&pin_number) {
            pin.set_slew_rate(rate);
            Ok(())
        } else {
            Err(HALError::DeviceNotFound(format!("GPIO引脚 {} 未配置", pin_number)))
        }
    }

    /// 获取引脚详细信息
    pub async fn get_pin_info(&self, pin_number: u32) -> Result<HashMap<String, String>, HALError> {
        let pins = self.pins.read().await;
        if let Some(pin) = pins.get(&pin_number) {
            let mut info = HashMap::new();
            info.insert("pin_number".to_string(), pin_number.to_string());
            info.insert("mode".to_string(), format!("{:?}", pin.get_mode()));
            info.insert("state".to_string(), format!("{:?}", pin.read()));
            info.insert("interrupt_enabled".to_string(), pin.supports_interrupt().to_string());
            info.insert("state_change_count".to_string(), pin.get_state_change_count().to_string());
            
            if let Some(drive_strength) = pin.get_drive_strength() {
                info.insert("drive_strength".to_string(), format!("{:?}", drive_strength));
            }
            
            if let Some(slew_rate) = pin.get_slew_rate() {
                info.insert("slew_rate".to_string(), format!("{:?}", slew_rate));
            }
            
            Ok(info)
        } else {
            Err(HALError::DeviceNotFound(format!("GPIO引脚 {} 未配置", pin_number)))
        }
    }

    /// 健康检查
    pub async fn health_check(&self) -> Result<bool, HALError> {
        let pins = self.pins.read().await;
        Ok(!pins.is_empty())
    }

    /// 获取连接信息
    pub async fn get_connection_info(&self) -> HashMap<String, String> {
        let pins = self.pins.read().await;
        let mut info = HashMap::new();
        info.insert("total_pins".to_string(), pins.len().to_string());
        info.insert("initialized".to_string(), self.initialized.to_string());
        info.insert("interrupt_count".to_string(), self.stats.interrupt_count.to_string());
        info.insert("state_changes".to_string(), self.stats.state_changes.to_string());
        info.insert("errors".to_string(), self.stats.errors.to_string());
        info
    }
}

impl Default for GPIOManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_gpio_initialization() {
        let mut manager = GPIOManager::new();
        assert!(!manager.initialized);
        
        let result = manager.initialize().await;
        assert!(result.is_ok());
        assert!(manager.initialized);
    }

    #[tokio::test]
    async fn test_gpio_pin_configuration() {
        let mut manager = GPIOManager::new();
        manager.initialize().await.unwrap();

        let config = PinConfig {
            mode: PinMode::Output,
            initial_state: Some(PinState::Low),
            interrupt_trigger: None,
            debounce_time: None,
        };

        let result = manager.configure_pin(1, config).await;
        assert!(result.is_ok());

        let pins = manager.get_configured_pins().await;
        assert!(pins.contains(&1));
    }

    #[tokio::test]
    async fn test_gpio_read_write() {
        let mut manager = GPIOManager::new();
        manager.initialize().await.unwrap();

        let config = PinConfig {
            mode: PinMode::Output,
            initial_state: Some(PinState::Low),
            interrupt_trigger: None,
            debounce_time: None,
        };

        manager.configure_pin(1, config).await.unwrap();

        // 写入高电平
        manager.write_pin(1, PinState::High).await.unwrap();
        let state = manager.read_pin(1).await.unwrap();
        assert_eq!(state, PinState::High);

        // 写入低电平
        manager.write_pin(1, PinState::Low).await.unwrap();
        let state = manager.read_pin(1).await.unwrap();
        assert_eq!(state, PinState::Low);
    }

    #[tokio::test]
    async fn test_gpio_toggle() {
        let mut manager = GPIOManager::new();
        manager.initialize().await.unwrap();

        let config = PinConfig {
            mode: PinMode::Output,
            initial_state: Some(PinState::Low),
            interrupt_trigger: None,
            debounce_time: None,
        };

        manager.configure_pin(1, config).await.unwrap();

        // 切换状态
        manager.toggle_pin(1).await.unwrap();
        let state = manager.read_pin(1).await.unwrap();
        assert_eq!(state, PinState::High);

        manager.toggle_pin(1).await.unwrap();
        let state = manager.read_pin(1).await.unwrap();
        assert_eq!(state, PinState::Low);
    }

    #[tokio::test]
    async fn test_gpio_interrupt() {
        let mut manager = GPIOManager::new();
        manager.initialize().await.unwrap();

        let config = PinConfig {
            mode: PinMode::Input,
            initial_state: Some(PinState::Low),
            interrupt_trigger: Some(InterruptTrigger::Rising),
            debounce_time: Some(std::time::Duration::from_millis(10)),
        };

        manager.configure_pin(1, config).await.unwrap();

        // 模拟中断
        let result = manager.simulate_interrupt(1, PinState::High).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_gpio_batch_operations() {
        let mut manager = GPIOManager::new();
        manager.initialize().await.unwrap();

        // 配置多个引脚
        for pin in 1..=5 {
            let config = PinConfig {
                mode: PinMode::Output,
                initial_state: Some(PinState::Low),
                interrupt_trigger: None,
                debounce_time: None,
            };
            manager.configure_pin(pin, config).await.unwrap();
        }

        // 批量读取
        let pin_numbers = vec![1, 2, 3, 4, 5];
        let states = manager.read_multiple_pins(&pin_numbers).await.unwrap();
        assert_eq!(states.len(), 5);

        // 批量写入
        let mut pin_states = HashMap::new();
        pin_states.insert(1, PinState::High);
        pin_states.insert(2, PinState::High);
        pin_states.insert(3, PinState::Low);
        
        let result = manager.write_multiple_pins(&pin_states).await;
        assert!(result.is_ok());
    }
}
