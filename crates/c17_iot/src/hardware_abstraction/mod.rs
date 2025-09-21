//! 硬件抽象层模块
//! 
//! 本模块提供了基于Rust 1.90的硬件抽象层，包括：
//! - GPIO控制
//! - I2C通信
//! - SPI通信
//! - UART通信
//! - PWM控制
//! - ADC/DAC转换
//! - CAN总线
//! - 以太网接口
//! - 硬件定时器
//! - 中断处理

pub mod gpio;
// pub mod i2c;
// pub mod spi;
// pub mod uart;
// pub mod pwm;
// pub mod adc_dac;
// pub mod can;
// pub mod ethernet;
// pub mod timer;
// pub mod interrupt;
// pub mod device_manager;

pub use gpio::{GPIOPin, GPIOManager, PinMode, PinState};
// pub use i2c::{I2CDevice, I2CManager, I2CError};
// pub use spi::{SPIDevice, SPIManager, SPIMode, SPIBitOrder};
// pub use uart::{UARTDevice, UARTManager, UARTConfig, BaudRate};
// pub use pwm::{PWMChannel, PWMManager, PWMConfig};
// pub use adc_dac::{ADCChannel, DACChannel, ADCManager, DACManager};
// pub use can::{CANDevice, CANManager, CANMessage, CANError};
// pub use ethernet::{EthernetInterface, EthernetManager, EthernetConfig};
// pub use timer::{HardwareTimer, TimerManager, TimerConfig};
// pub use interrupt::{InterruptHandler, InterruptManager, InterruptType};
// pub use device_manager::{HardwareDeviceManager, DeviceType, DeviceInfo};

/// 硬件抽象层错误类型
#[derive(Debug, thiserror::Error)]
pub enum HALError {
    #[error("设备初始化失败: {0}")]
    InitializationFailed(String),
    
    #[error("设备未找到: {0}")]
    DeviceNotFound(String),
    
    #[error("设备忙: {0}")]
    DeviceBusy(String),
    
    #[error("通信错误: {0}")]
    CommunicationError(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("权限错误: {0}")]
    PermissionError(String),
    
    #[error("超时错误: {0}")]
    TimeoutError(String),
    
    #[error("硬件错误: {0}")]
    HardwareError(String),
    
    #[error("不支持的操作: {0}")]
    UnsupportedOperation(String),
}

/// 硬件平台类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HardwarePlatform {
    /// Raspberry Pi
    RaspberryPi,
    /// STM32系列
    STM32,
    /// Nordic nRF系列
    NordicNRF,
    /// ESP32系列
    ESP32,
    /// 通用Linux设备
    Linux,
    /// 模拟器
    Simulator,
}

/// 硬件信息
#[derive(Debug, Clone)]
pub struct HardwareInfo {
    pub platform: HardwarePlatform,
    pub model: String,
    pub version: String,
    pub cpu_cores: u32,
    pub memory_total: usize,
    pub gpio_pins: u32,
    pub i2c_buses: u32,
    pub spi_buses: u32,
    pub uart_ports: u32,
    pub pwm_channels: u32,
    pub adc_channels: u32,
    pub dac_channels: u32,
    pub can_buses: u32,
    pub ethernet_ports: u32,
    pub timers: u32,
}

/// 硬件抽象层管理器
pub struct HALManager {
    platform: HardwarePlatform,
    hardware_info: Option<HardwareInfo>,
    gpio_manager: GPIOManager,
    // i2c_manager: I2CManager,
    // spi_manager: SPIManager,
    // uart_manager: UARTManager,
    // pwm_manager: PWMManager,
    // adc_manager: ADCManager,
    // dac_manager: DACManager,
    // can_manager: CANManager,
    // ethernet_manager: EthernetManager,
    // timer_manager: TimerManager,
    // interrupt_manager: InterruptManager,
    // device_manager: HardwareDeviceManager,
}

impl HALManager {
    /// 创建新的硬件抽象层管理器
    pub fn new(platform: HardwarePlatform) -> Self {
        Self {
            platform,
            hardware_info: None,
            gpio_manager: GPIOManager::new(),
            // i2c_manager: I2CManager::new(),
            // spi_manager: SPIManager::new(),
            // uart_manager: UARTManager::new(),
            // pwm_manager: PWMManager::new(),
            // adc_manager: ADCManager::new(),
            // dac_manager: DACManager::new(),
            // can_manager: CANManager::new(),
            // ethernet_manager: EthernetManager::new(),
            // timer_manager: TimerManager::new(),
            // interrupt_manager: InterruptManager::new(),
            // device_manager: HardwareDeviceManager::new(),
        }
    }

    /// 初始化硬件抽象层
    pub async fn initialize(&mut self) -> Result<(), HALError> {
        // 检测硬件平台
        let hardware_info = self.detect_hardware().await?;
        self.hardware_info = Some(hardware_info);

        // 初始化各个管理器
        self.gpio_manager.initialize().await?;
        // self.i2c_manager.initialize().await?;
        // self.spi_manager.initialize().await?;
        // self.uart_manager.initialize().await?;
        // self.pwm_manager.initialize().await?;
        // self.adc_manager.initialize().await?;
        // self.dac_manager.initialize().await?;
        // self.can_manager.initialize().await?;
        // self.ethernet_manager.initialize().await?;
        // self.timer_manager.initialize().await?;
        // self.interrupt_manager.initialize().await?;
        // self.device_manager.initialize().await?;

        Ok(())
    }

    /// 检测硬件平台
    async fn detect_hardware(&self) -> Result<HardwareInfo, HALError> {
        match self.platform {
            HardwarePlatform::RaspberryPi => {
                Ok(HardwareInfo {
                    platform: HardwarePlatform::RaspberryPi,
                    model: "Raspberry Pi 4".to_string(),
                    version: "1.0".to_string(),
                    cpu_cores: 4,
                    memory_total: 4 * 1024 * 1024 * 1024, // 4GB
                    gpio_pins: 40,
                    i2c_buses: 2,
                    spi_buses: 2,
                    uart_ports: 2,
                    pwm_channels: 4,
                    adc_channels: 0, // 需要外部ADC
                    dac_channels: 0, // 需要外部DAC
                    can_buses: 0,    // 需要外部CAN接口
                    ethernet_ports: 1,
                    timers: 4,
                })
            }
            HardwarePlatform::STM32 => {
                Ok(HardwareInfo {
                    platform: HardwarePlatform::STM32,
                    model: "STM32F4".to_string(),
                    version: "1.0".to_string(),
                    cpu_cores: 1,
                    memory_total: 256 * 1024, // 256KB
                    gpio_pins: 82,
                    i2c_buses: 3,
                    spi_buses: 3,
                    uart_ports: 6,
                    pwm_channels: 12,
                    adc_channels: 16,
                    dac_channels: 2,
                    can_buses: 2,
                    ethernet_ports: 1,
                    timers: 14,
                })
            }
            HardwarePlatform::NordicNRF => {
                Ok(HardwareInfo {
                    platform: HardwarePlatform::NordicNRF,
                    model: "nRF52840".to_string(),
                    version: "1.0".to_string(),
                    cpu_cores: 1,
                    memory_total: 256 * 1024, // 256KB
                    gpio_pins: 48,
                    i2c_buses: 2,
                    spi_buses: 3,
                    uart_ports: 1,
                    pwm_channels: 4,
                    adc_channels: 8,
                    dac_channels: 1,
                    can_buses: 0,
                    ethernet_ports: 0,
                    timers: 5,
                })
            }
            HardwarePlatform::ESP32 => {
                Ok(HardwareInfo {
                    platform: HardwarePlatform::ESP32,
                    model: "ESP32".to_string(),
                    version: "1.0".to_string(),
                    cpu_cores: 2,
                    memory_total: 520 * 1024, // 520KB
                    gpio_pins: 34,
                    i2c_buses: 2,
                    spi_buses: 4,
                    uart_ports: 3,
                    pwm_channels: 16,
                    adc_channels: 18,
                    dac_channels: 2,
                    can_buses: 1,
                    ethernet_ports: 0,
                    timers: 4,
                })
            }
            HardwarePlatform::Linux => {
                Ok(HardwareInfo {
                    platform: HardwarePlatform::Linux,
                    model: "Generic Linux".to_string(),
                    version: "1.0".to_string(),
                    cpu_cores: 4,
                    memory_total: 8 * 1024 * 1024 * 1024, // 8GB
                    gpio_pins: 0, // 通过sysfs访问
                    i2c_buses: 0, // 通过i2c-dev访问
                    spi_buses: 0, // 通过spidev访问
                    uart_ports: 0, // 通过tty访问
                    pwm_channels: 0, // 通过sysfs访问
                    adc_channels: 0, // 需要外部设备
                    dac_channels: 0, // 需要外部设备
                    can_buses: 0, // 通过socketcan访问
                    ethernet_ports: 1,
                    timers: 0, // 通过系统调用访问
                })
            }
            HardwarePlatform::Simulator => {
                Ok(HardwareInfo {
                    platform: HardwarePlatform::Simulator,
                    model: "Hardware Simulator".to_string(),
                    version: "1.0".to_string(),
                    cpu_cores: 1,
                    memory_total: 64 * 1024, // 64KB
                    gpio_pins: 16,
                    i2c_buses: 1,
                    spi_buses: 1,
                    uart_ports: 1,
                    pwm_channels: 4,
                    adc_channels: 8,
                    dac_channels: 2,
                    can_buses: 1,
                    ethernet_ports: 1,
                    timers: 2,
                })
            }
        }
    }

    /// 获取硬件信息
    pub fn get_hardware_info(&self) -> Result<&HardwareInfo, HALError> {
        self.hardware_info.as_ref()
            .ok_or_else(|| HALError::InitializationFailed("硬件信息未初始化".to_string()))
    }

    /// 获取GPIO管理器
    pub fn gpio(&self) -> &GPIOManager {
        &self.gpio_manager
    }

    // /// 获取I2C管理器
    // pub fn i2c(&self) -> &I2CManager {
    //     &self.i2c_manager
    // }

    // /// 获取SPI管理器
    // pub fn spi(&self) -> &SPIManager {
    //     &self.spi_manager
    // }

    // /// 获取UART管理器
    // pub fn uart(&self) -> &UARTManager {
    //     &self.uart_manager
    // }

    // /// 获取PWM管理器
    // pub fn pwm(&self) -> &PWMManager {
    //     &self.pwm_manager
    // }

    // /// 获取ADC管理器
    // pub fn adc(&self) -> &ADCManager {
    //     &self.adc_manager
    // }

    // /// 获取DAC管理器
    // pub fn dac(&self) -> &DACManager {
    //     &self.dac_manager
    // }

    // /// 获取CAN管理器
    // pub fn can(&self) -> &CANManager {
    //     &self.can_manager
    // }

    // /// 获取以太网管理器
    // pub fn ethernet(&self) -> &EthernetManager {
    //     &self.ethernet_manager
    // }

    // /// 获取定时器管理器
    // pub fn timer(&self) -> &TimerManager {
    //     &self.timer_manager
    // }

    // /// 获取中断管理器
    // pub fn interrupt(&self) -> &InterruptManager {
    //     &self.interrupt_manager
    // }

    // /// 获取设备管理器
    // pub fn device(&self) -> &HardwareDeviceManager {
    //     &self.device_manager
    // }
}

/// 硬件抽象层结果类型
pub type HALResult<T> = Result<T, HALError>;
