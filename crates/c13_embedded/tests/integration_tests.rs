//! 集成测试
//!
//! 验证 c13_embedded 各模块在 host 目标下的正确性。

use c13_embedded::{
    bare_metal_basics::{PanicHandlerConcept, StartupCode},
    ffi_c_interop::{rust_initialize_sensor, CBindingsConcept, SensorData, SensorStatus},
    hal_design_patterns::{states, Spi, UartBuilder, ZeroCostAbstraction},
    interrupt_handling::{CriticalSectionConcept, NvicConcept},
    memory_mapped_registers::{BitOps, GpioRegisters},
    no_std_practices::{CoreUsageDemo, FixedRingBuffer, SpinLockConcept},
    uart_driver::{lsr_flags, UartDriver, UartRegisters},
    get_library_info,
};

#[test]
fn test_library_info() {
    let info = get_library_info();
    assert_eq!(info.name, "c13_embedded");
    assert_eq!(info.target, "host (simulation)");
}

#[test]
fn test_startup_sequence() {
    let seq = StartupCode::startup_sequence();
    assert!(seq.contains("复位"));
    assert!(seq.contains(".data"));
}

#[test]
fn test_panic_handler_concept() {
    assert!(PanicHandlerConcept::description().contains("panic handler"));
}

#[test]
fn test_core_usage() {
    let mut buf = [0u8; 16];
    let len = CoreUsageDemo::format_number(999, &mut buf).unwrap();
    assert_eq!(&buf[..len], b"999");

    assert_eq!(CoreUsageDemo::sum_slice(&[1, 2, 3]), 6);
}

#[test]
fn test_ring_buffer() {
    let mut buf = FixedRingBuffer::<i32, 3>::new();
    assert!(buf.is_empty());

    buf.push(10).unwrap();
    buf.push(20).unwrap();
    buf.push(30).unwrap();
    assert!(buf.push(40).is_err());

    assert_eq!(buf.pop(), Some(10));
    assert_eq!(buf.pop(), Some(20));
    buf.push(40).unwrap();
    assert_eq!(buf.len(), 2);
}

#[test]
fn test_spin_lock_concept() {
    assert!(!SpinLockConcept::description().is_empty());
}

#[test]
fn test_bit_operations() {
    assert_eq!(BitOps::set_bit(0, 0), 1);
    assert_eq!(BitOps::clear_bit(0b1111, 0), 0b1110);
    assert_eq!(BitOps::toggle_bit(0b1010, 1), 0b1000);
    assert!(BitOps::is_bit_set(0b1000, 3));
}

#[test]
fn test_gpio_register_size() {
    assert_eq!(core::mem::size_of::<GpioRegisters>(), 32);
}

#[test]
fn test_uart_driver() {
    let mut uart_mem = UartRegisters {
        thr_rbr: 0,
        ier: 0,
        fcr: 0,
        lcr: 0,
        lsr: lsr_flags::THRE,
    };

    let mut uart = unsafe { UartDriver::new(&mut uart_mem as *mut _ as usize) };
    uart.init();
    assert_eq!(uart_mem.ier, 0);
    assert_eq!(uart_mem.fcr, 0x01);
}

#[test]
fn test_nvic_setup() {
    assert_eq!(NvicConcept::setup_steps().len(), 4);
}

#[test]
fn test_critical_section_practices() {
    assert!(CriticalSectionConcept::best_practices().contains("临界区"));
}

#[test]
fn test_spi_type_state() {
    let spi = Spi::<states::Uninitialized>::new(0x4001_3000);
    let spi = spi.init(8_000_000, 0);
    let spi = spi.send(b"test");
    assert!(spi.is_complete());
    let spi = spi.wait();
    let _spi = spi.deinit();
}

#[test]
fn test_uart_builder() {
    let uart = UartBuilder::new(0x4000_4400)
        .baudrate(115200)
        .data_bits(8)
        .parity(false)
        .build();
    assert!(uart.is_ok());
}

#[test]
fn test_zero_cost_abstraction() {
    let mut reg: u32 = 0;
    ZeroCostAbstraction::set_pin_optimized(&mut reg as *mut u32, 3, true);
}

#[test]
fn test_sensor_data_ffi() {
    assert_eq!(core::mem::size_of::<SensorData>(), 16);

    let status = SensorStatus::Running;
    assert_eq!(status as u32, 2);

    assert_eq!(rust_initialize_sensor(50), 0);
    assert_eq!(rust_initialize_sensor(200), -1);
}

#[test]
fn test_bindgen_workflow() {
    assert!(CBindingsConcept::bindgen_workflow().contains("bindgen"));
}
