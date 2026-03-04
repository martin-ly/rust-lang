# USB-Device协议栈形式化分析

> **主题**: USB设备端协议栈
> **形式化框架**: USB状态机 + 端点管理 + 描述符安全
> **参考**: usb-device crate

---

## 目录

- [USB-Device协议栈形式化分析](#usb-device协议栈形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. USB状态机](#2-usb状态机)
    - [定义 USB-STATE-1 ( 设备状态 )](#定义-usb-state-1--设备状态-)
    - [定义 USB-STATE-2 ( 枚举流程 )](#定义-usb-state-2--枚举流程-)
    - [定理 USB-T1 ( 状态安全 )](#定理-usb-t1--状态安全-)
  - [3. 端点管理](#3-端点管理)
    - [定义 EP-1 ( 端点类型 )](#定义-ep-1--端点类型-)
    - [定义 EP-2 ( 端点状态 )](#定义-ep-2--端点状态-)
    - [定义 EP-3 ( 端点操作 )](#定义-ep-3--端点操作-)
  - [4. 描述符安全](#4-描述符安全)
    - [定义 DESC-1 ( 描述符链 )](#定义-desc-1--描述符链-)
    - [定理 DESC-T1 ( 描述符完整性 )](#定理-desc-t1--描述符完整性-)
  - [5. 类实现](#5-类实现)
    - [定义 CLASS-1 ( CDC ACM )](#定义-class-1--cdc-acm-)
    - [定义 CLASS-2 ( HID )](#定义-class-2--hid-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 USB-T2 ( 端点隔离 )](#定理-usb-t2--端点隔离-)
    - [定理 USB-T3 ( 控制传输优先 )](#定理-usb-t3--控制传输优先-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: USB串口(CDC)](#示例1-usb串口cdc)
    - [示例2: USB HID键盘](#示例2-usb-hid键盘)
    - [示例3: 自定义USB类](#示例3-自定义usb类)

---

## 1. 引言

usb-device为嵌入式USB设备提供：

- USB协议状态机
- 端点抽象
- 描述符管理
- 类驱动框架（CDC、HID、MSC等）

---

## 2. USB状态机

### 定义 USB-STATE-1 ( 设备状态 )

$$
\text{UsbState} = \{
    \text{Default}, \text{Addressed}, \text{Configured}, \text{Suspended}
\}
$$

**状态转换**:

```text
Power On -> Default (总线复位)
Default -> Addressed (SET_ADDRESS)
Addressed -> Configured (SET_CONFIGURATION)
Configured -> Suspended (3ms无活动)
Suspended -> Configured (恢复信号)
```

### 定义 USB-STATE-2 ( 枚举流程 )

$$
\text{Enumeration} = \text{GET\_DESC}(\text{Device}) \to \text{SET\_ADDRESS} \to \text{GET\_DESC}(\text{Config}) \to \text{SET\_CONFIG}
$$

### 定理 USB-T1 ( 状态安全 )

状态转换只能在特定请求后发生。

$$
\delta(s, e) \neq \text{error} \leftrightarrow e \in \text{valid\_events}(s)
$$

---

## 3. 端点管理

### 定义 EP-1 ( 端点类型 )

| 类型 | 方向 | 用途 |
| :--- | :--- | :--- |
| Control | 双向 | 配置 |
| Bulk | 双向 | 数据传输 |
| Interrupt | IN | 事件通知 |
| Isochronous | 双向 | 实时数据 |

### 定义 EP-2 ( 端点状态 )

$$
\text{Endpoint} = \{
    \text{addr} : \text{u8},
    \text{type} : \text{EndpointType},
    \text{max\_packet\_size} : \text{u16},
    \text{buffer} : \text{Buffer}
\}
$$

### 定义 EP-3 ( 端点操作 )

$$
\text{read}(ep, buf) : \text{Endpoint} \times \text{Buffer} \to \text{Result}<\text{usize}, \text{Error}>
$$

$$
\text{write}(ep, data) : \text{Endpoint} \times \text{Data} \to \text{Result}<(), \text{Error}>
$$

---

## 4. 描述符安全

### 定义 DESC-1 ( 描述符链 )

```rust
struct UsbDeviceDescriptor {
    b_length: u8,
    b_descriptor_type: u8,
    bcd_usb: u16,
    b_device_class: u8,
    b_device_sub_class: u8,
    b_device_protocol: u8,
    b_max_packet_size0: u8,
    id_vendor: u16,
    id_product: u16,
    bcd_device: u16,
    i_manufacturer: u8,
    i_product: u8,
    i_serial_number: u8,
    b_num_configurations: u8,
}
```

### 定理 DESC-T1 ( 描述符完整性 )

所有描述符必须满足USB规范约束。

$$
\forall d : \text{Descriptor}.\ \text{validate}(d) \to \text{USB\_Spec}(d)
$$

---

## 5. 类实现

### 定义 CLASS-1 ( CDC ACM )

通信设备类 - 虚拟串口。

$$
\text{CDC\_ACM} = \{
    \text{control\_ep} : \text{Endpoint},
    \text{data\_in} : \text{Endpoint},
    \text{data\_out} : \text{Endpoint},
    \text{line\_coding} : \text{LineCoding}
\}
$$

### 定义 CLASS-2 ( HID )

人机接口设备 - 键盘/鼠标。

$$
\text{HID} = \{
    \text{in\_ep} : \text{Endpoint},
    \text{report\_descriptor} : \text{ReportDesc},
    \text{poll\_interval} : \text{u8}
\}
$$

---

## 6. 定理与证明

### 定理 USB-T2 ( 端点隔离 )

不同端点的数据传输相互隔离。

$$
\forall ep_1 \neq ep_2.\ \text{data}(ep_1) \cap \text{data}(ep_2) = \emptyset
$$

**证明**: 端点有独立硬件缓冲区和地址。$\square$

### 定理 USB-T3 ( 控制传输优先 )

控制端点(EP0)优先于其他端点。

$$
\text{priority}(EP0) > \text{priority}(EPn), n > 0
$$

---

## 7. 代码示例

### 示例1: USB串口(CDC)

```rust
use usb_device::{bus::UsbBusAllocator, device::{UsbDevice, UsbDeviceBuilder, UsbVidPid}};
use usb_device::class::cdc_acm::{CDCACMClass, Sender, Receiver};

fn usb_cdc_example() {
    static mut USB_BUS: Option<UsbBusAllocator<UsbBus>> = None;

    let usb = USB::new();
    let bus_allocator = UsbBusAllocator::new(usb);

    unsafe {
        USB_BUS = Some(bus_allocator);
    }

    let bus = unsafe { USB_BUS.as_ref().unwrap() };

    let mut serial = CDCACMClass::new(bus, 64);

    let mut usb_dev = UsbDeviceBuilder::new(bus, UsbVidPid(0x16c0, 0x27dd))
        .manufacturer("Example")
        .product("Serial Port")
        .serial_number("TEST")
        .device_class(0x02)  // CDC
        .build();

    loop {
        if !usb_dev.poll(&mut [&mut serial]) {
            continue;
        }

        let mut buf = [0u8; 64];
        match serial.read(&mut buf) {
            Ok(count) if count > 0 => {
                // 回声
                let _ = serial.write(&buf[..count]);
            }
            _ => {}
        }
    }
}
```

### 示例2: USB HID键盘

```rust
use usb_device::class::hid::HIDClass;

struct KeyboardReport {
    modifier: u8,
    reserved: u8,
    keycodes: [u8; 6],
}

fn usb_hid_keyboard() {
    static REPORT_DESC: &[u8] = &[
        0x05, 0x01,  // Usage Page (Generic Desktop)
        0x09, 0x06,  // Usage (Keyboard)
        0xa1, 0x01,  // Collection (Application)
        // ... 更多描述符
        0xc0,        // End Collection
    ];

    let bus = unsafe { USB_BUS.as_ref().unwrap() };
    let mut hid = HIDClass::new(bus, REPORT_DESC, 10);

    let mut usb_dev = UsbDeviceBuilder::new(bus, UsbVidPid(0x16c0, 0x27dd))
        .device_class(0x00)  // HID
        .build();

    loop {
        usb_dev.poll(&mut [&mut hid]);

        // 发送按键报告
        let report = KeyboardReport {
            modifier: 0,
            reserved: 0,
            keycodes: [0x04, 0, 0, 0, 0, 0],  // 'a'
        };

        hid.push_input(&report).ok();

        // 释放按键
        let release = KeyboardReport {
            modifier: 0,
            reserved: 0,
            keycodes: [0; 6],
        };
        hid.push_input(&release).ok();
    }
}
```

### 示例3: 自定义USB类

```rust
use usb_device::class::UsbClass;
use usb_device::endpoint::{EndpointType, EndpointAddress};

struct CustomClass<'a, B: UsbBus> {
    interface: InterfaceNumber,
    endpoint_in: EndpointIn<'a, B>,
    endpoint_out: EndpointOut<'a, B>,
}

impl<'a, B: UsbBus> CustomClass<'a, B> {
    fn new(alloc: &'a UsbBusAllocator<B>) -> Self {
        Self {
            interface: alloc.interface(),
            endpoint_in: alloc.bulk(64),
            endpoint_out: alloc.bulk(64),
        }
    }

    fn write(&mut self, data: &[u8]) -> Result<usize, UsbError> {
        self.endpoint_in.write(data)
    }

    fn read(&mut self, buf: &mut [u8]) -> Result<usize, UsbError> {
        self.endpoint_out.read(buf)
    }
}

impl<B: UsbBus> UsbClass<B> for CustomClass<'_, B> {
    fn get_configuration_descriptors(&self, writer: &mut DescriptorWriter) -> UsbResult<()> {
        writer.interface(self.interface, 0xFF, 0x00, 0x00)?;
        writer.endpoint(&self.endpoint_in)?;
        writer.endpoint(&self.endpoint_out)?;
        Ok(())
    }
}
```

---

**维护者**: Rust Embedded Formal Methods Team
**创建日期**: 2026-03-05
**状态**: ✅ 已对齐
