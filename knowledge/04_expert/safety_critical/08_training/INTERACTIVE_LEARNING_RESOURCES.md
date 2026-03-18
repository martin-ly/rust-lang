# 交互式学习资源

## 概述

本文档收集Rust安全关键系统开发的交互式学习资源，包括在线课程、实验平台、虚拟环境等。

---

## 1. 在线学习平台

### 1.1 官方资源

```
Rust官方:
├── The Rust Book (中文/英文)
│   └── https://doc.rust-lang.org/book/
│
├── Rustlings (交互式练习)
│   └── https://github.com/rust-lang/rustlings
│
├── Rust By Example
│   └── https://doc.rust-lang.org/rust-by-example/
│
└── Rust Playground
    └── https://play.rust-lang.org/

安全特定:
├── Rust Secure Code Working Group
│   └── https://rust-secure-code.github.io/
│
├── Ferrous Systems Academy
│   └── https://ferrous-systems.com/training/
│
└── High Assurance Rust
    └── https://highassurance.rs/
```

### 1.2 推荐课程

| 课程 | 提供者 | 难度 | 费用 | 认证 |
|------|--------|------|------|------|
| **Rust for Safety Critical Systems** | Ferrous Systems | 中级 | $$$ | 有 |
| **Embedded Rust** | knurling-rs | 中级 | 免费 | 无 |
| **Advanced Rust** | O'Reilly | 高级 | $$ | 无 |
| **Functional Safety with Rust** | 内部培训 | 高级 | $$$ | 有 |

---

## 2. 虚拟实验室

### 2.1 在线实验环境

```bash
# 1. GitHub Codespaces
# 预配置Rust开发环境
# 包含: rust-analyzer, Clippy, Miri

# 2. GitPod
# 基于浏览器的IDE
# 一键启动Rust项目

# 3. Docker Playground
# 运行预构建的Rust容器
docker run -it rust:1.81-slim
```

### 2.2 嵌入式仿真

```
仿真平台:
├── QEMU
│   ├── arm-system-emulation
│   └── riscv64-system-emulation
│
├── Renode
│   ├── 多平台支持
│   ├── 自动化测试
│   └── CI集成
│
└── Wokwi
    ├── 浏览器仿真
    ├── 可视化调试
    └── 社区项目
```

### 2.3 实验项目

```rust
//! 在线实验: 安全LED闪烁器
//! 平台: https://wokwi.com/

#![no_std]
#![no_main]

use cortex_m_rt::entry;
use stm32f4::Peripherals;

#[entry]
fn main() -> ! {
    // 实验1: 基础LED控制
    // 实验2: 添加看门狗
    // 实验3: 故障检测
    // 实验4: 安全状态机

    let dp = Peripherals::take().unwrap();
    dp.GPIOA.moder.modify(|_, w| w.moder5().output());

    loop {
        dp.GPIOA.odr.modify(|r, w| w.odr5().bit(!r.odr5().bit()));
        cortex_m::asm::delay(8_000_000);
    }
}
```

---

## 3. 交互式教程

### 3.1 渐进式学习路径

```
Level 1: Hello Safety World (30分钟)
├── 目标: 运行第一个Rust嵌入式程序
├── 工具: 在线仿真器
└── 输出: LED闪烁

Level 2: 内存安全实验 (1小时)
├── 目标: 理解所有权和借用
├── 工具: Rust Playground + Miri
└── 输出: 通过Miri验证的代码

Level 3: 传感器读取 (2小时)
├── 目标: 安全地读取传感器数据
├── 工具: 仿真平台
└── 输出: 带错误处理的数据采集

Level 4: 状态机实现 (3小时)
├── 目标: 类型状态模式
├── 工具: 本地环境
└── 输出: 编译时验证的状态机

Level 5: 形式化验证 (4小时)
├── 目标: Kani验证
├── 工具: Kani在线/本地
└── 输出: 验证通过的属性
```

### 3.2 交互式代码示例

```rust
// 可编辑的代码模板
// 运行: https://play.rust-lang.org/

/// 实验: 安全的数组访问
///
/// 任务: 修改代码使其通过Miri检查
fn safe_access(arr: &[i32], index: usize) -> Option<i32> {
    // TODO: 添加边界检查
    Some(arr[index])  // 这里可能会panic!
}

fn main() {
    let data = vec![1, 2, 3, 4, 5];

    // 测试边界
    println!("{:?}", safe_access(&data, 2));   // Some(3)
    println!("{:?}", safe_access(&data, 10));  // None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bounds() {
        let arr = [1, 2, 3];
        assert_eq!(safe_access(&arr, 0), Some(1));
        assert_eq!(safe_access(&arr, 5), None);
    }
}
```

---

## 4. 社区学习

### 4.1 讨论平台

```
中文社区:
├── Rust语言中文社区
│   └── https://rustcc.cn/
│
├── Rust编程学院
│   └── 视频教程 + 练习
│
└── 知乎Rust话题
    └── 问答和学习笔记

国际社区:
├── Rust Users Forum
│   └── https://users.rust-lang.org/
│
├── Reddit r/rust
│   └── https://www.reddit.com/r/rust/
│
├── Discord Rust服务器
│   └── 实时交流
│
└── Zulip (安全关键Rust)
    └── https://rust-lang.zulipchat.com/
```

### 4.2 学习小组

```
线上学习小组:
├── 每周代码审查
├── 月度技术分享
├── 季度项目展示
└── 年度黑客松

指导计划:
├── 新人导师配对
├── 技术专家咨询
├── 职业发展规划
└── 认证考试辅导
```

---

## 5. 实践项目库

### 5.1 渐进式项目

```
项目1: 安全温度监控器 (1周)
├── 硬件: STM32 + 温度传感器
├── 目标: 读取+显示+报警
├── 技能: GPIO, ADC, 安全阈值
└── 难度: ⭐⭐

项目2: 电机控制器 (2周)
├── 硬件: 电机驱动板
├── 目标: PID控制+保护
├── 技能: PWM, 反馈控制, 故障检测
└── 难度: ⭐⭐⭐

项目3: 通信网关 (3周)
├── 硬件: 多协议接口
├── 目标: 协议转换+验证
├── 技能: UART/CAN, CRC, 状态机
└── 难度: ⭐⭐⭐⭐

项目4: 安全关键应用 (4周)
├── 硬件: 完整系统
├── 目标: ASIL等级功能
├── 技能: 全栈, 认证, 形式化验证
└── 难度: ⭐⭐⭐⭐⭐
```

### 5.2 开源贡献机会

```
入门级:
├── 文档改进
├── 示例代码
├── 测试用例
└── Bug报告

中级:
├── 驱动开发
├── 工具改进
├── 库功能添加
└── 性能优化

高级:
├── 架构设计
├── 安全审计
├── 形式化验证
└── 标准制定
```

---

## 6. 评估与认证

### 6.1 自测平台

```rust
/// 在线测验示例
/// 平台: 自建或第三方

#[test]
fn quiz_ownership() {
    // 问题1: 这段代码为什么编译失败?
    let s = String::from("hello");
    let s2 = s;
    // println!("{}", s); // 错误!

    // 答案:
    // s的所有权已转移到s2，s不再有效
    // 修复: 使用s2或clone()
}

#[test]
fn quiz_lifetime() {
    // 问题2: 如何修复这个生命周期错误?
    fn longest(x: &str, y: &str) -> &str {
        if x.len() > y.len() { x } else { y }
    }

    // 答案:
    // fn longest<'a>(x: &'a str, y: &'a str) -> &'a str
}
```

### 6.2 技能验证

```
验证方式:
├── 在线编程测试
├── 项目作品提交
├── 代码审查模拟
├── 技术面试练习
└── 同行评估

认证路径:
├── Level 1: 基础通过证书
├── Level 2: 应用开发证书
├── Level 3: 高级设计证书
└── Level 4: 专家认证
```

---

## 7. 学习工具推荐

### 7.1 开发环境

```
推荐配置:
├── VS Code + rust-analyzer
│   ├── 自动补全
│   ├── 实时错误检查
│   └── 代码导航
│
├── Rust Rover (JetBrains)
│   ├── 高级重构
│   ├── 深度分析
│   └── 调试支持
│
└── vim/emacs + LSP
    ├── 轻量级
    ├── 可定制
    └── 高效编辑
```

### 7.2 辅助工具

```
学习辅助:
├── cargo-expand (宏展开)
├── cargo-asm (汇编查看)
├── cargo-llvm-ir (LLVM IR)
└── rust-analyzer (IDE支持)

可视化工具:
├── cargo-tree (依赖图)
├── cargo-deps (依赖可视化)
├── sccache (编译缓存)
└── cargo-flamegraph (性能分析)
```

---

## 8. 持续更新

### 8.1 资源维护

```
更新频率:
├── 每周: 新教程添加
├── 每月: 项目更新
├── 每季: 课程修订
└── 每年: 大版本更新

反馈渠道:
├── GitHub Issues
├── 社区论坛
├── 邮件列表
└── 在线调查
```

---

**文档版本**: 1.0
**最后更新**: 2026-03-18

---

*学习是一个持续的过程，利用这些资源加速你的Rust安全关键开发之旅。*
