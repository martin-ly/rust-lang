# 运行时环境 (Runtime Environments)

> **目录定位**: C13 可靠性框架运行时环境支持文档  
> **适用人群**: 架构师、系统工程师  
> **相关文档**: [高级主题](../README.md) | [架构设计](../../architecture/)

**最后更新**: 2025-10-19  
**文档类型**: 🌐 运行时环境文档

---

## 📋 目录

- [运行时环境 (Runtime Environments)](#运行时环境-runtime-environments)
  - [📋 目录](#-目录)
  - [📚 文档列表](#-文档列表)
    - [核心文档](#核心文档)
  - [🌐 支持的运行时环境](#-支持的运行时环境)
    - [一、原生执行环境 (Native Execution) - 5种](#一原生执行环境-native-execution---5种)
      - [1.1 操作系统环境 (OS Environment)](#11-操作系统环境-os-environment)
      - [1.2 嵌入式裸机环境 (Embedded Bare Metal)](#12-嵌入式裸机环境-embedded-bare-metal)
      - [1.3 实时操作系统环境 (Real-Time OS)](#13-实时操作系统环境-real-time-os)
      - [1.4 游戏引擎环境 (Game Engine)](#14-游戏引擎环境-game-engine)
      - [1.5 移动应用环境 (Mobile)](#15-移动应用环境-mobile)
    - [二、虚拟化执行环境 (Virtualized Execution) - 4种](#二虚拟化执行环境-virtualized-execution---4种)
      - [2.1 虚拟机环境 (Virtual Machine)](#21-虚拟机环境-virtual-machine)
      - [2.2 微虚拟机环境 (MicroVM)](#22-微虚拟机环境-microvm)
      - [2.3 Docker容器环境 (Container)](#23-docker容器环境-container)
      - [2.4 Kubernetes Pod环境 (K8s Pod)](#24-kubernetes-pod环境-k8s-pod)
    - [三、沙箱执行环境 (Sandboxed Execution) - 2种](#三沙箱执行环境-sandboxed-execution---2种)
      - [3.1 WebAssembly环境 (WASM)](#31-webassembly环境-wasm)
      - [3.2 函数即服务环境 (FaaS)](#32-函数即服务环境-faas)
    - [四、特殊部署环境 (Special Deployment) - 2种](#四特殊部署环境-special-deployment---2种)
      - [4.1 边缘计算环境 (Edge Computing)](#41-边缘计算环境-edge-computing)
      - [4.2 区块链环境 (Blockchain)](#42-区块链环境-blockchain)
  - [🎯 快速选择](#-快速选择)
    - [按应用类型选择](#按应用类型选择)
    - [按资源约束选择](#按资源约束选择)
  - [📊 能力对比](#-能力对比)
  - [🔗 相关资源](#-相关资源)

---

## 📚 文档列表

### 核心文档

1. **[运行时环境总览](overview.md)** - 完整的环境支持说明
   - 13种运行时环境详解
   - 环境特性
   - 适用场景
   - 使用方式

2. **[环境分类体系](taxonomy.md)** - 环境分类学
   - 四大类别
   - 13种环境
   - 分类标准
   - 特性对比

3. **[实现细节](implementation.md)** - 实现报告
   - 适配器设计
   - 环境检测
   - 策略调整
   - 代码示例

4. **[扩展总结](expansion-summary.md)** - 扩展历程
   - 从3种到13种
   - 设计演进
   - 经验总结

5. **[能力矩阵](capabilities-matrix.md)** - 详细的能力对比表
   - 基础能力
   - 高级能力
   - 限制与约束

---

## 🌐 支持的运行时环境

### 一、原生执行环境 (Native Execution) - 5种

#### 1.1 操作系统环境 (OS Environment)

**特性**: 完整的操作系统支持，多进程、多线程、文件系统、网络

**适用场景**:

- 服务器应用
- 桌面应用
- 企业级服务

**文档**: [overview.md](overview.md#11-操作系统环境)

#### 1.2 嵌入式裸机环境 (Embedded Bare Metal)

**特性**: 无操作系统，直接硬件访问，资源受限

**适用场景**:

- IoT设备
- 嵌入式系统
- 实时控制系统

**文档**: [overview.md](overview.md#12-嵌入式裸机环境)

#### 1.3 实时操作系统环境 (Real-Time OS)

**特性**: 确定性实时响应，低延迟

**适用场景**:

- 工业控制系统
- 自动驾驶系统
- 医疗设备

**文档**: [overview.md](overview.md#13-实时操作系统环境)

#### 1.4 游戏引擎环境 (Game Engine)

**特性**: 高性能实时渲染，资源优化

**适用场景**:

- 游戏开发
- 实时图形应用
- VR/AR应用

**文档**: [overview.md](overview.md#14-游戏引擎环境)

#### 1.5 移动应用环境 (Mobile)

**特性**: 移动设备优化，电池管理

**适用场景**:

- 移动应用
- 跨平台应用
- 移动游戏

**文档**: [overview.md](overview.md#15-移动应用环境)

---

### 二、虚拟化执行环境 (Virtualized Execution) - 4种

#### 2.1 虚拟机环境 (Virtual Machine)

**特性**: 完整虚拟化，资源隔离，快照支持

**适用场景**:

- 传统虚拟化部署
- 云基础设施
- 开发测试环境

**文档**: [overview.md](overview.md#21-虚拟机环境)

#### 2.2 微虚拟机环境 (MicroVM)

**特性**: 轻量级虚拟化，快速启动

**适用场景**:

- 无服务器计算
- 边缘计算
- 容器化应用

**文档**: [overview.md](overview.md#22-微虚拟机环境)

#### 2.3 Docker容器环境 (Container)

**特性**: 进程级隔离，轻量级

**适用场景**:

- 微服务架构
- 云原生应用
- 容器化部署

**文档**: [overview.md](overview.md#23-docker容器环境)

#### 2.4 Kubernetes Pod环境 (K8s Pod)

**特性**: 容器编排，服务发现，自动扩缩容

**适用场景**:

- Kubernetes集群
- 微服务编排
- 云原生应用

**文档**: [overview.md](overview.md#24-kubernetes-pod环境)

---

### 三、沙箱执行环境 (Sandboxed Execution) - 2种

#### 3.1 WebAssembly环境 (WASM)

**特性**: 沙箱化，跨平台，安全隔离

**适用场景**:

- 浏览器应用
- 边缘计算
- 插件系统

**文档**: [overview.md](overview.md#31-webassembly环境)

#### 3.2 函数即服务环境 (FaaS)

**特性**: 无服务器架构，按需执行

**适用场景**:

- 事件驱动应用
- API服务
- 数据处理

**文档**: [overview.md](overview.md#32-函数即服务环境)

---

### 四、特殊部署环境 (Special Deployment) - 2种

#### 4.1 边缘计算环境 (Edge Computing)

**特性**: 低延迟，资源受限，离线能力

**适用场景**:

- IoT网关
- 边缘服务器
- CDN节点

**文档**: [overview.md](overview.md#41-边缘计算环境)

#### 4.2 区块链环境 (Blockchain)

**特性**: 去中心化，共识机制

**适用场景**:

- 区块链应用
- 去中心化服务
- 智能合约

**文档**: [overview.md](overview.md#42-区块链环境)

---

## 🎯 快速选择

### 按应用类型选择

- **服务器应用** → OS Environment
- **微服务** → Container / K8s Pod
- **IoT设备** → Embedded / RTOS / Edge
- **移动应用** → Mobile Environment
- **浏览器应用** → WebAssembly
- **无服务器** → FaaS / MicroVM

### 按资源约束选择

- **资源充足** → OS / VM / K8s
- **资源受限** → Embedded / Mobile / Edge
- **快速启动** → MicroVM / FaaS / Container
- **长期运行** → OS / VM / K8s

---

## 📊 能力对比

详见：[能力矩阵](capabilities-matrix.md)

| 环境 | 多进程 | 多线程 | 文件系统 | 网络 | 启动速度 |
|------|--------|--------|----------|------|----------|
| OS | ✅ | ✅ | ✅ | ✅ | 慢 |
| Embedded | ❌ | ❌ | ❌ | ❌ | 快 |
| Container | ✅ | ✅ | ✅ | ✅ | 快 |
| K8s | ✅ | ✅ | ✅ | ✅ | 中等 |
| WASM | ❌ | ✅ | ❌ | ✅ | 很快 |
| FaaS | ❌ | ✅ | ❌ | ✅ | 很快 |

---

## 🔗 相关资源

- [架构设计](../../architecture/) - 整体架构
- [功能文档](../../features/) - 具体功能
- [最佳实践](../../guides/best-practices.md) - 使用建议

---

**文档维护**: C13 运行时团队  
**最后审核**: 2025-10-19
