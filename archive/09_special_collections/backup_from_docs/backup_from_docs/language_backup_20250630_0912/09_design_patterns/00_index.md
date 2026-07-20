# 设计模式模块索引 {#设计模式索引}

## 目录 {#目录}

1. [形式化设计模式理论](01_formal_theory.md#设计模式理论概述)
2. [创建型模式](02_creational_patterns.md#创建型模式概述)
3. [结构型模式](03_structural_patterns.md#结构型模式概述)
4. [行为型模式](04_behavioral_patterns.md#行为型模式概述)
5. [函数式模式](05_functional_patterns.md#函数式模式概述)
6. [并发模式](06_concurrency_patterns.md#并发模式概述)

## 模块概述 {#模块概述}

Rust设计模式模块提供了对Rust语言特有的设计模式的形式化定义和理论基础。这些模式充分利用Rust的类型系统、所有权模型和零成本抽象，提供安全、高效和表达力强的解决方案。

**主要内容**:

- **设计模式理论** {#设计模式理论} - 设计模式的形式化定义和数学基础
- **模式分类** {#模式分类} - 创建型、结构型、行为型和Rust特有的函数式与并发模式
- **安全保证** {#安全保证} - 每种模式提供的编译时和运行时安全保证
- **形式化验证** {#形式化验证} - 设计模式的形式化验证和证明

**相关概念**:

- [类型系统](../02_type_system/01_formal_type_system.md#类型系统) (模块 02)
- [所有权系统](../01_ownership_borrowing/01_formal_theory.md#所有权系统) (模块 01)
- [泛型参数化](../04_generics/01_formal_theory.md#泛型参数化) (模块 04)
- [trait抽象](../12_traits/01_formal_theory.md#trait抽象) (模块 12)

## 核心概念 {#核心概念}

### 创建型模式 {#创建型模式}

- **单例模式** {#单例模式} - 确保一个类只有一个实例，并提供全局访问点
- **工厂模式** {#工厂模式} - 将对象的创建与使用分离，提供创建对象的接口
- **构建器模式** {#构建器模式} - 分步骤构建复杂对象，支持流式API

**相关概念**:

- [构造函数](../02_type_system/01_formal_type_system.md#构造函数) (模块 02)
- [资源获取即初始化](../01_ownership_borrowing/01_formal_theory.md#资源获取) (模块 01)
- [类型状态模式](../19_advanced_language_features/01_formal_spec.md#类型状态) (模块 19)

### 结构型模式 {#结构型模式}

- **适配器模式** {#适配器模式} - 将不兼容接口转换为客户端期望的接口
- **装饰器模式** {#装饰器模式} - 动态地向对象添加新功能，不改变其接口
- **组合模式** {#组合模式} - 将对象组合成树结构表示"部分-整体"层次

**相关概念**:

- [Trait对象](../12_traits/01_formal_theory.md#trait对象) (模块 12)
- [泛型约束](../04_generics/01_formal_theory.md#泛型约束) (模块 04)
- [代数数据类型](../02_type_system/01_formal_type_system.md#代数数据类型) (模块 02)

### 行为型模式 {#行为型模式}

- **策略模式** {#策略模式} - 定义一族算法，使它们可以互相替换
- **观察者模式** {#观察者模式} - 定义对象间的一对多依赖关系
- **命令模式** {#命令模式} - 将请求封装为对象，支持操作的参数化与撤销

**相关概念**:

- [函数特性](../03_control_flow/01_formal_control_flow.md#函数特性) (模块 03)
- [闭包](../03_control_flow/01_formal_control_flow.md#闭包) (模块 03)
- [迭代器](../08_algorithms/01_formal_algorithm_system.md#迭代器系统) (模块 08)

### 函数式模式 {#函数式模式}

- **函数组合** {#函数组合} - 通过组合小函数构建复杂功能
- **管道模式** {#管道模式} - 将数据通过一系列转换流水线处理
- **惰性求值** {#惰性求值} - 推迟计算直到需要结果

**相关概念**:

- [函数式编程](../20_theoretical_perspectives/01_programming_paradigms.md#函数式编程) (模块 20)
- [迭代器适配器](../08_algorithms/01_formal_algorithm_system.md#迭代器适配器) (模块 08)
- [高阶函数](../03_control_flow/01_formal_control_flow.md#高阶函数) (模块 03)

### 并发模式 {#并发模式}

- **线程池模式** {#线程池模式} - 管理和重用线程资源
- **异步通信模式** {#异步通信模式} - 使用通道进行线程间通信
- **锁范围模式** {#锁范围模式} - 精确控制锁的作用范围

**相关概念**:

- [并发模型](../05_concurrency/01_formal_concurrency_model.md#并发模型) (模块 05)
- [异步执行](../06_async_await/01_formal_async_system.md#异步执行) (模块 06)
- [所有权共享](../01_ownership_borrowing/01_formal_theory.md#所有权共享) (模块 01)

## 相关模块 {#相关模块}

本模块与以下模块紧密相连:

- [模块 01: 所有权与借用](../01_ownership_borrowing/00_index.md#所有权索引) - 设计模式中的资源管理基础
- [模块 02: 类型系统](../02_type_system/00_index.md#类型系统索引) - 设计模式的类型理论基础
- [模块 04: 泛型](../04_generics/00_index.md#泛型索引) - 支持设计模式的参数化与多态性
- [模块 05: 并发](../05_concurrency/00_index.md#并发索引) - 并发设计模式的理论基础
- [模块 08: 算法](../08_algorithms/00_index.md#算法索引) - 算法与设计模式的关联
- [模块 12: 特征](../12_traits/00_index.md#特征索引) - 设计模式中的接口抽象
- [模块 20: 理论视角](../20_theoretical_perspectives/00_index.md#理论视角索引) - 设计模式的理论基础

## 数学符号说明 {#数学符号说明}

- $\mathcal{P}$: 设计模式
- $\Sigma$: 模式签名
- $\mathcal{T}$: 类型约束
- $\mathcal{R}$: 实现规则
- $\mathcal{S}$: 安全保证
- $\vdash$: 类型推导
- $\models$: 满足关系

**相关概念**:

- [形式化符号](../20_theoretical_perspectives/01_programming_paradigms.md#形式化符号) (模块 20)
- [数学基础](../20_theoretical_perspectives/04_mathematical_foundations.md#数学基础) (模块 20)
