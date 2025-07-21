# C05. 并发：线程、消息与同步 (Concurrency: Threads, Messaging, and Synchronization)

## 模块简介

本模块系统梳理Rust并发编程的理论基础、核心机制与工程实践，涵盖线程与所有权、消息传递、共享状态、同步原语、Send/Sync trait、并行计算、无锁编程等。通过所有权模型与类型系统的深度结合，Rust在编译期消除数据竞争，实现“无畏并发”。模块强调理论与工程的结合，助力开发者实现高安全、高性能、可验证的并发系统。

## 章节导航

1. [线程与所有权](./01_threads_and_ownership.md) —— thread::spawn, JoinHandle, move闭包，所有权防止数据竞争
2. [消息传递并发](./02_message_passing.md) —— 通道(Channel)、mpsc，所有权转移与线程安全通信
3. [共享状态与同步原语](./03_synchronization_primitives.md) —— Mutex, Arc, RwLock，Send/Sync trait与同步机制
4. [并行计算与生态](./04_parallelism_and_beyond.md) —— 并发vs并行、Rayon、数据并行与调度
5. [高级主题与总结](./05_advanced_topics_and_summary.md) —— 原子类型、无锁编程、内存排序、并发安全回顾

## 学习目标

- 理解Rust并发安全的理论基础与所有权模型
- 掌握线程、消息传递、共享状态、同步原语等核心机制
- 能够分析和解决实际工程中的数据竞争与并发安全问题
- 熟悉Send/Sync trait、原子类型、无锁并发等高级特性
- 跟踪并发与并行领域的前沿理论与工程创新

## 前置知识

- Rust基础语法与所有权模型
- 变量、借用、生命周期等内存安全机制
- 基本的线程与同步原语概念

## 实践项目

1. 实现多线程安全的消息传递系统
2. 设计并发安全的共享状态数据结构
3. 利用Rayon实现高性能数据并行计算
4. 编写无锁并发算法与原子操作实验
5. 形式化验证并发程序的数据竞争免疫性

## 交叉引用

- [所有权与借用](../01_ownership_borrowing/)
- [类型系统与Send/Sync](../02_type_system/)
- [分离逻辑与并发安全](../05_formal_verification/)
- [标准库与并发原语](../11_memory_management/)

## 总结

本模块为Rust并发安全与高性能系统开发提供理论与实践基础。通过深入理解所有权、Send/Sync、消息传递与同步原语等机制，开发者可编写高效、安全、可验证的并发程序，为后续探索并行计算、无锁算法等前沿领域打下坚实基础。