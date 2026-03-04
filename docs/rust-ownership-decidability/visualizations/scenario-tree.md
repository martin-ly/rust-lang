# 应用场景决策树

## 1. Web服务开发

```
Web服务架构
│
├─► 请求处理模式
│   ├─ 同步处理 ─► 线程池模型
│   │               └─ 每个请求一个线程
│   └─ 异步处理 ─► async/await
│                   └─ tokio/async-std runtime
│
├─► 状态管理
│   ├─ 无状态 ─► 函数式处理
│   ├─ 会话状态 ─► Redis/Session存储
│   └─ 应用状态 ─► Arc<State> + Mutex
│
├─► 数据库访问
│   ├─ 连接池 ─► deadpool/sqlx/r2d2
│   └─ 事务 ─► 生命周期管理
│
```

## 2. 数据处理管道

```
数据处理流程
│
├─► 数据源
│   ├─ 文件 ─► BufReader + Iterator
│   ├─ 网络 ─► Stream API
│   └─ 数据库 ─► 连接池 + 流式查询
│
├─► 转换阶段
│   ├─ 串行处理 ─► Iterator链
│   └─ 并行处理 ─► rayon parallel iter
│
├─► 输出
│   ├─ 文件 ─► BufWriter
│   ├─ 网络 ─► Sink trait
│   └─ 数据库 ─► 批量插入
│
```

## 3. 游戏开发

```
游戏架构模式
│
├─► ECS (Entity Component System)
│   ├─ Entity ─► ID生成
│   ├─ Component ─► SoA存储
│   └─ System ─► 并行查询
│
├─► 资源管理
│   ├─ 纹理/模型 ─► Asset Cache
│   ├─ 场景图 ─► 所有权树
│   └─ 热重载 ─► 资源句柄
│
├─► 游戏循环
│   ├─ 固定更新 ─► 物理模拟
│   ├─ 可变更新 ─► 渲染
│   └─ 事件处理 ─► 通道模式
│
```

## 4. 嵌入式/IoT

```
嵌入式开发模式
│
├─► 裸机 (no_std)
│   ├─ 全局状态 ─► static + UnsafeCell
│   ├─ 中断处理 ─► 临界区 + Mutex
│   └─ 内存分配 ─► 全局分配器 / 固定数组
│
├─► RTOS集成
│   ├─ 任务 ─► 线程抽象
│   ├─ 同步 ─► 信号量/互斥
│   └─ 消息 ─► 队列/邮箱
│
├─► 外设访问
│   ├─ MMIO ─► volatile访问
│   ├─ DMA ─► 所有权转移
│   └─ 中断 ─► 回调注册
│
```

## 5. CLI工具开发

```
CLI工具设计
│
├─► 参数解析
│   ├─ 简单 ─► std::env::args
│   └─ 复杂 ─► clap/structopt
│
├─► 配置文件
│   ├─ TOML ─► serde + toml
│   ├─ JSON ─► serde_json
│   └─ YAML ─► serde_yaml
│
├─► 输出格式化
│   ├─ 表格 ─► comfy-table
│   ├─ 进度 ─► indicatif
│   └─ 颜色 ─► colored/owo-colors
│
├─► 错误展示
│   ├─ 简单 ─► eprintln!
│   └─ 丰富 ─► anyhow + thiserror
│
```
