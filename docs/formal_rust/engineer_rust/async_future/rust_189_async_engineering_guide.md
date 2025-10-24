# Rust 1.89 异步工程实践指南


## 📊 目录

- [1. 指南概述](#1-指南概述)
- [2. 设计清单](#2-设计清单)
- [3. 性能清单](#3-性能清单)
- [4. 可靠性清单](#4-可靠性清单)
- [5. 代码模版](#5-代码模版)
- [6. 反模式清单](#6-反模式清单)
- [7. 度量与SLO](#7-度量与slo)
- [8. 迁移建议](#8-迁移建议)
- [9. 验证与基准方法学](#9-验证与基准方法学)
- [10. 风险登记表](#10-风险登记表)


## 1. 指南概述

- 目标: 用可操作清单帮助团队快速、安全落地Rust 1.89异步新能力
- 适用: 微服务、边缘计算、链上系统、实时Web

## 2. 设计清单

- 异步trait: 优先使用原生`async fn in traits`替代宏方案
- 返回类型: 利用RPITIT隐藏复杂返回类型，维持API稳定
- 背压策略: 统一使用`buffered/Ordered`，避免无界并发
- 取消传播: 以作用域为单位传播取消，提供幂等补偿
- 错误边界: `thiserror`统一错误类型，`anyhow`限制在边界层

## 3. 性能清单

- 批处理: `chunks(n)`+并发处理，n按P99延迟调参
- 最小捕获: 异步闭包仅捕获必要数据；优先借用，边界处移动
- 分配预算: 关键路径上预分配/对象池，避免热路径分配
- 原子/缓存: 合理使用Acquire/Release；避免不必要的SeqCst

## 4. 可靠性清单

- 结构化取消: 超时→取消→清理→补偿，确保不变量
- 重试策略: 指数回退+抖动；幂等保障先于重试
- 观测性: trace上下文贯穿任务树；区分取消/错误

## 5. 代码模版

```rust
#[allow(async_fn_in_trait)]
pub trait Service {
    async fn call(&self, req: Request) -> Result<Response, Error>;
}

type BoxFut<T> = impl std::future::Future<Output = T> + Send + 'static;

fn mk_pipeline<S: Service + Sync + Send + 'static>(svc: S) -> impl Fn(Request) -> BoxFut<Result<Response, Error>> {
    move |req| async move {
        let req = validate(req)?;
        let res = tokio::time::timeout(std::time::Duration::from_secs(2), svc.call(req)).await;
        match res {
            Ok(Ok(resp)) => Ok(resp),
            Ok(Err(e)) => Err(e),
            Err(_) => Err(Error::Timeout),
        }
    }
}
```

## 6. 反模式清单

- 无界`spawn`/`buffer_unordered`导致雪崩
- 忽视取消信号导致资源泄漏
- 在热路径中频繁`clone`大对象

## 7. 度量与SLO

- 关键指标: P50/P95/P99、队列长度、丢弃率、取消率
- SLO示例: `P99 < 150ms AND ErrorRate < 0.1%`

## 8. 迁移建议

- 先改接口: trait签名→异步化+RPITIT
- 再控并发: 引入有界并发/背压
- 最后治理: 取消传播、补偿与观测性

## 9. 验证与基准方法学

- 环境控制: 固定rustc(1.89.0)、禁用涡轮加速/频率缩放、隔离噪声
- 工具链: criterion、tokio-console、cargo-flamegraph、heaptrack
- 指标: P50/P95/P99、吞吐、RSS、allocs/op、取消率
- 步骤:
  1) 选择3类负载(AsyncIO/CPU/Mixed)并固定输入分布
  2) 预热≥10s，Trial≥30，置信区间95%
  3) 报告差异与效应量(Cliff's delta)

## 10. 风险登记表

```text
R1: 取消不被下游感知 → 泄漏/幽灵任务
  Mitigation: 统一取消语义/适配层，加入清理钩子
R2: 背压窗口配置失当 → 雪崩与抖动
  Mitigation: 自适应窗口+保护阈值，压测调参
R3: 生命周期外溢 → 'static 误用
  Mitigation: 借用优先、模块边界move、类型审计
R4: 回归与不确定优化 → 版本锚点与双轨CI
  Mitigation: perf CI + bisection 警戒线
```
