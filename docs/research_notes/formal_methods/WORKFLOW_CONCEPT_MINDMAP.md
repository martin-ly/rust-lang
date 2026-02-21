# 工作流概念族谱 - 思维导图

> **创建日期**: 2026-02-21
> **最后更新**: 2026-02-21
> **状态**: 🔄 新建
> **对应任务**: P1-T12

---

## 全局思维导图

```
                          工作流概念族
                               │
        ┌──────────────────────┼──────────────────────┐
        │                      │                      │
   【核心概念】              【模式】                【引擎】
        │                      │                      │
    ├─状态机               ├─顺序流               ├─Temporal
    │  ├─状态               │  └─串行执行           ├─Cadence
    │  ├─转换               ├─并行流               ├─自建Rust
    │  └─事件               │  ├─Fork/Join          └─LiteFlow
    ├─活动                  ├─条件分支
    │  ├─自动活动           │  ├─If/Else
    │  ├─人工任务           │  └─Switch
    │  └─子流程             ├─循环
    ├─补偿                  │  ├─While
    │  ├─补偿链             │  └─ForEach
    │  └─Saga集成           └─异常处理
    └─超时/重试                ├─Try/Catch
       ├─活动超时              └─补偿
       ├─工作流超时
       └─重试策略
```

---

## 详细概念族谱

### 1. 工作流状态机

```
                          工作流状态
                               │
            ┌──────────────────┼──────────────────┐
            │                  │                  │
       【初始状态】          【执行状态】        【终止状态】
            │                  │                  │
        ├─Created           ├─Running          ├─Completed
        │                   │  ├─ActivityX     │  └─成功完成
        └─Initialized       │  ├─Waiting       ├─Failed
                            │  └─Compensating  │  └─失败补偿
                            │                  └─Cancelled
                            └─Suspended           └─被取消
```

**状态转换规则**:

| 当前状态 | 事件 | 下一状态 | 条件 |
|:---|:---|:---|:---|
| Created | Start | Running | - |
| Running(act) | ActivityComplete(act, Success) | Running(next) | next = transition(act) |
| Running(act) | ActivityComplete(act, Failure) | Compensating(act) | has_compensation |
| Compensating(act) | CompensateComplete | Compensating(prev) | prev = predecessor(act) |
| Compensating(first) | CompensateComplete | Failed | - |
| Running(act) | ExternalEvent(e) | Running(next) | e triggers transition |
| Running(act) | Timeout | Compensating(act) | timeout_policy = compensate |

**形式化定义** (Coq):
```coq
Inductive WorkflowState :=
  | WS_Created
  | WS_Running (current : string)
  | WS_Waiting (event : string)
  | WS_Compensating (failed : string)
  | WS_Completed (result : Value)
  | WS_Failed (error : string)
  | WS_Cancelled.
```

---

### 2. 活动(Activity)类型族

```
                            活动类型
                               │
            ┌──────────────────┼──────────────────┐
            │                  │                  │
       【自动活动】          【人工活动】        【控制活动】
            │                  │                  │
        ├─Service调用        ├─用户任务         ├─开始/结束
        │  ├─同步调用          │  ├─审批          ├─分支/合并
        │  └─异步调用          │  └─填写          ├─条件
        ├─脚本执行            ├─会签             └─子流程
        │  ├─表达式            │  └─多人审批
        │  └─函数              └─接收任务
        └─规则执行               └─消息等待
           ├─DMN决策
           └─规则引擎
```

**活动属性**:

| 属性 | 类型 | 说明 |
|:---|:---|:---|
| id | string | 活动唯一标识 |
| input | Value -> Value | 输入转换函数 |
| execute | Value -> ActivityResult | 执行逻辑 |
| compensate | option (Value -> ActivityResult) | 补偿逻辑 |
| timeout | option nat | 超时时间(秒) |
| retry_policy | option RetryPolicy | 重试策略 |

**形式化定义** (Coq):
```coq
Record Activity := mkActivity {
  act_id : string;
  act_execute : Value -> ActivityResult;
  act_compensate : option (Value -> ActivityResult);
  act_timeout : option nat;
  act_retry_policy : option RetryPolicy
}.
```

---

### 3. 补偿链模式

```
                          补偿链
                               │
            ┌──────────────────┼──────────────────┐
            │                  │                  │
       【补偿策略】          【补偿顺序】        【补偿结果】
            │                  │                  │
        ├─向后补偿          ├─逆序补偿         ├─完全补偿
        │  └─撤销已执行        │  └─LIFO          ├─部分补偿
        ├─向前补偿          ├─选择性补偿        └─补偿失败
        │  └─继续执行          │  └─跳过可选
        └─混合补偿          └─并行补偿
           ├─向后为主
           └─向前为辅
```

**补偿链执行流程**:

```
Activity1 -> Activity2 -> Activity3 [FAILS]
    ↓           ↓           ↓
Comp3(undo) <- Comp2(undo) <- Comp1(undo)
    ↓           ↓           ↓
  [OK]        [OK]        [OK]
    ↓           ↓           ↓
           [FAILED]
```

**形式化定义** (Coq):
```coq
Fixpoint execute_compensation (stack : CompensationStack) : CompensationResult :=
  match stack with
  | nil => CR_Success nil
  | cr :: rest =>
      match cr_activity cr with
      | mkActivity _ _ None _ _ => execute_compensation rest
      | mkActivity _ _ (Some comp) _ _ =>
          match comp (cr_output cr) with
          | AR_Success _ => execute_compensation rest
          | _ => CR_Failed "Compensation failed"
          end
      end
  end.
```

---

### 4. 工作流引擎对比

```
                        工作流引擎
                               │
        ┌──────────────────────┼──────────────────────┐
        │                      │                      │
   【Temporal】             【Cadence】            【自建Rust】
        │                      │                      │
    ├─持久化优先           ├─Uber开源            ├─轻量级
    ├─多语言SDK            ├─兼容Temporal        ├─无外部依赖
    ├─可见性UI             ├─性能优化            ├─完全控制
    └─云原生               └─内部部署            └─学习成本
        │                      │                      │
        └──────────────────────┼──────────────────────┘
                                 │
                         【选型维度】
                         ├─持久化需求
                         ├─吞吐量要求
                         ├─可见性需求
                         └─运维复杂度
```

**引擎能力矩阵**:

| 特性 | Temporal | Cadence | 自建Rust |
|:---|:---:|:---:|:---:|
| 持久化 | ✅ 内置 | ✅ 内置 | ⚠️ 需实现 |
| 可见性UI | ✅ | ✅ | ❌ |
| 多语言 | ✅ Go/Java/TS/... | ✅ Go/Java | ⚠️ 仅Rust |
| 补偿事务 | ✅ | ✅ | ⚠️ 需实现 |
| 人工任务 | ⚠️ 外部 | ⚠️ 外部 | ⚠️ 需实现 |
| 云原生 | ✅ | ⚠️ | ✅ |
| 学习曲线 | 中 | 中 | 高 |

---

## 概念关系矩阵

| 概念A | 关系 | 概念B | 说明 |
|:---|:---:|:---|:---|
| 工作流 | 使用 | 活动 | 工作流由活动组成 |
| 活动 | 有 | 补偿 | 活动可选定义补偿 |
| 补偿链 | 组成 | 补偿 | 按逆序执行活动补偿 |
| 状态机 | 描述 | 工作流 | 工作流是特殊状态机 |
| Saga | 是一种 | 工作流 | Saga 是长事务工作流 |
| 超时 | 触发 | 补偿 | 超时可选触发补偿 |
| 重试 | 控制 | 活动 | 重试策略控制活动执行 |

---

## 与其他概念族的关系

```
                    工作流概念族
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
   【分布式模式】        【类型系统】        【异步编程】
        │                  │                  │
    ├─Saga            ├─Result类型        ├─Future
    ├─CQRS            ├─泛型活动           ├─async/await
    └─事务            └─类型安全补偿       └─超时控制
        │                      │
        └──────────────────────┘
                  │
           【Rust实现】
           ├─tokio::time (超时)
           ├─futures::channel (通信)
           └─serde (序列化)
```

---

## 形式化验证目标

| 定理 | 描述 | 优先级 |
|:---|:---|:---:|
| WF-1 | 工作流终止性 | P0 |
| WF-2 | 补偿最终一致性 | P0 |
| WF-3 | 状态机确定性 | P1 |
| WF-4 | 组合有效性 | P1 |

---

## 相关文档

- [Coq 形式化定义](../coq_skeleton/WORKFLOW_FORMALIZATION.v)
- [Saga 与补偿链](../coq_skeleton/DISTRIBUTED_PATTERNS.v)
- [工作流引擎指南](../../../docs/05_guides/WORKFLOW_ENGINE_GUIDE.md)

---

**维护者**: Rust Formal Methods Research Team  
**对应任务**: P1-T12 - 工作流概念族谱新建
