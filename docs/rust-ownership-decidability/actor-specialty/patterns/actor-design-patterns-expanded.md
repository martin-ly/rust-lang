# Actor设计模式 - 扩展版

> **形式化定义、定理证明与生产实践**

---

## 设计模式形式化框架

### 模式定义模板

```text
定义 PATTERN-STRUCTURE:
每个设计模式包含:
    - 名称 (Name)
    - 意图 (Intent)
    - 结构 (Structure)
    - 参与者 (Participants)
    - 协作 (Collaborations)
    - 形式化语义 (Formal Semantics)
    - 安全保证 (Safety Guarantees)
```

---

## 1. Ask vs Tell 模式

### 1.1 形式化定义

```text
定义 ASK-TELL-MODE:

Tell模式 (Fire-and-Forget):
    tell(a: ActorRef, m: Message) → ()
    效果: 消息m被异步发送到Actor a的邮箱
    返回: 立即返回，无结果

Ask模式 (Request-Response):
    ask(a: ActorRef, m: Message) → Future<Response>
    效果: 发送消息m并等待响应
    返回: Future，可等待响应或超时

形式化区别:
    tell: M → ()              (单元类型)
    ask:  M → Future<R>       (响应类型)
```

### 1.2 定理 ASK-TELL-SAFETY

```text
定理 ASK-TELL-SAFETY-1: Ask模式不会导致Actor状态不一致

证明:
1. Ask发送消息m给Actor a
2. a在处理m期间，其邮箱中其他消息等待
3. a完成处理，发送响应r
4. 请求者收到r后，可以继续执行

由于Actor a顺序处理消息，不会并发处理其他消息，
∴ 状态一致性保证

定理 ASK-TELL-SAFETY-2: Tell模式保证最终一致性

证明:
1. Tell发送消息m，立即返回
2. 消息m最终到达Actor a的邮箱
3. a按顺序处理所有消息
4. ∴ m的效果最终可见
```

### 1.3 决策矩阵

| 场景 | Tell | Ask | 理由 |
|:---|:---:|:---:|:---|
| 事件通知 | ✅ | ❌ | 不需要响应 |
| 日志记录 | ✅ | ❌ | 异步性能 |
| 查询请求 | ❌ | ✅ | 需要结果 |
| 事务处理 | ❌ | ✅ | 需要确认 |
| 广播消息 | ✅ | ❌ | 一对多 |
| 同步协调 | ❌ | ✅ | 需要等待 |

---

## 2. 监督树模式

### 2.1 形式化定义

```text
定义 SUPERVISION-TREE:

监督树是一个层次结构 T = (N, E, strategy)

N = Workers ∪ Supervisors
E ⊆ N × N  (监督关系，父监督子)
strategy: N → {OneForOne, OneForAll, RestForOne}

监督规则:
    ∀s ∈ Supervisors, ∀c ∈ children(s).
    failure(c) → action(s, c, strategy(s))

其中:
    action(s, c, OneForOne) = restart(c)
    action(s, c, OneForAll) = restart(children(s))
    action(s, c, RestForOne) = restart({c' | c' ∈ children(s) ∧ order(c') ≥ order(c)})
```

### 2.2 定理 SUPERVISION-SAFETY

```text
定理 SUPERVISION-FAULT-ISOLATION: 监督树隔离故障

∀监督树T. ∀节点n ∈ T.
failure(n) ⇒ impact(n) ⊆ subtree(parent(n))

证明:
1. 节点n失败
2. 父监督者p检测到失败
3. p根据策略采取行动
4. 影响仅限于p的子树
5. ∴ 故障被隔离

定理 SUPERVISION-EVENTUAL-RECOVERY: 监督树最终恢复

∀可恢复错误e. ∃n ∈ ℕ.
经过n次重启后，系统恢复正常或达到最大重启限制
```

### 2.3 监督策略矩阵

| 策略 | 使用场景 | 恢复时间 | 影响范围 |
|:---|:---|:---:|:---|
| OneForOne | 独立任务 | 快 | 单个Actor |
| OneForAll | 相互依赖 | 中 | 整个组 |
| RestForOne | 启动顺序依赖 | 中 | 子集 |

---

## 3. Circuit Breaker 模式

### 3.1 形式化定义

```text
定义 CIRCUIT-BREAKER:

状态机:
    State ::= Closed | Open | HalfOpen

转换:
    Closed --failure_count >= threshold--> Open
    Open --timeout--> HalfOpen
    HalfOpen --success--> Closed
    HalfOpen --failure--> Open

变量:
    failure_count: ℕ
    success_count: ℕ (在HalfOpen状态)
    threshold: ℕ
    timeout: Duration

语义:
    request(cb, msg) =
        case cb.state of
            Closed → forward(target, msg)
            Open → fail_fast()
            HalfOpen → forward(target, msg) with tracking
```

### 3.2 定理 CIRCUIT-BREAKER-SAFETY

```text
定理 CIRCUIT-BREAKER-PROTECTION: 熔断器保护系统免受过载

证明:
1. 当失败率超过阈值，状态变为Open
2. Open状态下，请求立即失败
3. 这阻止了请求到达故障服务
4. 给故障服务恢复时间
5. ∴ 系统整体可用性提高

定理 CIRCUIT-BREAKER-AUTOMATIC-RECOVERY: 熔断器自动检测恢复

HalfOpen状态下的试探请求成功
→ 状态转为Closed
→ 正常流量恢复
```

### 3.3 参数选择矩阵

| 参数 | 敏感服务 | 容错服务 | 外部依赖 |
|:---|:---:|:---:|:---:|
| 失败阈值 | 3-5 | 10-20 | 1-3 |
| 超时时间 | 5s | 30s | 10s |
| 恢复超时 | 30s | 5min | 1min |
| HalfOpen请求 | 1 | 5 | 1 |

---

## 4. 路由模式

### 4.1 一致性哈希路由

```text
定义 CONSISTENT-HASHING:

哈希环: [0, 2³²-1]

节点映射:
    nodes: Set<Node>
    hash: Key → [0, 2³²-1]
    ring_position: Node → [0, 2³²-1]

路由:
    route(key) = min { n ∈ nodes | ring_position(n) ≥ hash(key) }
                 or min(nodes) if no such n

虚拟节点:
    ∀n ∈ nodes. replicas(n) = {n#1, n#2, ..., n#k}
    每个虚拟节点在环上有不同位置
```

### 4.2 定理 ROUTING-CONSISTENCY

```text
定理 CONSISTENT-HASHING-MINIMAL-MOVEMENT: 一致性哈希最小化重新分配

当节点n失败或加入时:
|{key | route_before(key) ≠ route_after(key)}| ≈ |keys| / |nodes|

即只有约1/N的键需要重新分配

证明:
1. 键在哈希环上均匀分布
2. 每个节点负责一个区间
3. 节点变化只影响相邻区间
4. ∴ 影响范围最小化
```

### 4.3 路由策略对比矩阵

| 策略 | 负载均衡 | 状态亲和 | 实现复杂度 | 适用场景 |
|:---:|:---:|:---:|:---:|:---|
| Round Robin | 完美 | 无 | 低 | 无状态服务 |
| Random | 统计 | 无 | 低 | 无状态服务 |
| 一致性哈希 | 好 | 是 | 中 | 有状态服务 |
| 最少连接 | 动态 | 无 | 中 | 长连接服务 |
| 加权 | 可控 | 无 | 低 | 异构节点 |

---

## 5. 状态机模式

### 5.1 形式化定义

```text
定义 ACTOR-FSM:

有限状态机:
    M = (S, Σ, δ, s₀, F)

    S: 状态集合
    Σ: 输入消息集合
    δ: S × Σ → S  (状态转换函数)
    s₀: 初始状态
    F: 终止状态集合 (可选)

Actor实现:
    struct FsmActor {
        state: S,
        context: Context,
    }

    impl Handler<Σ> for FsmActor {
        fn handle(&mut self, msg: Σ) {
            let new_state = δ(self.state, msg);
            self.state = new_state;
        }
    }
```

### 5.2 定理 FSM-SAFETY

```text
定理 FSM-INVALID-TRANSITION-PREVENTION: FSM Actor防止无效状态转换

证明:
1. δ函数只定义有效的状态转换
2. 未定义的(s, msg)组合不处理或报错
3. Actor顺序处理消息
4. ∴ 无效转换被阻止

定理 FSM-DETERMINISM: FSM Actor是确定性的

∀s ∈ S. ∀m ∈ Σ.
δ(s, m) 是唯一的
∴ 给定相同的消息序列，Actor到达相同的状态
```

### 5.3 状态机复杂度矩阵

| 复杂度 | 状态数 | 转换数 | 适用场景 |
|:---:|:---:|:---:|:---|
| 简单 | < 5 | < 10 | 基本工作流 |
| 中等 | 5-15 | 10-30 | 订单生命周期 |
| 复杂 | > 15 | > 30 | 业务流程引擎 |

---

## 6. Event Sourcing 模式

### 6.1 形式化定义

```text
定义 EVENT-SOURCING:

事件存储:
    EventStore = List<Event>

状态恢复:
    State₀ = initial_state()
    Stateₙ = fold(apply_event, State₀, events[0..n])

快照优化:
    ∀k ∈ ℕ. Snapshotₖ = State_{k×interval}
    Recovery = Snapshotₘ + events[m×interval..n]

不变式:
    current_state = apply_event(snapshot_state, new_events)
```

### 6.2 定理 EVENT-SOURCING-PROPERTIES

```text
定理 EVENT-SOURCING-AUDIT-TRAIL: 事件溯源提供完整审计跟踪

证明:
1. 所有事件按顺序存储
2. 事件不可变
3. 当前状态可由事件重放得到
4. ∴ 任何历史状态都可重建

定理 EVENT-SOURCING-TEMPORAL-QUERY: 事件溯源支持时间查询

∀t. state_at_time(t) = fold(apply_event, initial, events.filter(λe. e.time ≤ t))
```

### 6.3 事件溯源 vs CRUD 矩阵

| 特性 | Event Sourcing | CRUD |
|:---:|:---:|:---:|
| 审计性 | ⭐⭐⭐⭐⭐ | ⭐⭐ |
| 复杂度 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| 存储空间 | ⭐⭐ | ⭐⭐⭐⭐⭐ |
| 查询灵活性 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| 并发冲突 | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| 调试难度 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |

---

## 7. Pub-Sub 模式

### 7.1 形式化定义

```text
定义 PUB-SUB:

主题: Topic = String
订阅者: Subscriber = ActorRef

发布者状态:
    topics: Map<Topic, Set<Subscriber>>

操作:
    subscribe(t: Topic, s: Subscriber):
        topics[t] = topics[t] ∪ {s}

    unsubscribe(t: Topic, s: Subscriber):
        topics[t] = topics[t] \ {s}

    publish(t: Topic, m: Message):
        ∀s ∈ topics[t]. s.send(m)

消息传递保证:
    at-most-once: 尽力交付
    at-least-once: 确认机制
```

### 7.2 定理 PUB-SUB-SCALABILITY

```text
定理 PUB-SUB-DECOUPLING: Pub-Sub解耦生产者和消费者

证明:
1. 发布者不知道订阅者存在
2. 订阅者动态加入/离开
3. 双方独立扩展
4. ∴ 完全解耦

定理 PUB-SUB-FANOUT: Pub-Sub支持高效扇出

时间复杂度: O(|subscribers|)
与订阅者数量成线性关系
```

---

## 8. Saga 模式

### 8.1 形式化定义

```text
定义 SAGA:

Saga = 事务步骤序列
    steps: List<Step>

Step = {
    action: () → Result,
    compensate: () → Result,
}

执行:
    for step in steps:
        match step.action():
            Ok → continue
            Err → {
                for completed_step in reverse(completed):
                    completed_step.compensate()
                return Err
            }
    return Ok

补偿保证:
    补偿操作是幂等的
```

### 8.2 定理 SAGA-CONSISTENCY

```text
定理 SAGA-EVENTUAL-CONSISTENCY: Saga保证最终一致性

证明:
1. 所有步骤成功 → 事务完成
2. 某步失败 → 已执行步骤补偿
3. 补偿执行后，系统回到一致状态
4. ∴ 最终一致性

定理 SAGA-ISOLATION: Saga不提供隔离性

注意: Saga不保证ACID中的I（隔离性）
中间状态对其他事务可见
```

---

## 模式组合建议

### 8.1 常用组合

| 组合 | 模式 | 应用场景 |
|:---|:---|:---|
| 容错服务 | 监督树 + Circuit Breaker | 微服务 |
| 分布式事务 | Saga + Event Sourcing | 金融系统 |
| 状态服务 | FSM + Event Sourcing | 订单系统 |
| 消息系统 | Pub-Sub + 一致性哈希 | IM系统 |

---

**维护者**: Rust Actor Patterns Team
**更新日期**: 2026-03-05
**覆盖模式**: 8个核心模式 + 形式化定义
