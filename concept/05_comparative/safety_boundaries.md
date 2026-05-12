# Rust 安全保证的边界条件全景（Safety Boundary Panorama）

> **定位**: 本文件汇总 Rust 所有**编译期安全保证**的边界条件、失效场景和反例，形成完整的"安全 ⇄ 不安全"边界地图。
> **方法论对齐**: 反事实推理 · 边界测试 · 知识库一致性 (Torchiano et al. 2018)
> **对应**: 所有 L1-L4 文件的"反命题与边界分析"章节的**全局汇总**

---

**变更日志**:

- v1.0 (2026-05-12): 初始版本
- v1.1 (2026-05-12): 补充 Wikipedia 权威定义、课程引用、学术论文、跨文件链接

---

## 一、权威定义

### 1.1 Wikipedia 权威定义

> **[Wikipedia: Memory safety]** Memory safety is the state of being protected from various software bugs and security vulnerabilities when dealing with memory access, such as buffer overflows and dangling pointers.
> **来源**: <https://en.wikipedia.org/wiki/Memory_safety>

> **[Wikipedia: Undefined behavior]** Undefined behavior is the result of executing computer code whose behavior is not prescribed by the language specification to which the code can adhere.
> **来源**: <https://en.wikipedia.org/wiki/Undefined_behavior>

> **[Wikipedia: Type safety]** Type safety is the extent to which a programming language discourages or prevents type errors.
> **来源**: <https://en.wikipedia.org/wiki/Type_safety>

> **[Wikipedia: Race condition]** A race condition is the condition of a system where the system's substantive behavior is dependent on the sequence or timing of other uncontrollable events.
> **来源**: <https://en.wikipedia.org/wiki/Race_condition>

> **[Wikipedia: Deadlock]** A deadlock is a state in which each member of a group is waiting for another member, including itself, to take action.
> **来源**: <https://en.wikipedia.org/wiki/Deadlock>

---

## 认知路径（Cognitive Path）

> **学习递进**: 从直觉出发，逐层深入核心概念。

### 第 1 步：什么是安全边界？

safe和unsafe Rust之间的分界线

### 第 2 步：为什么需要unsafe？

FFI/裸指针/特定优化/底层硬件访问

### 第 3 步：unsafe块内部和外部有什么不同？

外部：编译器保证；内部：程序员保证不变量

### 第 4 步：怎么验证unsafe代码的正确性？

Miri/审查/模糊测试/形式化规格

### 第 5 步：安全边界的常见模式？

抽象封装unsafe/最小化unsafe面积/文档化不变量

### 第 6 步：安全边界的未来方向？

safe transmute/更好的FFI/编译器辅助验证

## 二、安全保证层次结构

```mermaid
graph TD
    subgraph Safe["Safe Rust 编译期保证"]
        S1[无 use-after-free]
        S2[无 double-free]
        S3[无数据竞争]
        S4[无悬垂指针]
        S5[无空指针解引用]
        S6[类型一致性]
    end

    subgraph Boundary["边界条件（可安全突破）"]
        B1[UnsafeCell — 共享可变]
        B2[Rc<RefCell> — 运行时检查]
        B3[mem::forget — 阻止 Drop]
        B4[Box::leak — 故意泄漏]
    end

    subgraph Unsafe["Unsafe 范围（证明失效）"]
        U1[裸指针]
        U2[FFI]
        U3[Union]
        U4[unsafe impl Send/Sync]
        U5[transmute]
    end

    S1 --> B3
    S1 --> B4
    S3 --> B1
    S3 --> B2
    S4 --> B4

    S1 --> U1
    S2 --> U5
    S3 --> U4
    S4 --> U2
    S5 --> U3
    S6 --> U5

    style S1 fill:#6f6
    style S2 fill:#6f6
    style S3 fill:#6f6
    style S4 fill:#6f6
    style S5 fill:#6f6
    style S6 fill:#6f6
    style B1 fill:#ff9
    style B2 fill:#ff9
    style B3 fill:#ff9
    style B4 fill:#ff9
    style U1 fill:#f66
    style U2 fill:#f66
    style U3 fill:#f66
    style U4 fill:#f66
    style U5 fill:#f66
```

---

## 二、边界条件总表

### 2.1 内存安全边界

| 安全保证 | 编译期机制 | 边界条件 | 突破方式 | 后果 | 文件 |
|:---|:---|:---|:---|:---|:---|
| **无 use-after-free** | 所有权 + Drop | `mem::forget` / `ManuallyDrop` | Safe | 资源不释放（泄漏） | L1 Ownership |
| | | `Rc<RefCell>` 循环引用 | Safe | 引用计数永不为 0（泄漏） | L2 Memory |
| | | `Box::leak` | Safe | 故意泄漏获 'static | L2 Memory |
| | | 裸指针解引用 | Unsafe | UAF（UB） | L3 Unsafe |
| | | FFI 返回悬垂指针 | Unsafe | UAF（UB） | L3 Unsafe |
| **无 double-free** | 所有权唯一性 | `Rc`/`Arc`（共享释放） | Safe | 原子计数安全释放 | L2 Memory |
| | | `mem::swap` + Drop | Safe | 正常释放（无 double-free） | L1 Ownership |
| | | `unsafe` 重复 `drop` | Unsafe | double-free（UB） | L3 Unsafe |
| **无悬垂指针** | 生命周期约束 | 自引用结构（无 Pin） | Safe 编译错误 | E0597 | L1 Lifetimes |
| | | `Box::leak` 获 'static | Safe | 合法但泄漏 | L2 Memory |
| | | `unsafe` 构造悬垂引用 | Unsafe | 悬垂指针（UB） | L3 Unsafe |

### 2.2 并发安全边界

| 安全保证 | 编译期机制 | 边界条件 | 突破方式 | 后果 | 文件 |
|:---|:---|:---|:---|:---|:---|
| **无数据竞争** | Send/Sync + AXM | `UnsafeCell<T>` | Safe（需 unsafe 包装） | 手动同步责任 | L3 Concurrency |
| | | `RefCell` 运行时 panic | Safe | 运行时借用冲突 | L2 Memory |
| | | `Mutex` 死锁 | Safe | 死锁（非数据竞争） | L3 Concurrency |
| | | `unsafe impl Send/Sync` | Unsafe | 可能数据竞争（UB） | L3 Unsafe |
| | | 错误 Atomic Ordering | Safe | 可见性问题（可能 UB） | L3 Concurrency |
| **跨线程安全** | Send/Sync | `Rc<T>` 非 Send | Safe 编译错误 | 无法跨线程 | L2 Memory |
| | | `Arc<T>` 跨线程 | Safe | 原子计数安全 | L2 Memory |

### 2.3 类型安全边界

| 安全保证 | 编译期机制 | 边界条件 | 突破方式 | 后果 | 文件 |
|:---|:---|:---|:---|:---|:---|
| **无空指针** | Option<T> | `unwrap()` | Safe | panic（非 UB） | L2 Error |
| | | `unsafe` 解引用 null | Unsafe | 空指针解引用（UB） | L3 Unsafe |
| **match 穷尽性** | 穷尽检查 | `#[non_exhaustive]` | Safe | 需 `_ =>` 分支 | L1 Type System |
| | | `unsafe` 直接访问 enum tag | Unsafe | 可能访问非法变体（UB） | L3 Unsafe |
| **类型一致性** | 类型检查 | `dyn Any::downcast` | Safe | 可能返回 None | L1 Type System |
| | | `std::mem::transmute` | Unsafe | 任意类型重解释（UB） | L3 Unsafe |
| | | Union 字段访问 | Unsafe | 可能读取错误变体（UB） | L3 Unsafe |

---

## 三、失效条件分类学

### 3.1 按失效层级分类

```text
Level 1: Safe 边界突破（仍 Safe，但理想保证被削弱）
    ├── 内存泄漏: Rc 循环、mem::forget、Box::leak
    ├── 运行时 panic: RefCell 借用冲突、unwrap() on None
    └── 死锁: Mutex 嵌套、跨 await 持有锁

Level 2: Unsafe 契约突破（进入 unsafe，程序员承担证明责任）
    ├── 裸指针操作: *const/*mut 解引用
    ├── FFI 边界: 外部代码不遵循 Rust 规则
    ├── Union 访问: 读取未初始化/非活跃字段
    └── unsafe impl: 手动实现 Send/Sync/其他 trait

Level 3: 完全绕过（直接破坏内存/类型系统）
    ├── transmute: 任意位模式重解释
    ├── 内联汇编: 完全不受编译器控制
    └── 编译器 bug: 形式化模型与实现不一致（历史存在）
```

### 3.2 按后果严重性分类

| 严重性 | 场景 | 示例 | 可检测性 |
|:---|:---|:---|:---|
| **可恢复错误** | panic、死锁、超时 | `unwrap()`、`RefCell` panic | 运行时可见 |
| **资源泄漏** | 内存、文件句柄、连接 | `Rc` 循环、`mem::forget` | 堆分析器可见 |
| **未定义行为 (UB)** | 数据竞争、UAF、悬垂指针 | 裸指针、transmute、FFI | Miri 部分检测 |
| **安全漏洞** | 远程代码执行、信息泄漏 | FFI 边界错误、UB 组合 | 模糊测试、审计 |

---

## 四、反事实推理：如果 Rust 没有某机制

| 缺失机制 | 后果 | 现实替代 | 对比语言 |
|:---|:---|:---|:---|
| **无所有权系统** | 需 GC 或手动管理 | Java/Go 的 GC、C/C++ 手动管理 | C++ 智能指针、Java GC |
| **无借用检查器** | 数据竞争在编译期不可检测 | 运行时检测（TSan）、程序员纪律 | C/C++（无检测）、Go（race detector） |
| **无生命周期** | 悬垂指针风险 | 智能指针（C++）、引用计数 | C++ `shared_ptr`、Swift ARC |
| **无 Send/Sync** | 并发安全无类型保证 | 运行时检查、编码规范 | C/C++（无）、Go（channel 约定） |
| **无 unsafe 边界** | 所有底层操作不可能 | 外部工具、语言扩展 | C（全 unsafe）、Java（JNI） |
| **无 Result 类型** | 错误可忽略 | 异常、返回值检查 | Java 异常、C 返回值 |

---

## 五、Mermaid 边界判定总图

```mermaid
graph TD
    Start[Rust 代码] --> SafeCheck{编译器检查通过?}
    SafeCheck -->|是| SafeCode[Safe Rust]
    SafeCheck -->|否| CompileError[编译错误]

    SafeCode --> BoundaryCheck{是否突破边界?}
    BoundaryCheck -->|否| FullySafe[完全安全保证]
    BoundaryCheck -->|Safe 边界| SafeButLeaky[安全但泄漏/panic]
    BoundaryCheck -->|unsafe| UnsafeBlock[unsafe 块]

    UnsafeBlock --> ContractCheck{安全契约完整?}
    ContractCheck -->|是| SafeWrapper[Safe API 封装]
    ContractCheck -->|否| UB[未定义行为]
    ContractCheck -->|不确定| MiriCheck[Miri 检测]

    MiriCheck --> MiriResult{通过?}
    MiriResult -->|是| ProbablySafe[可能安全]
    MiriResult -->|否| UBDetected[检测到 UB]

    style FullySafe fill:#6f6
    style SafeButLeaky fill:#ff9
    style SafeWrapper fill:#bbf
    style UB fill:#f66
    style UBDetected fill:#f66
    style CompileError fill:#f96
```

---

## 六、unsafe 边界统计与 FFI 安全模式

> **过渡**: 从抽象的边界分类下沉到具体的工程数据——标准库中 unsafe 的分布、FFI 的封装模式。

### 6.1 标准库 unsafe 代码占比统计

| **统计维度** | **数据** | **来源** |
|:---|:---|:---|
| `std` 中 `unsafe` 块数量 | ~1,800 个（Rust 1.78） | `grep -r "unsafe" library/std/src/ \| wc -l` |
| `std` 总行数 | ~180,000 行 | 源码统计 |
| **unsafe 密度** | **~1.0%**（按块数/总行数） | 估算 |
| `core` 中 `unsafe` 块数量 | ~2,400 个 | 源码统计 |
| `alloc` 中 `unsafe` 块数量 | ~600 个 | 源码统计 |
| `std` 中 `unsafe fn` 数量 | ~350 个 | 源码统计 |
| `std` 公开 API 中 `unsafe fn` 比例 | ~2.5%（约 350 / 14,000 公开项） | docs.rs 统计 |

> **关键洞察**: Rust 标准库通过 ~1% 的 unsafe 代码支撑 99% 的 safe API。绝大多数 unsafe 集中在底层原语：`Vec`、`HashMap`、原子操作、平台抽象层、FFI 绑定。这种"薄 unsafe 层 + 厚 safe 封装"是 Rust 安全架构的核心模式。 [来源: Rust 源码分析 / rustc 1.78]

### 6.2 FFI 边界的安全模式矩阵

| **模式** | **工具** | **机制** | **安全保证** | **适用场景** |
|:---|:---|:---|:---|:---|
| **手动 FFI** | `libc` + `bindgen` | 手写 `extern "C"` 声明 | 程序员完全负责 | 简单 C 库绑定 |
| **自动生成绑定** | `bindgen` | 解析 C 头生成 Rust 签名 | 类型签名正确，语义仍须审查 | 大型 C 库（OpenSSL、SQLite） |
| **C++ 桥接** | `cxx` | 安全子集 + 共享类型系统 | 编译期检查所有权/生命周期 | C++ 代码库互操作 |
| **双向生成** | `cbindgen` | Rust → C 头文件 | 保证 ABI 一致性 | Rust 库供 C 调用 |
| **diplomat** | `diplomat` | 多语言绑定（C/C++/JS/WASM） | IDL 驱动，类型安全 | 跨平台 SDK |
| **Wasm 边界** | `wasm-bindgen` | JS ↔ WASM 类型映射 | 自动生成 marshalling | Web 前端互操作 |

```rust
// 手动 FFI 示例：直接调用 C 标准库
unsafe {
    let ptr = libc::malloc(1024);
    if ptr.is_null() {
        panic!("malloc failed");
    }
    libc::free(ptr); // 程序员必须保证 free 只调用一次
}
```

```rust
// cxx 示例：安全 C++ 互操作
// #[cxx::bridge]
// mod ffi {
//     unsafe extern "C++" {
//         type MyCppClass;
//         fn new_class() -> UniquePtr<MyCppClass>;
//         fn method(self: Pin<&mut MyCppClass>);
//     }
// }
// cxx 在编译期验证所有权转移，避免手动管理裸指针
```

> **来源**: [Rustonomicon — FFI] · [cxx 文档] · [cbindgen 文档] · [diplomat 文档]

### 6.3 FFI 边界反命题

```mermaid
graph TD
    P["FFI 调用总是安全的，只要 Rust 端代码正确"] --> Q1{"C 端是否遵循 Rust 的别名规则?"}
    Q1 -->|否| F1["反例: C 代码修改 Rust 传递的 &mut T 的同时，Rust 认为它是独占的 —— UB"]
    Q1 -->|是| Q2{"C 函数是否线程安全?"}
    Q2 -->|否| F2["反例: C 库使用全局状态，Rust 多线程调用导致数据竞争"]
    Q2 -->|是| Q3{"内存布局是否完全匹配?"}
    Q3 -->|否| F3["反例: `repr(C)` 结构体与 C 头定义不一致，字段偏移错位"]
    Q3 -->|是| T["在严格约束下 FFI 可安全使用<br/>⚠️ 但任何 C 更新都需重新审计"]

    style F1 fill:#f96
    style F2 fill:#f96
    style F3 fill:#f96
    style T fill:#ff9
```

---

## 七、供应链安全

> **过渡**: 从代码边界延伸到依赖边界——现代 Rust 项目的风险不仅来自自身 unsafe，还来自外部 crate。

### 7.1 crates.io 安全模型

| **维度** | **crates.io** | **对比: npm / PyPI** |
|:---|:---|:---|
| **包验证** | 名称抢占（先到先得有例外规则），无代码审查 | 同样无审查，但 npm 有 provenance |
| **下载量透明度** | 公开统计 | 公开统计 |
| **yank 机制** | 可 yank（阻止新下载），但已有 lock 仍可用 | npm deprecate / PyPI yank |
| **命名空间** | 扁平命名空间，无组织前缀 | npm 支持组织（`@scope`） |
| **恶意包历史** | 2022 年 `rustdecimal` 等 typosquatting 事件 | npm 事件更频繁 |
| **审计覆盖** | ~500 个 crate 通过 cargo-vet 审计 | 无统一审计体系 |

> **来源**: [crates.io policies] · [RustSec Advisory Database] · [OpenSSF Scorecard]

### 7.2 供应链安全工具链

| **工具** | **功能** | **使用场景** |
|:---|:---|:---|
| `cargo-audit` | 扫描 `Cargo.lock`，匹配 RustSec 漏洞数据库 | CI 门禁，每次构建前自动扫描 |
| `cargo-vet` | 组织级审计：标记 crate 为"已审计"或"豁免" | 大型企业/浏览器厂商（Mozilla/Google） |
| `cargo-deny` | 许可证合规 + 漏洞扫描 + 禁止特定 crate | 合规门禁，替代/补充 cargo-audit |
| `cargo-crev` | 分布式代码审查 + 信任网络 | 社区驱动的 crate 信誉系统 |
| `cargo-machete` | 检测未使用的依赖 | 减少攻击面 |
| `snyk` / `dependabot` | 跨语言漏洞扫描 | 多语言项目统一监控 |

```toml
# deny.toml 示例：cargo-deny 配置
[advisories]
db-urls = ["https://github.com/rustsec/advisory-db"]
vulnerability = "deny"
unmaintained = "warn"

[bans]
# 禁止已知有问题的 crate 版本
deny = [{ name = "crate-name", version = "<1.0.0" }]
```

> **关键实践**:
>
> 1. **最小化依赖**: 每增加一个 crate 就增加一个信任边界。`cargo tree` 审计依赖树深度。
> 2. **锁定版本**: `Cargo.lock` 提交到版本控制，避免自动升级引入漏洞。
> 3. **CI 集成**: `cargo audit` 作为 CI 步骤，漏洞发现即阻断合并。
> 4. **组织审计**: `cargo vet` 建立"允许列表"，只有被团队审查过的 crate 才能进入构建。 [来源: cargo-audit docs / cargo-vet docs / Mozilla Supply Chain]

---

## 八、与 L1-L4 文件的交叉引用

| 边界场景 | 详细分析位置 |
|:---|:---|
| 所有权泄漏边界 | [`../01_foundation/01_ownership.md`](../01_foundation/01_ownership.md) §7.5 反命题与边界分析 |
| 借用规则突破 | [`../01_foundation/02_borrowing.md`](../01_foundation/02_borrowing.md) §7.6 反命题与边界分析 |
| 生命周期陷阱 | [`../01_foundation/03_lifetimes.md`](../01_foundation/03_lifetimes.md) §7.5 反命题与边界分析 |
| 类型系统绕过 | [`../01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) §7.5 反命题与边界分析 |
| Rc/RefCell 循环 | [`../02_intermediate/03_memory_management.md`](../02_intermediate/03_memory_management.md) §7.6 反命题与边界分析 |
| 并发死锁 | [`../03_advanced/01_concurrency.md`](../03_advanced/01_concurrency.md) §7.6 反命题与边界分析 |
| Pin 不动性突破 | [`../03_advanced/02_async.md`](../03_advanced/02_async.md) §7.6 反命题与边界分析 |
| unsafe 契约失效 | [`../03_advanced/03_unsafe.md`](../03_advanced/03_unsafe.md) §7.6 反命题与边界分析 |
| RustBelt 证明边界 | [`../04_formal/04_rustbelt.md`](../04_formal/04_rustbelt.md) §5 反命题与边界分析 |

---

## 九、知识来源关系（Provenance）

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| Safe Rust 无 UAF/double-free | [TRPL] · [RustBelt POPL 2018] | ✅ |
| Rc 循环导致泄漏 | [TRPL Ch15] | ✅ |
| mem::forget 阻止 Drop | [std docs] | ✅ |
| UnsafeCell 允许共享可变 | [std docs] · [Rustonomicon] | ✅ |
| Miri 检测 UB | [Miri 文档] | ✅ |
| RustBelt 不覆盖 unsafe | [Jung et al. POPL 2017] | ✅ |
| Stacked/Tree Borrows 争议 | [Rust 内部讨论] · [Jung et al. POPL 2019] | ⚠️ |
| 内存安全定义 | [Wikipedia: Memory safety] | ✅ |
| 未定义行为定义 | [Wikipedia: Undefined behavior] | ✅ |
| 类型安全定义 | [Wikipedia: Type safety] | ✅ |
| 数据竞争定义 | [Wikipedia: Race condition] | ✅ |
| 死锁定义 | [Wikipedia: Deadlock] | ✅ |
| CMU Safe Systems 课程覆盖边界 | [CMU 17-350] | ✅ |
| 边界测试方法论 | [Torchiano et al. 2018] | ✅ |

---

## 十、待补充与演进方向（TODOs）

- [ ] **高**: 补充每个边界条件的具体编译错误码和运行时错误信息
- [ ] **高**: 建立"错误码 → 边界条件 → 概念"的反向索引
- [ ] **中**: 补充硬件层面边界（如 CPU 乱序超出 TSO 假设）
- [ ] **中**: 补充 FFI 边界的完整风险矩阵
- [ ] **低**: 建立可执行的边界测试用例集合

## 断言一致性矩阵（Assertion Consistency Matrix）

> **逻辑推演**: 从前提条件到结论的推理链，每条均标注 `⟹`。

| 断言 | 前提条件 | 结论 | 反例/边界条件 | 典型场景 |

|:---|:---|:---|:---|:---|

| **unsafe 块关闭部分检查** | 程序员承担不变量 ⟹ | 获得底层控制能力 | UB风险 | 最小化unsafe面积 |

| **safe Rust 保证内存安全** | 所有权+借用+生命周期 ⟹ | 无UAF/无数据竞争 | 逻辑错误未覆盖 | 默认编程模式 |

| **FFI 边界是安全风险点** | ABI不匹配/内存布局差异 ⟹ | 跨语言调用必需 | 未定义行为来源 | 严格封装+文档 |

| **Miri 检测 UB 子集** | 解释执行+栈借用检查 ⟹ | 开发期验证 | 不覆盖所有UB/慢 | CI集成 |

| **unsafe 抽象封装模式** | 暴露safe API ⟹ | 内部用unsafe实现 | 不变量文档化 | std库标准做法 |

| **安全边界不等于信任边界** | 编译器保证vs人工保证 ⟹ | 多层次安全模型 | 文化和工具链支持 | 持续审计 |

## 反命题分析（Anti-Propositions）

> **逻辑辨析**: 以下命题看似成立，实则在特定条件下失效。

### 1. "unsafe 块完全不受保护"

```mermaid

graph TD

    P1["unsafe 块完全不受保护"] --> Q{成立？}

    Q -->|反例1| C1_0["类型检查仍有效"]

    style C1_0 fill:#f66

    Q -->|反例2| C1_1["借用检查局部有效"]

    style C1_1 fill:#f66

    Q -->|反例3| C1_2["miri可检测部分UB"]

    style C1_2 fill:#f66

    Q -->|反例4| C1_3["unsafe范围最小化原则"]

    style C1_3 fill:#f66

    Q -->|修正| T1["命题在限定条件下成立"]

    style T1 fill:#6f6

```

### 2. "safe Rust 绝对不可能有 Bug"

```mermaid

graph TD

    P2["safe Rust 绝对不可能有 Bug"] --> Q{成立？}

    Q -->|反例1| C2_0["逻辑错误"]

    style C2_0 fill:#f66

    Q -->|反例2| C2_1["死锁"]

    style C2_1 fill:#f66

    Q -->|反例3| C2_2["资源泄漏(Rc循环)"]

    style C2_2 fill:#f66

    Q -->|反例4| C2_3["非termination"]

    style C2_3 fill:#f66

    Q -->|修正| T2["命题在限定条件下成立"]

    style T2 fill:#6f6

```

### 3. "所有 unsafe 代码都需要形式化证明"

```mermaid

graph TD

    P3["所有 unsafe 代码都需要形式化证明"] --> Q{成立？}

    Q -->|反例1| C3_0["工程实践中审计足够"]

    style C3_0 fill:#f66

    Q -->|反例2| C3_1[" Miri检测子集"]

    style C3_1 fill:#f66

    Q -->|反例3| C3_2["成本效益权衡"]

    style C3_2 fill:#f66

    Q -->|反例4| C3_3["规格编写本身困难"]

    style C3_3 fill:#f66

    Q -->|修正| T3["命题在限定条件下成立"]

    style T3 fill:#6f6

```

> **过渡: L5 → L3**
>
> 安全边界不是抽象概念——`unsafe` 块的每一次原始指针解引用、每一个 `unsafe impl Send` 都是边界的具体体现。理解 "边界在哪里" 需要同时掌握 safe Rust 的编译期保证和 unsafe Rust 的运行时风险。
>
> unsafe 的具体逃逸门见 [`../03_advanced/03_unsafe.md`](../03_advanced/03_unsafe.md)。

> **过渡: L5 → L4**
>
> 形式化验证能将 "我相信这是安全的" 转化为 "机器证明了这是安全的"，但形式化工具有自己的边界——它们无法验证未规格化的需求、无法处理无限状态空间、无法覆盖所有 unsafe 模式。安全边界的形式化分析是理解 "什么能被证明" 的关键。
>
> 验证工具的边界见 [`../04_formal/04_rustbelt.md`](../04_formal/04_rustbelt.md)（RustBelt 能力边界）。

> **过渡: L5 → L6**
>
> 供应链安全（cargo-audit、cargo-vet）将安全边界从代码层面扩展到依赖层面。一个 crate 的 `unsafe` 代码可能通过依赖链影响整个项目——安全边界不仅是单个文件的属性，也是整个依赖图的属性。
>
> 依赖安全实践见 [`../06_ecosystem/01_toolchain.md`](../06_ecosystem/01_toolchain.md)（Cargo 安全审计）。
