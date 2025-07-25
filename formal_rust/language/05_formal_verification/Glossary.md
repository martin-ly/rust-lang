# 05 形式化验证 术语表

| 术语 | 英文 | 定义/解释 |
|------|------|-----------|
| 类型安全 | Type Safety | 良类型程序在运行时不会发生未定义行为（如类型不匹配、非法内存访问等） |
| 健全性 | Soundness | 类型系统的规则能够保证类型安全 |
| 进展定理 | Progress Theorem | 良类型程序要么是值，要么可以继续执行（不会卡死） |
| 保持定理 | Preservation Theorem | 良类型程序每一步求值后，类型保持不变 |
| 所有权 | Ownership | 每个值有唯一所有者，离开作用域自动释放 |
| 借用 | Borrowing | 允许临时访问资源，分为可变借用与不可变借用 |
| 生命周期 | Lifetime | 静态追踪引用的有效期，防止悬垂指针 |
| 分离逻辑 | Separation Logic | 用于推理带指针和堆内存的程序，核心为分离合取（*）和帧规则 |
| 帧规则 | Frame Rule | 支持局部推理与资源隔离的分离逻辑推理规则 |
| 并发安全 | Concurrency Safety | 类型系统与分离逻辑共同保证无数据竞争、原子性与资源独占 |
| 机械化证明 | Mechanized Proof | 利用定理证明器对程序或类型系统进行形式化建模与自动化证明 |
| Prusti | Prusti | 基于Viper的Rust自动化验证工具，支持前后置条件、不变式等静态验证 |
| Kani | Kani | 基于模型检查的Rust验证工具，适合嵌入式、并发等场景 |
| Creusot | Creusot | 面向高阶函数、trait等复杂特性的Rust验证工具 |
| Coq | Coq | 基于依赖类型理论的交互式定理证明器，广泛用于类型系统与编译器验证 |
| Isabelle | Isabelle | 高阶逻辑定理证明器，适合大规模工程化验证 |
| Lean | Lean | 新兴定理证明器，强调可编程性与社区协作 |
| RustBelt | RustBelt | 用分离逻辑与高阶验证工具形式化证明Rust安全性的前沿项目 |
| Progress/Preservation | 进展/保持 | 类型安全性证明的两大核心定理 |
| Send/Sync | Send/Sync | Rust类型系统中标记线程安全能力的trait |
| unsafe | unsafe | Rust中允许绕过类型系统安全检查的代码块，需配合形式化验证保障安全 |
