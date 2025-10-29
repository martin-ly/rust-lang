# 🚀 可持续执行计划 - 行动手册

> **计划日期**: 2025-10-30  
> **规划周期**: 3 个月（2025-11 至 2026-01）  
> **目标**: 将项目从"过度工程化"转向"可持续发展"  
> **参考**: [批判性评价报告](CRATES_CRITICAL_EVALUATION_2025_10_30.md)

---

## 🎯 总体目标

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
当前状态:
• 500+ 文档
• 300,000+ 行代码/文档
• 维护成本: 极高
• 用户上手: 困难
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
3 个月后目标:
• 200 个核心文档（↓ 60%）
• 清晰的学习路径
• 维护成本: ↓ 70%
• 新人上手: < 4 小时
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 📅 Week 1-2: 紧急清理（11月第1-2周）

### Day 1-2: 文档归档 ✅ 最高优先级

**时间**: 4-6 小时

#### 任务 1.1: 清理 docs/docs/ 

```bash
# 执行自动归档
cd /e/_src/rust-lang
./scripts/archive_docs.sh

# 验证结果
ls docs/docs/*.md | wc -l  # 应该 ≤ 35 个

# 创建归档说明
cat > docs/docs/archive/README.md << 'EOF'
# 归档文档说明

本目录包含历史文档，仅作参考：

- phase_reports/ - 各阶段完成报告
- module_reports/ - 模块详细报告
- planning/ - 历史计划文档
- temp/ - 临时文档

**注意**: 这些文档已过时，请参考主目录的最新文档。
EOF
```

**检查点**: ✅ docs/docs/ 只剩 30-35 个核心文档

---

#### 任务 1.2: 清理各模块内部

```bash
# 创建清理脚本
cat > scripts/clean_modules.sh << 'EOF'
#!/bin/bash

MODULES=(
    "c01_ownership_borrow_scope"
    "c02_type_system"
    "c03_control_fn"
    "c04_generic"
    "c05_threads"
    "c06_async"
    "c07_process"
    "c08_algorithms"
    "c09_design_pattern"
    "c10_networks"
    "c11_macro_system"
)

for module in "${MODULES[@]}"; do
    echo "清理 $module..."
    
    # 创建归档目录
    mkdir -p "crates/$module/docs/archive"
    mkdir -p "crates/$module/backup"
    
    # 移动 swap.rar
    mv "crates/$module/docs/swap.rar" "crates/$module/backup/" 2>/dev/null
    
    # 移动历史报告
    mv "crates/$module/docs/"*PHASE*.md "crates/$module/docs/archive/" 2>/dev/null
    mv "crates/$module/docs/"*COMPLETION*.md "crates/$module/docs/archive/" 2>/dev/null
    
    # 移动旧报告到 reports/
    mkdir -p "crates/$module/reports"
    mv "crates/$module/docs/"*REPORT*.md "crates/$module/reports/" 2>/dev/null
    mv "crates/$module/docs/"*STATUS*.md "crates/$module/reports/" 2>/dev/null
    
    echo "✅ $module 清理完成"
done

echo ""
echo "🎉 所有模块清理完成！"
EOF

chmod +x scripts/clean_modules.sh
./scripts/clean_modules.sh
```

**检查点**: ✅ 每个模块 docs/ 只有核心文档

---

### Day 3-4: 创建简化标准

**时间**: 6-8 小时

#### 任务 2.1: 文档标准

创建文件: `docs/DOCUMENTATION_STANDARDS_V2.md`

```markdown
# 文档标准 v2.0 - 简化版

## 🎯 核心原则

1. **少即是多**: 宁缺毋滥
2. **用户优先**: 为学习者而写，非专家
3. **可维护**: 一人能够维护

---

## 📏 强制规则

### 规则 1: 文件数量限制

| 目录 | 最大文件数 | 说明 |
|------|-----------|------|
| docs/ | 20 个 | 核心文档 |
| docs/advanced/ | 10 个 | 可选 |
| examples/ | 20 个 | 精选示例 |

**超过限制？说明需要拆分或删减！**

---

### 规则 2: 文件长度限制

| 文件类型 | 最大行数 | 原因 |
|---------|---------|------|
| README.md | 200 行 | 快速浏览 |
| 指南文档 | 300 行 | 一次读完 |
| 参考文档 | 500 行 | 可查阅 |
| 理论文档 | 800 行 | 深度内容 |

**超过限制？拆分成多个文件！**

---

### 规则 3: 必须有的 5 个文件

每个模块必须有且仅有：

1. **README.md** (< 200 行)
   ```markdown
   # C0X - [模块名]
   
   ## 🎯 5 分钟了解
   [3 段介绍]
   
   ## 🚀 快速开始
   [1 个最简示例]
   
   ## 📚 学习路径
   - 🟢 入门 (2-4h)
   - 🟡 进阶 (1-2天)
   - 🔴 高级 (持续)
   
   ## 📖 文档
   - [完整指南](docs/guide.md)
   - [API参考](docs/reference.md)
   - [FAQ](docs/FAQ.md)
   ```

2. **docs/guide.md** (< 300 行)
   - 实战教程
   - 常见场景
   - 代码示例

3. **docs/reference.md** (< 200 行)
   - API 速查
   - 最佳实践
   - 性能提示

4. **docs/FAQ.md** (< 100 行)
   - 常见问题
   - 错误排查

5. **CHANGELOG.md**
   - 版本历史

---

### 规则 4: 禁止事项 ❌

| 禁止 | 原因 |
|------|------|
| ❌ 多个主索引 | 造成混乱 |
| ❌ swap.rar 在主目录 | 污染项目 |
| ❌ PHASE*.md 在主目录 | 历史文件应归档 |
| ❌ 5 层以上嵌套 | 难以导航 |
| ❌ 未测试的代码示例 | 误导用户 |

---

## ✅ 质量检查清单

创建 PR 前必须检查：

- [ ] README.md < 200 行
- [ ] 所有代码示例可运行
- [ ] 没有死链接
- [ ] 没有重复内容
- [ ] 符合上述规则
```

**检查点**: ✅ 标准文档创建完成

---

#### 任务 2.2: 创建自动检查脚本

```bash
# 创建文件: scripts/check_standards.sh
#!/bin/bash

echo "📋 检查文档标准..."

# 检查 README 长度
for readme in crates/*/README.md; do
    lines=$(wc -l < "$readme")
    if [ $lines -gt 200 ]; then
        echo "⚠️  $readme 太长: $lines 行 (限制 200 行)"
    fi
done

# 检查 docs/ 文件数
for module in crates/*; do
    if [ -d "$module/docs" ]; then
        count=$(find "$module/docs" -maxdepth 1 -name "*.md" | wc -l)
        if [ $count -gt 20 ]; then
            echo "⚠️  $module/docs/ 文件过多: $count 个 (限制 20 个)"
        fi
    fi
done

# 检查是否有 swap.rar
if find crates/*/docs -name "swap.rar" | grep -q .; then
    echo "⚠️  发现 swap.rar 文件，应移到 backup/"
fi

echo "✅ 检查完成"
```

**检查点**: ✅ 自动检查脚本可用

---

### Day 5-7: 重写核心 README

**时间**: 12-15 小时

#### 任务 3.1: C01 Ownership README

当前: 600+ 行 → 目标: < 200 行

```markdown
# C01 - Rust 所有权系统

> **学习时间**: 入门 4h | 精通 2-3 天  
> **前置知识**: 基本编程概念  
> **Rust版本**: 1.90+

---

## 🎯 5 分钟了解

**所有权系统**是 Rust 最核心的特性，它在编译时保证内存安全，无需垃圾回收。

**三大规则**:
1. 每个值有一个所有者
2. 同一时间只能有一个所有者
3. 所有者离开作用域，值被丢弃

**为什么重要？**
- ✅ 零成本内存安全
- ✅ 无数据竞争
- ✅ 无悬垂指针

---

## 🚀 10 分钟上手

```rust
// 1. 所有权转移
let s1 = String::from("hello");
let s2 = s1;  // s1 不再有效
// println!("{}", s1);  // ❌ 编译错误

// 2. 借用
let s1 = String::from("hello");
let len = calculate_length(&s1);  // 借用
println!("{} 的长度是 {}", s1, len);  // ✅ s1 仍然有效

fn calculate_length(s: &String) -> usize {
    s.len()
}
```

[▶️ 运行完整示例](examples/01_basics.rs)

---

## 📚 学习路径

### 🟢 入门（4 小时）

1. **基础概念** (1h)
   - [所有权规则](docs/01_ownership_rules.md)
   - [Move vs Copy](docs/02_move_copy.md)
   
2. **借用系统** (1.5h)
   - [引用与借用](docs/03_borrowing.md)
   - [可变借用](docs/04_mut_borrow.md)
   
3. **实战练习** (1.5h)
   - [常见错误](docs/05_common_errors.md)
   - [动手练习](examples/exercises/)

**完成后**: 你能写出基本的 Rust 程序

---

### 🟡 进阶（1-2 天）

4. **生命周期** (4h)
   - [生命周期基础](docs/06_lifetimes.md)
   - [高级生命周期](docs/07_advanced_lifetimes.md)
   
5. **智能指针** (4h)
   - [Box/Rc/Arc](docs/08_smart_pointers.md)
   - [RefCell 内部可变性](docs/09_refcell.md)
   
6. **实战项目** (4h)
   - [构建 LRU 缓存](examples/projects/lru_cache/)
   - [实现链表](examples/projects/linked_list/)

**完成后**: 你能处理复杂的所有权场景

---

### 🔴 高级（持续学习）

7. **性能优化** (8h+)
   - [零成本抽象](docs/advanced/zero_cost.md)
   - [内存布局](docs/advanced/memory_layout.md)
   
8. **高级模式** (8h+)
   - [自引用结构](docs/advanced/self_referential.md)
   - [跨线程所有权](docs/advanced/send_sync.md)

---

## 📖 完整文档

| 文档 | 用途 | 时长 |
|------|------|------|
| [完整指南](docs/guide.md) | 系统学习 | 8-12h |
| [API 参考](docs/reference.md) | 速查手册 | 查阅 |
| [FAQ](docs/FAQ.md) | 常见问题 | 30min |
| [高级主题](docs/advanced/) | 深入研究 | 20h+ |

---

## 💻 代码示例

**基础** (examples/basic/):
- `01_ownership.rs` - 所有权转移
- `02_borrowing.rs` - 引用与借用
- `03_lifetimes.rs` - 生命周期

**进阶** (examples/intermediate/):
- `04_smart_pointers.rs` - 智能指针
- `05_self_referential.rs` - 自引用

**实战** (examples/projects/):
- `lru_cache/` - LRU 缓存实现
- `linked_list/` - 链表实现

[查看所有示例](examples/)

---

## 🤝 贡献与反馈

发现问题？有改进建议？

- 🐛 [报告 Bug](../../issues)
- 💬 [讨论交流](../../discussions)
- 📝 [贡献指南](CONTRIBUTING.md)

---

## 📊 模块统计

```text
📚 核心文档: 15 个
💻 代码示例: 50+ 个
🧪 测试覆盖: 100%
⭐ 用户评分: ⭐⭐⭐⭐⭐
📅 最后更新: 2025-10-30
```

---

**下一步**: [开始学习](docs/01_ownership_rules.md) | [快速参考](docs/reference.md)
```

**检查点**: ✅ C01 README 精简完成

---

#### 任务 3.2: C06 Async README

**检查点**: ✅ C06 README 精简完成

#### 任务 3.3: C09 Design Pattern README

**检查点**: ✅ C09 README 精简完成

---

### Day 8-10: 创建快速路径

**时间**: 8-10 小时

#### 任务 4: 创建 QUICK_PATHS.md

```markdown
# 🚀 Rust 快速学习路径

> **目标**: 不同时间预算的最优学习路径  
> **原则**: 实战优先，理论够用即可

---

## 🏃 路径 1: 30 分钟体验 Rust

**目标**: 感受 Rust 的特点

```text
时间分配:
━━━━━━━━━━━━━━━━━━━━━━━━━━
1. 安装 Rust (5 分钟)
2. Hello World (5 分钟)
3. 所有权快速理解 (10 分钟)
4. 运行一个示例 (10 分钟)
━━━━━━━━━━━━━━━━━━━━━━━━━━
```

**操作步骤**:

```bash
# 1. 安装
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 2. Hello World
cargo new hello_rust
cd hello_rust
cargo run

# 3. 所有权示例
cd crates/c01_ownership_borrow_scope
cargo run --example 01_ownership

# 4. 阅读
cat examples/01_ownership.rs
```

**学完后你将**:
- ✅ 知道 Rust 长什么样
- ✅ 理解所有权的基本概念
- ✅ 决定是否继续学习

---

## 🚶 路径 2: 2 小时快速入门

**目标**: 能写简单的 Rust 程序

| 时间 | 模块 | 内容 | 输出 |
|------|------|------|------|
| 30 min | C01 | 所有权基础 | 理解 Move/Borrow |
| 30 min | C02 | 类型系统 | 掌握基本类型 |
| 30 min | C03 | 控制流 | if/loop/match |
| 30 min | 实战 | 写一个小程序 | CLI 工具 |

**实战项目**: 构建一个简单的 TODO CLI

```bash
cd examples/quickstart_projects/todo_cli
cargo run
```

---

## 🚴 路径 3: 1 天掌握核心

**目标**: 能写中等复杂的程序

### 上午（4 小时）

| 时间 | 内容 |
|------|------|
| 9:00-10:00 | C01 所有权系统 |
| 10:00-11:00 | C02 类型系统 |
| 11:00-12:00 | C03 控制流 |
| 12:00-13:00 | C04 泛型 |

### 下午（4 小时）

| 时间 | 内容 |
|------|------|
| 14:00-16:00 | C05 并发编程 |
| 16:00-17:00 | 实战项目：多线程文件处理 |
| 17:00-18:00 | 错误处理与测试 |

**实战项目**: 
- 多线程文件搜索工具
- 简单的 Web 服务器

---

## 🏃‍♂️ 路径 4: 1 周深入学习

**目标**: 能独立开发项目

### Day 1-2: 基础巩固
- C01-C04 深入学习
- 完成 20+ 练习题
- 实战: CLI 工具

### Day 3-4: 并发与异步
- C05 线程与并发
- C06 异步编程
- 实战: 异步 Web 服务

### Day 5: 高级特性
- C09 设计模式
- C11 宏系统
- 实战: 构建 DSL

### Day 6-7: 综合项目
- 构建一个完整应用
- 测试、文档、部署
- 代码审查与优化

**项目建议**:
- Web API 服务
- 命令行工具
- 系统工具

---

## 🚗 路径 5: 1 个月精通

**Week 1: 语言基础**
- 系统学习 C01-C04
- 刷 50+ 练习题
- 阅读他人代码

**Week 2: 系统编程**
- C05 并发
- C07 进程管理
- C10 网络编程

**Week 3: 现代特性**
- C06 异步
- C09 设计模式
- C11 宏

**Week 4: 实战与生态**
- 完整项目开发
- 生态工具学习
- 开源贡献

---

## 🎯 按需求选路径

### 我想做 Web 开发

**必学**: C01, C02, C06 (async), C10 (network)  
**推荐**: C09 (patterns)  
**时间**: 2-3 周  
**项目**: RESTful API + 数据库

---

### 我想做系统编程

**必学**: C01, C02, C05 (threads), C07 (process)  
**推荐**: C10 (network)  
**时间**: 3-4 周  
**项目**: 文件系统工具 / 网络代理

---

### 我想做命令行工具

**必学**: C01, C02, C03  
**推荐**: C04 (generics)  
**时间**: 1-2 周  
**项目**: 实用 CLI 工具

---

### 我想深入理解 Rust

**必学**: 所有模块  
**推荐**: 阅读标准库源码  
**时间**: 2-3 个月  
**目标**: 贡献 Rust 生态

---

## 📚 配套资源

### 官方资源
- [The Rust Book](https://doc.rust-lang.org/book/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)
- [Rustlings](https://github.com/rust-lang/rustlings)

### 本项目资源
- [模块导航](../crates/)
- [完整文档](../docs/)
- [代码示例](../examples/)

### 社区资源
- [Rust 中文社区](https://rust.cc/)
- [r/rust](https://reddit.com/r/rust)
- [Rust Users Forum](https://users.rust-lang.org/)

---

## 🎓 学习建议

1. **边做边学**: 不要只看不练
2. **写注释**: 用自己的话解释代码
3. **读错误**: Rust 编译器很友好
4. **多提问**: 社区很友善
5. **写博客**: 教是最好的学

---

**开始学习**: [选择你的路径](#) | [查看模块](../crates/)
```

**检查点**: ✅ QUICK_PATHS.md 创建完成

---

## 📅 Week 3-4: 精简核心模块（11月第3-4周）

### 任务 5: 精简 C01 Ownership

**时间**: 20-25 小时

#### 5.1 分析现有内容

```bash
cd crates/c01_ownership_borrow_scope/docs

# 统计现有文档
find . -name "*.md" | wc -l
find . -name "*.md" -exec wc -l {} + | tail -1

# 识别重要文档
ls -lh tier_*/*.md
```

#### 5.2 保留清单（20 个文档）

**Tier 1 基础 (5 个)**:
1. `tier_01_foundations/01_项目概览.md`
2. `tier_01_foundations/02_主索引导航.md`
3. `tier_01_foundations/03_术语表.md`
4. `tier_01_foundations/04_常见问题.md`
5. `tier_01_foundations/README.md`

**Tier 2 实践 (8 个)**:
1. `tier_02_guides/01_所有权快速入门.md`
2. `tier_02_guides/02_借用实践指南.md`
3. `tier_02_guides/03_生命周期实践.md`
4. `tier_02_guides/04_作用域管理实践.md`
5. `tier_02_guides/05_智能指针实践.md`
6. `tier_02_guides/06_代码示例集合.md`
7. `tier_02_guides/07_实战项目集.md`
8. `tier_02_guides/README.md`

**Tier 3 进阶 (5 个)**:
1. `tier_03_references/01_所有权规则参考.md`
2. `tier_03_references/02_借用检查器详解.md`
3. `tier_03_references/05_智能指针API参考.md`
4. `tier_03_references/09_性能优化参考.md`
5. `tier_03_references/README.md`

**主目录 (2 个)**:
1. `FAQ.md`
2. `Glossary.md`

#### 5.3 移动到 advanced/ (Tier 4内容)

```bash
mkdir -p docs/advanced
mv tier_04_advanced/* docs/advanced/
```

#### 5.4 清理 examples/

```bash
# 只保留精选示例
cd examples
mkdir -p archive

# 移动过时示例
mv rust_189_*.rs archive/
mv *_exp*.rs archive/

# 只保留核心示例（约 15 个）
```

**检查点**: ✅ C01 精简到 20 个核心文档

---

### 任务 6: 精简 C06 Async

**时间**: 15-20 小时

#### 6.1 examples/ 大清理

当前: 89 个 examples → 目标: 20 个精选

**保留**:
```text
核心异步 (5 个):
- 01_async_basics.rs
- 02_async_await.rs
- 03_futures.rs
- 04_tokio_basics.rs
- 05_async_errors.rs

实战场景 (10 个):
- 10_http_client.rs
- 11_http_server.rs
- 12_database.rs
- 13_websocket.rs
- 14_grpc.rs
- 15_retry_pattern.rs
- 16_circuit_breaker.rs
- 17_rate_limiter.rs
- 18_batch_processor.rs
- 19_task_scheduler.rs

进阶 (5 个):
- 20_actor_pattern.rs
- 21_csp_pattern.rs
- 22_async_recursion.rs
- 23_custom_runtime.rs
- 24_performance_tuning.rs
```

**移动其他到 archive/**

#### 6.2 移除 K8s/Docker（创建独立项目）

```bash
# 创建独立仓库（可选）
mkdir -p ../rust-async-deploy
mv deployment/* ../rust-async-deploy/
mv configs/* ../rust-async-deploy/
mv scripts/start_observe.* ../rust-async-deploy/
```

**在 README 中链接**:
```markdown
## 🚀 生产部署

本模块专注于异步编程学习。

部署相关内容请参考: [rust-async-deploy](https://github.com/xxx/rust-async-deploy)
```

**检查点**: ✅ C06 精简到 15 个核心文档 + 20 个示例

---

### 任务 7: 精简 C09 Design Patterns

**时间**: 15-20 小时

#### 7.1 模式分级

**核心 10 种** (所有人必学):
1. Builder
2. Factory Method
3. Singleton
4. Strategy
5. Observer
6. Decorator
7. Adapter
8. Iterator
9. Command
10. RAII

**进阶 10 种** (推荐):
11-20. [其他 GoF 模式]

**高级 27 种** (选学):
21-47. [并发/异步/Rust特有]

#### 7.2 重组文档

```text
docs/
├── tier_01_foundations/ (保留)
├── tier_02_guides/
│   ├── 01_核心10种模式.md (新建，整合)
│   ├── 02_进阶模式速查.md
│   └── 03_实战场景映射.md (新建)
├── tier_03_references/
│   └── 01_完整模式索引.md (简化)
└── tier_04_advanced/
    └── 移到 docs/advanced/
```

#### 7.3 创建场景导航

新建: `docs/tier_02_guides/03_实战场景映射.md`

```markdown
# 实战场景模式映射

## 场景 1: 我要构建一个配置系统

**推荐模式**: Builder + Singleton

**为什么**: 
- Builder: 复杂配置对象
- Singleton: 全局访问

**示例**: [config_system.rs](../../examples/config_system.rs)

---

## 场景 2: 我要实现插件系统

**推荐模式**: Strategy + Factory

[...]

---

[20+ 场景]
```

**检查点**: ✅ C09 重组完成，场景导航创建

---

## 📅 Week 5-6: 质量提升（12月第1-2周）

### 任务 8: 真实案例（每个模块 2 个）

**时间**: 30-40 小时

#### 模板: 真实案例文档

```markdown
# 真实案例：[案例名称]

> **难度**: ⭐⭐⭐  
> **时间**: 1-2 小时  
> **前置知识**: [列出]

---

## 📋 需求描述

[真实世界的问题，不是玩具]

---

## 🎯 学习目标

完成后你将掌握：
1. [技能 1]
2. [技能 2]
3. [技能 3]

---

## 💡 设计思路

### 方案对比

| 方案 | 优点 | 缺点 | 适用场景 |
|------|------|------|---------|
| 方案A | ... | ... | ... |
| 方案B | ... | ... | ... |

**我们选择**: [方案X]，因为 [原因]

---

## 💻 完整实现

[完整可运行代码，带详细注释]

---

## 🐛 常见错误

### 错误 1: [错误描述]

```rust
// ❌ 错误代码
[...]

// ✅ 正确代码
[...]
```

**为什么错**: [解释]

---

## 📊 性能分析

[benchmark 数据]

---

## 🚀 扩展挑战

1. 添加功能X
2. 优化性能
3. 支持并发

---

## 📚 延伸阅读

- [相关文档]
- [外部资源]
```

#### 案例优先级

**C01 Ownership**:
1. LRU 缓存实现（高频）
2. 双向链表（经典难题）

**C06 Async**:
1. 异步 HTTP 服务器（实用）
2. 异步数据库连接池（常见）

**C09 Design Patterns**:
1. 插件系统（Builder + Factory）
2. 事件总线（Observer + Mediator）

**检查点**: ✅ 每个核心模块有 2 个完整真实案例

---

### 任务 9: CI 自动化

**时间**: 10-15 小时

#### 9.1 创建 CI 配置

文件: `.github/workflows/ci.yml`

```yaml
name: CI

on:
  push:
    branches: [ main, dev ]
  pull_request:
    branches: [ main ]

env:
  RUST_VERSION: "1.90"

jobs:
  # 作业 1: 文档检查
  docs-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: 检查 README 长度
        run: |
          chmod +x scripts/check_standards.sh
          ./scripts/check_standards.sh
      
      - name: 检查死链接
        uses: gaurav-nelson/github-action-markdown-link-check@v1
        with:
          config-file: '.github/markdown-link-check-config.json'

  # 作业 2: 编译检查
  build:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        crate:
          - c01_ownership_borrow_scope
          - c02_type_system
          - c06_async
          - c09_design_pattern
    steps:
      - uses: actions/checkout@v4
      
      - uses: dtolnay/rust-toolchain@stable
        with:
          toolchain: ${{ env.RUST_VERSION }}
      
      - name: Build
        run: cd crates/${{ matrix.crate }} && cargo build --verbose
      
      - name: Run tests
        run: cd crates/${{ matrix.crate }} && cargo test --verbose

  # 作业 3: 示例测试
  examples:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        crate:
          - c01_ownership_borrow_scope
          - c06_async
          - c09_design_pattern
    steps:
      - uses: actions/checkout@v4
      
      - uses: dtolnay/rust-toolchain@stable
        with:
          toolchain: ${{ env.RUST_VERSION }}
      
      - name: Test examples
        run: |
          cd crates/${{ matrix.crate }}
          for example in examples/*.rs; do
            name=$(basename $example .rs)
            echo "Testing $name..."
            cargo run --example $name || exit 1
          done

  # 作业 4: Clippy 检查
  clippy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          toolchain: ${{ env.RUST_VERSION }}
          components: clippy
      
      - name: Run Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

  # 作业 5: 格式检查
  fmt:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          toolchain: ${{ env.RUST_VERSION }}
          components: rustfmt
      
      - name: Check formatting
        run: cargo fmt --all -- --check
```

#### 9.2 创建链接检查配置

文件: `.github/markdown-link-check-config.json`

```json
{
  "ignorePatterns": [
    {
      "pattern": "^http://localhost"
    },
    {
      "pattern": "^https://github.com/your-repo"
    }
  ],
  "timeout": "20s",
  "retryOn429": true,
  "retryCount": 5,
  "fallbackRetryDelay": "30s"
}
```

**检查点**: ✅ CI 配置完成，自动运行

---

## 📅 Week 7-8: 建立反馈循环（12月第3-4周）

### 任务 10: 用户反馈系统

**时间**: 8-10 小时

#### 10.1 在每个 README 添加反馈区

```markdown
---

## 📊 这个模块有帮助吗？

**快速反馈**（点击投票）:
- 👍 很有帮助！继续保持
- 👎 需要改进
- 💬 [我有建议](../../discussions)

**详细反馈**: [提交 Issue](../../issues/new/choose)

---

## 🎯 学习进度追踪

- [ ] 完成快速入门（2-4h）
- [ ] 完成核心概念（8-12h）
- [ ] 完成实战项目
- [ ] 能独立解决问题

**分享你的进度**: [学习打卡](../../discussions/categories/learning-progress)
```

#### 10.2 创建 Issue 模板

文件: `.github/ISSUE_TEMPLATE/documentation-issue.yml`

```yaml
name: 📝 文档问题
description: 报告文档中的错误、不清楚的地方
labels: ["documentation"]
body:
  - type: dropdown
    id: module
    attributes:
      label: 哪个模块?
      options:
        - C01 - Ownership
        - C02 - Type System
        - C06 - Async
        - C09 - Design Patterns
        - 其他
    validations:
      required: true
  
  - type: input
    id: file
    attributes:
      label: 文件路径
      placeholder: "例如: crates/c01_ownership/docs/guide.md"
    validations:
      required: true
  
  - type: textarea
    id: problem
    attributes:
      label: 问题描述
      placeholder: "描述你遇到的困惑或错误"
    validations:
      required: true
  
  - type: textarea
    id: suggestion
    attributes:
      label: 改进建议（可选）
      placeholder: "你认为应该如何改进？"
```

**检查点**: ✅ 反馈系统建立

---

### 任务 11: 月度审查机制

创建文件: `docs/MONTHLY_REVIEW_CHECKLIST.md`

```markdown
# 月度审查清单

## 📅 审查时间: [YYYY-MM]

---

## 1. 用户反馈统计

### GitHub Issues
- 新增: ___个
- 已解决: ___个
- 未解决: ___个

### Discussions
- 新讨论: ___个
- 活跃度: [高/中/低]

### 反馈分类
| 类别 | 数量 | 占比 |
|------|------|------|
| 文档不清楚 | ___ | ___% |
| 代码示例错误 | ___ | ___% |
| 缺少内容 | ___ | ___% |
| 其他 | ___ | ___% |

---

## 2. 内容质量检查

### 文档数量
- docs/docs/: ___个 (目标: ≤35)
- C01 docs/: ___个 (目标: ≤20)
- C06 docs/: ___个 (目标: ≤15)
- C09 docs/: ___个 (目标: ≤20)

### 文档长度
- README 平均: ___行 (目标: <200)
- 最长 README: ___行

---

## 3. CI/CD 状态

### 构建成功率
- 主分支: ___%
- PR: ___%

### 测试覆盖
- C01: ___%
- C06: ___%
- C09: ___%

---

## 4. 维护时间统计

### 本月投入
- 文档更新: ___小时
- Bug 修复: ___小时
- 新内容: ___小时
- 回复反馈: ___小时
- **总计**: ___小时

### 对比目标
- 目标: <8 小时/周 (32小时/月)
- 实际: ___小时
- 状态: [✅ 达标 / ⚠️ 超标]

---

## 5. 优先改进事项

### Top 3 用户痛点
1. [...]
2. [...]
3. [...]

### 下月行动计划
- [ ] [行动 1]
- [ ] [行动 2]
- [ ] [行动 3]

---

## 6. 文档健康度评分

| 指标 | 得分 (1-10) | 目标 |
|------|------------|------|
| 文档数量合理性 | ___ | ≥8 |
| 文档清晰度 | ___ | ≥8 |
| 代码示例质量 | ___ | ≥9 |
| 维护成本 | ___ | ≥7 |
| 用户满意度 | ___ | ≥8 |
| **平均分** | ___ | ≥8 |

---

**审查人**: [姓名]  
**审查日期**: [YYYY-MM-DD]  
**下次审查**: [YYYY-MM-DD]
```

**检查点**: ✅ 月度审查机制建立

---

## 📅 Week 9-12: 长期机制（1月）

### 任务 12: 冻结机制

**时间**: 4-6 小时

#### 12.1 标记稳定模块

在已完成模块的 README 顶部添加:

```markdown
# C01 - Ownership System

> **📌 模块状态**: ✅ **稳定版 v1.0** (2025-11-30)  
> 
> **冻结说明**: 
> - ✅ 核心内容已完成且稳定
> - ✅ 只接受: Bug修复、错别字、Rust版本兼容
> - ❌ 不再接受: 新章节、大重构、"完善"
> 
> **贡献新内容？** → 考虑创建[扩展项目](#扩展项目)
```

#### 12.2 创建扩展项目指南

文件: `docs/EXTENSION_PROJECTS_GUIDE.md`

```markdown
# 扩展项目指南

## 🎯 什么是扩展项目？

当核心模块已冻结，但你想添加更深入/小众的内容时，创建独立的扩展项目。

---

## 📋 扩展项目列表

### 已有扩展

1. **[rust-formal-verification](link)**
   - 基于: C01 Ownership
   - 内容: 形式化验证、类型理论
   - 维护者: [姓名]

2. **[rust-async-deploy](link)**
   - 基于: C06 Async
   - 内容: K8s、Docker、生产部署
   - 维护者: [姓名]

---

## 🚀 创建新扩展

### 1. 确定主题

**适合扩展的内容**:
- ✅ 高级/小众主题
- ✅ 特定领域深入
- ✅ 实验性特性
- ✅ 工具/部署相关

**不适合**:
- ❌ 核心概念
- ❌ 通用最佳实践
- ❌ 入门内容

### 2. 项目结构

```text
rust-[主题名]/
├── README.md (<200 行)
├── docs/
│   ├── guide.md
│   └── examples/
├── src/ 或 examples/
└── CONTRIBUTING.md
```

### 3. 链接回主项目

在扩展项目 README 中:

```markdown
> **扩展自**: [Rust Learning - C0X](link)  
> **前置知识**: 需先完成 C0X 模块
```

在主项目中添加链接:

```markdown
## 🚀 扩展学习

完成本模块后，可以探索:
- [高级主题名称](扩展项目链接)
```

---

## 🤝 维护协议

- 扩展项目独立维护
- 主项目不负责扩展内容
- 鼓励社区贡献
```

**检查点**: ✅ 冻结机制和扩展指南完成

---

### 任务 13: 自动化工具完善

**时间**: 15-20 小时

#### 13.1 Dependabot 配置

文件: `.github/dependabot.yml`

```yaml
version: 2
updates:
  # Cargo dependencies
  - package-ecosystem: "cargo"
    directory: "/"
    schedule:
      interval: "weekly"
      day: "monday"
    labels:
      - "dependencies"
      - "rust"
    commit-message:
      prefix: "chore"
      prefix-development: "chore"
      include: "scope"
  
  # GitHub Actions
  - package-ecosystem: "github-actions"
    directory: "/"
    schedule:
      interval: "weekly"
    labels:
      - "dependencies"
      - "github-actions"
```

#### 13.2 自动化文档检查 Bot

创建: `scripts/weekly_doc_check.sh`

```bash
#!/bin/bash
# 每周运行，检查文档健康度

echo "📋 周度文档健康检查"
echo "===================="

# 1. 统计文档数量
echo ""
echo "📊 文档数量:"
echo "  docs/docs/: $(find docs/docs -maxdepth 1 -name '*.md' | wc -l) (目标: ≤35)"
echo "  C01 docs/: $(find crates/c01_ownership_borrow_scope/docs -maxdepth 1 -name '*.md' | wc -l) (目标: ≤20)"
echo "  C06 docs/: $(find crates/c06_async/docs -maxdepth 1 -name '*.md' | wc -l) (目标: ≤15)"

# 2. 检查 README 长度
echo ""
echo "📏 README 长度检查:"
for readme in crates/*/README.md; do
    lines=$(wc -l < "$readme")
    if [ $lines -gt 200 ]; then
        echo "  ⚠️  $readme: $lines 行"
    else
        echo "  ✅ $readme: $lines 行"
    fi
done

# 3. 检查死链接
echo ""
echo "🔗 链接检查:"
# 使用 markdown-link-check
find docs crates -name '*.md' -exec markdown-link-check {} \;

# 4. 检查 CI 状态
echo ""
echo "🤖 CI 状态:"
# 调用 GitHub API 获取最新 CI 状态
# ...

echo ""
echo "✅ 检查完成！"
```

#### 13.3 GitHub Actions 定时任务

文件: `.github/workflows/weekly-health-check.yml`

```yaml
name: Weekly Health Check

on:
  schedule:
    # 每周一早上 8:00 UTC
    - cron: '0 8 * * 1'
  workflow_dispatch:  # 允许手动触发

jobs:
  health-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install dependencies
        run: |
          npm install -g markdown-link-check
      
      - name: Run health check
        run: |
          chmod +x scripts/weekly_doc_check.sh
          ./scripts/weekly_doc_check.sh > health_report.txt
      
      - name: Create Issue if problems found
        if: failure()
        uses: actions/github-script@v7
        with:
          script: |
            const fs = require('fs');
            const report = fs.readFileSync('health_report.txt', 'utf8');
            
            github.rest.issues.create({
              owner: context.repo.owner,
              repo: context.repo.repo,
              title: '📋 周度健康检查发现问题',
              body: `\`\`\`\n${report}\n\`\`\``,
              labels: ['maintenance', 'automated']
            });
```

**检查点**: ✅ 自动化工具完整部署

---

## 🎯 里程碑检查

### ✅ Week 2 结束

- [ ] docs/docs/ ≤ 35 个文档
- [ ] 所有模块清理完 swap.rar
- [ ] 文档标准 v2 创建
- [ ] C01/C06/C09 README < 200 行
- [ ] QUICK_PATHS.md 完成

### ✅ Week 4 结束

- [ ] C01 精简到 20 个核心文档
- [ ] C06 精简到 15 个核心文档 + 20 示例
- [ ] C09 重组完成
- [ ] 场景导航创建

### ✅ Week 6 结束

- [ ] 每个核心模块 2 个真实案例
- [ ] CI 全面配置
- [ ] 所有示例通过 CI
- [ ] 反馈系统建立

### ✅ Week 8 结束

- [ ] 月度审查机制运行
- [ ] 第一次月度审查完成
- [ ] 维护时间 < 8 小时/周

### ✅ Week 12 结束

- [ ] 冻结机制实施
- [ ] 扩展项目指南完成
- [ ] 自动化工具完整部署
- [ ] 项目进入"可持续维护模式"

---

## 📊 成功指标（3 个月后）

| 指标 | 当前 | 目标 | 完成 |
|------|------|------|------|
| 总文档数 | 500+ | <200 | [ ] |
| 核心模块 README | 500+ 行 | <200 行 | [ ] |
| 维护时间/周 | ? | <8 小时 | [ ] |
| CI 通过率 | ? | >95% | [ ] |
| 用户上手时间 | ? | <4 小时 | [ ] |
| 月度问题数 | ? | <10 个 | [ ] |
| 新人贡献 | ? | >2 人/月 | [ ] |

---

## 🔄 持续优化

### 每周任务（1-2 小时）

- [ ] 检查 CI 状态
- [ ] 回复 Issues/Discussions
- [ ] 审查 PR
- [ ] 更新 CHANGELOG

### 每月任务（4-6 小时）

- [ ] 月度审查
- [ ] 分析反馈
- [ ] 规划改进
- [ ] 更新依赖

### 每季度任务（8-10 小时）

- [ ] Rust 版本升级
- [ ] 大的改进项目
- [ ] 文档质量审计
- [ ] 用户调研

---

## 🚨 应急预案

### 如果维护时间超标

**触发条件**: 连续 2 周 > 10 小时/周

**行动**:
1. 暂停新功能
2. 识别时间黑洞
3. 进一步精简或冻结模块

### 如果文档数量反弹

**触发条件**: docs/docs/ > 50 个文件

**行动**:
1. 紧急归档
2. 审查添加原因
3. 收紧标准

### 如果 CI 失败率高

**触发条件**: 通过率 < 85%

**行动**:
1. 优先修复 CI
2. 审查测试质量
3. 考虑简化测试

---

## 📞 负责人与联系方式

**项目维护者**: [姓名]  
**紧急联系**: [邮箱]  
**进度追踪**: [看板链接]  

---

## 🎬 开始执行

**准备好了吗？**

→ [Week 1 任务清单](#week-1-2-紧急清理11月第1-2周)  
→ [加入讨论](../../discussions)  
→ [查看批判性评价](CRATES_CRITICAL_EVALUATION_2025_10_30.md)

---

**计划创建**: 2025-10-30  
**预计完成**: 2026-01-31  
**状态**: 📋 待执行

🦀 **Less is More! 可持续才是最好的！** 🦀

