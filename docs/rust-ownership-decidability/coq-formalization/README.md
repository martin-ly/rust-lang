# Rust 所有权系统 Coq 形式化

## 项目结构

```text
coq-formalization/
├── README.md                 # 本文件
├── _CoqProject              # Coq 项目配置
├── Makefile                 # 构建脚本
│
├── theories/                # 主要形式化理论
│   ├── Utils/               # 辅助定义和引理
│   │   ├── ListUtils.v
│   │   ├── MapUtils.v
│   │   └── ArithUtils.v
│   │
│   ├── Syntax/              # 语法定义
│   │   ├── Types.v          # 类型定义
│   │   ├── Expressions.v    # 表达式定义
│   │   └── Places.v         # 位置表达式定义
│   │
│   ├── Semantics/           # 语义定义
│   │   ├── SemanticDomains.v   # 语义域
│   │   ├── OperationalSemantics.v  # 操作语义
│   │   └── OwnershipSafety.v       # 所有权安全
│   │
│   ├── Typing/              # 类型系统
│   │   ├── TypeSystem.v     # 主要类型判断
│   │   ├── Subtyping.v      # 子类型关系
│   │   └── WellFormedness.v # 良构性判断
│   │
│   ├── Metatheory/          # 元理论证明
│   │   ├── Preservation.v   # 类型保持
│   │   ├── Progress.v       # 进展定理
│   │   ├── TypeSafety.v     # 类型安全
│   │   └── Termination.v    # 终止性证明
│   │
│   └── Decidability/        # 可判定性
│       ├── Rank.v           # 类型秩的定义
│       ├── Linearizability.v # 线性化定义
│       └── DecidabilityTheorems.v # 可判定性定理
│
├── examples/                # 示例程序
│   ├── SimpleBorrow.v
│   ├── MutableBorrow.v
│   └── NestedBorrow.v
│
└── tests/                   # 测试套件
    ├── TestFramework.v
    └── RegressionTests.v
```

## 构建说明

### 依赖

- Coq 8.17 或更高版本
- Mathematical Components (MathComp) 可选
- Iris 框架 (用于高级分离逻辑证明)

### 构建命令

```bash
# 配置项目
coq_makefile -f _CoqProject -o Makefile

# 编译所有文件
make

# 编译特定文件
make theories/Metatheory/Termination.vo

# 清理
make clean
```

## 核心定义索引

| 定义/定理 | 文件 | 描述 |
|-----------|------|------|
| `ty` | `Syntax/Types.v` | 类型归纳定义 |
| `expr` | `Syntax/Expressions.v` | 表达式归纳定义 |
| `has_type` | `Typing/TypeSystem.v` | 类型判断 |
| `ownership_safe` | `Semantics/OwnershipSafety.v` | 所有权安全 |
| `eval` | `Semantics/OperationalSemantics.v` | 求值关系 |
| `preservation` | `Metatheory/Preservation.v` | 类型保持定理 |
| `progress` | `Metatheory/Progress.v` | 进展定理 |
| `termination` | `Metatheory/Termination.v` | 终止性定理 |

## 证明状态跟踪

### 已完成

- [x] 基础语法定义
- [x] 语义域定义
- [x] 类型系统框架

### 进行中

- [ ] 所有权安全判断的详细规则
- [ ] 求值关系的核心规则

### 待开始

- [ ] Preservation 完整证明
- [ ] Progress 完整证明
- [ ] Termination 完整证明
- [ ] 可判定性证明

## 参考论文

1. Weiss et al. "Oxide: The Essence of Rust" - 类型系统基础
2. Payet et al. "On the Termination of Borrow Checking in Featherweight Rust" - 终止性
3. Jung et al. "RustBelt" - 分离逻辑方法
4. Jung et al. "Stacked Borrows" - 别名模型

---

**最后更新**: 2026-03-05
