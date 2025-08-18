# Rust 形式化验证框架(Framework)

- 范围: 仅包含验证相关的最小核心文档与索引
- 面向: 类型安全、内存安全、并发安全与性能保证的形式化规则与可验证示例

## 当前文件

- `verification_index.md`: 索引
- `type_system_verification.md`: 类型系统验证
- `memory_safety_verification.md`: 内存安全验证
- `concurrency_safety_verification.md`: 并发安全验证
- `performance_formal_methods.md`: 性能形式化方法
- `verify_integrity.py`: 目录完整性与内容稽核脚本

## 准入规范

- 仅允许验证类文档与配套脚本，禁止引入通用“架构/生态/组件罗列”等跑题内容
- 每个验证文档需包含:
  - “最小可验证示例(MVE)”
  - “证明义务清单(Proof Obligations)”

## 校验

```bash
python formal_rust/framework/verify_integrity.py
```

- 输出任何违规项将返回非零退出码

## 贡献建议

- 以“先规则、后示例、再证明义务”的结构组织
- 变更后始终执行校验脚本，保持目录收敛与文档实质度
