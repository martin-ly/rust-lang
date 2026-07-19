# Proofs 目录使用说明

- 目的: 承载与 `formal_rust/framework/*.md` 中“证明义务(Proof Obligations)”一一对应的Coq/Lean证明草案。
- 结构:
  - `coq/`: Coq 工程片段与最小证明文件
  - `lean/`: Lean 工程片段与最小证明文件
- 约定:
  - 文件命名: `<文档名>__<义务标识>.<v|lean>`，例如 `type_system_verification__preservation.v`
  - 每个文件须可被基础工具链检查(语法与最小检查通过)，不要求完整终结证明
  - 不引入与验证无关的示例或大体量依赖
- 入门:
  - Coq: 安装 Coq 平台后，使用 `coqc <file>.v` 进行语法/最小检查
  - Lean: 安装 elan/Lean，使用 `lake build` 或 `lean --make <file>.lean` 进行最小检查
