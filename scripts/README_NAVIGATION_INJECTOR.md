# 导航区块自动注入与校验脚本使用说明

脚本：`scripts/navigation_injector.ps1`

## 功能

- 扫描仓库内 `.md` 与 `.rs` 文件
- 为缺少“返回知识图谱”导航的文档自动插入标准区块
- 自动计算相对路径，指向 `formal_rust/refactor/01_knowledge_graph/*`
- Rust 源码以文件头注释方式注入回链与参考指引
- 支持只校验不修改模式

## 参数

- `-Root <path>`：扫描根目录，默认当前目录
- `-IncludeExtensions <.md,.rs,...>`：包含的扩展名，默认 `('.md','.rs')`
- `-ExcludeDirs <dir1,dir2,...>`：排除目录，默认 `('target','.git','node_modules','.cursor','.vscode')`
- `-CheckOnly`：仅校验是否存在导航区块，不执行修改

## 使用示例

```powershell
# 1) 仅校验
pwsh -File scripts/navigation_injector.ps1 -Root . -CheckOnly

# 2) 执行注入（全仓）
pwsh -File scripts/navigation_injector.ps1 -Root .

# 3) 仅处理 Markdown
pwsh -File scripts/navigation_injector.ps1 -IncludeExtensions .md

# 4) 自定义排除目录
pwsh -File scripts/navigation_injector.ps1 -ExcludeDirs target,.git,docs/migration-backup
```

## 注入规范

- 文首信息区后插入：
  - `---` 分隔线
  - 引用块形式的“返回知识图谱”区块（含全局图谱、分层图谱、索引与映射）
- 文末插入：
  - `---` 分隔线
  - “参考指引”行（指向节点映射和综合快照/导出）
- Rust 源码使用 `//` 注释注入对应链接

## 路径计算

脚本会根据文件所在目录与 `formal_rust/refactor/` 的相对关系自动拼接路径，确保多层级目录下的链接正确。

## 注意事项

- 脚本会跳过已包含“返回知识图谱”的文件
- 对超大文件请在版本控制下运行，便于回滚
- 执行前建议先用 `-CheckOnly` 模式评估影响范围

## 兼容性

- 需要 PowerShell 7+（建议 `pwsh`）

## 问题反馈

- 如发现相对路径异常或格式不一致，请反馈文件路径与预期行为，以便改进脚本逻辑
