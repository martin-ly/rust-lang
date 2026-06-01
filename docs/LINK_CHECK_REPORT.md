# 链接有效性检查报告
>
> **Rust 版本**: 1.96.0+ (Edition 2024)

## 统计

| 类别 | 数量 |
|:---|:---:|
| 总链接数 | 113573 |
| 有效链接 | 48409 |
| 损坏链接 | 1 |
| 外部链接 | 65151 |
| 仅锚点链接 | 39285 |

## 损坏链接清单（按问题类型分组）

### 锚点不存在 (1个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
|:---|:---|:---|:---|
| docs\research_notes\type_theory\10_trait_system_formalization.md | RPITIT 与 async fn in trait（Rust 1.75.0 稳定化） | `#rpitit-与-async-fn-in-traitrust-193-稳定化` | 同文件锚点不存在: #rpitit-与-async-fn-in-traitrust-193-稳定化 |

## 修复建议

### 1. 文件不存在问题

- 检查链接路径是否正确
- 确认目标文件是否已被移动或删除
- 更新链接指向正确的文件位置

### 2. 锚点不存在问题

- 检查锚点ID是否与目标文件中的标题匹配
- GitHub风格锚点：将标题转换为小写，空格替换为连字符，移除标点
- 示例：`## Hello World!` -> `#hello-world`

### 3. 同文件锚点问题

- 检查文档中是否存在对应的标题
- 可能是文档结构已更改但目录未更新

## 源文件问题统计

| 源文件 | 损坏链接数 |
|:---|:---:|
| docs\research_notes\type_theory\10_trait_system_formalization.md | 1 |

**总计 1 个文件包含损坏链接**
