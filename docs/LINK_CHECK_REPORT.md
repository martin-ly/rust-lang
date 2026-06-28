# 链接有效性检查报告

## 统计
| 类别 | 数量 |
|:---|:---:|
| 总链接数 | 20045 |
| 有效链接 | 9048 |
| 损坏链接 | 9 |
| 外部链接 | 10988 |
| 仅锚点链接 | 6557 |

## 损坏链接清单（按问题类型分组）

### 锚点不存在 (9个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
|:---|:---|:---|:---|
| docs\07_project\07_completion_status.md | ⚠️ 已知问题 | `#️-已知问题` | 同文件锚点不存在: #️-已知问题 |
| docs\07_project\07_documentation_cross_reference_guide.md | 🗺️ 文档网络总览 {#️-文档网络总览} | `#️-文档网络总览-️-文档网络总览` | 同文件锚点不存在: #️-文档网络总览-️-文档网络总览 |
| docs\07_project\07_knowledge_structure_framework.md | 🗺️ 思维表征方式 | `#️-思维表征方式` | 同文件锚点不存在: #️-思维表征方式 |
| docs\07_project\07_module_knowledge_structure_guide.md | 🗺️ 思维表征方式补充 | `#️-思维表征方式补充` | 同文件锚点不存在: #️-思维表征方式补充 |
| docs\07_project\07_project_architecture_guide.md | 🏗️ 项目结构 | `#️-项目结构` | 同文件锚点不存在: #️-项目结构 |
| docs\content\emerging\README.md | **状态**: 🔄 持续跟踪更新 | `#状态--持续跟踪更新` | 同文件锚点不存在: #状态--持续跟踪更新 |
| docs\content\production\README.md | 🛡️ 可靠性 | `#️-可靠性` | 同文件锚点不存在: #️-可靠性 |
| docs\content\representations\10_knowledge_representation_matrix.md | 🗺️ 思维导图索引 | `#️-思维导图索引` | 同文件锚点不存在: #️-思维导图索引 |
| docs\content\representations\10_knowledge_representation_matrix.md | **状态**: 🔄 85% 完成，持续扩充中 | `#状态--85-完成持续扩充中` | 同文件锚点不存在: #状态--85-完成持续扩充中 |

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
| docs\content\representations\10_knowledge_representation_matrix.md | 2 |
| docs\07_project\07_completion_status.md | 1 |
| docs\07_project\07_documentation_cross_reference_guide.md | 1 |
| docs\07_project\07_knowledge_structure_framework.md | 1 |
| docs\07_project\07_module_knowledge_structure_guide.md | 1 |
| docs\07_project\07_project_architecture_guide.md | 1 |
| docs\content\emerging\README.md | 1 |
| docs\content\production\README.md | 1 |

**总计 8 个文件包含损坏链接**