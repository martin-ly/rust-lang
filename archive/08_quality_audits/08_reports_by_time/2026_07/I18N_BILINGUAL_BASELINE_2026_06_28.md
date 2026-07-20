# 国际化双语标注基线报告

> 生成日期: 2026-06-28 15:25:12 UTC
> 扫描文件数: 95
> 生成工具: `scripts/add_bilingual_annotations.py --mode check-only --report`

## 统计

| 指标 | 数值 |
|---|---:|
| 扫描文件数 | 95 |
| 缺少 EN 字段 | 0 |
| 缺少 Summary 字段 | 0 |
| 未覆盖术语种类 | 29 |

## 未覆盖术语 TOP 20

| 术语 | 出现文件数 |
|---|---:|
| 内存安全 | 6 |
| trait | 5 |
| 不可变引用 | 5 |
| 类型推断 | 4 |
| 可变借用 | 4 |
| 生命周期 | 4 |
| 借用 | 4 |
| 不可变借用 | 4 |
| 可变引用 | 3 |
| 运行时 | 3 |
| 所有权 | 3 |
| 类型系统 | 3 |
| 零成本抽象 | 2 |
| 原子操作 | 2 |
| 宏 | 2 |
| 单态化 | 2 |
| 智能指针 | 2 |
| 结构体 | 2 |
| 模块 | 2 |
| 错误处理 | 1 |

## 缺少 EN 字段的文件

无

## 缺少 Summary 字段的文件

无

## 建议

1. 优先处理 TOP 未覆盖术语，它们在最多文件中出现。
2. 对缺失 EN/Summary 的文件，参考 `concept/00_meta/bilingual_template.md` 补齐头部。
3. 使用 `python scripts/add_bilingual_annotations.py --mode annotate --dir concept/XX_YYYY` 自动标注指定目录。

---

*本报告为基线数据，用于追踪国际化覆盖进度。*
