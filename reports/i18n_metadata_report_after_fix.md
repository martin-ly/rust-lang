# 国际化双语标注基线报告

> 生成日期: 2026-07-04 11:45:23 UTC
> 扫描文件数: 371
> 生成工具: `scripts/add_bilingual_annotations.py --mode check-only --report`

## 统计

| 指标 | 数值 |
|---|---:|
| 扫描文件数 | 371 |
| 缺少 EN 字段 | 0 |
| 缺少 Summary 字段 | 0 |
| 未覆盖术语种类 | 46 |

## 未覆盖术语 TOP 20

| 术语 | 出现文件数 |
|---|---:|
| 零成本抽象 | 65 |
| 运行时 | 35 |
| 生命周期 | 20 |
| crate | 17 |
| 一致性 | 14 |
| trait | 13 |
| 宏 | 12 |
| 类型推断 | 11 |
| 模块 | 10 |
| 闭包 | 10 |
| 结构体 | 10 |
| Vec | 9 |
| 不可变引用 | 8 |
| 枚举 | 8 |
| 切片 | 7 |
| 原子操作 | 6 |
| 可变借用 | 6 |
| 不可变借用 | 6 |
| 过程宏 | 6 |
| unsafe | 6 |

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