# 国际化双语标注基线报告

> 生成日期: 2026-06-28 12:23:11 UTC
> 扫描文件数: 321
> 生成工具: `scripts/add_bilingual_annotations.py --mode check-only --report`

## 统计

| 指标 | 数值 |
|---|---:|
| 扫描文件数 | 321 |
| 缺少 EN 字段 | 0 |
| 缺少 Summary 字段 | 0 |
| 未覆盖术语种类 | 39 |

## 未覆盖术语 TOP 20

| 术语 | 出现文件数 |
|---|---:|
| crate | 17 |
| trait | 13 |
| 生命周期 | 10 |
| 运行时 | 10 |
| 一致性 | 10 |
| 类型推断 | 9 |
| Vec | 9 |
| 不可变引用 | 7 |
| 内存安全 | 7 |
| unsafe | 7 |
| 可变借用 | 6 |
| 借用 | 6 |
| 不可变借用 | 6 |
| 类型系统 | 5 |
| 宏 | 4 |
| 模块 | 4 |
| Option | 4 |
| Pin | 4 |
| 零成本抽象 | 3 |
| 可变引用 | 3 |

## 缺少 EN 字段的文件

无

## 缺少 Summary 字段的文件

无

## 建议

1. 优先处理 TOP 未覆盖术语，它们在最多文件中出现。
2. 对缺失 EN/Summary 的文件，参考 `concept/00_meta/BILINGUAL_TEMPLATE.md` 补齐头部。
3. 使用 `python scripts/add_bilingual_annotations.py --mode annotate --dir concept/XX_YYYY` 自动标注指定目录。

---

*本报告为基线数据，用于追踪国际化覆盖进度。*