# 国际化双语标注基线报告

> 生成日期: 2026-07-04 14:47:50 UTC
> 扫描文件数: 371
> 生成工具: `scripts/add_bilingual_annotations.py --mode check-only --report`

## 统计

| 指标 | 数值 |
|---|---:|
| 扫描文件数 | 371 |
| 缺少 EN 字段 | 0 |
| 缺少 Summary 字段 | 0 |
| 未覆盖术语种类 | 32 |

## 未覆盖术语 TOP 20

| 术语 | 出现文件数 |
|---|---:|
| crate | 17 |
| trait | 13 |
| 一致性 | 11 |
| Vec | 9 |
| 不可变引用 | 8 |
| 类型推断 | 7 |
| 不可变借用 | 6 |
| unsafe | 6 |
| 可变借用 | 5 |
| 内存安全 | 5 |
| 生命周期 | 5 |
| 运行时 | 5 |
| Future | 4 |
| Option | 4 |
| Pin | 4 |
| 零成本抽象 | 3 |
| 原子操作 | 3 |
| 可变引用 | 3 |
| 错误处理 | 3 |
| 借用 | 3 |

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
