# Book 目录

> **定位**: 本目录为 `mdbook build` 的**输出目录**，存放由 `concept/`、`knowledge/`、`docs/` 等源文件构建而成的静态站点产物。
> **注意**: 不要直接编辑此目录下的文件；所有内容修改应在源文件中进行，然后重新运行 `mdbook build`。

---

## 构建方式

```bash
# 若项目根目录存在 book.toml
mdbook build

# 或指定输出目录
mdbook build --dest-dir book
```

---

## 目录结构

```text
book/
├── README.md          # 本文件
├── 00_meta/           # 元信息、学习路径、术语表
├── 01_foundation/     # L1 基础概念
├── 02_intermediate/   # L2 进阶概念
├── 03_advanced/       # L3 高级概念
├── 04_formal/         # L4 形式化理论
├── 05_comparative/    # L5 对比分析
├── 06_ecosystem/      # L6 生态工程
├── 07_future/         # L7 前沿趋势
└── ...                # mdBook 生成的搜索、字体、CSS 等资源
```

---

## 与源文件的关系

| 本目录 (`book/`) | 源目录 |
|---|---|
| 构建产物、只读 | `concept/`、`knowledge/`、`docs/` 等 |
| 由 mdBook 自动生成 | 人工维护、版本控制 |
| 不适合提交到源码仓库（除本 README） | 项目核心资产 |

> 如果你发现 `book/` 中的内容有误，请回到对应源文件修改并重新构建。
