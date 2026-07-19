#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Fix remaining old 1.94 TOC entries and methodology body section."""

from pathlib import Path
import re

ROOT = Path("e:/_src/rust-lang/docs/research_notes")


def read(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def write(path, text):
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


# ---- 10_research_methodology.md ----
f = ROOT / "10_research_methodology.md"
t = read(f)

# TOC old entries
old_toc = """  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)
  - [**最后更新**: 2026-03-14 (Rust 1.94 深度整合)](#最后更新-2026-03-14-rust-194-深度整合)
  - [权威来源索引](#权威来源索引)"""
new_toc = """  - [🆕 权威国际化内容升级](#-权威国际化内容升级)
  - [权威来源索引](#权威来源索引)"""
t = t.replace(old_toc, new_toc)

# Maintenance block before old section (status has bold)
old_maint = """**维护者**: Rust Research Methodology Group
**最后更新**: 2026-01-26
**状态**: ✅ **已完成** (100%)"""
new_maint = """**维护者**: Rust Research Methodology Group
**最后更新**: 2026-06-29
**状态**: ✅ 完成"""
t = t.replace(old_maint, new_maint)

# Replace old 1.94 body + final meta before ## 权威来源索引
new_section = """## 🆕 权威国际化内容升级 (Rust 1.96.0+)
>
> **来源**: [Rust Research Methodology Group]

> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本次升级要点

- 补充 Rust 形式化方法的国际权威论文索引：RustBelt、Aeneas、RustHorn、RustHornBelt、Iris。
- Coq/Lean 示例对齐 Iris/RustBelt 的分离逻辑与生命周期逻辑。
- 方法论文献与工具文档增加官方 PDF、GitHub、项目主页链接。
- 删除旧版 Rust 1.94 模板内容，状态更新为 ✅ 完成。

---

**维护者**: Rust Research Methodology Group
**最后更新**: 2026-06-29 (权威国际化内容升级)
**状态**: ✅ 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf), [Iris Project](https://iris-project.org/), [Aeneas](https://aeneas-verif.github.io/aeneas/), [RustHorn](https://www.kb.is.s.u-tokyo.ac.jp/old-users/yskm24t/web/papers/esop2020-rust-horn.pdf)
>
> **权威来源对齐变更日志**: 2026-06-29 新增 RustBelt、Aeneas、RustHorn、Iris 等国际形式化方法来源 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.2
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 权威来源索引"""

t = re.sub(
    r"## 🆕 Rust 1\.94 深度整合更新.*?---\n\n## 权威来源索引",
    new_section,
    t,
    count=1,
    flags=re.DOTALL,
)
write(f, t)
print(f"Fixed {f.name}")


# ---- 10_tools_guide.md ----
f = ROOT / "10_tools_guide.md"
t = read(f)
old_toc = """  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)
  - [**最后更新**: 2026-03-14 (Rust 1.94 深度整合)](#最后更新-2026-03-14-rust-194-深度整合)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)"""
new_toc = """  - [🆕 权威国际化内容升级](#-权威国际化内容升级)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)"""
t = t.replace(old_toc, new_toc)
write(f, t)
print(f"Fixed {f.name}")


# ---- 10_research_roadmap.md ----
f = ROOT / "10_research_roadmap.md"
t = read(f)
old_toc = """  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)
  - [**最后更新**: 2026-03-14 (Rust 1.94 深度整合)](#最后更新-2026-03-14-rust-194-深度整合)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)"""
new_toc = """  - [🌐 与 Rust 官方发布路线图的同步](#-与-rust-官方发布路线图的同步)
  - [🆕 权威国际化内容升级](#-权威国际化内容升级)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)"""
t = t.replace(old_toc, new_toc)
write(f, t)
print(f"Fixed {f.name}")


# ---- 10_best_practices.md ----
f = ROOT / "10_best_practices.md"
t = read(f)
old_toc = """  - [🆕 Rust 1.94 研究更新](#-rust-194-研究更新)
    - [核心研究点](#核心研究点)
  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)"""
new_toc = """  - [🎯 与 Rust 官方规范的对齐](#-与-rust-官方规范的对齐)
  - [🆕 权威国际化内容升级](#-权威国际化内容升级)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)"""
t = t.replace(old_toc, new_toc)
write(f, t)
print(f"Fixed {f.name}")


# ---- 10_practical_applications.md ----
f = ROOT / "10_practical_applications.md"
t = read(f)
old_toc = """  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档-1)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)"""
new_toc = """  - [🌐 案例官方文档、源码与基准索引](#-案例官方文档源码与基准索引)
  - [🧭 Rust 机制与官方文档对照](#-rust-机制与官方文档对照)
  - [🆕 权威国际化内容升级](#-权威国际化内容升级)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)"""
t = t.replace(old_toc, new_toc)
write(f, t)
print(f"Fixed {f.name}")

print("\nTOC and methodology fixes applied.")
