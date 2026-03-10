# mdBook 在线文档平台

> **最后更新**: 2026-03-08

---

## 简介

本项目使用 [mdBook](https://github.com/rust-lang/mdBook) 搭建在线文档平台，提供舒适的阅读体验。

## 快速开始

### 安装 mdBook

```bash
cargo install mdbook
```

### 本地预览

```bash
cd book
mdbook serve --open
```

访问 <http://localhost:3000> 查看文档。

## 构建

```bash
mdbook build
```

构建输出位于 `book/book` 目录。

## 部署到 GitHub Pages

1. 推送代码到 GitHub
2. 启用 GitHub Pages (Settings → Pages → Source: GitHub Actions)
3. 等待自动部署完成

## 文档结构

```
book/
├── book.toml       # mdBook 配置
├── src/            # 文档源文件
│   ├── SUMMARY.md  # 目录结构
│   └── chapter_*.md # 各章节
└── README.md       # 本文件
```

## 相关文档

- [部署指南](./DEPLOYMENT.md)
- [项目 README](../README.md)
