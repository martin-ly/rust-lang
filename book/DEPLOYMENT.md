# 部署指南

> **最后更新**: 2026-03-08

---

## GitHub Pages 部署

### 自动部署

项目已配置 GitHub Actions 工作流，推送代码后自动部署：

1. 修改文档内容
2. 提交并推送：`git push origin main`
3. 等待 Actions 完成
4. 访问 `https://<username>.github.io/rust-lang/`

### 手动部署

```bash
cd book
mdbook build

# 部署到 gh-pages 分支
git worktree add /tmp/book gh-pages
cp -r book/* /tmp/book/
cd /tmp/book
git add .
git commit -m "Update documentation"
git push origin gh-pages
```

## 自定义域名

1. 在 `book/static/` 目录创建 `CNAME` 文件
2. 添加域名：`docs.example.com`
3. 在 DNS 配置中添加 CNAME 记录指向 `<username>.github.io`

## 相关文档

- [mdBook 使用说明](./README.md)
- [项目 README](../README.md)
