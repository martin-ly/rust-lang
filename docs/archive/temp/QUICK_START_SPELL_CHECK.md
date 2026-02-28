# 🚀 拼写检查快速启动指南


> **创建日期**: 2026-01-26
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已归档
## ⚡ 3 步解决所有拼写错误

### 第 1 步: 安装扩展（如果未安装）

在 VS Code 中：

```text
Ctrl+Shift+X → 搜索 "Code Spell Checker" → 安装
```

### 第 2 步: 重新加载 VS Code

```text
Ctrl+Shift+P → 输入 "Reload Window" → 回车
```

### 第 3 步: 验证

✅ 所有专业术语的拼写错误提示应该消失！

---

## 📊 配置覆盖

已添加 **300+ 专业术语**，涵盖：

- ✅ WASM/WebAssembly 生态
- ✅ Rust 语言和标准库
- ✅ 网络协议 (HTTP/TCP/WebSocket)
- ✅ 设计模式 (Actor/Reactor/Singleton)
- ✅ 算法术语 (BFS/DFS/Dijkstra)
- ✅ 并发异步 (tokio/Future/Stream)
- ✅ 宏系统 (proc-macro/syn/quote)
- ✅ 测试工具 (Criterion/Playwright)

---

## 🔧 配置文件位置

```text
rust-lang/
├── .vscode/
│   ├── settings.json       ← 主配置文件（300+ 术语）
│   └── extensions.json     ← 推荐扩展
├── cspell.json            ← 全局配置
└── SPELL_CHECK_CONFIGURATION.md  ← 完整文档
```

---

## ❓ 还有拼写错误？

### 临时禁用（单个文件）

在文件顶部添加：

```markdown
<!-- cSpell:disable -->
```

### 添加新词汇

编辑 `.vscode/settings.json`，在相应类别下添加：

```json
{
  "cSpell.words": [
    // ... 现有词汇 ...
    "你的新术语"
  ]
}
```

---

## 📖 详细文档

查看完整配置文档：

- [SPELL_CHECK_CONFIGURATION.md](./SPELL_CHECK_CONFIGURATION.md)

---

**状态**: ✅ 配置完成
**日期**: 2025-10-30
**覆盖项目**: c08-c12 所有子模块