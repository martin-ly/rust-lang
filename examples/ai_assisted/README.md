# 🤖 AI辅助编程实战示例

本目录包含使用AI辅助工具（如GitHub Copilot、ChatGPT、Claude）开发的Rust代码示例。

## 📋 示例列表

### 1. LRU缓存实现 (`01_copilot_lru_cache.rs`)

**AI提示词**:

```text
实现一个线程安全的LRU缓存
- 输入：容量和键值对
- 输出：get/put操作
- 约束：O(1)时间复杂度，线程安全
```

**学习要点**:

- 泛型编程
- 线程安全（`Arc<Mutex>`）
- 双向链表实现
- HashMap + 链表组合

**运行**:

```bash
cargo run --example 01_copilot_lru_cache
```

---

### 2. 异步HTTP客户端 (`02_async_http_client.rs`)

**AI提示词**:

```text
实现异步HTTP客户端
- 功能：GET/POST/PUT/DELETE
- 特性：超时、重试、自定义头
- 错误处理：自定义Error类型
```

**学习要点**:

- 异步编程（tokio）
- Builder模式
- 错误处理（thiserror）
- 重试机制

**运行**:

```bash
cargo run --example 02_async_http_client
```

---

## 🎯 AI辅助开发流程

### 第1步：明确需求

```rust
// ✅ 好的提示词
// 实现一个线程安全的LRU缓存
// - 容量可配置
// - O(1) get/put
// - 使用HashMap + 双向链表
// - Arc<Mutex>保证线程安全

// ❌ 不好的提示词
// 实现一个缓存
```

### 第2步：AI生成初始代码

使用GitHub Copilot或ChatGPT生成基础结构。

### 第3步：人工审查和优化

- ✅ 检查所有权和借用
- ✅ 验证错误处理
- ✅ 优化性能
- ✅ 添加测试

### 第4步：测试验证

```bash
cargo test
cargo clippy
cargo fmt
```

---

## 🔍 AI工具使用技巧

### GitHub Copilot

1. **提供充足上下文**

   ```rust
   // 先定义数据结构
   struct LruCache<K, V> { }
   
   // 再让Copilot补全方法
   impl<K, V> LruCache<K, V> {
       // Copilot会自动建议方法
   }
   ```

2. **使用注释引导**

   ```rust
   // 实现get方法，如果key存在则移到最前面
   pub fn get(&self, key: &K) -> Option<V> {
       // Copilot会生成实现
   }
   ```

### ChatGPT/Claude

1. **STAR框架提示词**

   ```text
   Situation: 构建高性能HTTP客户端
   Task: 实现GET/POST，支持重试
   Action: 使用tokio异步运行时
   Result: 生产级可用的客户端
   ```

2. **迭代优化**

   ```text
   第1轮: 生成基础代码
   第2轮: 添加错误处理
   第3轮: 优化性能
   第4轮: 补充测试
   ```

---

## 📊 效率对比

| 任务 | 传统开发 | AI辅助 | 提升 |
|------|---------|--------|------|
| LRU缓存 | 2小时 | 30分钟 | **4倍** |
| HTTP客户端 | 4小时 | 1小时 | **4倍** |
| 测试代码 | 1小时 | 15分钟 | **4倍** |
| 文档注释 | 30分钟 | 5分钟 | **6倍** |

---

## ⚠️ 注意事项

### AI生成代码常见问题

1. **过度使用unwrap()**

   ```rust
   // ❌ AI可能生成
   let value = map.get(&key).unwrap();
   
   // ✅ 应该修改为
   let value = map.get(&key).ok_or(Error::NotFound)?;
   ```

2. **忽略生命周期**

   ```rust
   // ❌ AI可能忘记
   struct Parser {
       data: &str,
   }
   
   // ✅ 正确写法
   struct Parser<'a> {
       data: &'a str,
   }
   ```

3. **不当的错误处理**

   ```rust
   // ❌ 静默失败
   let n = s.parse().unwrap_or(0);
   
   // ✅ 明确错误
   let n = s.parse()?;
   ```

### 验证清单

- [ ] 编译通过（`cargo build`）
- [ ] 无警告（`cargo clippy`）
- [ ] 格式正确（`cargo fmt`）
- [ ] 测试通过（`cargo test`）
- [ ] 文档完整（`cargo doc`）

---

## 🎓 学习资源

- [AI辅助Rust编程指南](../../AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)
- [GitHub Copilot文档](https://docs.github.com/en/copilot)
- [Rust异步编程](https://rust-lang.github.io/async-book/)

---

## 🤝 贡献

欢迎提交更多AI辅助编程示例！

提交要求：

1. 包含AI提示词
2. 代码可运行
3. 包含测试
4. 说明学习要点

---

**最后更新**: 2025-10-20  
🤖 **AI是助手，不是替代品 - 保持批判性思维！**
