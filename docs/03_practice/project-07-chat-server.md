# 实践项目 07: 聊天服务器

> **难度**: ⭐⭐ 进阶级
> **所需知识**: c05-c06, c10
> **预计时间**: 5-7小时

---

## 项目目标

创建一个支持多客户端的TCP聊天服务器。

---

## 功能需求

- [ ] 多客户端连接
- [ ] 广播消息
- [ ] 私聊功能
- [ ] 用户认证
- [ ] 消息历史

---

## 学习要点

### TCP服务器

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

async fn run_server() -> tokio::io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;

    loop {
        let (socket, _) = listener.accept().await?;
        tokio::spawn(handle_client(socket));
    }
}
```

---

## 参考实现

完整参考实现位于: `examples/chat-server/`
