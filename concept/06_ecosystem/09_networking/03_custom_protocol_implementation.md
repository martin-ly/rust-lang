> **内容分级**: [专家级]
> **代码状态**: ✅ 含可编译示例
>
# 自定义协议实现
>
> **EN**: Custom Network Protocol Implementation in Rust
> **Summary**: Designing and implementing custom binary protocols in Rust: framing, state machines, zero-copy serialization, batching, streaming, and RPC patterns.
>
> **受众**: [专家]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L6 应用主题
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **前置概念**: [Rust 网络编程](../../03_advanced/06_low_level_patterns/18_network_programming.md) · [Async/Await](../../03_advanced/01_async/02_async.md) · [Error Handling](../../02_intermediate/03_error_handling/04_error_handling.md)
> **后置概念**: [高级网络协议](01_advanced_network_protocols.md) · [分布式系统](../04_web_and_networking/18_distributed_systems.md)
>
> **来源**: [Tokio](https://tokio.rs/) · [bytes crate](https://docs.rs/bytes/) · [byteorder crate](https://docs.rs/byteorder/)

---

## 1. 协议设计原则

优秀的自定义协议应在以下维度取得平衡：

| 维度 | 目标 |
| :--- | :--- |
| 性能 | 高序列化/反序列化速度、低 overhead |
| 可扩展性 | 向后兼容、模式演化 |
| 安全性 | 长度前缀防止缓冲区溢出、校验和 |
| 易用性 | 调试友好、工具支持 |

## 2. 二进制协议帧结构

```rust
use std::io::{self, Read, Write};
use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};

/// +--------+--------+--------+------------+----------+----------+
/// | Magic  | Version| MsgType| Length     | Seq ID   | Payload  |
/// | (2B)   | (1B)   | (1B)   | (4B)       | (4B)     | (N bytes)|
/// +--------+--------+--------+------------+----------+----------+
const MAGIC: u16 = 0xCAFE;
const VERSION: u8 = 1;
const HEADER_SIZE: usize = 12;

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq)]
enum MsgType {
    Request = 1,
    Response = 2,
    Error = 3,
    Heartbeat = 4,
}

#[derive(Debug, Clone)]
struct Frame {
    msg_type: MsgType,
    seq_id: u32,
    payload: Vec<u8>,
}

impl Frame {
    fn new_request(seq_id: u32, payload: Vec<u8>) -> Self {
        Self { msg_type: MsgType::Request, seq_id, payload }
    }

    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_u16::<BigEndian>(MAGIC)?;
        writer.write_u8(VERSION)?;
        writer.write_u8(self.msg_type as u8)?;
        writer.write_u32::<BigEndian>(self.payload.len() as u32)?;
        writer.write_u32::<BigEndian>(self.seq_id)?;
        writer.write_all(&self.payload)?;
        Ok(())
    }

    fn deserialize<R: Read>(reader: &mut R) -> io::Result<Self> {
        let magic = reader.read_u16::<BigEndian>()?;
        if magic != MAGIC {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "bad magic"));
        }
        let version = reader.read_u8()?;
        if version != VERSION {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "bad version"));
        }
        let msg_type = reader.read_u8()?;
        let length = reader.read_u32::<BigEndian>()? as usize;
        let seq_id = reader.read_u32::<BigEndian>()?;

        if length > 16 * 1024 * 1024 {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "payload too large"));
        }

        let mut payload = vec![0u8; length];
        reader.read_exact(&mut payload)?;

        Ok(Self { msg_type: unsafe { std::mem::transmute(msg_type) }, seq_id, payload })
    }
}
```

## 3. 协议状态机

使用 `enum` 显式建模协议状态：

```rust
#[derive(Debug, Clone, Copy, PartialEq)]
enum ConnectionState {
    Handshake,
    Established,
    Closing,
    Closed,
}

struct ProtocolConnection {
    state: ConnectionState,
    next_seq_id: u32,
}

impl ProtocolConnection {
    fn transition(&mut self, new_state: ConnectionState) -> Result<(), &'static str> {
        match (self.state, new_state) {
            (ConnectionState::Handshake, ConnectionState::Established) => Ok(()),
            (ConnectionState::Established, ConnectionState::Closing) => Ok(()),
            (ConnectionState::Closing, ConnectionState::Closed) => Ok(()),
            _ => Err("invalid state transition"),
        }?;
        self.state = new_state;
        Ok(())
    }
}
```

## 4. 零拷贝序列化

对于极高吞吐场景，可考虑 `bytes::Bytes` 和手动内存布局，避免多次拷贝：

```rust
use bytes::{Bytes, BytesMut, BufMut};

fn encode_frame_zero_copy(frame: &Frame) -> Bytes {
    let mut buf = BytesMut::with_capacity(HEADER_SIZE + frame.payload.len());
    buf.put_u16(MAGIC);
    buf.put_u8(VERSION);
    buf.put_u8(frame.msg_type as u8);
    buf.put_u32(frame.payload.len() as u32);
    buf.put_u32(frame.seq_id);
    buf.extend_from_slice(&frame.payload);
    buf.freeze()
}
```

## 5. 批量处理与流式传输

| 技术 | 适用场景 |
| :--- | :--- |
| 批量处理 | 高吞吐、可接受延迟 |
| 流式传输 | 大文件、实时数据 |
| 请求-响应 | RPC、命令控制 |

## 6. 错误处理与重试

- 使用序列号匹配请求与响应。
- 定义明确的错误码，避免用字符串传递错误。
- 对网络抖动实现指数退避重试，对不可恢复错误快速失败。

## 7. 生产级实践

- 为所有网络消息设置超时。
- 限制单连接内存使用（如 payload 大小上限）。
- 使用连接 keep-alive 和心跳检测死连接。
- 记录协议级指标（消息数、延迟、错误率）。

> **L5 对比**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [Rust vs Go](../../05_comparative/01_systems_languages/02_rust_vs_go.md)

---

## 相关概念

- [Rust 网络编程](../../03_advanced/06_low_level_patterns/18_network_programming.md)
- [网络安全](02_network_security.md)
- [高级网络协议](01_advanced_network_protocols.md)

---

> **来源**: [Tokio](https://tokio.rs/) · [bytes crate](https://docs.rs/bytes/) · [byteorder crate](https://docs.rs/byteorder/)


---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Hoare: Communicating Sequential Processes (CACM 1978)](https://dl.acm.org/doi/10.1145/359576.359585)
