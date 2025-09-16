//! 跨平台协议层说明：
//! - I/O 事件：Linux 使用 epoll（LT/ET），macOS 使用 kqueue，Windows 使用 IOCP。
//! - 本库示例使用 Tokio 提供的跨平台抽象，底层细节在 epoll 模块给出占位接口。
pub mod dns;
pub mod http;
pub mod ip;
pub mod tcp;
pub mod udp;
pub mod websocket;
