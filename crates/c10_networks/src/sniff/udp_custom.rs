use crate::error::{NetworkError, NetworkResult};
use bytes::{BufMut, Bytes, BytesMut};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct UdpCustomMessage {
    pub version: u8,
    pub msg_type: u8,
    pub payload: Vec<u8>,
}

impl UdpCustomMessage {
    pub fn encode(&self) -> Bytes {
        let mut buf = BytesMut::with_capacity(4 + self.payload.len());
        buf.put_u8(self.version);
        buf.put_u8(self.msg_type);
        buf.put_u16(self.payload.len() as u16);
        buf.extend_from_slice(&self.payload);
        buf.freeze()
    }

    pub fn decode(b: &[u8]) -> NetworkResult<Self> {
        if b.len() < 4 { return Err(NetworkError::Protocol("short packet".into())); }
        let version = b[0];
        let msg_type = b[1];
        let len = u16::from_be_bytes([b[2], b[3]]) as usize;
        if b.len() < 4 + len { return Err(NetworkError::Protocol("invalid length".into())); }
        let payload = b[4..4+len].to_vec();
        Ok(Self { version, msg_type, payload })
    }
}

pub async fn udp_custom_roundtrip(addr: &str, msg: &UdpCustomMessage) -> NetworkResult<UdpCustomMessage> {
    let sock = tokio::net::UdpSocket::bind("127.0.0.1:0").await?;
    let data = msg.encode();
    sock.send_to(&data, addr).await?;
    let mut buf = vec![0u8; 2048];
    let (n, _peer) = sock.recv_from(&mut buf).await?;
    UdpCustomMessage::decode(&buf[..n])
}

pub async fn udp_custom_server(bind: SocketAddr) -> Result<(), NetworkError> {
    let sock = tokio::net::UdpSocket::bind(bind).await?;
    let mut buf = vec![0u8; 2048];
    loop {
        let (n, peer) = sock.recv_from(&mut buf).await?;
        match UdpCustomMessage::decode(&buf[..n]) {
            Ok(mut m) => {
                // 简单回显：将 msg_type + 1
                m.msg_type = m.msg_type.wrapping_add(1);
                let out = m.encode();
                let _ = sock.send_to(&out, peer).await;
            }
            Err(_) => { /* ignore */ }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_decode_roundtrip() {
        let msg = UdpCustomMessage { version: 1, msg_type: 7, payload: b"abc".to_vec() };
        let b = msg.encode();
        let got = UdpCustomMessage::decode(&b).unwrap();
        assert_eq!(got, msg);
    }

    #[test]
    fn decode_short_packet() {
        let err = UdpCustomMessage::decode(&[1,2,0]).unwrap_err();
        match err { NetworkError::Protocol(_) => {}, _ => panic!("expect protocol error") }
    }
}

