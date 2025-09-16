use crate::error::NetworkResult;
use pnet_datalink::{self as datalink, Channel, Config};
use pnet_packet::Packet;
use pnet_packet::ethernet::{EtherTypes, EthernetPacket};
use pnet_packet::ip::IpNextHeaderProtocols;
use pnet_packet::ipv4::Ipv4Packet;
use pnet_packet::tcp::TcpPacket;
use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Default)]
pub struct TcpStats {
    pub packets: u64,
    pub bytes: u64,
}

#[derive(Debug, Clone)]
pub struct TcpFlowKey {
    pub src: (IpAddr, u16),
    pub dst: (IpAddr, u16),
}

#[derive(Debug)]
pub struct TcpTrafficReport {
    pub total: TcpStats,
    pub by_flow: HashMap<String, TcpStats>,
    pub duration: Duration,
}

pub fn monitor_tcp_once(iface_name: Option<&str>, seconds: u64) -> NetworkResult<TcpTrafficReport> {
    let iface = super::arp::ArpSniffer::pick_interface(iface_name)
        .ok_or_else(|| crate::error::NetworkError::Configuration("no suitable interface".into()))?;
    let mut cfg = Config::default();
    cfg.promiscuous = true;
    let (_tx, mut rx) = match datalink::channel(&iface, cfg) {
        Ok(Channel::Ethernet(tx, rx)) => (tx, rx),
        Ok(_) => {
            return Err(crate::error::NetworkError::Other(
                "unsupported channel type".into(),
            ));
        }
        Err(e) => {
            return Err(crate::error::NetworkError::Other(format!(
                "open channel failed: {e}"
            )));
        }
    };

    let start = Instant::now();
    let deadline = start + Duration::from_secs(seconds);
    let mut total = TcpStats::default();
    let mut by_flow: HashMap<String, TcpStats> = HashMap::new();

    while Instant::now() < deadline {
        if let Ok(frame) = rx.next() {
            if let Some(eth) = EthernetPacket::new(frame) {
                if eth.get_ethertype() == EtherTypes::Ipv4 {
                    if let Some(ip) = Ipv4Packet::new(eth.payload()) {
                        if ip.get_next_level_protocol() == IpNextHeaderProtocols::Tcp {
                            if let Some(tcp) = TcpPacket::new(ip.payload()) {
                                let src = (
                                    IpAddr::V4(Ipv4Addr::from(ip.get_source())),
                                    tcp.get_source(),
                                );
                                let dst = (
                                    IpAddr::V4(Ipv4Addr::from(ip.get_destination())),
                                    tcp.get_destination(),
                                );
                                let key = format!("{}:{} -> {}:{}", src.0, src.1, dst.0, dst.1);
                                let len = tcp.packet().len() as u64;
                                total.packets += 1;
                                total.bytes += len;
                                let s = by_flow.entry(key).or_default();
                                s.packets += 1;
                                s.bytes += len;
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(TcpTrafficReport {
        total,
        by_flow,
        duration: start.elapsed(),
    })
}
