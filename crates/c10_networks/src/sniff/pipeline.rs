use crate::error::{NetworkError, NetworkResult};
use crate::sniff::{ArpRecord, ArpSniffConfig};
use pnet_datalink::{self as datalink, Channel, Config};
use pnet_packet::arp::{ArpHardwareTypes, ArpOperations, ArpPacket};
use pnet_packet::ethernet::{EtherTypes, EthernetPacket};
use pnet_packet::ip::IpNextHeaderProtocols;
use pnet_packet::ipv4::Ipv4Packet;
use pnet_packet::tcp::TcpPacket;
use pnet_packet::Packet;
use std::net::{IpAddr, Ipv4Addr};
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::mpsc;

#[derive(Debug, Clone, Default)]
pub struct TcpStats {
    pub packets: u64,
    pub bytes: u64,
}

#[derive(Debug, Clone)]
pub struct TcpStatsSnapshot {
    pub total: TcpStats,
    pub since: Instant,
    pub until: Instant,
}

/// 启动 ARP 抓包异步流，返回一个 mpsc Receiver
pub async fn arp_stream(cfg: ArpSniffConfig, channel_size: usize) -> NetworkResult<mpsc::Receiver<ArpRecord>> {
    let (tx, rx) = mpsc::channel(channel_size.max(1));

    let iface = super::arp::ArpSniffer::pick_interface(cfg.iface_name.as_deref())
        .ok_or_else(|| NetworkError::Configuration("no suitable interface".into()))?;

    let mut dl_cfg = Config::default();
    dl_cfg.promiscuous = cfg.promiscuous;

    let (tx_dl, mut rx_dl) = match datalink::channel(&iface, dl_cfg) {
        Ok(Channel::Ethernet(tx, rx)) => (tx, rx),
        Ok(_) => return Err(NetworkError::Other("unsupported channel type".into())),
        Err(e) => return Err(NetworkError::Other(format!("open channel failed: {e}"))),
    };

    tokio::task::spawn_blocking(move || {
        let _ = tx_dl; // 保持发送端在作用域内
        while let Ok(frame) = rx_dl.next() {
            if let Some(rec) = parse_arp_frame(frame) {
                if tx.blocking_send(rec).is_err() { break; }
            }
        }
    });

    Ok(rx)
}

fn parse_arp_frame(frame: &[u8]) -> Option<ArpRecord> {
    let eth = EthernetPacket::new(frame)?;
    if eth.get_ethertype() != EtherTypes::Arp { return None; }
    let arp = ArpPacket::new(eth.payload())?;
    if arp.get_hardware_type() != ArpHardwareTypes::Ethernet { return None; }
    let sender_mac = format!("{}", eth.get_source());
    let target_mac = Some(format!("{}", eth.get_destination()));
    let sender_ip = IpAddr::V4(Ipv4Addr::from(arp.get_sender_proto_addr()));
    let target_ip = IpAddr::V4(Ipv4Addr::from(arp.get_target_proto_addr()));
    let op = match arp.get_operation() { ArpOperations::Request => "request", ArpOperations::Reply => "reply", _ => "other" }.to_string();
    Some(ArpRecord { sender_mac, sender_ip, target_mac, target_ip, op, at: SystemTime::now() })
}

/// 启动 TCP 统计异步流：定期输出一个统计快照
pub async fn tcp_stats_stream(iface_name: Option<&str>, interval: Duration, channel_size: usize) -> NetworkResult<mpsc::Receiver<TcpStatsSnapshot>> {
    let (tx, rx) = mpsc::channel(channel_size.max(1));
    let iface = super::arp::ArpSniffer::pick_interface(iface_name)
        .ok_or_else(|| NetworkError::Configuration("no suitable interface".into()))?;
    let mut cfg = Config::default();
    cfg.promiscuous = true;

    let (_tx_dl, mut rx_dl) = match datalink::channel(&iface, cfg) {
        Ok(Channel::Ethernet(tx, rx)) => (tx, rx),
        Ok(_) => return Err(NetworkError::Other("unsupported channel type".into())),
        Err(e) => return Err(NetworkError::Other(format!("open channel failed: {e}"))),
    };

    tokio::task::spawn_blocking(move || {
        let mut total = TcpStats::default();
        let mut last_tick = Instant::now();
        loop {
            match rx_dl.next() {
                Ok(frame) => {
                    if let Some(eth) = EthernetPacket::new(frame) {
                        if eth.get_ethertype() == EtherTypes::Ipv4 {
                            if let Some(ip) = Ipv4Packet::new(eth.payload()) {
                                if ip.get_next_level_protocol() == IpNextHeaderProtocols::Tcp {
                                    if let Some(tcp) = TcpPacket::new(ip.payload()) {
                                        let len = tcp.packet().len() as u64;
                                        total.packets += 1;
                                        total.bytes += len;
                                    }
                                }
                            }
                        }
                    }
                }
                Err(_) => { /* ignore */ }
            }

            if last_tick.elapsed() >= interval {
                let now = Instant::now();
                let snap = TcpStatsSnapshot { total: total.clone(), since: last_tick, until: now };
                if tx.blocking_send(snap).is_err() { break; }
                last_tick = now;
            }
        }
    });

    Ok(rx)
}


