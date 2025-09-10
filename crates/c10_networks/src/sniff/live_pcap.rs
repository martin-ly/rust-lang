#![cfg(feature = "pcap_live")]
use crate::error::{NetworkError, NetworkResult};
use crate::sniff::arp::ArpRecord;
use pcap::{Active, Capture, Device};
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
pub struct LiveTcpStats { pub packets: u64, pub bytes: u64 }

pub fn list_devices() -> NetworkResult<Vec<String>> {
    let devs = Device::list().map_err(|e| NetworkError::Other(e.to_string()))?;
    Ok(devs.into_iter().map(|d| d.name).collect())
}

fn open_live(name: &str, snaplen: i32, promisc: bool, timeout_ms: i32) -> NetworkResult<Capture<Active>> {
    let mut cap = Capture::from_device(name)
        .map_err(|e| NetworkError::Other(e.to_string()))?
        .promisc(promisc)
        .snaplen(snaplen)
        .timeout(timeout_ms)
        .open()
        .map_err(|e| NetworkError::Other(e.to_string()))?;
    Ok(cap)
}

pub async fn arp_stream_bpf(device: &str, bpf: &str, chan: usize) -> NetworkResult<mpsc::Receiver<ArpRecord>> {
    let (tx, rx) = mpsc::channel(chan.max(1));
    let dev = device.to_string();
    let filter = bpf.to_string();
    tokio::task::spawn_blocking(move || {
        let mut cap = match open_live(&dev, 65535, true, 10) { Ok(c) => c, Err(_) => return };
        let _ = cap.filter(&filter, true);
        while let Ok(p) = cap.next_packet() {
            if let Some(eth) = EthernetPacket::new(p.data) {
                if eth.get_ethertype() == EtherTypes::Arp {
                    if let Some(arp) = ArpPacket::new(eth.payload()) {
                        if arp.get_hardware_type() == ArpHardwareTypes::Ethernet {
                            let rec = ArpRecord {
                                sender_mac: format!("{}", eth.get_source()),
                                target_mac: Some(format!("{}", eth.get_destination())),
                                sender_ip: IpAddr::V4(Ipv4Addr::from(arp.get_sender_proto_addr())),
                                target_ip: IpAddr::V4(Ipv4Addr::from(arp.get_target_proto_addr())),
                                op: match arp.get_operation() { ArpOperations::Request => "request", ArpOperations::Reply => "reply", _ => "other" }.to_string(),
                                at: SystemTime::now(),
                            };
                            if tx.blocking_send(rec).is_err() { break; }
                        }
                    }
                }
            }
        }
    });
    Ok(rx)
}

pub async fn tcp_stats_stream_bpf(device: &str, bpf: &str, interval: Duration, chan: usize) -> NetworkResult<mpsc::Receiver<(Instant, LiveTcpStats)>> {
    let (tx, rx) = mpsc::channel(chan.max(1));
    let dev = device.to_string();
    let filter = bpf.to_string();
    tokio::task::spawn_blocking(move || {
        let mut cap = match open_live(&dev, 65535, true, 10) { Ok(c) => c, Err(_) => return };
        let _ = cap.filter(&filter, true);
        let mut stats = LiveTcpStats::default();
        let mut last = Instant::now();
        loop {
            match cap.next_packet() {
                Ok(p) => {
                    if let Some(eth) = EthernetPacket::new(p.data) {
                        if eth.get_ethertype() == EtherTypes::Ipv4 {
                            if let Some(ip) = Ipv4Packet::new(eth.payload()) {
                                if ip.get_next_level_protocol() == IpNextHeaderProtocols::Tcp {
                                    if let Some(tcp) = TcpPacket::new(ip.payload()) {
                                        stats.packets += 1;
                                        stats.bytes += tcp.packet().len() as u64;
                                    }
                                }
                            }
                        }
                    }
                }
                Err(_) => {}
            }
            if last.elapsed() >= interval {
                let now = Instant::now();
                let _ = tx.blocking_send((now, stats.clone()));
                last = now;
            }
        }
    });
    Ok(rx)
}


