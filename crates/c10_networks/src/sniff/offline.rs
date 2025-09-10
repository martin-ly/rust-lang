#[cfg(feature = "offline")]
use crate::error::{NetworkError, NetworkResult};
#[cfg(feature = "offline")]
use pcap::Capture;
#[cfg(feature = "offline")]
use pnet_packet::arp::{ArpHardwareTypes, ArpOperations, ArpPacket};
#[cfg(feature = "offline")]
use pnet_packet::ethernet::{EtherTypes, EthernetPacket};
#[cfg(feature = "offline")]
use pnet_packet::ip::IpNextHeaderProtocols;
#[cfg(feature = "offline")]
use pnet_packet::ipv4::Ipv4Packet;
#[cfg(feature = "offline")]
use pnet_packet::tcp::TcpPacket;
#[cfg(feature = "offline")]
use pnet_packet::udp::UdpPacket;
#[cfg(feature = "offline")]
use pnet_packet::Packet;
#[cfg(feature = "offline")]
use std::net::{IpAddr, Ipv4Addr};

#[cfg(feature = "offline")]
use super::arp::ArpRecord;

#[cfg(feature = "offline")]
pub fn parse_pcap_arp(path: &str, limit: Option<usize>) -> NetworkResult<Vec<ArpRecord>> {
    let mut cap = Capture::from_file(path).map_err(|e| NetworkError::Other(e.to_string()))?;
    let mut out = Vec::new();
    let mut count = 0usize;
    while let Ok(packet) = cap.next_packet() {
        let data = packet.data;
        if let Some(eth) = EthernetPacket::new(data) {
            if eth.get_ethertype() == EtherTypes::Arp {
                if let Some(arp) = ArpPacket::new(eth.payload()) {
                    if arp.get_hardware_type() == ArpHardwareTypes::Ethernet {
                        use std::time::SystemTime;
                        let sender_mac = format!("{}", eth.get_source());
                        let target_mac = Some(format!("{}", eth.get_destination()));
                        let sender_ip = IpAddr::V4(Ipv4Addr::from(arp.get_sender_proto_addr()));
                        let target_ip = IpAddr::V4(Ipv4Addr::from(arp.get_target_proto_addr()));
                        let op = match arp.get_operation() { ArpOperations::Request => "request", ArpOperations::Reply => "reply", _ => "other" }.to_string();
                        out.push(ArpRecord { sender_mac, sender_ip, target_mac, target_ip, op, at: SystemTime::now() });
                        count += 1;
                        if limit.map(|n| count >= n).unwrap_or(false) { break; }
                    }
                }
            }
        }
    }
    Ok(out)
}

#[cfg(feature = "offline")]
#[derive(Debug, Default, Clone)]
pub struct TcpOfflineStats { pub packets: u64, pub bytes: u64 }

#[cfg(feature = "offline")]
pub fn parse_pcap_tcp_stats(path: &str) -> NetworkResult<TcpOfflineStats> {
    let mut cap = Capture::from_file(path).map_err(|e| NetworkError::Other(e.to_string()))?;
    let mut stats = TcpOfflineStats::default();
    while let Ok(packet) = cap.next_packet() {
        let data = packet.data;
        if let Some(eth) = EthernetPacket::new(data) {
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
    Ok(stats)
}

#[cfg(feature = "offline")]
#[derive(Debug, Default, Clone)]
pub struct UdpOfflineStats { pub packets: u64, pub bytes: u64 }

#[cfg(feature = "offline")]
pub fn parse_pcap_udp_stats(path: &str) -> NetworkResult<UdpOfflineStats> {
    let mut cap = Capture::from_file(path).map_err(|e| NetworkError::Other(e.to_string()))?;
    let mut stats = UdpOfflineStats::default();
    while let Ok(packet) = cap.next_packet() {
        let data = packet.data;
        if let Some(eth) = EthernetPacket::new(data) {
            if eth.get_ethertype() == EtherTypes::Ipv4 {
                if let Some(ip) = Ipv4Packet::new(eth.payload()) {
                    if ip.get_next_level_protocol() == IpNextHeaderProtocols::Udp {
                        if let Some(udp) = UdpPacket::new(ip.payload()) {
                            stats.packets += 1;
                            stats.bytes += udp.packet().len() as u64;
                        }
                    }
                }
            }
        }
    }
    Ok(stats)
}


