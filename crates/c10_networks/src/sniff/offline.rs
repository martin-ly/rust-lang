//! Offline pcap file analysis
//! 
//! This module requires the `sniff` and `pcap` features to be enabled.

#![cfg(all(feature = "sniff", feature = "pcap"))]

use crate::error::{NetworkError, NetworkResult};
use pcap::Capture;
use pnet_packet::Packet;
use pnet_packet::arp::{ArpHardwareTypes, ArpOperations, ArpPacket};
use pnet_packet::ethernet::{EtherTypes, EthernetPacket};
use pnet_packet::ip::IpNextHeaderProtocols;
use pnet_packet::ipv4::Ipv4Packet;
use pnet_packet::tcp::TcpPacket;
use pnet_packet::udp::UdpPacket;
use std::net::IpAddr;

use super::arp::ArpRecord;

pub fn parse_pcap_arp(path: &str, limit: Option<usize>) -> NetworkResult<Vec<ArpRecord>> {
    let mut cap = Capture::from_file(path).map_err(|e| NetworkError::Other(e.to_string()))?;
    let mut out = Vec::new();
    let mut count = 0usize;
    while let Ok(packet) = cap.next_packet() {
        let data = packet.data;
        if let Some(eth) = EthernetPacket::new(data)
            && eth.get_ethertype() == EtherTypes::Arp
            && let Some(arp) = ArpPacket::new(eth.payload())
            && arp.get_hardware_type() == ArpHardwareTypes::Ethernet
        {
            use std::time::SystemTime;
            let sender_mac = format!("{}", eth.get_source());
            let target_mac = Some(format!("{}", eth.get_destination()));
            let sender_ip = IpAddr::V4(arp.get_sender_proto_addr());
            let target_ip = IpAddr::V4(arp.get_target_proto_addr());
            let op = match arp.get_operation() {
                ArpOperations::Request => "request",
                ArpOperations::Reply => "reply",
                _ => "other",
            }
            .to_string();
            out.push(ArpRecord {
                sender_mac,
                sender_ip,
                target_mac,
                target_ip,
                op,
                at: SystemTime::now(),
            });
            count += 1;
            if limit.map(|n| count >= n).unwrap_or(false) {
                break;
            }
        }
    }
    Ok(out)
}

#[derive(Debug, Default, Clone)]
pub struct TcpOfflineStats {
    pub packets: u64,
    pub bytes: u64,
}

pub fn parse_pcap_tcp_stats(path: &str) -> NetworkResult<TcpOfflineStats> {
    let mut cap = Capture::from_file(path).map_err(|e| NetworkError::Other(e.to_string()))?;
    let mut stats = TcpOfflineStats::default();
    while let Ok(packet) = cap.next_packet() {
        let data = packet.data;
        if let Some(eth) = EthernetPacket::new(data)
            && eth.get_ethertype() == EtherTypes::Ipv4
            && let Some(ip) = Ipv4Packet::new(eth.payload())
            && ip.get_next_level_protocol() == IpNextHeaderProtocols::Tcp
            && let Some(tcp) = TcpPacket::new(ip.payload())
        {
            stats.packets += 1;
            stats.bytes += tcp.packet().len() as u64;
        }
    }
    Ok(stats)
}

#[derive(Debug, Default, Clone)]
pub struct UdpOfflineStats {
    pub packets: u64,
    pub bytes: u64,
}

pub fn parse_pcap_udp_stats(path: &str) -> NetworkResult<UdpOfflineStats> {
    let mut cap = Capture::from_file(path).map_err(|e| NetworkError::Other(e.to_string()))?;
    let mut stats = UdpOfflineStats::default();
    while let Ok(packet) = cap.next_packet() {
        let data = packet.data;
        if let Some(eth) = EthernetPacket::new(data)
            && eth.get_ethertype() == EtherTypes::Ipv4
            && let Some(ip) = Ipv4Packet::new(eth.payload())
            && ip.get_next_level_protocol() == IpNextHeaderProtocols::Udp
            && let Some(udp) = UdpPacket::new(ip.payload())
        {
            stats.packets += 1;
            stats.bytes += udp.packet().len() as u64;
        }
    }
    Ok(stats)
}
