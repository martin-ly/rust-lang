use crate::error::{NetworkError, NetworkResult};
use pnet_datalink::{self as datalink, Channel, Config, NetworkInterface};
use pnet_packet::Packet;
use pnet_packet::arp::{ArpHardwareTypes, ArpOperations, ArpPacket};
use pnet_packet::ethernet::{EtherTypes, EthernetPacket};
use std::net::{IpAddr, Ipv4Addr};
use std::time::SystemTime;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArpRecord {
    pub sender_mac: String,
    pub sender_ip: IpAddr,
    pub target_mac: Option<String>,
    pub target_ip: IpAddr,
    pub op: String,
    pub at: SystemTime,
}

#[derive(Debug, Clone)]
pub struct ArpSniffConfig {
    pub iface_name: Option<String>,
    pub promiscuous: bool,
}

impl Default for ArpSniffConfig {
    fn default() -> Self {
        Self {
            iface_name: None,
            promiscuous: true,
        }
    }
}

pub struct ArpSniffer;

impl ArpSniffer {
    pub fn list_interfaces() -> Vec<NetworkInterface> {
        datalink::interfaces()
    }

    pub fn pick_interface(name_hint: Option<&str>) -> Option<NetworkInterface> {
        let interfaces = datalink::interfaces();
        if let Some(hint) = name_hint {
            interfaces.into_iter().find(|i| i.name == hint)
        } else {
            interfaces
                .into_iter()
                .find(|i| !i.is_loopback() && !i.ips.is_empty())
        }
    }

    pub fn sniff_arp_sync(
        cfg: ArpSniffConfig,
        limit: Option<usize>,
    ) -> NetworkResult<Vec<ArpRecord>> {
        let iface = Self::pick_interface(cfg.iface_name.as_deref())
            .ok_or_else(|| NetworkError::Configuration("no suitable interface".into()))?;

        let mut config = Config::default();
        config.promiscuous = cfg.promiscuous;

        let (_tx, mut rx) = match datalink::channel(&iface, config) {
            Ok(Channel::Ethernet(tx, rx)) => (tx, rx),
            Ok(_) => return Err(NetworkError::Other("unsupported channel type".into())),
            Err(e) => return Err(NetworkError::Other(format!("open channel failed: {e}"))),
        };

        let mut out = Vec::new();
        let mut count = 0usize;
        while limit.map(|n| count < n).unwrap_or(true) {
            match rx.next() {
                Ok(frame) => {
                    if let Some(rec) = parse_arp_frame(frame) {
                        out.push(rec);
                        count += 1;
                    }
                }
                Err(_e) => {
                    // ignore transient errors
                }
            }
        }
        Ok(out)
    }
}

fn parse_arp_frame(frame: &[u8]) -> Option<ArpRecord> {
    let eth = EthernetPacket::new(frame)?;
    if eth.get_ethertype() != EtherTypes::Arp {
        return None;
    }
    let arp = ArpPacket::new(eth.payload())?;
    if arp.get_hardware_type() != ArpHardwareTypes::Ethernet {
        return None;
    }

    let sender_mac = format!("{}", eth.get_source());
    let target_mac = Some(format!("{}", eth.get_destination()));
    let sender_ip = IpAddr::V4(Ipv4Addr::from(arp.get_sender_proto_addr()));
    let target_ip = IpAddr::V4(Ipv4Addr::from(arp.get_target_proto_addr()));
    let op = match arp.get_operation() {
        ArpOperations::Request => "request",
        ArpOperations::Reply => "reply",
        _ => "other",
    }
    .to_string();

    Some(ArpRecord {
        sender_mac,
        sender_ip,
        target_mac,
        target_ip,
        op,
        at: SystemTime::now(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn list_ifaces_ok() {
        let _v = ArpSniffer::list_interfaces();
        //assert!(_v.len() >= 0);
    }
}
