//! 抓包与流量分析入口

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub mod arp;

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub mod live_pcap;

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub mod offline;

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub mod pipeline;

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub mod tcp_monitor;

// udp_custom does not require pnet/pcap crates, always available
pub mod udp_custom;

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub use arp::{ArpRecord, ArpSniffConfig, ArpSniffer};

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub use live_pcap::{LiveTcpStats, arp_stream_bpf, list_devices, tcp_stats_stream_bpf};

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub use offline::{
    TcpOfflineStats, UdpOfflineStats, parse_pcap_arp, parse_pcap_tcp_stats, parse_pcap_udp_stats,
};

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub use pipeline::{TcpStats as AsyncTcpStats, TcpStatsSnapshot, arp_stream, tcp_stats_stream};

#[cfg(all(feature = "sniff", feature = "pcap"))]
pub use tcp_monitor::{TcpStats, TcpTrafficReport, monitor_tcp_once};

pub use udp_custom::{UdpCustomMessage, udp_custom_roundtrip, udp_custom_server};
