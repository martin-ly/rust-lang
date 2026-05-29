//! Rust 1.97 特性跟踪模块 —— 网络编程
#![allow(clippy::incompatible_msrv)]

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use std::ops::{BitAnd, BitOr, Not};

/// # Rust 1.97 网络特性演示
///
/// Rust 1.97 稳定化的核心网络 API：
/// - `Ipv6Addr::is_unique_local` / `is_unicast_link_local`
/// - `IpAddr::to_canonical` / `Ipv6Addr::to_canonical`
/// - `Not`, `BitAnd`, `BitOr` 等位运算 trait 为 IP 地址实现
pub struct Rust197NetworkFeatures;

impl Rust197NetworkFeatures {
    /// 检查 IPv6 地址是否为 Unique Local Address (ULA, fc00::/7)
    pub fn is_unique_local(addr: Ipv6Addr) -> bool {
        addr.is_unique_local()
    }

    /// 检查 IPv6 地址是否为 Unicast Link-Local (fe80::/10)
    pub fn is_unicast_link_local(addr: Ipv6Addr) -> bool {
        addr.is_unicast_link_local()
    }

    /// 将 IPv6 地址转换为其规范形式
    ///
    /// 对于 IPv4-mapped IPv6 地址，返回对应的 IPv4 地址；否则返回自身。
    pub fn to_canonical(addr: IpAddr) -> IpAddr {
        addr.to_canonical()
    }

    /// 演示 IPv6 地址的位运算（Rust 1.97+）
    ///
    /// IP 地址现在支持 `!`, `&`, `|`, `^` 等位运算。
    pub fn ipv6_bitwise_mask(addr: Ipv6Addr, mask: Ipv6Addr) -> Ipv6Addr {
        addr.bitand(mask)
    }

    /// 演示 IPv4 地址的位或运算
    pub fn ipv4_bitwise_or(a: Ipv4Addr, b: Ipv4Addr) -> Ipv4Addr {
        a.bitor(b)
    }

    /// 演示 IPv4 地址的取反运算
    pub fn ipv4_invert(addr: Ipv4Addr) -> Ipv4Addr {
        addr.not()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_unique_local() {
        let ula = Ipv6Addr::new(0xfc00, 0, 0, 0, 0, 0, 0, 1);
        assert!(Rust197NetworkFeatures::is_unique_local(ula));

        let global = Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1);
        assert!(!Rust197NetworkFeatures::is_unique_local(global));
    }

    #[test]
    fn test_is_unicast_link_local() {
        let link_local = Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 1);
        assert!(Rust197NetworkFeatures::is_unicast_link_local(link_local));

        let global = Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1);
        assert!(!Rust197NetworkFeatures::is_unicast_link_local(global));
    }

    #[test]
    fn test_to_canonical_ipv4_mapped() {
        let mapped = IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0xffff, 0xc000, 0x0280));
        let canonical = Rust197NetworkFeatures::to_canonical(mapped);
        assert_eq!(canonical, IpAddr::V4(Ipv4Addr::new(192, 0, 2, 128)));
    }

    #[test]
    fn test_to_canonical_regular_ipv6() {
        let v6 = IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1));
        let canonical = Rust197NetworkFeatures::to_canonical(v6);
        assert_eq!(canonical, v6);
    }

    #[test]
    fn test_ipv6_bitwise_mask() {
        let addr = Ipv6Addr::new(0xffff, 0xffff, 0xffff, 0xffff, 0, 0, 0, 0);
        let mask = Ipv6Addr::new(
            0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
        );
        let result = Rust197NetworkFeatures::ipv6_bitwise_mask(addr, mask);
        assert_eq!(result, addr);
    }

    #[test]
    fn test_ipv4_bitwise_or() {
        let a = Ipv4Addr::new(192, 168, 0, 0);
        let b = Ipv4Addr::new(0, 0, 1, 1);
        let result = Rust197NetworkFeatures::ipv4_bitwise_or(a, b);
        assert_eq!(result, Ipv4Addr::new(192, 168, 1, 1));
    }

    #[test]
    fn test_ipv4_invert() {
        let addr = Ipv4Addr::new(255, 255, 255, 0);
        let result = Rust197NetworkFeatures::ipv4_invert(addr);
        assert_eq!(result, Ipv4Addr::new(0, 0, 0, 255));
    }
}
