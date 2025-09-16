//! MAC 地址工具

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacAddress([u8; 6]);

impl MacAddress {
    pub fn parse(s: &str) -> Option<Self> {
        let parts: Vec<&str> = s.split(|c| c == ':' || c == '-').collect();
        if parts.len() != 6 {
            return None;
        }
        let mut b = [0u8; 6];
        for (i, p) in parts.iter().enumerate() {
            b[i] = u8::from_str_radix(p, 16).ok()?;
        }
        Some(MacAddress(b))
    }
    pub fn to_colon_string(&self) -> String {
        self.0
            .iter()
            .map(|x| format!("{:02x}", x))
            .collect::<Vec<_>>()
            .join(":")
    }
}
