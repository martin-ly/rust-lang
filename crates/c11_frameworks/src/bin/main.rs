fn main() {
    println!("c11_frameworks entry");
    // 演示如何在业务侧通过环境变量切换 c10_networks 的 DNS 解析后端：
    // C10_DNS_BACKEND=cloudflare_doh|cloudflare_dot|google_doh|google_dot|quad9_doh|quad9_dot
    // 这里仅打印提示，具体解析在 c10_networks::unified_api::NetClient 中完成。
}
