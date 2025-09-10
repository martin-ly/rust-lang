set shell := ["bash", "-cu"]

# DNS examples via c10_networks
dns-doh-dot domain="example.com":
    cargo run -p c10_networks --example dns_doh_dot -- {{domain}}

dns-custom-ns domain="internal.service.local":
    cargo run -p c10_networks --example dns_custom_ns -- {{domain}}

dns-ptr:
    cargo run -p c10_networks --example dns_ptr

dns-records domain="example.com":
    cargo run -p c10_networks --example dns_records -- {{domain}}

dns-negative-cache:
    cargo run -p c10_networks --example dns_negative_cache -- nonexistent.example.invalid

dns-all domain="example.com":
    bash crates/c10_networks/scripts/run_examples.sh {{domain}}

test-skip-net:
    C10_SKIP_NETWORK_TESTS=1 cargo test -p c10_networks


