Crate:     atomic-polyfill
Version:   1.0.3
Warning:   unmaintained
Title:     atomic-polyfill is unmaintained
Date:      2023-07-11
ID:        RUSTSEC-2023-0089
URL:       <https://rustsec.org/advisories/RUSTSEC-2023-0089>
Dependency tree:
atomic-polyfill 1.0.3
└── heapless 0.7.17
    └── postcard 1.1.3
        └── c10_networks 0.1.0

Crate:     bare-metal
Version:   0.2.5
Warning:   unmaintained
Title:     bare-metal is deprecated
Date:      2026-04-23
ID:        RUSTSEC-2026-0110
URL:       <https://rustsec.org/advisories/RUSTSEC-2026-0110>
Dependency tree:
bare-metal 0.2.5
└── cortex-m 0.7.7
    └── c13_embedded 0.1.0

Crate:     instant
Version:   0.1.13
Warning:   unmaintained
Title:     `instant` is unmaintained
Date:      2024-09-01
ID:        RUSTSEC-2024-0384
URL:       <https://rustsec.org/advisories/RUSTSEC-2024-0384>
Dependency tree:
instant 0.1.13
└── fastrand 1.9.0
    └── futures-lite 1.13.0
        └── glommio 0.9.0
            └── c06_async 0.1.0

Crate:     paste
Version:   1.0.15
Warning:   unmaintained
Title:     paste - no longer maintained
Date:      2024-10-07
ID:        RUSTSEC-2024-0436
URL:       <https://rustsec.org/advisories/RUSTSEC-2024-0436>
Dependency tree:
paste 1.0.15
├── tokenizers 0.22.2
│   └── candle-core 0.10.2
│       ├── candle-nn 0.10.2
│       │   └── c08_algorithms 0.1.0
│       └── c08_algorithms 0.1.0
├── pulp 0.22.3
│   └── gemm-common 0.19.0
│       ├── gemm-f64 0.19.0
│       │   └── gemm 0.19.0
│       │       └── candle-core 0.10.2
│       ├── gemm-f32 0.19.0
│       │   ├── gemm-f16 0.19.0
│       │   │   └── gemm 0.19.0
│       │   └── gemm 0.19.0
│       ├── gemm-f16 0.19.0
│       ├── gemm-c64 0.19.0
│       │   └── gemm 0.19.0
│       ├── gemm-c32 0.19.0
│       │   └── gemm 0.19.0
│       └── gemm 0.19.0
├── netlink-packet-core 0.8.1
│   ├── rtnetlink 0.20.0
│   │   └── if-watch 3.2.2
│   │       ├── libp2p-tcp 0.44.1
│   │       │   └── libp2p 0.56.0
│   │       │       └── c10_networks 0.1.0
│   │       ├── libp2p-quic 0.13.1
│   │       │   └── libp2p 0.56.0
│   │       └── libp2p-mdns 0.48.0
│   │           └── libp2p 0.56.0
│   ├── netlink-proto 0.12.0
│   │   ├── rtnetlink 0.20.0
│   │   └── if-watch 3.2.2
│   ├── netlink-packet-route 0.28.0
│   │   ├── rtnetlink 0.20.0
│   │   └── if-watch 3.2.2
│   └── if-watch 3.2.2
├── macro_rules_attribute 0.2.2
│   └── tokenizers 0.22.2
├── gemm-f64 0.19.0
├── gemm-f32 0.19.0
├── gemm-f16 0.19.0
├── gemm-common 0.19.0
├── gemm-c64 0.19.0
├── gemm-c32 0.19.0
└── gemm 0.19.0
