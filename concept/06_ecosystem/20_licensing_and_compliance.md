# 许可证与合规：Rust 项目的法律工程

> **Bloom 层级**: 应用 → 评价
> **定位**: 系统讲解 Rust **开源许可证选择**、**依赖合规**和**版权管理**——从 MIT [来源: [MIT License](https://opensource.org/licenses/MIT)]/Apache [来源: [Apache 2.0](https://www.apache.org/licenses/LICENSE-2.0)]-2.0 双许可到 cargo-deny 的许可证审计，揭示如何在工程实践中管理法律风险。
> **前置概念**: [Toolchain](./01_toolchain.md) · [Cargo](./01_toolchain.md) · [Security Practices](./19_security_practices.md)
> **后置概念**: [Cross Compilation](./17_cross_compilation.md) · [Distributed Systems](./18_distributed_systems.md)

---

> **来源**: [Rust FAQ — Why MIT/Apache-2.0](https://www.rust-lang.org/policies/licenses) · [Choose a License](https://choosealicense.com/) · [SPDX License List](https://spdx.org/licenses/) · [cargo-deny](https://github.com/EmbarkStudios/cargo-deny) · [OSI Approved Licenses](https://opensource.org/licenses) · [Wikipedia — Software License](https://en.wikipedia.org/wiki/Software_license)

## 📑 目录

- [许可证与合规：Rust 项目的法律工程](#许可证与合规rust-项目的法律工程)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 Rust 生态的许可证文化](#11-rust-生态的许可证文化)
    - [1.2 主要开源许可证对比](#12-主要开源许可证对比)
    - [1.3 依赖传递与许可证传染](#13-依赖传递与许可证传染)
  - [二、技术细节](#二技术细节)
    - [2.1 许可证合规工具链](#21-许可证合规工具链)
    - [2.2 双重许可策略](#22-双重许可策略)
    - [2.3 商业使用考量](#23-商业使用考量)
  - [三、许可证模式矩阵](#三许可证模式矩阵)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)

---

## 一、核心概念

### 1.1 Rust 生态的许可证文化

```text
Rust 生态的许可证现状:

  标准库与编译器:
  ├── MIT/Apache-2.0 双许可
  ├── 最大化兼容性
  └── 允许商业使用、修改、分发

  主流 crate 的许可证分布:
  ├── MIT: ~60%
  ├── Apache-2.0: ~20%
  ├── MIT/Apache-2.0 双许可: ~15%
  ├── BSD/ISC: ~3%
  ├── GPL [来源: [GPL](https://www.gnu.org/licenses/gpl-3.0)]/LGPL: ~1%
  └── 其他/专有: ~1%

  Rust 的许可证选择理由:
  ├── MIT: 简单、宽松、广泛兼容
  ├── Apache-2.0: 专利保护、明确权利
  ├── 双许可: 让使用者选择更合适的
  └── 与 GPL 不同: 不强制开源衍生作品

  为什么不是 GPL:
  ├── GPL 的 copyleft 限制商业使用
  ├── 与某些企业政策冲突
  ├── Rust 追求最大生态参与度
  └── 但 GPL crate 在生态中存在
```

> **认知功能**: Rust 生态的**MIT/Apache-2.0 双许可**是**工程与法律权衡**的结果——它平衡了开发者自由、商业友好和法律保护。
> [来源: [Rust License FAQ](https://www.rust-lang.org/policies/licenses)]

---

### 1.2 主要开源许可证对比

```text
许可证对比:

  宽松许可证（Permissive）:
  ┌─────────────────┬─────────────────┬─────────────────┐
  │ 许可证          │ 专利授权        │ 必须开源衍生作品│
  ├─────────────────┼─────────────────┼─────────────────┤
  │ MIT             │ 无              │ 否              │
  │ Apache-2.0      │ 有              │ 否              │
  │ BSD-2/3-Clause  │ 无              │ 否              │
  │ ISC             │ 无              │ 否              │
  │ zlib            │ 无              │ 否              │
  └─────────────────┴─────────────────┴─────────────────┘

  Copyleft 许可证:
  ┌─────────────────┬─────────────────┬─────────────────┐
  │ 许可证          │ 专利授权        │ 必须开源衍生作品│
  ├─────────────────┼─────────────────┼─────────────────┤
  │ GPL-2.0/3.0     │ 有              │ 是（同等许可证）│
  │ LGPL            │ 有              │ 修改库时必须    │
  │ AGPL            │ 有              │ 网络服务也必须  │
  │ MPL-2.0         │ 有              │ 修改文件时必须  │
  └─────────────────┴─────────────────┴─────────────────┘

  关键差异:
  ├── MIT: 最简单，只有版权声明
  ├── Apache-2.0: 有专利授权和终止条款
  ├── GPL: 强制衍生作品开源（传染性）
  └── 企业通常偏好 Apache-2.0（专利保护）

  代码示例:
  // MIT 许可证头
  // Copyright (c) 2024 Author Name
  // SPDX-License-Identifier: MIT

  // Apache-2.0 许可证头
  // Copyright 2024 Author Name
  // Licensed under the Apache License, Version 2.0
  // SPDX-License-Identifier: Apache-2.0
```

> **许可证洞察**: **Apache-2.0 优于 MIT**——它提供**专利保护**，在专利诉讼频发的环境中更安全。
> [来源: [Choose a License](https://choosealicense.com/licenses/)]

---

### 1.3 依赖传递与许可证传染

```text
许可证传染（License Contagion）:

  基本原则:
  ├── 使用 GPL 库 → 你的代码必须是 GPL
  ├── 使用 LGPL 库 → 修改库代码时必须开源
  ├── 使用 MIT 库 → 无限制（保留版权声明）
  └── 使用 Apache-2.0 → 无限制（保留 NOTICE）

  静态链接 vs 动态链接:
  ├── GPL: 静态链接 = 衍生作品，动态链接 = 灰色地带
  ├── LGPL: 动态链接通常安全
  └── Rust: 默认静态链接，需特别注意

  Rust 的特殊性:
  ├── 编译时依赖（build-dependencies）
  ├── 运行时依赖（dependencies）
  ├── dev-dependencies 不传染
  └── proc-macro 的许可证影响

  合规检查:
  ├── 所有依赖的许可证清单
  ├── 与组织政策的兼容性
  ├── 专利风险评估
  └── 第三方代码归属
```

> **传染洞察**: Rust 的**静态链接默认**使 GPL 传染问题**更严重**——使用 GPL crate 可能需要整个项目开源。
> [来源: [GNU GPL FAQ — Static vs Dynamic](https://www.gnu.org/licenses/gpl-faq.html#StaticVsDynamic)]

---

## 二、技术细节

### 2.1 许可证合规工具链

```text
Rust 许可证工具:

  cargo-deny:
  ├── 许可证检查
  ├── 漏洞检查（整合 cargo-audit）
  ├── 禁止特定 crate
  └── 配置策略文件

  cargo-about:
  ├── 生成许可证清单
  ├── 生成 THIRD-PARTY-LICENSES 文件
  └── HTML/JSON 输出

  cargo-license:
  ├── 简单列出所有依赖许可证
  └── 快速概览

  配置示例 (deny.toml):
  [licenses]
  allow = ["MIT", "Apache-2.0", "BSD-3-Clause", "ISC"]
  deny = ["GPL-2.0", "GPL-3.0", "AGPL-3.0"]
  copyleft = "deny"

  [bans]
  # 禁止特定 crate
  multiple-versions = "warn"

  [advisories]
  # 漏洞数据库
  db-path = "~/.cargo/advisory-db"
  db-urls = ["https://github.com/RustSec/advisory-db"]

  CI 集成:
  ├── cargo deny check
  ├── cargo deny check licenses
  └── 阻止合并不符合的 PR
```

> **工具洞察**: **cargo-deny 是 Rust 许可证合规的标配**——它将许可证策略编码为配置，自动执行检查。
> [来源: [cargo-deny Book](https://embarkstudios.github.io/cargo-deny/)]

---

### 2.2 双重许可策略

```text
MIT/Apache-2.0 双许可的实施:

  项目设置:
  ├── LICENSE-MIT 文件
  ├── LICENSE-APACHE 文件
  ├── Cargo.toml: license = "MIT OR Apache-2.0"
  └── 源码文件头: SPDX-License-Identifier: MIT OR Apache-2.0

  为什么双许可:
  ├── MIT: 简单、兼容 GPL
  ├── Apache-2.0: 专利保护
  └── 使用者可选择任一许可条款

  Cargo.toml 配置:
  [package]
  name = "my-crate"
  version = "1.0.0"
  license = "MIT OR Apache-2.0"
  repository = "https://github.com/user/repo"

  源码文件头:
  // Copyright (c) 2024 Author Name
  //
  // Licensed under the Apache License, Version 2.0
  // <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
  // or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
  // at your option. All files in the project carrying such notice may not be
  // copied, modified, or distributed except according to those terms.
  // SPDX-License-Identifier: MIT OR Apache-2.0

  归属要求:
  ├── 保留版权声明
  ├── 保留许可证文本
  └── 修改时注明变更
```

> **双许可洞察**: **MIT OR Apache-2.0** 是 Rust 生态的**事实标准**——它最大化兼容性同时提供专利保护。
> [来源: [Rust RFC — License](https://rust-lang.github.io/rfcs/0007-privacy-and-visibility.html)]

---

### 2.3 商业使用考量

```text
商业使用场景:

  闭源产品使用 Rust:
  ├── 使用 MIT/Apache-2.0 crate: 安全
  ├── 使用 LGPL crate: 动态链接或提供 object files
  ├── 使用 GPL crate: 必须开源或避免使用
  └── 修改 crate: 注意许可证要求

  云服务/ SaaS:
  ├── 传统 GPL: 不传染（不"分发"软件）
  ├── AGPL: 网络使用也需开源
  └── 特别注意 AGPL 依赖

  专利风险:
  ├── MIT: 无专利保护
  ├── Apache-2.0: 有专利授权
  │   └── 但专利诉讼时授权终止
  └── 企业通常偏好 Apache-2.0

  合规清单:
  ├── [ ] 所有依赖的许可证清单
  ├── [ ] 与法务确认兼容性
  ├── [ ] 生成 THIRD-PARTY-LICENSES
  ├── [ ] 保留所有版权声明
  ├── [ ] 检查 copyleft 依赖
  └── [ ] 定期审计（季度）
```

> **商业洞察**: **Apache-2.0 是商业项目的安全选择**——它提供专利保护且不强制开源衍生作品。
> [来源: [Apache 2.0 License](https://www.apache.org/licenses/LICENSE-2.0)]

---

## 三、许可证模式矩阵

```text
场景 → 推荐许可证 → 原因

开源库（Rust 生态）:
  → MIT OR Apache-2.0
  → 生态标准，最大兼容

企业内部工具:
  → 企业专有许可 / 不公开
  → 或 MIT 如果希望开源

商业产品:
  → 闭源 + 依赖 MIT/Apache-2.0
  → 避免 GPL/AGPL

GPL 项目:
  → GPL-3.0 / AGPL-3.0
  → 强制衍生作品开源

嵌入式/固件:
  → MIT / BSD-3-Clause
  → 简单，无专利条款

学术论文代码:
  → MIT / Apache-2.0
  → 促进复现和引用
```

> **模式矩阵**: **许可证选择是策略决策**——取决于项目目标、商业模式和风险偏好。
> [来源: [Choose a License](https://choosealicense.com/)]

---

## 四、反命题与边界分析

### 4.1 反命题树

```mermaid
graph TD
    ROOT["命题: 所有 Rust 项目都应使用 MIT OR Apache-2.0"]
    ROOT --> Q1{"是否强制衍生作品开源?"}
    Q1 -->|是| GPL["✅ GPL/AGPL"]
    Q1 -->|否| Q2{"是否需要专利保护?"}
    Q2 -->|是| APACHE["✅ Apache-2.0"]
    Q2 -->|否| MIT["✅ MIT"]

    style GPL fill:#c8e6c9
    style APACHE fill:#c8e6c9
    style MIT fill:#c8e6c9
```

> **认知功能**: **没有 universally best 许可证**——选择取决于项目哲学（自由软件 vs 开源 vs 专有）。
> [来源: [OSI License Comparison](https://opensource.org/licenses)]

---

### 4.2 边界极限

```text
边界 1: 许可证兼容性
├── MIT 与 GPL 兼容（MIT 可被 GPL 吸收）
├── Apache-2.0 与 GPL-3.0 兼容
├── Apache-2.0 与 GPL-2.0 不兼容
└── 混合项目需仔细审查

边界 2: 归属要求
├── MIT 要求保留版权声明
├── Apache-2.0 要求保留 NOTICE
├── 大量依赖时归属文件巨大
└── 缓解: cargo-about 自动生成

边界 3: 无许可证 ≠ 公共领域
├── 无许可证代码默认受版权保护
├── 不能随意使用
├── 需联系作者获取许可
└── 缓解: 只使用明确许可的代码

边界 4: 公司政策限制
├── 某些公司禁止特定许可证
├── 开源贡献需审批
├── 与内部工具许可冲突
└── 缓解: cargo-deny 策略配置

边界 5: 国际法律差异
├── 不同国家版权法不同
├── 美国有明确的开源法律先例
├── 其他地区可能模糊
└── 缓解: 咨询当地法务
```

> **边界要点**: 许可证的边界主要与**兼容性**、**归属**、**默认版权**、**公司政策**和**国际法律**相关。
> [来源: [SPDX License List](https://spdx.org/licenses/)]

---

## 五、常见陷阱

```text
陷阱 1: 忽略依赖的依赖
  ❌ 只检查直接依赖的许可证
     // 传递依赖可能有 GPL

  ✅ 使用 cargo-deny 检查所有依赖
     // 包括传递依赖

陷阱 2: 无许可证发布代码
  ❌ GitHub 仓库无 LICENSE 文件
     // 默认全版权所有，他人无权使用

  ✅ 明确添加 LICENSE 文件
     // 即使选择 "All Rights Reserved"

陷阱 3: 混用不兼容许可证
  ❌ 将 Apache-2.0 代码与 GPL-2.0 代码合并
     // 法律上可能不兼容

  ✅ 使用 cargo-deny 检查兼容性
     // 或咨询法务

陷阱 4: 修改许可证头
  ❌ 删除原始作者的版权声明
     // 违反许可证条款

  ✅ 保留原始版权声明
     // 添加自己的修改声明

陷阱 5: 混淆 SPDX 表达式
  ❌ Cargo.toml: license = "MIT/Apache-2.0"
     // 语法错误，应为 "MIT OR Apache-2.0"

  ✅ 使用正确的 SPDX 表达式
     // "MIT OR Apache-2.0" 或 "MIT AND Apache-2.0"
```

> **陷阱总结**: 许可证陷阱主要与**传递依赖**、**无许可证**、**兼容性**、**版权归属**和**SPDX 语法**相关。
> [来源: [SPDX Specification](https://spdx.github.io/spdx-spec/)]

---

## 六、来源与延伸阅读

| 来源 | 可信度 | 说明 |
| [Rust Standard Library](https://doc.rust-lang.org/std/) | ✅ 一级 | 标准库参考 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | ✅ 一级 | 交互式教程 |
| [This Week in Rust](https://this-week-in-rust.org/) | ✅ 二级 | 社区动态 |

| [Rust Reference](https://doc.rust-lang.org/reference/) | ✅ 一级 | 语言参考 |
|:---|:---:|:---|
| [Choose a License](https://choosealicense.com/) | ✅ 一级 | 许可证选择指南 |
| [SPDX License List](https://spdx.org/licenses/) | ✅ 一级 | 标准许可证标识 |
| [cargo-deny](https://github.com/EmbarkStudios/cargo-deny) | ✅ 一级 | 许可证审计工具 |
| [OSI Licenses](https://opensource.org/licenses) | ✅ 一级 | 开源倡议组织 |
| [Rust License Policy](https://www.rust-lang.org/policies/licenses) | ✅ 一级 | Rust 官方 |

---

## 相关概念文件

- [Toolchain](./01_toolchain.md) — 工具链
- [Security Practices](./19_security_practices.md) — 安全实践
- [Cross Compilation](./17_cross_compilation.md) — 交叉编译

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 10]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成
