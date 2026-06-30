> **Rust 版本**: 1.96.0+ (Edition 2024)
>
> **状态**: ✅ 已完成
>
> **概念族**: Crate 架构 / azure-sdk-rust
>
> **层级**: L3-L5

---

# azure-sdk-rust 架构解构 {#azure-sdk-rust-架构解构}

> **最后更新**: 2026-06-29
>
> **内容分级**: [归档级]
>
> **分级**: [B]
>
> **Bloom 层级**: L3-L5 (应用/分析/评价)
>
> **知识领域**: 云厂商 SDK、Azure、异步 HTTP 客户端、TokenCredential、Pager/Poller
>
> **对应 Rust 版本**: 1.96.0+ (azure-sdk-rust 稳定版)

---

## 1. 引言：azure-sdk-rust 的生态定位 {#1-引言azure-sdk-rust-的生态定位}

> **[来源: [Azure SDK for Rust](https://github.com/Azure/azure-sdk-for-rust)]**

`azure-sdk-rust` 是微软官方提供的 Rust 语言 Azure SDK，采用与 .NET / Java / Python / Go / JavaScript SDK 统一的设计准则（Azure SDK Guidelines）。它以 `azure_core` 为统一内核，各服务（Blob、Key Vault、Queue 等）分别发布独立 crate，提供类型化的异步客户端、`TokenCredential` 认证抽象、以及 `Pager<T>` / `Poller<T>` 等分页与长运行操作原语。

> [来源: [Azure SDK releases (Rust)](https://azure.github.io/azure-sdk/releases/latest/rust.html)]

与其他云 SDK 相比，`azure-sdk-rust` 的核心取舍是：

| 维度 | 设计选择 | 工程价值 |
|:--|:--|:--|
| **核心抽象** | `azure_core` 统一 HTTP、凭证、分页、重试 | 跨服务 API 风格一致，学习成本低 |
| **crate 组织** | 每服务一个 crate | 按需依赖，避免引入未使用的服务 |
| **认证模型** | `TokenCredential` trait 抽象 | 本地开发、托管身份、服务主体可无缝切换 |
| **异步运行时** | 原生 async/await，默认 Tokio | 与 Rust 生态一致，可插拔运行时 |

> [来源: [docs.rs azure_core](https://docs.rs/azure_core)] · [docs.rs azure_identity](https://docs.rs/azure_identity)] · [docs.rs azure_storage_blob](https://docs.rs/azure_storage_blob)]

---

## 2. 核心 API 与使用模式 {#2-核心-api-与使用模式}

### 2.1 凭证：`TokenCredential` 与 `DeveloperToolsCredential` {#21-凭证tokencredential-与-developertoolscredential}

Azure SDK 将所有认证逻辑抽象为 `TokenCredential` trait，服务客户端接收 `Arc<dyn TokenCredential>` 或具体凭证类型。

```rust
use azure_identity::DeveloperToolsCredential;

let credential = DeveloperToolsCredential::new(None)?;
```

本地开发优先使用 `DeveloperToolsCredential`，它会依次尝试 Azure CLI (`az login`) 与 Azure Developer CLI (`azd auth login`) 获取令牌。生产环境可替换为 `ManagedIdentityCredential`、`ClientSecretCredential` 等，而服务客户端构造代码保持不变。

> [来源: [Azure Identity library for Rust](https://docs.rs/azure_identity/latest/azure_identity/)]

### 2.2 服务客户端：`BlobServiceClient` {#22-服务客户端blobserviceclient}

服务客户端通常采用 `new(url, credential, options)` 构造，并暴露具体操作的构造器方法。

```rust
use azure_identity::DeveloperToolsCredential;
use azure_storage_blob::BlobServiceClient;

let credential = DeveloperToolsCredential::new(None)?;
let service_client = BlobServiceClient::new(
    "https://<account>.blob.core.windows.net/",
    Some(credential),
    None,
)?;
```

> [来源: [Azure Storage Blob client library for Rust](https://docs.rs/azure_storage_blob/latest/azure_storage_blob/)]

### 2.3 分页：统一 `Pager<T>` {#23-分页统一-pagert}

列表类操作返回 `Pager<T>`，通过 `TryStreamExt::try_next()` 按 item 遍历，自动处理 continuation token。

```rust
use futures::TryStreamExt;

let mut pager = service_client.list_containers(None)?;
while let Some(container) = pager.try_next().await? {
    println!("{:?}", container.name);
}
```

这种设计让调用方无需关心分页协议细节，与 AWS SDK 的 `.into_paginator()` 形成对照。

> [来源: [Azure SDK design guidelines - Pagination](https://azure.github.io/azure-sdk/general_design_patterns.html#pagination)]

### 2.4 长运行操作：`Poller<T>` {#24-长运行操作pollert}

对于异步完成的资源创建/删除操作，SDK 返回 `Poller<T>`，可通过 `.await` 直接等待完成，也可手动轮询状态。

```rust
let poller = container_client.create(None).await?;
let response = poller.await?;
```

---

## 3. 类型系统价值 {#3-类型系统价值}

| Rust 类型机制 | 在 azure-sdk-rust 中的体现 |
|:--|:--|
| **Trait 抽象** | `TokenCredential` 用 trait object 统一多种凭证，避免客户端泛型爆炸 |
| **泛型分页** | `Pager<T, F>` 对 item 类型 `T` 与 page 格式 `F` 参数化，编译期保证类型安全 |
| **Builder 模式** | 每个操作通过 `ClientOptions` / request builder 逐步构造，必填参数由类型系统保证 |
| `Response<T, F>` | 原始 HTTP 响应被包装为强类型响应，`.into_model()` 将 body 反序列化为业务模型 |
| **错误分离** | `azure_core::Error` 统一网络、认证、服务错误；服务级错误通过生成的具体类型暴露 |

> [来源: [Azure SDK Rust API Guidelines](https://azure.github.io/azure-sdk/rust_introduction.html)]

### 3.1 与 AWS SDK 的类型对比 {#31-与-aws-sdk-的类型对比}

| 设计点 | aws-sdk-rust | azure-sdk-rust |
|:--|:--|:--|
| 认证抽象 | `SharedCredentialsBundle` + `ProvideCredentials` | `TokenCredential` trait |
| 分页 | 各服务 `.into_paginator().items()` | 统一 `Pager<T>` / `try_next()` |
| 长运行 | `Poller`（部分服务） | 统一 `Poller<T>` / `.await` |
| 请求构造 | Smithy 生成的 builder | 服务客户端方法 + `ClientOptions` builder |
| 运行时 | 默认 Tokio | 默认 Tokio，可 `set_async_runtime` 替换 |

---

## 4. 反例边界与常见陷阱 {#4-反例边界与常见陷阱}

### 4.1 不要直接传递字符串 URL 而不处理生命周期 {#41-不要直接传递字符串-url-而不处理生命周期}

`BlobServiceClient::new` 接受 `&str`，但内部会 clone；调用方需确保 URL 格式正确。

### 4.2 不要混淆 `RequestContent` 与原始字节 {#42-不要混淆-requestcontent-与原始字节}

上传操作要求 `RequestContent` 包装，`Vec<u8>` 不会自动转换；错误类型会导致编译失败。

### 4.3 注意 beta → stable 的 API 变动 {#43-注意-beta-stable-的-api-变动}

`azure-sdk-rust` 在 2026 年 5 月宣布 GA，此前大量示例使用旧的 `DefaultAzureCredential`（已移除）。当前应使用 `DeveloperToolsCredential` / `ManagedIdentityCredential`。

> [来源: [From beta to stable: Azure SDK for Rust GA](https://devblogs.microsoft.com/azure-sdk/from-beta-to-stable-announcing-the-azure-sdk-for-rust-ga/)]

### 4.4 RBAC 权限不足导致运行时认证成功但操作失败 {#44-rbac-权限不足导致运行时认证成功但操作失败}

凭证获取成功不代表有权限；需为身份分配 `Storage Blob Data Reader` / `Contributor` 等角色。

---

## 5. 权威来源分层 {#5-权威来源分层}

### P0（官方规范 / 官方文档） {#p0官方规范-官方文档}

- [Azure SDK for Rust GitHub](https://github.com/Azure/azure-sdk-for-rust)
- [Azure SDK releases (Rust)](https://azure.github.io/azure-sdk/releases/latest/rust.html)
- [docs.rs azure_core](https://docs.rs/azure_core)
- [docs.rs azure_identity](https://docs.rs/azure_identity)
- [docs.rs azure_storage_blob](https://docs.rs/azure_storage_blob)
- [Azure SDK Rust API Guidelines](https://azure.github.io/azure-sdk/rust_introduction.html)
- [Azure Identity library docs](https://docs.rs/azure_identity/latest/azure_identity/)

### P1（生态实现 / 设计规范） {#p1生态实现-设计规范}

- [TypeSpec / typespec-client-core](https://github.com/microsoft/typespec)
- [Azure REST API docs](https://learn.microsoft.com/rest/api/azure/)
- [Azure SDK general design patterns](https://azure.github.io/azure-sdk/general_design_patterns.html)

### P2（案例 / 最佳实践） {#p2案例-最佳实践}

- [Azure SDK for Rust samples](https://github.com/Azure/azure-sdk-for-rust/tree/main/sdk/storage/azure_storage_blob/examples)
- [Microsoft Learn - Azure for Rust developers](https://learn.microsoft.com/azure/developer/rust/)

---

## 6. 相关概念与索引 {#6-相关概念与索引}

- 上游依赖：`Tokio` / `async/await` · `http` / `hyper` · `url`
- 同层对照：[37_aws_sdk_architecture.md](37_aws_sdk_architecture.md)
- 下游应用：云原生服务、无状态微服务、对象存储客户端
- 代码示例：[crates/c10_networks/examples/azure_blob_list_containers.rs](../../../../crates/c10_networks/examples/azure_blob_list_containers.rs)

---

> **权威来源**: [Azure SDK for Rust](https://github.com/Azure/azure-sdk-for-rust) | [Azure Docs](https://learn.microsoft.com/azure/) | [docs.rs](https://docs.rs/) | [crates.io](https://crates.io/)

> **来源: [Microsoft Azure SDK for Rust](https://github.com/Azure/azure-sdk-for-rust)**

> **来源: [Azure Documentation](https://learn.microsoft.com/azure/)**

> **来源: [IEEE Standards](https://standards.ieee.org/)**

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**