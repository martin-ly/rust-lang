# 测验：安全与测试生态（L6）

> **EN**: Security and Testing Ecosystem Quiz
> **Summary**: L6 standalone quiz on the Rust security and testing ecosystem: Kerckhoffs's principle and crypto primitives, cargo vet supply-chain auditing, and the testing pyramid with property testing, fuzzing, and Miri.
> **受众**: [进阶] / [专家]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` L6 生态层独立测验。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**: [安全实践](../07_security_and_cryptography/01_security_practices.md) · [安全与密码学](../07_security_and_cryptography/02_security_cryptography.md) · [cargo vet 供应链审计](../07_security_and_cryptography/03_cargo_vet_supply_chain.md) · [测试策略](../09_testing_and_quality/01_testing_strategies.md)
>
> **前置概念**:
> [安全实践](../07_security_and_cryptography/01_security_practices.md) ·
> [安全与密码学](../07_security_and_cryptography/02_security_cryptography.md) ·
> [cargo vet 供应链审计](../07_security_and_cryptography/03_cargo_vet_supply_chain.md) ·
> [测试策略](../09_testing_and_quality/01_testing_strategies.md) ·
> [安全边界对比](../../05_comparative/03_domain_comparisons/01_safety_boundaries.md)

---

> **Bloom 层级**: L2-L4
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题 + 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`）的 .md 落地形态组织，不引入 TOML 插件）
> **定位**: 验证学习者对 L6 安全/密码学与测试质量子领域的掌握（密码学原则、供应链审计、分层测试）。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、密码学原则与原语

### Q1. 🟢【单选】Kerckhoffs 原则（1883）主张密码系统的安全性应依赖于？

- A. 算法实现的保密性
- B. 密钥的保密性，即使攻击者完全了解算法细节系统仍应安全
- C. 代码不开源
- D. 频繁更换加密算法

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：按 [安全与密码学](../07_security_and_cryptography/02_security_cryptography.md) §1.1，Kerckhoffs 原则指"密码系统的安全性不应依赖于算法的保密性，而应完全依赖于**密钥的保密性**"——即使攻击者完全了解算法实现细节，系统仍然应该是安全的。这是现代密码学的基石；A/C 是"security by obscurity"反模式；D 与原则无关。

</details>

---

### Q2. 🟢 为 TLS 类场景选择对称加密原语。按权威页的原语分类，下列哪组属于认证加密（AEAD）候选？

| 选项 | 判断 |
|:---|:---|
| A | AES-GCM 与 ChaCha20-Poly1305 |
| B | 裸 AES-ECB 与 MD5 |
| C | Ed25519 与 X25519 |
| D | SHA-256 与 HMAC 单独使用即等价 AEAD |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：A。

**解析**：[安全与密码学](../07_security_and_cryptography/02_security_cryptography.md) §三「对称加密」的两大主角正是 AES-GCM（§3.1）与 ChaCha20-Poly1305（§3.2），均为带认证的加密（AEAD）。B 中 ECB 模式与 MD5 均已不安全；C 是非对称原语（Ed25519 签名、X25519 密钥交换，§四）；D 中哈希/MAC 不提供加密。

</details>

---

### Q3. 🟡【单选】在 Rust 安全实践中，"不安全边界的管理"指的是？

- A. 删除所有 `unsafe` 代码
- B. 把 `unsafe` 收敛在最小边界内、用安全抽象封装并记录契约，辅以审计工具链
- C. 用 `#[allow(unsafe_code)]` 全局放行
- D. 只在 release 构建中启用安全检查

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：[安全实践](../07_security_and_cryptography/01_security_practices.md) §1.2「不安全边界的管理」：Rust 的安全基础（§1.1）不排斥 `unsafe`，而是要求把不安全操作收敛在可审计的最小边界、以安全 API 封装、明确不变量契约，并配合 §2.3 的审计工具链。A 不现实（标准库与 FFI 依赖 unsafe）；C/D 与安全工程实践相反。

</details>

---

### Q4. 🟡 签名与密钥交换场景选型：需要"数字签名"与"密钥交换"各一个原语。按权威页 §四，正确配对是？

| 选项 | 判断 |
|:---|:---|
| A | 签名 Ed25519；密钥交换 X25519 |
| B | 签名 AES-GCM；密钥交换 ChaCha20 |
| C | 签名 X25519；密钥交换 Ed25519（两者互换） |
| D | 两者都用 SHA-256 即可 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：A。

**解析**：[安全与密码学](../07_security_and_cryptography/02_security_cryptography.md) §四「非对称加密与数字签名」：§4.1 ECC 与 Ed25519（数字签名），§4.2 X25519（密钥交换）。C 把二者职责颠倒（Ed25519 用于签名、X25519 用于 ECDH 密钥交换，不可互换）；B/D 用对称/哈希原语承担非对称职能，类别错误。

</details>

---

## 二、供应链审计：cargo vet 与 cargo audit

### Q5. 🟡【多选】cargo vet 的全部状态存放在仓库 `supply-chain/` 目录的三个文件中，包括？（选出所有正确项）

- A. `config.toml`：审计策略（policy / imports / exemptions）
- B. `audits.toml`：本仓库完成的审计记录（谁、按什么标准、审了哪个版本或 delta）
- C. `imports.lock`：导入的外部审计集快照，锁定到具体条目保证可重现
- D. `vet-report.json`：每次 CI 自动生成的审计报告，需手工提交

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：按 [cargo vet 供应链审计](../07_security_and_cryptography/03_cargo_vet_supply_chain.md) §2.1，三个文件全部提交：`config.toml`（审计策略，评审重点）、`audits.toml`（审计记录，持续追加）、`imports.lock`（外部审计集快照，由 `cargo vet` 维护）。D 中文件不存在于该模型中。

</details>

---

### Q6. 🟡【判断】cargo vet 内置的 `safe-to-run` 标准保证代码不会引入严重安全漏洞，可直接进入生产部署。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：按 §2.2 内置审计标准（criteria）：`safe-to-deploy` 才是"代码不会引入严重安全漏洞（内存安全 UB、恶意行为、不安全的 crypto 误用等），可进入生产"；`safe-to-run` 仅表示"代码可以执行（构建/测试工具、开发依赖），不做部署级安全保证"。二者级别不可混淆。

</details>

---

### Q7. 🔴【单选】cargo vet 与 cargo audit 在供应链安全中的分工是？

- A. 两者功能完全重复，任选其一即可
- B. cargo vet 管"信任"（人工审计与标准、导入公共审计集、豁免收敛）；cargo audit 管"已知漏洞"（跟踪安全公告数据库）
- C. cargo audit 负责人工代码审计，cargo vet 负责漏洞数据库
- D. cargo vet 只在 nightly 工具链可用

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：[cargo vet 供应链审计](../07_security_and_cryptography/03_cargo_vet_supply_chain.md) §三标题即"cargo audit：漏洞跟踪的另一条腿"——cargo vet 建立"谁审过、按什么标准"的信任链（含导入 Mozilla 等公共审计集与 exemptions 收敛机制），cargo audit 对照安全公告数据库报告已知漏洞，二者互补。本项目质量门 5（`cargo vet --locked`）与门 4（`cargo audit --no-fetch`）正是这一分工的实例（§四）。

</details>

---

### Q8. 🔴 某仓库新增第三方依赖后 `cargo vet --locked` 失败。按权威页模型，合规的收敛路径是？

| 选项 | 判断 |
|:---|:---|
| A | 直接从 CI 删除 vet 质量门 |
| B | 在 `audits.toml` 追加真实审计记录，或导入可信外部审计集，或对确有理由的依赖在 `config.toml` 加 `exemptions` 并评审 |
| C | 把依赖版本锁死永不升级即可通过 |
| D | 将 `supply-chain/` 目录加入 `.gitignore` |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：cargo vet 的工作模型（§二）给出三条合规路径：自己完成审计并记录到 `audits.toml`、通过 `imports` 信任并导入外部审计集（锁定进 `imports.lock`）、或在 `config.toml` 声明 `exemptions`（豁免需评审并逐步收敛，§2.4）。A/D 是绕过治理而非收敛；C 不解决"未审计"状态且违背安全更新原则。

</details>

---

## 三、分层测试策略

### Q9. 🔴【多选】按测试策略权威页，Rust 测试生态中"编译期即测试"之外的动态验证手段包括？（选出所有正确项）

- A. 内置测试框架（单元/集成测试）
- B. 属性测试（proptest）：对随机生成输入断言不变量
- C. 模糊测试（fuzzing）：面向解析器等输入边界的崩溃挖掘
- D. Miri：解释执行检测未定义行为（UB）

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C、D**

**解析**：[测试策略](../09_testing_and_quality/01_testing_strategies.md) §1.3 提出"编译期即测试"（类型系统排除整类错误），§二「技术细节」给出动态手段全景：内置测试框架（§2.1）、属性测试与模糊测试（§2.2，proptest 对随机输入断言属性）、Miri（§2.3，未定义行为检测）。四者构成从类型保证到运行时验证的完整谱系，对应 §三的分层测试策略。

</details>

---

### Q10. 🟡【判断】Rust 的测试金字塔映射主张：由于类型系统在编译期排除整类错误，E2E 测试应成为测试投入的主体。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：测试金字塔（[测试策略](../09_testing_and_quality/01_testing_strategies.md) §1.2）在任何语言中都主张底层快测试为主、E2E 少量——E2E 慢且脆。Rust 的特殊之处在于"编译期即测试"（§1.3）把一部分原本需要运行时测试兜底的责任前移到类型系统，使金字塔底部更厚，而非反转金字塔。

</details>

---

## 四、属性测试、模糊测试与基准（W3-b 扩展）

### Q11. 🟢【单选】`proptest` 相对手写示例测试（example-based testing）的核心增益是？

- A. 完全替代单元测试，不再需要任何手写用例
- B. 由策略（strategy）自动生成大量输入验证性质（property），失败时自动收缩（shrinking）到最小反例
- C. 在编译期证明程序正确，无需运行
- D. 只适用于 `#[cfg(test)]` 之外的基准测试

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：按 [测试生态](../09_testing_and_quality/03_testing.md)：property-based testing 用 `proptest!` 声明输入策略与待验证性质，框架生成数百个随机输入执行断言；失败时 shrinking 自动把反例收缩到最小可复现形式。A 错——性质测试与示例测试互补（边界用例仍需手写）；C 错——proptest 是动态验证，编译期证明是 Verus/Kani 等形式化工具的领域；D 定位错误。

</details>

---

### Q12. 🟡 以下 `proptest` 用例验证的性质，哪条表述准确？

```rust,ignore
proptest! {
    #[test]
    fn reverse_twice_is_identity(v: Vec<i32>) {
        let mut r = v.clone();
        r.reverse();
        r.reverse();
        prop_assert_eq!(r, v);
    }
}
```

| 选项 | 判断 |
|:---|:---|
| A | 验证 `reverse` 对所有 `Vec<i32>` 满足对合性（involution）：两次反转等于恒等 |
| B | 验证 `reverse` 的时间复杂度为 O(n) |
| C | 验证 `Vec` 不会溢出 |
| D | 只测试了空向量一个用例 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：A。

**解析**：策略 `v: Vec<i32>` 让 proptest 生成任意长度/内容的向量，断言 `reverse(reverse(v)) == v`——即反转操作的对合性质，覆盖空向量、单元素、重复元素等大量用例（D 错）。性质测试验证的是**逻辑性质**而非性能（B 错，性能属 Criterion 基准的领域）或资源约束（C 错）。

</details>

---

### Q13. 🟡【判断】Criterion.rs 的基准结果以多样本测量加置信区间呈现，并支持基线（baseline）存储用于 CI 中的自动回归检测。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：按 [基准测试](../09_testing_and_quality/04_benchmarking.md)：Criterion.rs 做统计化基准——多样本测量、置信区间、参数化与吞吐基准、基线存储与自动回归检测；并强调测量卫生（warm-up、噪声隔离、分配器影响）是优化前的必要前提。这与 `#[bench]`（nightly 内置、单点测量）形成对比。

</details>

---

### Q14. 🔴【多选】按 [测试生态](../09_testing_and_quality/03_testing.md) 的动态验证谱系，下列手段与定位匹配正确的有？（选出所有正确项）

- A. `cargo-fuzz`（libFuzzer 系）：以覆盖率引导的随机输入探索解析器/解码器的 panic 与 UB 面
- B. `proptest`：验证业务性质在自动生成输入空间上成立
- C. `loom`：穷举并发交错（interleaving）验证无锁代码的内存序正确性
- D. `miri`：作为主力性能基准工具使用

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：模糊测试（cargo-fuzz）面向解析/解码类攻击面做覆盖率引导探索（A）；proptest 验证性质（B）；loom 通过穷举线程交错暴露无锁代码在弱内存序下的缺陷（C）。D 错：miri 是 Rust 的解释器，用于检测 unsafe 代码的未定义行为（UB），不是性能工具——基准属于 Criterion 的定位。

</details>

---

### Q15. 🔴 某库收到安全 issue："JSON 解析器在特定嵌套深度下栈溢出"。按测试与安全实践，哪条收敛路径最完整？

| 选项 | 路径 |
|:---|:---|
| A | 只修复该用例并关闭 issue |
| B | 复现用例 ⟹ 修复 ⟹ 回归测试固化；再用 cargo-fuzz 对解析面做持续模糊测试，并把解析器纳入 proptest 性质测试（如深度限制/往返序列化） |
| C | 改用 unsafe 手写解析器提升鲁棒性 |
| D | 在文档声明"深层嵌套不支持"即可，无需代码改动 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：安全 issue 的完整收敛是"修复 + 防回归 + 攻击面持续探索"：回归测试固化该用例，cargo-fuzz 对解析面做覆盖率引导的模糊测试（解析器是模糊测试的头号目标），proptest 补充往返/深度等性质。A 治标；C 方向相反——unsafe 扩大 UB 面；D 把缺陷转嫁为文档约定，不符合 [安全实践](../07_security_and_cryptography/01_security_practices.md) 的纵深防御口径。

</details>

---

> **变更记录**: 2026-07-12 新建（W3-b：L6 安全/测试 quiz，10 题：单选 3 / 代码阅读 3 / 多选 2 / 判断 2；难度 🟢2 / 🟡5 / 🔴3）；2026-07-13 扩展至 15 题（+5 题「属性测试、模糊测试与基准」：proptest 性质与收缩、Criterion 统计基准、fuzz/loom/miri 定位、安全 issue 收敛；难度 🟢3 / 🟡7 / 🔴5）。
