# Rust安全关键系统快速参考卡片

## 一页纸速查

```
╔═══════════════════════════════════════════════════════════════════════════════╗
║                        RUST SAFETY-CRITICAL QUICK REF                        ║
╚═══════════════════════════════════════════════════════════════════════════════╝

┌─────────────────────────────────────────────────────────────────────────────┐
│  SAFETY LEVELS                                                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  QM      →  Safe Rust + clippy + tests                                      │
│  ASIL A  →  Safe Rust + audit deps + coverage > 80%                         │
│  ASIL B  →  Safe Rust + miri + kani + coverage > 90%                        │
│  ASIL C  →  Mostly Safe + isolated unsafe + Ferrocene                       │
│  ASIL D  →  Certified toolchain + formal methods + 100% coverage            │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  UNSAFE CODE CHECKLIST                                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ☐ Is the unsafe block as small as possible?                                │
│  ☐ Are all invariants documented?                                           │
│  ☐ Is there a safe wrapper?                                                 │
│  ☐ Are inputs validated before unsafe?                                      │
│  ☐ Is miri clean for this code?                                             │
│  ☐ Is there a # Safety comment?                                             │
│  ☐ Has this been code-reviewed?                                             │
│  ☐ Is there a fuzz test?                                                    │
│                                                                              │
│  Example:                                                                    │
│  /// # Safety                                                                │
│  /// ptr must be valid and aligned for T                                     │
│  unsafe fn read_unchecked<T>(ptr: *const T) -> T {                          │
│      ptr.read()                                                              │
│  }                                                                           │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  FFI BEST PRACTICES                                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  1. Use safer_ffi or cxx for automatic bindings                             │
│  2. Validate all C inputs at boundary                                       │
│  3. Document memory ownership in comments                                   │
│  4. Use CString for C strings (check for null bytes)                        │
│  5. Box::into_raw / Box::from_raw pairs must match                          │
│                                                                              │
│  Pattern:                                                                    │
│  pub struct SafeWrapper { inner: *mut RawType }                              │
│  impl Drop for SafeWrapper {                                                 │
│      fn drop(&mut self) { unsafe { free_raw(self.inner) } }                  │
│  }                                                                           │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  TESTING PYRAMID                                                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│                    ┌─────────┐                                               │
│                    │  Kani   │  Formal verification (critical functions)     │
│                    │  proofs │                                               │
│                   ┌┴─────────┴┐                                              │
│                   │  Miri tests │  UB detection (unsafe code)                 │
│                  ┌┴─────────────┴┐                                             │
│                  │ Property tests │  proptest (state machines)                │
│                 ┌┴────────────────┴┐                                           │
│                 │   Unit tests      │  Standard cargo test                     │
│                ┌┴───────────────────┴┐                                         │
│                │  Integration tests  │  Full component testing                  │
│               ┌┴─────────────────────┴┐                                       │
│               │   Hardware-in-loop    │  Target testing                          │
│               └───────────────────────┘                                       │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  DEPENDENCY AUDIT                                                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Daily:   cargo audit                                                        │
│  Weekly:  cargo outdated                                                     │
│  Monthly: Full dependency review                                             │
│                                                                              │
│  Red flags:                                                                  │
│  • No updates in 1+ years                                                    │
│  • Single maintainer                                                         │
│  • Unsafe code without audit                                                 │
│  • Transitive dependencies from unknown sources                              │
│                                                                              │
│  Cargo.toml:                                                                 │
│  [dependencies]                                                              │
│  trusted-crate = { version = "1.0", registry = "private" }                  │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  CI/CD CHECKLIST                                                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Build:   cargo build --release                                              │
│  Lint:    cargo clippy -- -D warnings                                        │
│  Format:  cargo fmt --check                                                  │
│  Test:    cargo test                                                         │
│  Doc:     cargo doc --no-deps                                                │
│  Audit:   cargo audit                                                        │
│  Miri:    cargo miri test (for unsafe code)                                  │
│  Kani:    cargo kani (for critical functions)                                │
│  Coverage: cargo tarpaulin --fail-under 90                                   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  CERTIFICATION STANDARDS                                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────┬─────────────┬─────────────┬─────────────────┐               │
│  │ Automotive  │ Industrial  │ Aerospace   │ Medical         │               │
│  ├─────────────┼─────────────┼─────────────┼─────────────────┤               │
│  │ ISO 26262   │ IEC 61508   │ DO-178C     │ IEC 62304       │               │
│  │ ASIL D      │ SIL 4       │ DAL A       │ Class C         │               │
│  │ Ferrocene   │ Ferrocene   │ AdaCore     │ Ferrocene       │               │
│  └─────────────┴─────────────┴─────────────┴─────────────────┘               │
│                                                                              │
│  Common requirements:                                                        │
│  • Requirements traceability                                                 │
│  • 100% statement coverage (MC/DC for highest levels)                        │
│  • Tool qualification (TQL-1)                                                │
│  • Independence of verification                                              │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  COMMON PATTERNS                                                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  State Machine:                                                              │
│  enum State { Init, Running, Error }                                         │
│  impl StateMachine {                                                         │
│      fn transition(&mut self, event: Event) -> Result<(), Error> {           │
│          match (self.state, event) {                                         │
│              (State::Init, Event::Start) => { ... }                          │
│              _ => Err(Error::InvalidTransition),                             │
│          }                                                                   │
│      }                                                                       │
│  }                                                                           │
│                                                                              │
│  Type State Pattern:                                                         │
│  struct Uninitialized; struct Initialized;                                   │
│  struct Device<State = Uninitialized> { _state: PhantomData<State> }         │
│  impl Device<Uninitialized> { fn init(self) -> Device<Initialized> { ... } } │
│                                                                              │
│  Error Handling:                                                             │
│  type Result<T> = std::result::Result<T, SafetyError>;                       │
│  enum SafetyError { Hardware, Software, Configuration }                      │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  EMERGENCY CONTACTS                                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Security:   security@rust-lang.org                                          │
│  Ferrocene:  support@ferrous-systems.com                                     │
│  Community:  users.rust-lang.org                                             │
│  Embedded:   matrix.to/#/#rust-embedded:matrix.org                          │
│                                                                              │
│  Tools:                                                                      │
│  Miri:       github.com/rust-lang/miri                                       │
│  Kani:       github.com/model-checking/kani                                  │
│  Verus:      github.com/verus-lang/verus                                     │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  KEY METRICS                                                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Code Quality:                                                               │
│  • unsafe ratio: < 5% of total LOC                                           │
│  • clippy warnings: 0                                                        │
│  • test coverage: > 90% (ASIL B+)                                            │
│  • miri clean: yes                                                           │
│                                                                              │
│  Safety Metrics:                                                             │
│  • panics: documented, expected only                                         │
│  • unwrap() count: < 1 per 1000 LOC                                          │
│  • unsafe blocks: < 10 per module                                            │
│  • CVE history: tracked                                                      │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘

Print this page and keep it at your desk!
Last updated: 2026-03-18
Version: 1.0
```

---

## 速查命令

### 日常开发

```bash
# 构建和测试
cargo build --release
cargo test
cargo clippy -- -D warnings

# 安全审计
cargo audit
cargo outdated

# 高级验证
cargo miri test
cargo kani
cargo tarpaulin

# 格式化
cargo fmt
cargo doc --no-deps
```

### 依赖管理

```bash
# 更新依赖
cargo update

# 查看依赖树
cargo tree
cargo tree -d  # 查看重复依赖

# 检查许可证
cargo license

# 漏洞扫描
cargo audit
```

### 嵌入式

```bash
# 添加目标
rustup target add thumbv7em-none-eabihf

# 交叉编译
cargo build --target thumbv7em-none-eabihf

# 烧录
cargo flash --chip STM32F407VG

# 调试
cargo embed
```

---

## 关键资源链接

| 资源 | URL |
|------|-----|
| Rust Book | <https://doc.rust-lang.org/book/> |
| Rust Reference | <https://doc.rust-lang.org/reference/> |
| Embedded Book | <https://docs.rust-embedded.org/book/> |
| High Assurance Rust | <https://highassurance.rs> |
| Ferrocene | <https://ferrocene.dev> |
| Rust Safety WG | <https://rust-lang.org/governance> |

---

将此卡片打印并放在工作台上，随时查阅！
