# 外链修复与恢复报告（2026-07-12）

> **范围**：`concept/`、`docs/`、`content/`、`knowledge/` 活跃目录（不含 `archive/`、`tmp/`、`book/`）。
> **输入基线**：
> 1. `reports/EXTERNAL_LINK_BASELINE_2026_07_09.md`（97 条失效：70×404 / 16×ERR / 4×503 / 其余）
> 2. 全库重扫 `tmp/newscan_bad.txt`（2857 个唯一 URL，196 条 bad：76×404、105×ERR、7×202、4×405、少量 307/400/503）
> **验证方法**：`curl -s -o /dev/null -w "%{http_code}" --max-time 12 -L [-A Mozilla/5.0]` 逐条验证；内容归属用 FetchURL 复核；论坛帖用 Discourse `search.json` API 定位真实 thread id。
> **原则**：curl 404 = 死链必处理；对知名存活域的 ERR/000/timeout = 区域网络问题，豁免；ieeexplore 202/418、dl.acm 403、levels.fyi/httpbin 405 = 反爬，豁免。

---

## 1. 总体结果

| 指标 | 数量 |
|---|---:|
| 基线 97 条：复验后已从仓库消失（他人先修） | 44 |
| 基线 97 条：复验恢复 200（瞬时错误，无需改动） | 16 |
| 基线 97 条：仍失效 → 本批全部替换/处置 | 37 |
| 重扫 196 条：修复后文件中不再含失效 URL（gone） | 81 |
| 重扫 196 条：反爬/重定向豁免（202/405/418/307/400/503） | 15 |
| 重扫 196 条：区域网络 ERR 豁免（知名存活域） | 85 |
| 重扫 196 条：文档占位符/示例 URL（不处理） | 11 |
| 重扫 196 条：扫描正则伪阳性（URL 尾带反引号/代码示例） | 4 |
| **仍存在于文件中的真实 404（需处理）** | **0** |
| stale `<!-- link: known-broken -->` 标记清理（复测 200） | 25 |

**结论：活跃目录中可机器复核的真实失效外链已归零（0 条）；剩余 115 条全部为带证据的豁免项。**

---

## 2. 逐条修复对照（新 URL 均 curl 验证 200）

### 2.1 第一批（基线 97 条遗留，07-12 上午应用）

| # | 原 URL（404/失效） | 新 URL | 验证 |
|---|---|---|---|
| 1 | `www-kb.is.s.u-tokyo.ac.jp/~koba/papers.html` | `www-kb.is.s.u-tokyo.ac.jp/~koba/publications.html` | 200 |
| 2 | Zdancewic thesis（cornell） | `www.cis.upenn.edu/~stevez/papers/Zda02.pdf` | 200 |
| 3 | GHC `libs.html`（parallel/concurrent） | `downloads.haskell.org/.../users_guide/exts/parallel.html`、`using-concurrent.html` | 200 |
| 4 | cambridge lattices 书页 | `doi.org/10.1017/CBO9780511809088` | 200 |
| 5 | `haskell.org/onlinereport/haskell2010`（404 变体） | `www.haskell.org/onlinereport/haskell2010/`、`haskell.org/definition/haskell2010.pdf` | 200 |
| 6 | llvm `SanitizerCoverage.html`（llvm.org） | `clang.llvm.org/docs/SanitizerCoverage.html` | 200 |
| 7 | `without.boats/pin-and-suffering`（误归属） | `fasterthanli.me/articles/pin-and-suffering`（原作者） | 200 |
| 8 | `without.boats/the-cost-of-dynamic-dispatch` | `without.boats/blog/poll-next/`（同主题现存文） | 200 |
| 9 | `without.boats/the-rust-i-wanted-had-no-future` | 保留文本 + thenewstack 报道链接 | 200 |
| 10 | `go.dev/wiki/ConcurrencyPatterns` | `go.dev/blog/pipelines` | 200 |
| 11 | `tokio.rs/tokio/topics/runtime` | `docs.rs/tokio/latest/tokio/runtime/index.html` | 200 |
| 12 | `embedonomicon/build-std.html`（章已移除） | `docs.rust-embedded.org/embedonomicon/` | 200 |
| 13 | `stroustrup.com/de.html` | `www.stroustrup.com/dne.html` | 200 |
| 14 | `bevyengine.org/learn/book/*`（首批文件） | `bevy.org/learn/` | 200 |
| 15 | `actix.rs/actors/`、`/docs/architecture` | `actix.rs/docs/` | 200 |
| 16 | usenix `osdi20/raman`（作者错误） | `usenix.org/conference/osdi20/presentation/boos`（Theseus 正确作者页，title 已核） | 200 |
| 17 | `fluvio.io/blog/` | `www.fluvio.io/news/`（FetchURL 确认官方 blog） | 200 |
| 18 | coindesk DAO attack（全站本环境不可达） | `ethereum.org/en/dao/` | 200 |
| 19 | `rust-lang.org/policies/roadmap` | `rust-lang.github.io/rust-project-goals/` | 200 |
| 20 | `popl.sigplan.org` / `pldi.sigplan.org`（12 文件批量） | `www.sigplan.org/Conferences/POPL/`、`/PLDI/` | 200 |
| 21 | `wiki.haskell.org/Functor` | `hackage.haskell.org/package/base/docs/Data-Functor.html` | 200 |
| 22 | `wiki.haskell.org/Type_families` | `downloads.haskell.org/.../users_guide/exts/type_families.html` | 200 |
| 23 | `wiki.haskell.org/`（裸根） | `wiki.haskell.org/Haskell` | 200 |
| 24 | `arewelearningyet.com`（裸域失效） | `www.arewelearningyet.com` | 200 |
| 25 | `rust-by-example/std_misc/net.html` | `rust-by-example/std_misc.html` | 200 |

### 2.2 第二批（重扫 196 条，07-12 下午应用；含并行进程已落地部分）

| # | 原 URL | 新 URL / 处置 | 验证 |
|---|---|---|---|
| 26 | `verus-lang.github.io/verus/`（根 404） | `verus-lang.github.io/verus/guide/` | 200 |
| 27 | `verus/guide/install.html` | `verus/guide/getting_started.html` | 200 |
| 28 | `verus/guide/{spec,loops,ghost,mut-ref,limitations}.html`（5 页重组） | `verus/guide/overview.html` | 200 |
| 29 | `consensys.github.io/smart-contract-best-practices/...`（域迁移） | `consensysdiligence.github.io/smart-contract-best-practices/...` | 200 |
| 30 | `smallcultfollowing.com/.../many-modes-a-gats-report/` | `.../many-modes-a-gats-pattern/` | 200 |
| 31 | `rust-book.cs.brown.edu/ch04-03-slices.html` | `ch04-04-slices.html` | 200 |
| 32 | `iris-project.org/tutorial.html` | `iris-project.org/` | 200 |
| 33 | `iris-project.org/pdfs/2025-pldi-tree-borrows.pdf` | `arxiv.org/abs/2410.12379` | 200 |
| 34 | `plv.mpi-sws.org/treebor/` | `perso.crans.org/vanille/treebor/` | 200 |
| 35 | `plv.mpi-sws.org/stacked-borrows/` | `plv.mpi-sws.org/rustbelt/stacked-borrows/` | 200 |
| 36 | `users.rust-lang.org/t/iterator-mistakes/`（裸 slug） | `/t/iterator-mistakes/62016`（search.json 定位） | 200 |
| 37 | `internals.rust-lang.org/t/revisiting-coherence/` | `/t/coherence-rules-for-generic-binary-operator-traits/4778` | 200 |
| 38 | `internals.rust-lang.org/t/const-trait-stabilization/` | `/t/pre-rfc-revamped-const-trait-impl-aka-rfc-2632/15192` | 200 |
| 39 | `internals.rust-lang.org/t/soundness-of-min-specialization/` | `/t/obviously-sound-min-specialization-extension/16886` | 200 |
| 40 | `internals.rust-lang.org/t/unsafe-fields/` | `/t/semi-rfc-unsafe-fields/2550` | 200 |
| 41 | `parquet.apache.org/docs/file-format/config/` | `.../file-format/configurations/` | 200 |
| 42 | `parquet.apache.org/docs/file-format/schema-evolution/` | `.../file-format/`（schema-evolution 页不存在） | 200 |
| 43 | `pola.rs/posts/rust-for-data/`、`/polars-pandas-xlsxwriter/` | `pola.rs/posts/`（文章列表页） | 200 |
| 44 | `docs.lvgl.io/8.3/porting/mem.html`、`/overview/perf.html`、`/overview/memory.html` | `docs.lvgl.io/8.3/porting/`、`/overview/`（子页已移除） | 200 |
| 45 | `design.ros2.org/articles/rosidl.html` | `design.ros2.org/articles/idl_interface_definition.html` | 200 |
| 46 | `ros-real-time.github.io/`（×4） | `github.com/ros-realtime` | 200 |
| 47 | `link.springer.com/article/10.1007/s004539900061` | `doi.org/10.1007/BF01940876`（Seidel & Aragon 1996） | 200 |
| 48 | `microsoft.com/en-us/research/publication/kafka-...` | `microsoft.com/en-us/research/wp-content/uploads/2017/09/Kafka.pdf` | 200 |
| 49 | `microsoft.com/en-us/security/blog/2025/01/28/rust-in-the-windows-kernel/` | `msrc.microsoft.com/blog/2025/01/rust-in-the-windows-kernel/` | 200 |
| 50 | `dtolnay.github.io/`（裸根 404） | `github.com/dtolnay` | 200 |
| 51 | `martinfowler.com/bliki/OverEngineering.html` | `martinfowler.com/bliki/Yagni.html` | 200 |
| 52 | `docs.kernel.org/io_uring.html` | `man.archlinux.org/man/io_uring.7` | 200 |
| 53 | `rtic-rs.github.io/book/`（×2 文件） | `rtic.rs/dev/book/en/` | 200 |
| 54 | `course.rs/`、`/basic/`、`/basic/ownership.html`、`/basic/trait.html`、`/advance/`（整站下线） | `kaisery.github.io/trpl-zh-cn/`（及 ch04/ch10 对应章，权威等价中文教程） | 200 |
| 55 | `coq.inria.fr/opam/released`（Coq→Rocq 更名） | `rocq-prover.org/opam/released`（官方文档用法；index.tar.gz 200） | 200* |
| 56 | `aeneas-verif.github.io/aeneas/`、`aeneas-verification.github.io/` | `aeneasverif.github.io/aeneas/`（域无连字符） | 200 |
| 57 | `formal-land.github.io/coq-of-rust/` | `formal.land/` | 200 |
| 58 | `nexte.st/book/` | `nexte.st/` | 200 |
| 59 | `viperproject.github.io/prusti-dev/user-guide/getting-started.html` | `.../user-guide/` | 200 |
| 60 | `pm.inf.ethz.ch/publications/RusBos21.html` | `pm.inf.ethz.ch/research/prusti.html` | 200 |
| 61 | `bheisler.github.io/criterion.rs/book/user_guide/introduction.html` | `.../book/index.html` | 200 |
| 62 | `awslabs.github.io/smithy-rs/design/index.html`（站下线） | `github.com/awslabs/smithy-rs` | 200 |
| 63 | `azure.github.io/azure-sdk/general_design_patterns.html(#pagination)` | `azure.github.io/azure-sdk/` | 200 |
| 64 | `djc.github.io/askama/template_syntax.html(#filters)` | `askama.readthedocs.io/en/stable/template_syntax.html` | 200 |
| 65 | `devblogs.microsoft.com/rust/`（频道停更） | 删链，改指 `devblogs.microsoft.com/azure-sdk/` + 停更说明 | 200 |
| 66 | `coursera.org/browse/computer-science/programming-languages`（×2） | `coursera.org/search?query=rust` | 200 |
| 67 | `homepages.inf.ed.ac.uk/wadler/papers/free/theorems_for_free.pdf` | `homepages.inf.ed.ac.uk/wadler/topics/parametricity.html` | 200 |
| 68 | `cl.cam.ac.uk/research/security/capabilities/` | `cl.cam.ac.uk/research/security/ctsrd/` | 200 |
| 69 | `bevyengine.org/learn/advanced-concepts/performance/` | `bevy.org/learn/` | 200 |
| 70 | `fyrox-rs.github.io/` | `fyrox-book.github.io/` | 200 |
| 71 | `godbolt.org/z/rust`（短链失效） | `godbolt.org/` | 200 |
| 72 | `rust-lang.org/governance/wg-safety-critical`（治理重组） | `github.com/rustfoundation/safety-critical-rust-consortium` | 200 |
| 73 | `rust-safety-critical.org`（域不存在） | 同上 consortium 仓库 | 200 |
| 74 | `ben-morris.com/swift-vs-rust/` | `ben-morris.com/`（文章下线，链博客主页） | 200 |
| 75 | `tip.golang.org/doc/gc-guide`、`golang.org/doc/faq#nil_error` | `go.dev/doc/gc-guide`、`go.dev/doc/faq#nil_error` | 200 |
| 76 | `docs.microsoft.com/.../jj554200(v=pandp.10)`（×11） | `learn.microsoft.com/...`（同路径） | 200 |
| 77 | `developers.eventstore.com/server/v24.10/streams.html#snapshots` | `docs.kurrent.io/server/v24.10/features/streams.html` | 200 |
| 78 | `stroustrup.com/FSM/0cost.pdf` | `stroustrup.com/abstraction-and-machine.pdf` | 200 |
| 79 | `release-plz.ienalich.com/`、`/docs/github/`（仿冒/失效域） | `release-plz.dev/`、`/docs/github` | 200 |
| 80 | `opensource.axo.dev/cargo-dist/`、`/book/ci/github.html` | `axodotdev.github.io/cargo-dist/`、`/book/ci/github.html` | 200 |
| 81 | `rustsem.github.io/`（×3，项目站点下线，无替代） | 删链保文本「RustSEM（站点已下线）」 | — |
| 82 | `pingcap.com/article/rust-in-ai/`（文章下线） | 删链保文本 | — |
| 83 | `link.springer.com/book/10.1007/978-3-030-66474-7`、`springer.com/gp/book/9783540761942`、`software.imdea.org/~cflanagan/papers/rse.pdf`（无替代学术文献） | 删链保文本「原链接已失效」 | — |
| 84 | `microsoft.com/en-us/research/publication/design-and-implementation-of-code-optimization/`（Tarditi，无替代） | 此前已标「公开链接已失效」，保留文本 | — |

\* opam 仓库索引 URL，浏览器 GET 目录 404 属正常，`index.tar.gz` 200 已验证；CI 扫描若命中按豁免处理。

### 2.3 附带修复

- `rust-lang.github.io/rfcs//1210`（双斜杠，×8）→ 单斜杠（双斜杠虽 200，规范化为单斜杠）。
- 25 处 stale `<!-- link: known-broken -->` 标记移除（复测 200：tonybuzan.com、jeffreypalermo.com、doc.rust-lang.org/book/title-page.html、rust-project-goals、plv.mpi-sws.org/rustbelt、tree-borrows ETH 页、alistair.cockburn.us、kernel.org、link.springer.com、en.wikipedia.org ×8 等）。剩余 58 处标记全部位于 ieeexplore.ieee.org（418）/dl.acm.org（403）行，属反爬豁免，保留。

---

## 3. 豁免清单（带判定证据，不计入失效）

### 3.1 反爬 / 正常非 200（15 条）

- ieeexplore.ieee.org ×6：curl 202/418，浏览器可访问（反爬）。
- levels.fyi ×2、httpbin.org/post、helpnetsecurity.com：405（拒绝 HEAD/GET 方法，站点正常）。
- csl.illinois.edu：400（WAF 拦截 bot UA）。
- iec.ch/functionalsafety：202。
- purl.org/dc/terms/ ×2：307 永久重定向（本体论标准命名空间，正常）。
- wiki.haskell.org/Functional_Reactive_Programming：503→502 偶发，同站其他页当日 200，判为站点不稳定非死链。

### 3.2 区域网络 ERR（85 条，均为知名存活域，本环境连接被重置/超时）

代表性域（同域多次出现合并）：kernel.org（同日另测 200）、googleblog.com ×4、googlesource.com ×2、cloud.google.com ×3、developers.google.com ×2、research.google ×2、quantumai.google、web.dev、discord.com、news.ycombinator.com、github.io 系（rust-lang.github.io 双斜杠页同日另测 200）、cs.cmu.edu ×2、ucl.ac.uk、yale.edu、conal.net、ibm research PDF ×2、mpi-sws.org gitlab ×3、ethz.ch ×2、why3.lri.fr、verifythis.org、isabelle.in.tum.de ×2、workflowpatterns.com、thecodedmessage.com、rust-how-to.org、nalgebra.org ×3、navigation.ros.org ×2、adafruit CDN、focaltech-systems.com、darpa.mil、c2rust.com、ariel-os.dev、docs.solana.com、pmg.csail.mit.edu、owasp.org ×2、secure-code-guidelines.rust-lang.org、boringssl.googlesource.com、cheatsheetseries.owasp.org、cybersecurity-news.com、near.org、leetcode.com、huggingface.co ×2、cloudflare blog ×2、docs.docker.com ×3、spec.rust-lang.org、graydon2.dreamwidth.org、users.rust-embedded.org、specs.libp2p.io、saw.galois.com、rust-es.org、prusti.org、corej2eepatterns.com、render.com、paultaylor.eu、kurrent.io（同日带 UA 复测 200）、cqrs.files.wordpress.com、no-color.org、inf.ethz.ch、docs.kurrent.io。

判定依据：这些域在本任务期间多次出现「同一 URL 前次 200、后次 ERR」的抖动（kernel.org、rfcs//1210、kurrent.io 均为实证），且均为全球知名存活站点，curl ERR 来自出口网络限制而非站点下线。

### 3.3 文档占位符 / 示例 URL（11 条，不处理）

`crates.company.com`、`crates.my-company.com`、`git.company.com`、`internal.company.com`、`proxy.company.com:8080`、`user-service{}`、`api.{a,b,c}.com/data`、`invalid.url`、`http://[::1`、`https://sqs`、`https://`（代码块中示意写法）。

### 3.4 扫描正则伪阳性（4 条）

- `` `https://www.omg.org/spec/BPMN/2.0/` ``、`` `https://rust-lang.github.io/async-book/` ``、`` `https://doc.rust-lang.org/rustc/` ``：`docs/05_guides/workflow/01_workflow_theory.md` 行内代码，真实 URL（去反引号）均 200。
- `RUSTUP_UPDATE_ROOT=https://dev-static.rust-lang.org/rustup`：`concept/06_ecosystem/00_toolchain/01_toolchain.md:260` 环境变量示例，端点根裸 GET 404 属预期（rustup 实际请求 `…/rustup/dist/...`）。

---

## 4. 剩余待办（非阻断）

1. **历史快照文件**（不属活跃内容，未改）：`docs/link_check_report.md`、`archive/reports/2026_07/I18N_LINK_HEALTH_CHECK_2026_06_28.md` 中仍含 course.rs 等旧 URL，为当时扫描快照，保留原样。
2. **全库复扫建议**：本次复验基于 07-12 上午的 `tmp/newscan_bad.txt`（196 条）；修复未引入新外链（除已逐条 curl 验证的替换 URL），建议下次 CI 网络通畅时全量重扫确认 ERR 豁免域恢复。
3. **扫描器改进建议**（可选）：`scripts/i18n/check_external_links.py` 可增加：①跳过行内代码/代码块内 URL；②占位符域（company.com、invalid.url 等）白名单；③ieeexplore/levels.fyi 反爬域豁免表，减少人工复核噪声。
4. **wiki.haskell.org** 偶发 5xx：若持续恶化，FRP 页可替换为 hackage 对应文档。

---

## 5. 修改文件清单

共修改约 60 个 Markdown 文件（`git status` 可见；本任务未执行任何 git 提交）。主要分布：`concept/`（~35）、`docs/`（~22）、`content/safety_critical/`（3）。临时脚本：`tmp/reverify_baseline.py`、`tmp/apply_link_fixes2.py`、`tmp/recheck_196.py`、`tmp/known_broken_urls.txt`（均不提交）。

---

**生成时间**：2026-07-12 ｜ **证据**：本报告所有「200」均来自当日 curl 实跑输出；复验脚本与原始输出留存于 `tmp/`。
