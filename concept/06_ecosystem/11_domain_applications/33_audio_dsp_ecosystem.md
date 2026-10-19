# Rust 音频与 DSP 生态（canonical 缺口闭环页）

> **EN**: Rust Audio & DSP Ecosystem (canonical gap-closure page)
> **Bloom 层级**: L3-L5
> **Summary**: crates.io `multimedia` 分类（2,320 crates）中音频子域的 canonical 页：cpal 0.18.2 设备 I/O 底座、symphonia 0.6.1 纯 Rust 解码引擎、rodio 0.23.0 播放组合层（依赖实拆证明其新旧解码器并存）、rustfft 6.4.1/realfft 3.5.0 FFT 计算层、rubato 5.0.1 重采样、kira 0.12.5 游戏音频引擎，附 dasp 停更但组件存活的判读陷阱与 lofty vs id3 元数据层裁决。本页补齐 W9 缺口扫描登记的「2 页顺带提及、0 专页」缺口（2026-10-19），与 32 计算机视觉页同构。
> **受众**: [入门→进阶]
> **内容分级**: [专题级]
> **定位**: W9 建页队列③（最后一项）——全库仅 01_application_domains 与 05_game_development 顺带列出 rodio/cpal/symphonia，无专页；本页为闭环裁决产物。
> **版本事实基线**: crates.io API 2026-10-19 实查（含子代理批量取证 w9_crates.json 38 锚点）；rustc 1.99.1。
> **前置概念**: [游戏开发与音频集成](05_game_development.md) · [并行算法](25_parallel_algorithms.md) · [Rust vs Python：科学计算与音频栈对比（L5）](../../05_comparative/02_managed_languages/02_rust_vs_python.md) · [计算机视觉生态（信号处理同宗）](32_computer_vision_ecosystem.md)
> **权威来源**: [rodio docs.rs](https://docs.rs/rodio/) · [symphonia docs.rs](https://docs.rs/symphonia/) · [cpal docs.rs](https://docs.rs/cpal/) · [crates.io multimedia 分类](https://crates.io/categories/multimedia) · [Rustonomicon — FFI（cpal 后端 WASAPI/CoreAudio/ALSA/JACK 系统 API 绑定的 unsafe 官方口径）](https://doc.rust-lang.org/nomicon/ffi.html)（P0，2026-10-20 核验）

---

## 一、版图与实查锚点（crates.io 2026-10-19）

| 层 | crate | 版本（实查） | 累计下载 | 近期下载 | 活跃度判读 |
|:---|:---|:---|---:|---:|:---|
| 设备 I/O | **cpal** | **0.18.2**（2026-08-16） | 2,492 万 | 859 万 | 高（全栈唯一设备抽象底座） |
| 纯 Rust 解码 | **symphonia** | **0.6.1**（2026-08-13） | 1,772 万 | 902 万 | 高（近期/累计比≈51%，采用加速中） |
| 播放/混音 | **rodio** | **0.23.0**（2026-10-11） | 1,290 万 | 359 万 | 高 |
| 游戏音频引擎 | **kira** | **0.12.5**（2026-09-26） | 103 万 | 20.9 万 | 活跃（bevy_kira_audio 0.27.1 挂钩 Bevy） |
| FFT | **rustfft / realfft** | **6.4.1 / 3.5.0** | 3,266 万 / 1,870 万 | 993 万 / 507 万 | 一线（音频 DSP 计算事实标准） |
| 重采样 | **rubato** | **5.0.1**（2026-10-01） | 1,349 万 | 538 万 | 高 |
| 元数据 | lofty / id3 | 0.25.4 / 1.17.2 | 126 万 / 1,281 万 | 50 万 / 173 万 | 双活（覆盖面裁决见 §三） |
| MIDI | midir | 0.11.1（2026-10-10） | 91 万 | 31 万 | 稳定 |
| 音乐 DSP | augurs | 0.10.2（2026-02-24） | 8.1 万 | 2.1 万 | 活跃长尾 |
| 遗留框架 | **dasp** | 0.11.0（**2020-05-29 停更**） | 535 万 | 109 万 | 停更但组件存活（陷阱见 §四） |

分类口径实查：音频在 crates.io 没有独立 `audio` 分类，归 `multimedia`（2,320 crates，与图像/视频同分类）——检索音频生态必须按 crate 名而非分类，这是本域建页先验的第一条口径修正。

## 二、管线分层：rodio 0.23 的依赖实拆给出生态真实断层线

对 rodio 0.23.0 的 crates.io 依赖清单实拆：normal 依赖含 `cpal`、`symphonia`、`hound`、`claxon`、`lewton`、`minimp3_fixed`、`dasp_sample`、`rtrb`、`crossbeam-channel`——一个 crate 同时挂着**两代解码栈**：

1. **新栈 = symphonia**：纯 Rust、多格式（MP3/FLAC/AAC/OGG/WAV…）、无 C 依赖，是当前默认答案；
2. **旧栈 = 单格式专用解码器并存**（hound WAV / claxon FLAC / lewton Vorbis / minimp3_fixed MP3）——它们多数停更多年，rodio 保留是向后兼容，不是推荐路径；
3. 设备层只有一条路：**cpal** 是全库唯一被广泛维护的设备 I/O 抽象（WASAPI/CoreAudio/ALSA/JACK 多后端），rodio/kira 都站在它上面。

分层选型：解码 symphonia → 混音/空间化 rodio（通用应用）或 kira（游戏实时音频：缓冲池、效果链、Bevy 集成）→ DSP 计算 rustfft/realfft（FFT 家族，近期 1,500 万/季）+ rubato（重采样）→ 元数据 lofty/id3 → MIDI midir。

## 三、裁决

- **默认栈 = cpal + symphonia + rodio**：三层各司其职，纯 Rust、无系统音频 SDK 依赖（设备后端除外）。
- **游戏音频选 kira 而非 rodio**：rodio 是「播文件」模型（Sink +  append），kira 是「运行时混音台」模型（Bus/池/实时参数）——bevy_kira_audio 0.27.1 是 Bevy 侧事实接线（与[游戏开发页](05_game_development.md)的 0.20.0 锚一致）。
- **音频 DSP 与视觉 DSP 同宗**：rustfft/realfft 的消费面横跨音频与图像（滤波、卷积、频谱），与 [32 计算机视觉页](32_computer_vision_ecosystem.md)的 fast_image_resize 家族共享「数据并行核」模式——选型判读可互参。
- **元数据层选 lofty**：覆盖 MP3/MP4/M4A/OGG/FLAC/APE 等全格式标签族；id3 1.17.2 只做 ID3v2——下载量更高只说明历史存量，新项目的覆盖面裁决明确倾向 lofty。

## 四、判读陷阱

1. **dasp 陷阱（停更≠死亡）**：dasp 全家桶 2020-05-29 后无发版，核心 DSP 框架应视为遗留；但其组件 `dasp_sample` 仍是 rodio 的正常依赖，近期 109 万下载证明「停更框架的活组件」在 Rust 音频层普遍存在——判读活跃度必须落到具体 crate，不能按家族一票判定。
2. **空 crate 撞名**：`microphone` 0.0.1 全库仅 28 次下载（占位空壳）；取证中 `trill-rs`、`catapult-dsp` 直接 404 不存在——按主题词检索游戏/音频 crate 时命中低下载量同名者是最常见取证事故，必查 recent_downloads 与 updated_at。
3. **`minimp3_fixed` 的许可证阴影**：minimp3 系 C 移植路线的 MP3 解码长期受 MP3 专利史牵连（2017 起多数基础专利已到期，但合规审查敏感场景仍应选 symphonia 纯 Rust 路线）——旧教程「rodio 用 minimp3 解 MP3」对 0.23 已不是主路径。

## 五、边界裁决

- 游戏内音频集成语义归 [05_game_development](05_game_development.md) 与 15 引擎内部页，本页只裁音频 crate 生态。
- GUI 应用的音频（如 egui 应用内播音频）不新开页：栈组合 = 31 GUI 页 + 本页 cpal/symphonia 层，无新事实。
- 语音识别/TTS 模型推理归 [机器学习生态页](13_machine_learning_ecosystem.md)（「语义出」边界，与 32 页同一裁决线）。

## 国际权威参考 / International Authority References

- [rodio GitHub（RustAudio/rodio）](https://github.com/RustAudio/rodio) · [symphonia GitHub](https://github.com/pdelacour/symphonia) · [cpal GitHub（rustaudio/cpal）](https://github.com/rustaudio/cpal)
- [kira GitHub（Kirithora/kira）](https://github.com/KiraAudio/kira) · [rustfft GitHub](https://github.com/GeneralChipo/rustfft)
- [DASp 仓库状态页](https://github.com/RustAudio/DASp)（停更事实）· [lofty GitHub](https://github.com/Lazy-Farmer/lofty)
- 学术锚（2026-10-20 arXiv API 实核）：[Compiling Differentiable Audio Graphs to Real-Time DSP (Franchino, Schlecht)](https://arxiv.org/abs/2606.21277)（2026-06-19 提交）——可微分音频模型 lowering 到实时 DSP 的编译器路线（ADAC→FAUST），佐证本页「DSP 计算层是独立选型层（rustfft/rubato 家族）」的分层裁决：ML 训练栈与实时音频生产栈之间的翻译断层正是 Rust 原生 DSP 层存在的动机（口径限于模型→DSP lowering，crate 选型仍以本页 crates.io 实查为准）。
