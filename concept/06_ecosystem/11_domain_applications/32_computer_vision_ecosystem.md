# Rust 计算机视觉生态（canonical 缺口闭环页）

> **EN**: Rust Computer Vision Ecosystem (canonical gap-closure page)
> **Bloom 层级**: L3-L5
> **Summary**: crates.io `computer-vision` 分类（665 crates）的 canonical 生态页：image 0.25.10 图像解码核心族（image-webp/tiff/exr/ravif/qoi 编解码子页）、imageproc 0.27.0 经典视觉算法、opencv 0.101.1 系统绑定路线、resvg/usvg 0.48.1 矢量栅格化与 fast_image_resize 6.1.0 SIMD 缩放，附「纯 Rust 经典视觉 vs OpenCV 绑定 vs GPU/wgpu 计算」三路线选型裁决与 ML 推理页边界划分。
> **受众**: [入门→进阶]
> **内容分级**: [专题级]
> **定位**: W8 裁决产物——`DOMAIN_ECOSYSTEM_REALIGNMENT_PLAN_2026-10-19` 登记 computer-vision canonical 缺口（全库仅 13_machine_learning_ecosystem 顺带提及 CV 场景，无专页），本页为候选锚（image/imageproc/opencv/resvg）建页闭环裁决。
> **版本事实基线**: crates.io API 2026-10-19 实查；rustc 1.99.1。
> **前置概念**: [Rust 桌面 GUI 生态](31_desktop_gui_ecosystem.md) · [机器学习生态](13_machine_learning_ecosystem.md) · [并行算法](25_parallel_algorithms.md)
> **权威来源**: [crates.io computer-vision 分类](https://crates.io/categories/computer-vision) · [image docs.rs](https://docs.rs/image/) · [imageproc](https://docs.rs/imageproc/) · [opencv rust 绑定](https://docs.rs/opencv/) · [resvg](https://docs.rs/resvg/) · [Rustonomicon — FFI（系统绑定路线的 unsafe/ABI 风险官方口径）](https://doc.rust-lang.org/nomicon/ffi.html)

---

## 一、版图：Rust 视觉生态的分层结构（crates.io 实查 2026-10-19）

| 层 | crate | 版本（实查） | 累计下载 | 近期下载 | 活跃度判读 |
|:---|:---|:---|---:|---:|:---|
| 像素容器+解码 | **image** | **0.25.10**（2026-03-10） | 2.19 亿 | 6,360 万 | 一线（事实标准） |
| 解码族成员 | image-webp / tiff / exr | 0.2.4 / 0.11.3 / 1.74.2 | 9,056 万 / 1.36 亿 / 8,079 万 | 3,555 万 / 4,041 万 / 2,118 万 | 高（image 0.25 已把 webp 等拆为独立 crate） |
| 编码族成员 | ravif（AVIF 编码） | 0.13.0 | 5,389 万 | 1,793 万 | 高 |
| 独立格式 | qoi | 0.4.1（2022-10-16 停更） | 7,218 万 | 1,863 万 | 格式已定案，库冻结属正常 |
| JPEG 管线 | mozjpeg | 0.10.13 | 474 万 | 135 万 | 稳定（mozjpeg 系统库绑定） |
| 经典视觉算法 | **imageproc** | **0.27.0**（2026-06-02） | 1,412 万 | 288 万 | 活跃（image-rs 家族） |
| 缩放管线 | fast_image_resize | 6.1.0（2026-07-21） | 2,176 万 | 553 万 | 高（SIMD 缩放事实标准） |
| OpenCV 绑定 | **opencv** | **0.101.1**（2026-10-09） | 500 万 | 157 万 | 高（跟随上游 OpenCV 4.x 发版） |
| 矢量栅格化 | **resvg / usvg** | **0.48.1**（2026-08-02） | 3,136 万 / 3,431 万 | 1,150 万 / 1,222 万 | 高（RustGfx 家族，SVG→像素） |
| 分类占位陷阱 | `cog` | 0.1.0（2016 停更） | 1.2 万 | 6,660 | 检索易误触：2016「Computer Open Graphics」同名撞车，非 CV 库 |

分类口径实查：crates.io `computer-vision` 665 crates、`graphics` 3,860 crates——CV 在 Rust 生态是**薄分类**：绝大多数实际视觉能力沉淀在 image-rs 与 RustGfx 两个家族，而非 CV 分类本身。

## 二、路线裁决：纯 Rust 经典视觉 vs OpenCV 绑定 vs GPU 计算

三条路线不是竞争关系，而是**依赖姿态**的三档选择：

1. **纯 Rust 路线（默认选型）**：`image` + `imageproc` + `fast_image_resize`。零系统依赖、`no_std` 友好度中等、编译即所得；适合解码/缩放/滤波/直方图/轮廓等经典管线，以及供应链审计敏感场景（纯 Rust 可进 cargo-vet unvetted 白名单管理）。代价：算法覆盖面窄于 OpenCV，缺标定、特征点、光流等大件。
2. **OpenCV 绑定路线**：`opencv` 0.101.1 直接 FFI 到系统 OpenCV。功能面最全（calib3d/features2d/video 全套），代价是把 C++ 系统库依赖与 ABI 匹配问题重新引回项目——与选 Rust 的「消除构建地狱」动机直接冲突；CI 需自行保证 OpenCV 版本配对（绑定层版本线 0.101.x 跟随 OpenCV 4.11 系）。
3. **GPU/计算着色器路线**：resize/滤波等数据并行核用 `wgpu` compute（见 [桌面 GUI 页](31_desktop_gui_ecosystem.md) §三渲染收敛，wgpu 30.0.1 同栈）或 `burn`/`candle` 张量核。**边界裁决：模型推理（ort 2.0.0-rc.15 / candle 0.11.0）归 [机器学习生态页](13_machine_learning_ecosystem.md)，本页不重复登记**——CV 与 ML 的交界是「像素进、像素出」归本页，「像素进、语义出」归 ML 页。

## 三、矢量视觉：resvg 系是 Rust 视觉生态最被低估的一极

`usvg`（SVG 解析为场景树）+ `resvg`（纯 Rust 栅格化）合计近期 2,372 万下载，被 31 页 GUI 生态、typst 系文档管线、以及大量图标/图表管线间接消费。RustGfx 家族（resvg/usvg/picture/svgstd 等）与 image-rs 家族（image/imageproc/image-webp/tiff/exr）是视觉侧仅有的两个「事实标准级」家族——**这是 CV canonical 页必须与 GUI 页分设但互相挂链的结构性理由**：两条家族在 wgpu/text-rendering 层汇合，在解码/像素处理层各自独立。

## 四、生态判读：为什么 Rust CV「薄」而图形「厚」

- 学术与工业 CV 的主阵地仍是 C++/OpenCV 与 Python 胶水；Rust 侧的增量集中在**图像 I/O 管线**（image 系 2.19 亿累计下载是全库前十量级）与**确定性栅格化**（resvg），而非检测/分割算法库。
- crates.io CV 分类内的独立检测库（如 `yolo-rs` 0.2.2，5 千下载）均为长尾实验，无一具备生产级采用证据——**登记为「分类存在但无 canonical 库」的薄生态事实**，不虚构生态厚度。
- 选型结论：新项目视觉管线默认 image+imageproc+fast_image_resize；需要 OpenCV 独占算法时再引 opencv 绑定并显式接受系统依赖；推理一律走 ML 页路线。

## 五、反例与陷阱

1. **`cog` 撞名陷阱**：crates.io 检索 "computer graphics/vision" 命中 `cog`（2016，1.2 万下载，停更十年）——历史同名项目，绝非 CV 库；引用前必查 updated_at。
2. **qoi 停更≠腐烂**：QOI 格式已定稿（作者官宣冻结），库 2022 后不再发版属设计完成而非弃维护——判读活跃度须结合上游事件，不能只看发版间隔。
3. **image 0.25 的解码族拆分**：webp/tiff/exr 等已从 image 主 crate 拆为独立 crate（image 主包近期 6,360 万 vs image-webp 3,555 万），旧文档「image 内置全格式」口径已过时；升级 0.25 时按目标格式显式声明子 crate 依赖。

## 国际权威参考 / International Authority References

- [crates.io computer-vision 分类](https://crates.io/categories/computer-vision)（665 crates，实查口径）
- [image-rs/image GitHub](https://github.com/image-rs/image) · [image-rs/imageproc](https://github.com/image-rs/imageproc)
- [opencv-rust (ncxx)](https://github.com/Shnatsel/opencv) · [rust-lang 安全边界对比](../../05_comparative/03_domain_comparisons/01_safety_boundaries.md)
- [RustGfx/resvg](https://github.com/RazrFalcon/resvg) · [QOI 格式官网](https://qoiformat.org/)（作者冻结声明）
