# 实际项目案例 (Real-World Case Studies)

## 📋 目录

- [实际项目案例 (Real-World Case Studies)](#实际项目案例-real-world-case-studies)
  - [📋 目录](#-目录)
  - [核心命题](#核心命题)
  - [案例 1: Figma - 在线设计工具](#案例-1-figma---在线设计工具)
    - [背景](#背景)
    - [实现细节](#实现细节)
    - [性能结果](#性能结果)
    - [遇到的坑](#遇到的坑)
    - [关键经验](#关键经验)
  - [案例 2: AutoCAD Web - CAD 设计工具](#案例-2-autocad-web---cad-设计工具)
    - [背景2](#背景2)
    - [迁移策略](#迁移策略)
    - [性能优化](#性能优化)
    - [代码组织](#代码组织)
    - [关键指标](#关键指标)
  - [案例 3: Zoom - 视频会议背景虚化](#案例-3-zoom---视频会议背景虚化)
    - [技术挑战](#技术挑战)
    - [技术方案](#技术方案)
    - [性能优化2](#性能优化2)
    - [部署挑战](#部署挑战)
    - [经验总结](#经验总结)
  - [案例 4: Shopify - 图片压缩服务](#案例-4-shopify---图片压缩服务)
    - [业务背景](#业务背景)
    - [技术实现](#技术实现)
    - [成本节省](#成本节省)
    - [遇到的挑战](#遇到的挑战)
  - [通用经验总结](#通用经验总结)
    - [成功模式](#成功模式)
    - [失败案例](#失败案例)
  - [决策树](#决策树)
    - [何时使用 Wasm？](#何时使用-wasm)
  - [最佳实践清单](#最佳实践清单)
    - [架构设计](#架构设计)
    - [性能优化1](#性能优化1)
    - [开发流程](#开发流程)
    - [部署策略](#部署策略)
  - [参考文献](#参考文献)
  - [相关文档](#相关文档)

## 核心命题

**案例学习价值**：
\[
\text{Learning}_{\text{case study}} > \text{Learning}_{\text{theory}} \quad (\text{实践中的真理})
\]

**失败教训权重**：
\[
\text{Value}(\text{failure}) \geq 2 \times \text{Value}(\text{success})
\]

**技术债务累积**：
\[
\text{Debt}(t) = \text{Debt}_0 \times e^{r \cdot t} \quad (\text{指数增长})
\]

---

## 案例 1: Figma - 在线设计工具

### 背景

**问题**：

- 复杂的图形渲染（数万图层）
- 实时协作（低延迟要求）
- 跨平台一致性

**技术选择**：

- C++ 渲染引擎 → Wasm
- Canvas API 渲染
- SharedArrayBuffer 多线程

### 实现细节

**架构**：

```text
JavaScript (UI逻辑)
     ↓
  Wasm (渲染引擎)
     ↓
  Canvas 2D API
```

**代码片段**（简化）：

```cpp
// C++ 渲染核心
class RenderEngine {
public:
    void render_scene(Scene* scene, Canvas* canvas) {
        // 场景图遍历
        for (auto& layer : scene->layers) {
            if (layer->visible) {
                render_layer(layer, canvas);
            }
        }
    }

private:
    void render_layer(Layer* layer, Canvas* canvas) {
        // Wasm 高效几何运算
        auto transformed = apply_transforms(layer);

        // 调用 JS Canvas API
        canvas->draw_path(transformed.path, layer->style);
    }
};
```

**JS 胶水代码**：

```javascript
// 零拷贝内存共享
const memory = new WebAssembly.Memory({
  initial: 256,
  maximum: 512,
  shared: true,
});

const renderWorker = new Worker('render-worker.js');
renderWorker.postMessage({ memory, module: wasmModule });

// 主线程处理 UI 事件
document.addEventListener('mousemove', (e) => {
  renderWorker.postMessage({
    type: 'mouse_move',
    x: e.clientX,
    y: e.clientY,
  });
});
```

### 性能结果

**对比**：

| 指标 | 纯 JavaScript | Wasm 版本 | 改进 |
|------|--------------|----------|------|
| 渲染 1万图层 | 850ms | 120ms | **7.1×** |
| 内存占用 | 1.2 GB | 450 MB | **2.7×** |
| 首次加载 | 3.5s | 1.8s | **1.9×** |

### 遇到的坑

**问题 1: 跨线程通信开销**:

**症状**：

- 多线程渲染反而更慢
- CPU 利用率不足 30%

**原因**：

- postMessage 拷贝开销大
- 线程间同步锁竞争

**解决方案**：

```javascript
// 使用 SharedArrayBuffer + Atomics
const sharedBuffer = new SharedArrayBuffer(4096);
const view = new Int32Array(sharedBuffer);

// 主线程写入任务
Atomics.store(view, 0, taskId);
Atomics.notify(view, 0, 1);

// Worker 读取任务
Atomics.wait(view, 0, 0);
const task = Atomics.load(view, 0);
```

**问题 2: Wasm 内存增长导致卡顿**:

**症状**：

- 内存增长时界面冻结
- 用户体验显著下降

**原因**：

- Wasm 内存增长需要同步操作
- 浏览器需要重新分配大块内存

**解决方案**：

```cpp
// 预分配足够内存
__attribute__((constructor))
void init_memory() {
    // 启动时分配 256MB
    void* large_buffer = malloc(256 * 1024 * 1024);
    // 防止被优化掉
    volatile char* p = (volatile char*)large_buffer;
    *p = 0;
}
```

### 关键经验

✅ **成功因素**：

1. 专注于计算密集型部分（渲染）
2. 充分利用 Canvas API（避免重新发明轮子）
3. 渐进式迁移（先迁移热点函数）

⚠️ **避坑指南**：

1. 不要过早优化（先 profile 再重写）
2. 注意 JS ↔ Wasm 边界开销
3. 预分配内存避免运行时增长

---

## 案例 2: AutoCAD Web - CAD 设计工具

### 背景2

**挑战**：

- 30 年历史的 C++ 代码库
- 数百万行代码
- 复杂的 3D 几何运算

**目标**：

- 将桌面应用移植到 Web
- 保持 90% 以上性能
- 代码复用率 > 80%

### 迁移策略

**Phase 1: 核心引擎迁移**:

```bash
# Emscripten 编译
emcc src/geometry/*.cpp src/renderer/*.cpp \
    -s WASM=1 -s ALLOW_MEMORY_GROWTH=1 \
    -s MODULARIZE=1 -s EXPORT_ES6=1 \
    -s EXPORTED_FUNCTIONS='["_compute_intersection", "_render_scene"]' \
    -O3 -o autocad-core.js
```

**Phase 2: UI 层重写**:

- React + Three.js (新 UI)
- Wasm 核心引擎（复用）
- WebGL 渲染（替代 DirectX）

**Phase 3: 增量加载**:

```javascript
// 按需加载模块
async function loadModule(name) {
  const response = await fetch(`/modules/${name}.wasm`);
  const buffer = await response.arrayBuffer();
  const module = await WebAssembly.instantiate(buffer, imports);
  return module.instance.exports;
}

// 延迟加载非核心功能
document.getElementById('open-file').addEventListener('click', async () => {
  if (!fileModule) {
    fileModule = await loadModule('file-io');
  }
  fileModule.open_dialog();
});
```

### 性能优化

**问题: 大文件加载慢**:

**初版性能**：

- 打开 100MB DWG 文件：45 秒
- 用户等待不可接受

**优化 1: 流式解析**:

```cpp
class StreamingParser {
public:
    void parse_chunk(const uint8_t* data, size_t len) {
        buffer_.insert(buffer_.end(), data, data + len);

        while (buffer_.size() >= MIN_CHUNK_SIZE) {
            auto entity = parse_entity(buffer_);
            if (entity) {
                emit_entity(entity);
                buffer_.erase(buffer_.begin(), buffer_.begin() + entity->size);
            } else {
                break;  // 需要更多数据
            }
        }
    }
};
```

**优化 2: Web Worker 并行**:

```javascript
// 主线程
const workers = Array.from({ length: navigator.hardwareConcurrency }, () =>
  new Worker('parser-worker.js')
);

const chunks = splitFileIntoChunks(fileBuffer);
const results = await Promise.all(
  chunks.map((chunk, i) => workers[i % workers.length].parse(chunk))
);
```

**最终性能**：

- 打开 100MB 文件：**8 秒** (5.6× 提升)
- 用户体验可接受

### 代码组织

**目录结构**：

```text
autocad-web/
├── core/                 # C++ 核心（编译为 Wasm）
│   ├── geometry/
│   ├── renderer/
│   ├── file-io/
│   └── algorithms/
├── web/                  # JavaScript UI
│   ├── components/
│   ├── workers/
│   └── wasm-bindings/    # Wasm 封装
├── build/
│   ├── emscripten.sh     # 构建脚本
│   └── optimize.sh       # 优化流水线
└── tests/
    ├── unit/             # C++ 单元测试
    └── integration/      # JS + Wasm 集成测试
```

### 关键指标

**开发成本**：

- 工程师：15 人
- 时间：18 个月
- 代码复用：**85%**（C++ 核心代码）

**运行性能**：

| 操作 | 桌面版 | Web 版 | 比率 |
|------|-------|--------|------|
| 打开文件 | 5s | 8s | 0.63 |
| 渲染场景 | 16ms | 22ms | 0.73 |
| 几何运算 | 100% | 92% | 0.92 |

**批判**：
> AutoCAD Web 证明了复杂桌面应用可以迁移到 Web，但性能仍有 10-40% 损失。对于专业用户，桌面版仍是首选。

---

## 案例 3: Zoom - 视频会议背景虚化

### 技术挑战

**实时要求**：

- 1080p @ 30fps
- 延迟 < 33ms/帧
- CPU 占用 < 50%

**算法复杂度**：

- 语义分割（人像抠图）
- 边缘羽化
- 背景替换/模糊

### 技术方案

**架构**：

```text
Video Stream → Wasm (AI 推理) → Canvas (合成) → Output
```

**Wasm 模块**：

```cpp
// TensorFlow Lite → Wasm
class BackgroundSegmenter {
private:
    // tflite is the TensorFlow Lite C++ namespace
    std::unique_ptr<tflite::Interpreter> interpreter_;

public:
    void process_frame(const uint8_t* rgba, uint8_t* mask) {
        // 1. 预处理
        auto input = preprocess(rgba);

        // 2. 推理
        interpreter_->SetInputs({input});
        interpreter_->Invoke();
        auto output = interpreter_->GetOutput(0);

        // 3. 后处理
        postprocess(output, mask);
    }

private:
    Tensor preprocess(const uint8_t* rgba) {
        // RGB 归一化到 [-1, 1]
        Tensor input(1, 256, 256, 3);
        for (int i = 0; i < input.size(); i++) {
            input[i] = (rgba[i] / 255.0f - 0.5f) * 2.0f;
        }
        return input;
    }
};
```

**WebGL 加速**：

```javascript
// 边缘羽化（GPU）
const featherShader = `
  precision highp float;
  uniform sampler2D mask;
  uniform vec2 resolution;
  varying vec2 vUv;

  void main() {
    vec2 texel = 1.0 / resolution;
    float sum = 0.0;

    // Gaussian blur
    for (int x = -2; x <= 2; x++) {
      for (int y = -2; y <= 2; y++) {
        vec2 offset = vec2(float(x), float(y)) * texel;
        sum += texture2D(mask, vUv + offset).r * kernel[abs(x)][abs(y)];
      }
    }

    gl_FragColor = vec4(sum, sum, sum, 1.0);
  }
`;
```

### 性能优化2

**问题: CPU 占用过高**:

**Profile 结果**：

```text
Total: 45ms/frame (无法达到 30fps)
├─ AI 推理: 28ms (62%)
├─ 图像拷贝: 10ms (22%)
├─ 边缘处理: 5ms (11%)
└─ 合成: 2ms (5%)
```

**优化策略**：

1. **降采样**：

   ```cpp
   // 从 1080p 降到 256×144 推理
   auto downsampled = resize(input, 256, 144);
   auto mask_low = segment(downsampled);
   auto mask_high = upsample(mask_low, 1920, 1080);
   ```

2. **SIMD 加速**：

   ```cpp
   // 使用 Wasm SIMD
   #include <wasm_simd128.h>

   void process_pixels_simd(const uint8_t* src, uint8_t* dst, size_t len) {
       for (size_t i = 0; i < len; i += 16) {
           v128_t pixels = wasm_v128_load(&src[i]);
           v128_t processed = wasm_i8x16_add_sat_u(pixels, wasm_i8x16_splat(10));
           wasm_v128_store(&dst[i], processed);
       }
   }
   ```

3. **多线程**：

   ```javascript
   // 4 个 Worker 并行处理
   const workers = createWorkerPool(4);

   async function processFrame(frame) {
       const tiles = splitIntoTiles(frame, 2, 2);  // 2×2 网格
       const results = await Promise.all(
           tiles.map((tile, i) => workers[i].process(tile))
       );
       return mergeResults(results);
   }
   ```

**最终性能**：

- 处理时间：**18ms/frame**
- CPU 占用：**35%**
- 达到 30fps 要求 ✅

### 部署挑战

**问题: 模型文件过大**:

**初版**：

- 模型大小：15 MB
- 首次加载：8 秒（不可接受）

**优化方案**：

```bash
# 模型量化（Float32 → Int8）
python quantize_model.py --input model.tflite --output model_q.tflite

# 大小对比
# model.tflite:    15 MB
# model_q.tflite:   4 MB  (73% 减少)

# 精度损失：< 2%（可接受）
```

**渐进式加载**：

```javascript
// 先加载低质量模型
const quickModel = await loadModel('model_quick.wasm');  // 1 MB
startProcessing(quickModel);

// 后台加载高质量模型
loadModel('model_full.wasm').then(fullModel => {
  replaceModel(fullModel);  // 无缝切换
});
```

### 经验总结

✅ **成功点**：

1. SIMD 指令带来 2-3× 提升
2. 降采样显著降低计算量
3. 量化模型平衡了大小与精度

⚠️ **教训**：

1. 初期过度优化模型精度（用户感知不到）
2. 低估了多线程同步开销
3. 未考虑低端设备性能

---

## 案例 4: Shopify - 图片压缩服务

### 业务背景

**规模**：

- 处理量：每天 1 亿+ 图片
- 图片大小：平均 5 MB
- 存储成本：每月 $50,000+

**目标**：

- 在客户端压缩（节省带宽）
- 压缩比 > 70%
- 视觉质量损失 < 5%

### 技术实现

**Wasm 压缩库**：

```cpp
// MozJPEG → Wasm
class ImageCompressor {
public:
    std::vector<uint8_t> compress(
        const uint8_t* rgba,
        int width,
        int height,
        int quality
    ) {
        // MozJPEG 压缩
        jpeg_compress_struct cinfo;
        jpeg_create_compress(&cinfo);

        // 配置
        cinfo.image_width = width;
        cinfo.image_height = height;
        cinfo.input_components = 3;
        cinfo.in_color_space = JCS_RGB;

        jpeg_set_defaults(&cinfo);
        jpeg_set_quality(&cinfo, quality, TRUE);

        // 压缩
        jpeg_start_compress(&cinfo, TRUE);
        // ... 压缩逻辑
        jpeg_finish_compress(&cinfo);

        return output;
    }
};
```

**前端集成**：

```javascript
// 文件上传时自动压缩
document.getElementById('upload').addEventListener('change', async (e) => {
  const file = e.target.files[0];
  console.log(`Original: ${(file.size / 1024 / 1024).toFixed(2)} MB`);

  // Wasm 压缩
  const compressed = await wasmCompressor.compress(file, { quality: 85 });
  console.log(`Compressed: ${(compressed.size / 1024 / 1024).toFixed(2)} MB`);

  // 上传压缩后的文件
  uploadToServer(compressed);
});
```

### 成本节省

**对比分析**：

| 方案 | 带宽成本 | 存储成本 | 总成本/月 |
|------|---------|---------|----------|
| 原始方案 | $80,000 | $50,000 | **$130,000** |
| 服务端压缩 | $50,000 | $15,000 | **$65,000** |
| 客户端 Wasm | $15,000 | $15,000 | **$30,000** |

**ROI**：

- 节省：**$100,000/月**
- 开发成本：$80,000（工程师 2人 × 2月）
- 回本周期：**< 1个月**

### 遇到的挑战

**问题: 移动设备性能不足**:

**症状**：

- iPhone 6 压缩 5MB 图片需 15 秒
- 导致应用无响应

**解决方案**：

```javascript
// 设备自适应
function getCompressionQuality() {
  const memory = navigator.deviceMemory || 4;
  const cores = navigator.hardwareConcurrency || 2;

  if (memory < 2 || cores < 2) {
    return 70;  // 低端设备：快速压缩
  } else if (memory < 4) {
    return 80;  // 中端设备：平衡
  } else {
    return 90;  // 高端设备：高质量
  }
}

// Web Worker 防止 UI 阻塞
const worker = new Worker('compressor-worker.js');
worker.postMessage({ image, quality: getCompressionQuality() });
```

---

## 通用经验总结

### 成功模式

**1. 计算密集型场景**:

- 图像/视频处理
- 数据压缩/解压
- 科学计算
- 游戏物理引擎

**2. 代码复用场景**:

- 桌面应用迁移
- 跨平台一致性
- 算法库移植

**3. 性能关键场景**:

- 实时渲染
- 大数据处理
- 机器学习推理

### 失败案例

**反模式 1: 过度工程化**:

**案例**：某公司将整个 Node.js 应用编译为 Wasm

**问题**：

- 文件大小：120 MB（不可接受）
- 启动时间：30 秒
- 调试困难

**教训**：
> Wasm 不是万能药。简单的业务逻辑用 JavaScript 更合适。

**反模式 2: 忽略 JS ↔ Wasm 边界开销**:

**案例**：频繁调用 Wasm 函数处理小数据

```javascript
// ❌ 错误：频繁跨边界
for (let i = 0; i < 1000000; i++) {
  result[i] = wasmModule.process(data[i]);  // 每次调用 1μs 开销
}
// 总开销：1 秒（纯粹浪费在调用上）

// ✅ 正确：批量处理
const result = wasmModule.processBatch(data);  // 单次调用
```

**反模式 3: 盲目使用 Wasm**:

**案例**：一个简单的表单验证逻辑也用 Wasm

**问题**：

- 增加了 200 KB 文件大小
- 性能反而下降（加载开销）
- 维护成本增加

**教训**：
> 先 profile，证明瓶颈，再重写。不要为了 Wasm 而 Wasm。

---

## 决策树

### 何时使用 Wasm？

```text
是否计算密集型？
├─ 否 → 使用 JavaScript
└─ 是 → 是否频繁跨边界？
    ├─ 是 → 重新设计接口 or 使用 JavaScript
    └─ 否 → 是否有现成 C/C++/Rust 代码？
        ├─ 是 → ✅ 使用 Wasm
        └─ 否 → 性能收益 > 开发成本？
            ├─ 是 → ✅ 使用 Wasm
            └─ 否 → 使用 JavaScript
```

---

## 最佳实践清单

### 架构设计

- [ ] 最小化 JS ↔ Wasm 边界跨越
- [ ] 使用 SharedArrayBuffer 共享大块数据
- [ ] Web Worker 隔离计算密集型任务
- [ ] 渐进式加载（先小模块再大模块）

### 性能优化1

- [ ] Profile 驱动优化（不要猜测）
- [ ] SIMD 加速关键循环
- [ ] 预分配内存避免运行时增长
- [ ] 多线程并行（如果任务可分解）

### 开发流程

- [ ] 调试构建 vs 发布构建分离
- [ ] 自动化测试覆盖 Wasm 模块
- [ ] CI/CD 集成 wasm-validate
- [ ] 监控生产环境性能指标

### 部署策略

- [ ] 使用 Brotli 压缩 Wasm 文件
- [ ] CDN 分发（减少延迟）
- [ ] 版本化 URL（缓存友好）
- [ ] 降级方案（Wasm 不可用时）

---

## 参考文献

1. **[Figma]** Evan Wallace. "WebAssembly at Figma" (2020)
2. **[Autodesk]** AutoCAD Web: Technical White Paper (2021)
3. **[Shopify]** "Client-Side Image Compression with WebAssembly" (2022)

---

## 相关文档

- **[09.1 开发工具链](09.1_Development_Toolchain.md)** - 工具选型
- **[09.2 测试策略](09.2_Testing_Strategies.md)** - 质量保证
- **[05 应用模式](../05_Application_Patterns/)** - 应用场景分类
- **[07.3 成本收益分析](../07_Engineering_Economics/07.3_Cost_Benefit_Analysis.md)** - ROI 计算
