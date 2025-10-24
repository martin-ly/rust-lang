# 模糊测试（Fuzzing）索引


## 📊 目录

- [目的](#目的)
- [工具](#工具)
- [常用命令（cargo-fuzz）](#常用命令cargo-fuzz)
- [快速开始（AFL++）](#快速开始afl)
- [CI 集成建议](#ci-集成建议)
- [建议](#建议)
- [导航](#导航)


## 目的

- 通过 Fuzz 提升健壮性，覆盖边界与异常路径。

## 工具

- cargo-fuzz：LibFuzzer 接入
- AFL++：进程级模糊

## 常用命令（cargo-fuzz）

```bash
cargo install cargo-fuzz
cargo fuzz init
cargo fuzz add fuzz_target_1
cargo fuzz run fuzz_target_1
```

## 快速开始（AFL++）

```bash
# 需安装 afl++
# Linux
sudo apt install afl++
# macOS
brew install afl-fuzz
```

## CI 集成建议

- 对解析/编解码库添加夜间 fuzz job（限定运行时间）
- 将崩溃样例持久化到工件或仓库字典目录

## 建议

- 为解析/编解码/状态机等模块优先添加 fuzz 目标
- 维护字典与最小崩溃样例，纳入 CI 轮转

## 导航

- 返回工具链：[`../00_index.md`](../00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

---

别名与规范说明：

- 本页为 Fuzz 专题页，编号为 `04_fuzz`。与“04_testing_frameworks”编号冲突已通过规范入口化处理：
  - 测试框架规范入口：[`../04_testing_frameworks/00_index.md`](../04_testing_frameworks/00_index.md)
  - Fuzz 作为质量保障的补充手段，相关综述也可在：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
