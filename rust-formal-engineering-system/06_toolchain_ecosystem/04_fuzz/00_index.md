# 模糊测试（Fuzzing）索引

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
