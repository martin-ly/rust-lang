# Rust 全局自动化工程 Makefile

all: test bench verify doc

# 测试
.PHONY: test
 test:
	cargo test --workspace

# 基准性能
.PHONY: bench
 bench:
	cargo bench --workspace

# 形式化验证（如有 kani/prusti 可用）
.PHONY: verify
 verify:
	cargo kani || true
	cargo prusti || true

# 文档
.PHONY: doc
 doc:
	cargo doc --workspace --open

# CI/CD
.PHONY: ci
 ci:
	git push && gh workflow run ci.yml

# Fuzz 测试
.PHONY: fuzz
 fuzz:
	cargo fuzz run fuzz_target

# 代码静态检查
.PHONY: lint
 lint:
	cargo clippy --workspace

# 模块依赖树
.PHONY: modules
 modules:
	cargo modules generate tree

# 安全审计
.PHONY: audit
 audit:
	cargo audit

# WebAssembly 构建
.PHONY: wasm
 wasm:
	wasm-pack build

# 系统建模
.PHONY: model
 model:
	@echo "自动化建模脚本（请根据实际项目补充）"

# 机器学习训练
.PHONY: train
 train:
	@echo "自动化训练脚本（请根据实际项目补充）"

# 远程升级
.PHONY: upgrade
 upgrade:
	@echo "远程升级脚本（请根据实际项目补充）" 