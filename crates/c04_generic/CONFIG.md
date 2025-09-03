# 项目配置文件说明

## 配置文件列表

### 1. Cargo.toml

- **作用**: Rust 项目的主要配置文件
- **内容**: 项目元数据、依赖、构建配置
- **位置**: 项目根目录

### 2. .gitignore

- **作用**: Git 版本控制忽略文件配置
- **内容**: 编译产物、IDE 文件、临时文件等
- **位置**: 项目根目录

### 3. rustfmt.toml

- **作用**: Rust 代码格式化配置
- **内容**: 代码风格、缩进、行宽等设置
- **位置**: 项目根目录

### 4. .clippy.toml

- **作用**: Clippy 代码质量检查配置
- **内容**: 允许/拒绝的警告、检查规则等
- **位置**: 项目根目录

### 5. build.bat (Windows)

- **作用**: Windows 批处理构建脚本
- **功能**: 自动化构建、测试、检查流程
- **位置**: 项目根目录

### 6. build.sh (Linux/macOS)

- **作用**: Unix 系统 Shell 构建脚本
- **功能**: 自动化构建、测试、检查流程
- **位置**: 项目根目录

## 使用说明

### Windows 用户

```cmd
# 运行构建脚本
build.bat

# 或手动执行命令
cargo check
cargo build
cargo test
cargo run --bin c04_generic
```

### Linux/macOS 用户

```bash
# 给脚本执行权限
chmod +x build.sh

# 运行构建脚本
./build.sh

# 或手动执行命令
cargo check
cargo build
cargo test
cargo run --bin c04_generic
```

## 配置说明

### 代码格式化 (rustfmt.toml)

- 最大行宽: 100 字符
- 缩进: 4 个空格
- 换行符: Unix 风格 (LF)
- 自动合并导入和派生

### 代码质量 (.clippy.toml)

- 严格的质量检查
- 拒绝不安全的代码模式
- 性能优化建议
- 代码风格指导

## 最佳实践

1. **提交前检查**: 使用构建脚本确保代码质量
2. **定期格式化**: 使用 `cargo fmt` 保持代码风格一致
3. **质量检查**: 使用 `cargo clippy` 发现潜在问题
4. **测试覆盖**: 确保所有功能都有测试用例
