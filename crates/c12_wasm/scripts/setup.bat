@echo off
REM C12 WASM 项目快速设置脚本 (Windows)
REM 用于快速设置开发环境

setlocal enabledelayedexpansion

echo.
echo 🦀 C12 WASM 项目环境设置 (Windows)
echo ========================
echo.

REM 1. 检查 Rust 安装
echo 📦 检查 Rust 安装...
where rustc >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    for /f "tokens=*" %%i in ('rustc --version') do set RUST_VERSION=%%i
    echo ✓ Rust 已安装: !RUST_VERSION!
) else (
    echo ✗ Rust 未安装
    echo 请访问 https://rustup.rs/ 下载并安装 Rust
    pause
    exit /b 1
)

REM 2. 安装 WASM 目标
echo.
echo 🎯 安装 WASM 编译目标...
echo   安装 wasm32-unknown-unknown...
rustup target add wasm32-unknown-unknown >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    echo ✓ wasm32-unknown-unknown 已安装
) else (
    echo ⚠ wasm32-unknown-unknown 可能已经安装
)

echo   安装 wasm32-wasi...
rustup target add wasm32-wasi >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    echo ✓ wasm32-wasi 已安装
) else (
    echo ⚠ wasm32-wasi 可能已经安装
)

REM 3. 检查 wasm-pack
echo.
echo 📦 检查 wasm-pack...
where wasm-pack >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    for /f "tokens=*" %%i in ('wasm-pack --version') do set WASM_PACK_VERSION=%%i
    echo ✓ wasm-pack 已安装: !WASM_PACK_VERSION!
) else (
    echo ⚠ wasm-pack 未安装
    echo 请访问 https://rustwasm.github.io/wasm-pack/installer/ 下载安装
    echo 或者运行: cargo install wasm-pack
)

REM 4. 安装开发工具
echo.
echo 🛠️  安装开发工具...
echo   安装 rustfmt...
rustup component add rustfmt >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    echo ✓ rustfmt 已安装
) else (
    echo ⚠ rustfmt 可能已经安装
)

echo   安装 clippy...
rustup component add clippy >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    echo ✓ clippy 已安装
) else (
    echo ⚠ clippy 可能已经安装
)

REM 5. 构建项目
echo.
echo 🏗️  构建项目...
cargo check --lib >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    echo ✓ 项目构建成功
) else (
    echo ✗ 项目构建失败
    pause
    exit /b 1
)

REM 6. 运行测试
echo.
echo 🧪 运行测试...
cargo test --lib >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    echo ✓ 测试通过
) else (
    echo ✗ 测试失败
    pause
    exit /b 1
)

REM 7. 构建 WASM（如果 wasm-pack 可用）
echo.
where wasm-pack >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    echo 🌐 构建 WASM 模块...
    wasm-pack build --target web >nul 2>&1
    if !ERRORLEVEL! EQU 0 (
        echo ✓ WASM 模块构建成功
        echo   输出目录: pkg\
    ) else (
        echo ⚠ WASM 模块构建失败
    )
)

REM 8. 完成
echo.
echo ========================
echo ✓ 环境设置完成！
echo.
echo 📚 下一步:
echo   1. 查看文档: type README.md
echo   2. 运行测试: cargo test
echo   3. 运行示例: cargo run --example 01_basic_add
echo   4. 启动演示: python -m http.server 8080
echo      然后访问: http://localhost:8080/demo/
echo.
echo 🎉 开始愉快地编码吧！
echo.
pause
