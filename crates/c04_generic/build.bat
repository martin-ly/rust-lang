@echo off
echo ========================================
echo Rust 泛型理论项目构建脚本
echo ========================================

echo.
echo 1. 检查代码质量...
cargo clippy --all-targets --all-features -- -D warnings
if %errorlevel% neq 0 (
    echo ❌ Clippy 检查失败
    pause
    exit /b 1
)
echo ✅ Clippy 检查通过

echo.
echo 2. 格式化代码...
cargo fmt --all -- --check
if %errorlevel% neq 0 (
    echo ❌ 代码格式化检查失败
    pause
    exit /b 1
)
echo ✅ 代码格式化检查通过

echo.
echo 3. 编译项目...
cargo build --release
if %errorlevel% neq 0 (
    echo ❌ 编译失败
    pause
    exit /b 1
)
echo ✅ 编译成功

echo.
echo 4. 运行测试...
cargo test --release
if %errorlevel% neq 0 (
    echo ❌ 测试失败
    pause
    exit /b 1
)
echo ✅ 所有测试通过

echo.
echo 5. 运行演示程序...
cargo run --bin c04_generic --release
if %errorlevel% neq 0 (
    echo ❌ 演示程序运行失败
    pause
    exit /b 1
)
echo ✅ 演示程序运行成功

echo.
echo ========================================
echo 🎉 所有检查完成！项目构建成功！
echo ========================================
pause
