@echo off
echo ========================================
echo Rust模型实现示例运行脚本
echo ========================================
echo.

echo 正在编译项目...
cargo build
if %errorlevel% neq 0 (
    echo 编译失败！
    pause
    exit /b 1
)

echo.
echo ========================================
echo 1. 运行系统建模示例
echo ========================================
cargo run --example system_modeling_examples
echo.

echo ========================================
echo 2. 运行机器学习示例
echo ========================================
cargo run --example machine_learning_examples
echo.

echo ========================================
echo 3. 运行形式化方法示例
echo ========================================
cargo run --example formal_methods_examples
echo.

echo ========================================
echo 4. 运行所有测试
echo ========================================
cargo test
echo.

echo ========================================
echo 所有示例运行完成！
echo ========================================
pause
