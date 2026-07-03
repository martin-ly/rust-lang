@echo off
REM Miri 测试运行脚本 (Windows)
REM 用于运行所有 Miri 测试并检测未定义行为

echo ==========================================
echo     Miri 测试运行脚本
echo ==========================================
echo.

REM 检查 Miri 是否安装
echo [1/4] 检查 Miri 安装...
rustup component list --installed | findstr miri >nul 2>&1
if %ERRORLEVEL% NEQ 0 (
    echo Miri 未安装，正在安装...
    rustup component add miri
) else (
    echo Miri 已安装
)

REM 设置 Miri
echo.
echo [2/4] 设置 Miri 环境...
cargo miri setup

REM 设置 Miri 环境变量
set MIRIFLAGS=-Zmiri-tree-borrows -Zmiri-disable-isolation
echo MIRIFLAGS: %MIRIFLAGS%

REM 运行测试
echo.
echo [3/4] 运行 Miri 测试...
echo.

REM 运行所有 crate 的测试
echo ------------------------------------------
echo 运行 Miri 测试...
echo ------------------------------------------

cargo miri test --workspace -- miri_tests

if %ERRORLEVEL% EQU 0 (
    echo.
    echo ==========================================
    echo [4/4] 测试总结
    echo ==========================================
    echo 所有 Miri 测试通过！
    echo.
    echo 测试说明:
    echo   - 使用了 Tree Borrows 模型
    echo   - 检测了内存安全问题
    echo   - 验证了 unsafe 代码的正确性
) else (
    echo.
    echo ==========================================
    echo [4/4] 测试总结
    echo ==========================================
    echo 部分测试失败
    echo.
    echo 可能的错误类型:
    echo   - Use-after-free: 使用已释放的内存
    echo   - Data race: 数据竞争
    echo   - Invalid memory access: 无效内存访问
    echo   - Alignment violation: 对齐违规
)
