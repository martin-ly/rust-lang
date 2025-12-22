@echo off
REM 依赖更新检查脚本 (Windows)
REM 创建日期: 2025-12-11
REM 用途: 检查项目依赖的可用更新

echo ==========================================
echo 依赖更新检查脚本
echo ==========================================
echo.

REM 1. 检查可用更新
echo [1/4] 检查可用更新...
cargo update --dry-run 2>&1 | findstr /C:"Updating" /C:"Locking" /C:"Unchanged" || echo.
echo.

REM 2. 详细检查
echo [2/4] 详细检查可用更新...
cargo update --verbose 2>&1 | findstr /C:"Unchanged.*available" || echo 所有依赖都是最新版本
echo.

REM 3. 检查安全漏洞
echo [3/4] 检查安全漏洞...
where cargo-audit >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    cargo audit || echo 警告: 发现安全漏洞，请查看详细报告
) else (
    echo 警告: cargo-audit 未安装，跳过安全检查
    echo 安装命令: cargo install cargo-audit
)
echo.

REM 4. 检查过时依赖
echo [4/4] 检查过时依赖...
where cargo-outdated >nul 2>&1
if %ERRORLEVEL% EQU 0 (
    cargo outdated || echo.
) else (
    echo 警告: cargo-outdated 未安装，跳过过时依赖检查
    echo 安装命令: cargo install cargo-outdated
)
echo.

echo ==========================================
echo 检查完成！
echo ==========================================
echo.
echo 待迁移的依赖请查看: DEPENDENCY_UPDATE_CHECK.md
