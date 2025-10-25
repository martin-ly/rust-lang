@echo off
REM ============================================
REM Cursor OOM 问题修复脚本
REM 创建时间: 2025-10-25
REM ============================================

echo ========================================
echo    Cursor OOM 修复工具
echo ========================================
echo.

echo [1/4] 检查配置文件...
if exist ".cursorignore" (
    echo [OK] .cursorignore 已存在
) else (
    echo [WARN] .cursorignore 不存在，请运行项目
)

if exist ".vscode\settings.json" (
    echo [OK] .vscode\settings.json 已存在
) else (
    echo [WARN] .vscode\settings.json 不存在，请运行项目
)
echo.

echo [2/4] 清理 Cursor 缓存...
set CURSOR_CACHE=%APPDATA%\Cursor\Cache
set CURSOR_CACHED_DATA=%APPDATA%\Cursor\CachedData
set CURSOR_CODE_CACHE=%APPDATA%\Cursor\Code Cache
set CURSOR_GPU_CACHE=%APPDATA%\Cursor\GPUCache

if exist "%CURSOR_CACHE%" (
    echo 删除: %CURSOR_CACHE%
    rmdir /s /q "%CURSOR_CACHE%" 2>nul
)

if exist "%CURSOR_CACHED_DATA%" (
    echo 删除: %CURSOR_CACHED_DATA%
    rmdir /s /q "%CURSOR_CACHED_DATA%" 2>nul
)

if exist "%CURSOR_CODE_CACHE%" (
    echo 删除: %CURSOR_CODE_CACHE%
    rmdir /s /q "%CURSOR_CODE_CACHE%" 2>nul
)

if exist "%CURSOR_GPU_CACHE%" (
    echo 删除: %CURSOR_GPU_CACHE%
    rmdir /s /q "%CURSOR_GPU_CACHE%" 2>nul
)
echo [OK] 缓存清理完成
echo.

echo [3/4] 项目统计...
echo 正在统计 Markdown 文件数量...
for /f %%i in ('dir /s /b *.md 2^>nul ^| find /c /v ""') do set MD_COUNT=%%i
echo [INFO] Markdown 文件数量: %MD_COUNT%
echo.

echo [4/4] 完成!
echo.
echo ========================================
echo   修复完成，请按照以下步骤操作:
echo ========================================
echo.
echo 1. 关闭所有 Cursor 窗口
echo 2. 重新启动 Cursor
echo 3. 打开本项目
echo.
echo 如果仍然出现 OOM:
echo - 查看 CURSOR_OOM_SOLUTION_2025_10_25.md
echo - 考虑使用工作区模式
echo - 联系技术支持
echo.
echo ========================================

pause

