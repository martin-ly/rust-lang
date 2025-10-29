@echo off
REM ================================================================
REM 文档归档脚本 - Rust Learning System (Windows版本)
REM ================================================================
REM 用途: 清理和归档 docs\docs\ 目录中的历史文档
REM 日期: 2025-10-30
REM 作者: AI Assistant
REM ================================================================

setlocal enabledelayedexpansion

:: 颜色代码 (Windows 10+)
set "GREEN=[32m"
set "YELLOW=[33m"
set "BLUE=[34m"
set "RED=[31m"
set "NC=[0m"

:: 基础目录
set "BASE_DIR=docs\docs"
set "ARCHIVE_DIR=%BASE_DIR%\archive"
set "BACKUP_DIR=docs\backup"

echo.
echo ================================================================
echo   Rust Learning System - 文档归档工具
echo ================================================================
echo.

:: ================================================================
:: 创建目录结构
:: ================================================================
:CREATE_DIRECTORIES
echo [33m创建归档目录结构...[0m

if not exist "%ARCHIVE_DIR%\phase_reports" mkdir "%ARCHIVE_DIR%\phase_reports"
if not exist "%ARCHIVE_DIR%\module_reports" mkdir "%ARCHIVE_DIR%\module_reports"
if not exist "%ARCHIVE_DIR%\planning" mkdir "%ARCHIVE_DIR%\planning"
if not exist "%ARCHIVE_DIR%\temp" mkdir "%ARCHIVE_DIR%\temp"
if not exist "%ARCHIVE_DIR%\language_restructure" mkdir "%ARCHIVE_DIR%\language_restructure"
if not exist "%BACKUP_DIR%" mkdir "%BACKUP_DIR%"

echo [32m目录结构创建完成[0m
echo.

:: ================================================================
:: 创建备份
:: ================================================================
:CREATE_BACKUP
echo [33m创建完整备份...[0m

set "BACKUP_FILE=docs_backup_%date:~0,4%%date:~5,2%%date:~8,2%_%time:~0,2%%time:~3,2%%time:~6,2%.zip"
set "BACKUP_FILE=%BACKUP_FILE: =0%"

powershell -Command "Compress-Archive -Path 'docs' -DestinationPath '%BACKUP_FILE%' -Force"

if errorlevel 1 (
    echo [31m备份创建失败[0m
    pause
    exit /b 1
)

echo [32m备份创建成功: %BACKUP_FILE%[0m
echo.

:: ================================================================
:: 归档阶段报告
:: ================================================================
:ARCHIVE_PHASE_REPORTS
echo [33m归档阶段报告...[0m

set count=0
for %%f in ("%BASE_DIR%\PHASE*.md") do (
    if exist "%%f" (
        move "%%f" "%ARCHIVE_DIR%\phase_reports\" >nul
        set /a count+=1
        echo   [32m√ %%~nxf[0m
    )
)

echo [34m归档了 !count! 个阶段报告[0m
echo.

:: ================================================================
:: 归档模块报告
:: ================================================================
:ARCHIVE_MODULE_REPORTS
echo [33m归档模块报告...[0m

set count=0
for %%f in ("%BASE_DIR%\C0*.md" "%BASE_DIR%\C1*.md") do (
    set "filename=%%~nxf"
    :: 排除最新文档
    echo !filename! | findstr /C:"2025_10_30" >nul
    if errorlevel 1 (
        echo !filename! | findstr /C:"COMPLETION_2025_10_25" >nul
        if errorlevel 1 (
            if exist "%%f" (
                move "%%f" "%ARCHIVE_DIR%\module_reports\" >nul
                set /a count+=1
                echo   [32m√ %%~nxf[0m
            )
        )
    )
)

echo [34m归档了 !count! 个模块报告[0m
echo.

:: ================================================================
:: 归档计划和状态文档
:: ================================================================
:ARCHIVE_PLANNING_DOCS
echo [33m归档计划和状态文档...[0m

set count=0
for %%p in (PLAN STATUS STRATEGY ANALYSIS OUTLINE) do (
    for %%f in ("%BASE_DIR%\*%%p*.md") do (
        set "filename=%%~nxf"
        :: 排除最新重要文档
        echo !filename! | findstr /C:"REMAINING_WORK" >nul
        if errorlevel 1 (
            echo !filename! | findstr /C:"2025_10_30" >nul
            if errorlevel 1 (
                if exist "%%f" (
                    move "%%f" "%ARCHIVE_DIR%\planning\" >nul
                    set /a count+=1
                    echo   [32m√ %%~nxf[0m
                )
            )
        )
    )
)

echo [34m归档了 !count! 个计划文档[0m
echo.

:: ================================================================
:: 归档临时文档
:: ================================================================
:ARCHIVE_TEMP_DOCS
echo [33m归档临时文档...[0m

set count=0
for %%p in (TASK LINK TOC FIX FALSE) do (
    for %%f in ("%BASE_DIR%\*%%p*.md") do (
        if exist "%%f" (
            move "%%f" "%ARCHIVE_DIR%\temp\" >nul
            set /a count+=1
            echo   [32m√ %%~nxf[0m
        )
    )
)

echo [34m归档了 !count! 个临时文档[0m
echo.

:: ================================================================
:: 移动压缩包
:: ================================================================
:MOVE_ARCHIVES
echo [33m移动压缩包文件...[0m

set count=0
for %%f in ("%BASE_DIR%\*.rar" "docs\swap\*.rar") do (
    if exist "%%f" (
        move "%%f" "%BACKUP_DIR%\" >nul
        set /a count+=1
        echo   [32m√ %%~nxf[0m
    )
)

echo [34m移动了 !count! 个压缩包[0m
echo.

:: ================================================================
:: 归档 language 子目录
:: ================================================================
:ARCHIVE_LANGUAGE_DIR
echo [33m归档 language 子目录...[0m

if exist "%BASE_DIR%\language\RESTRUCTURE_WORKING" (
    xcopy "%BASE_DIR%\language\RESTRUCTURE_WORKING\*" "%ARCHIVE_DIR%\language_restructure\" /E /I /Y >nul
    echo [32mlanguage\RESTRUCTURE_WORKING 内容已归档[0m
)

echo.

:: ================================================================
:: 生成归档报告
:: ================================================================
:GENERATE_REPORT
echo [33m生成归档报告...[0m

set "REPORT_FILE=%ARCHIVE_DIR%\ARCHIVE_INDEX.md"

(
echo # 归档文档索引
echo.
echo ^> **归档日期**: %date%  
echo ^> **归档工具**: archive_docs.bat  
echo ^> **归档版本**: v1.0
echo.
echo ---
echo.
echo ## 📁 目录结构
echo.
echo ```
echo archive/
echo ├── phase_reports/           # 阶段报告 ^(PHASE*.md^)
echo ├── module_reports/          # 模块报告 ^(C02-C14 详细报告^)
echo ├── planning/                # 计划和状态文档
echo ├── temp/                    # 临时工作文档
echo └── language_restructure/    # 语言重构报告
echo ```
echo.
echo ---
echo.
echo ## 📊 归档统计
echo.
) > "%REPORT_FILE%"

for /f %%c in ('dir /b "%ARCHIVE_DIR%\phase_reports\*.md" 2^>nul ^| find /c /v ""') do (
    echo ### 阶段报告 >> "%REPORT_FILE%"
    echo 文件数: %%c >> "%REPORT_FILE%"
    echo. >> "%REPORT_FILE%"
)

for /f %%c in ('dir /b "%ARCHIVE_DIR%\module_reports\*.md" 2^>nul ^| find /c /v ""') do (
    echo ### 模块报告 >> "%REPORT_FILE%"
    echo 文件数: %%c >> "%REPORT_FILE%"
    echo. >> "%REPORT_FILE%"
)

echo [32m归档报告已生成: %REPORT_FILE%[0m
echo.

:: ================================================================
:: 显示保留的核心文档
:: ================================================================
:SHOW_REMAINING_DOCS
echo [33m保留的核心文档列表:[0m
echo.

for %%f in ("%BASE_DIR%\*.md") do (
    echo   [32m√ %%~nxf[0m
)

echo.
for /f %%c in ('dir /b "%BASE_DIR%\*.md" 2^>nul ^| find /c /v ""') do (
    echo [34m核心文档数量: %%c[0m
)
echo.

:: ================================================================
:: 显示统计信息
:: ================================================================
:SHOW_STATISTICS
echo.
echo ================================================================
echo   归档完成统计
echo ================================================================
echo.

echo [33m归档文件统计:[0m

for /f %%c in ('dir /b "%ARCHIVE_DIR%\phase_reports\*.md" 2^>nul ^| find /c /v ""') do (
    echo   阶段报告: %%c 个
)

for /f %%c in ('dir /b "%ARCHIVE_DIR%\module_reports\*.md" 2^>nul ^| find /c /v ""') do (
    echo   模块报告: %%c 个
)

for /f %%c in ('dir /b "%ARCHIVE_DIR%\planning\*.md" 2^>nul ^| find /c /v ""') do (
    echo   计划文档: %%c 个
)

for /f %%c in ('dir /b "%ARCHIVE_DIR%\temp\*.md" 2^>nul ^| find /c /v ""') do (
    echo   临时文档: %%c 个
)

for /f %%c in ('dir /b "%BACKUP_DIR%\*.rar" 2^>nul ^| find /c /v ""') do (
    echo   备份文件: %%c 个
)

echo.
echo [33m核心文档:[0m

for /f %%c in ('dir /b "%BASE_DIR%\*.md" 2^>nul ^| find /c /v ""') do (
    echo   保留文档: %%c 个
)

echo.
echo [32m文档结构优化完成！[0m
echo.

:: ================================================================
:: 完成信息
:: ================================================================
echo.
echo ================================================================
echo   🎉 归档流程完成！
echo ================================================================
echo.
echo [34m归档位置: %ARCHIVE_DIR%[0m
echo [34m备份文件: %BACKUP_FILE%[0m
echo [34m归档索引: %ARCHIVE_DIR%\ARCHIVE_INDEX.md[0m
echo.
echo [33m建议: 检查归档结果后，可以安全删除 swap 目录[0m
echo.

pause
endlocal

