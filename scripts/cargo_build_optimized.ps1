#!/usr/bin/env pwsh
# Cargo 编译优化脚本
# 用法: ./scripts/cargo-build-optimized.ps1 [check|build|test|clean-cache|stats]

param(
    [Parameter(Position=0)]
    [ValidateSet("check", "build", "test", "clean-cache", "stats", "install-tools")]
    [string]$Command = "check",
    
    [Parameter(Position=1)]
    [string]$Profile = "dev"
)

$ErrorActionPreference = "Stop"

# 颜色输出函数
function Write-Info($msg) { Write-Host "[INFO] $msg" -ForegroundColor Cyan }
function Write-Success($msg) { Write-Host "[OK] $msg" -ForegroundColor Green }
function Write-Warning($msg) { Write-Host "[WARN] $msg" -ForegroundColor Yellow }

# 设置编译优化环境变量
function Set-BuildOptimizations {
    # 使用所有CPU核心
    $cores = (Get-CimInstance -ClassName Win32_Processor).NumberOfLogicalProcessors
    $jobs = [Math]::Max(1, $cores - 1)
    $env:CARGO_BUILD_JOBS = $jobs
    Write-Info "设置并行编译作业数: $jobs (检测到的核心数: $cores)"
    
    # 启用sccache (如果已安装)
    if (Get-Command sccache -ErrorAction SilentlyContinue) {
        $env:RUSTC_WRAPPER = "sccache"
        Write-Info "启用 sccache 缓存"
    } else {
        Write-Warning "sccache 未安装，建议安装: cargo install sccache"
    }
    
    # 内存优化 - 限制LLVM内存使用
    $env:LLVM_SYS_170_PREFIX = ""
    
    # 链接时优化
    $env:CARGO_PROFILE_DEV_LTO = "off"
    $env:CARGO_PROFILE_RELEASE_LTO = "thin"
}

# 显示编译统计
function Show-BuildStats {
    Write-Info "========== 编译统计信息 =========="
    
    # 项目统计
    $crateCount = (Get-ChildItem -Path "crates" -Directory).Count
    Write-Host "Workspace crates: $crateCount"
    
    # 依赖统计
    $depCount = (cargo tree --prefix=none 2>$null | Measure-Object).Count
    Write-Host "Total dependencies: ~$depCount"
    
    # 缓存统计 (sccache)
    if (Get-Command sccache -ErrorAction SilentlyContinue) {
        Write-Host "`nsccache 统计:"
        sccache --show-stats | Select-String -Pattern "Cache hits|Cache misses|Cache size"
    }
    
    # target目录大小
    if (Test-Path "target") {
        $targetSize = (Get-ChildItem -Recurse target -ErrorAction SilentlyContinue | 
                      Measure-Object -Property Length -Sum).Sum / 1MB
        Write-Host "`ntarget directory size: $([math]::Round($targetSize, 2)) MB"
    }
    
    # 编译时间文件
    if (Test-Path ".cargo-build-times") {
        Write-Host "`n历史编译时间:"
        Get-Content .cargo-build-times | Select-Object -Last 10
    }
}

# 清理缓存
function Clear-BuildCache {
    Write-Info "清理编译缓存..."
    
    # 清理cargo缓存
    cargo clean
    
    # 清理sccache
    if (Get-Command sccache -ErrorAction SilentlyContinue) {
        sccache --stop-server 2>$null
        sccache --start-server
        Write-Success "sccache 已重启"
    }
    
    # 清理旧的目标文件
    if (Test-Path "target") {
        Remove-Item -Recurse -Force target -ErrorAction SilentlyContinue
        Write-Success "target 目录已清理"
    }
}

# 安装推荐工具
function Install-BuildTools {
    Write-Info "安装编译优化工具..."
    
    $tools = @(
        @{ Name = "sccache"; Desc = "编译缓存" },
        @{ Name = "cargo-bloat"; Desc = "分析二进制大小" },
        @{ Name = "cargo-tree"; Desc = "依赖树查看" },
        @{ Name = "cargo-expand"; Desc = "宏展开" },
        @{ Name = "cargo-cache"; Desc = "缓存管理" }
    )
    
    foreach ($tool in $tools) {
        $name = $tool.Name
        $desc = $tool.Desc
        
        if (-not (Get-Command $name -ErrorAction SilentlyContinue)) {
            Write-Info "安装 $name ($desc)..."
            cargo install $name
        } else {
            Write-Success "$name 已安装"
        }
    }
}

# 主函数
function Main {
    Set-BuildOptimizations
    
    switch ($Command) {
        "check" {
            Write-Info "执行快速检查 (cargo check --profile check-fast)..."
            $sw = [System.Diagnostics.Stopwatch]::StartNew()
            cargo check --profile check-fast
            $sw.Stop()
            Write-Success "检查完成，耗时: $($sw.Elapsed.ToString('mm\:ss\.fff'))"
            "$([DateTime]::Now): check-fast - $($sw.Elapsed)" | Add-Content .cargo-build-times
        }
        
        "build" {
            Write-Info "执行优化构建 (profile: $Profile)..."
            $sw = [System.Diagnostics.Stopwatch]::StartNew()
            cargo build --profile $Profile
            $sw.Stop()
            Write-Success "构建完成，耗时: $($sw.Elapsed.ToString('mm\:ss\.fff'))"
            "$([DateTime]::Now): build-$Profile - $($sw.Elapsed)" | Add-Content .cargo-build-times
        }
        
        "test" {
            Write-Info "执行测试..."
            $sw = [System.Diagnostics.Stopwatch]::StartNew()
            cargo test --profile test
            $sw.Stop()
            Write-Success "测试完成，耗时: $($sw.Elapsed.ToString('mm\:ss\.fff'))"
        }
        
        "clean-cache" {
            Clear-BuildCache
        }
        
        "stats" {
            Show-BuildStats
        }
        
        "install-tools" {
            Install-BuildTools
        }
    }
}

Main
