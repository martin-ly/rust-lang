# 依赖版本冲突修复脚本 - 2025年1月
# 自动修复 Rust 项目中的依赖版本冲突

param(
    [switch]$DryRun,      # 仅显示将要执行的操作，不实际执行
    [switch]$Force,       # 强制修复，忽略警告
    [switch]$Clean,       # 清理 Cargo.lock 并重新生成
    [switch]$Help         # 显示帮助
)

if ($Help) {
    Write-Host @"
依赖版本冲突修复脚本

用法:
  .\fix_dependency_conflicts.ps1 [选项]

选项:
  -DryRun       仅显示将要执行的操作，不实际执行
  -Force        强制修复，忽略警告
  -Clean        清理 Cargo.lock 并重新生成
  -Help         显示此帮助信息

示例:
  .\fix_dependency_conflicts.ps1 -DryRun
  .\fix_dependency_conflicts.ps1 -Clean
  .\fix_dependency_conflicts.ps1 -Force -Clean
"@
    exit 0
}

# 颜色输出函数
function Write-ColorOutput {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    Write-Host $Message -ForegroundColor $Color
}

# 检查 cargo 是否可用
function Test-Cargo {
    try {
        $null = cargo --version
        return $true
    }
    catch {
        Write-ColorOutput "❌ Cargo 未找到，请确保 Rust 已正确安装" "Red"
        return $false
    }
}

# 检查版本冲突
function Get-VersionConflicts {
    Write-ColorOutput "🔍 检查版本冲突..." "Yellow"
    
    $conflicts = cargo tree --duplicates 2>$null
    if ($conflicts) {
        Write-ColorOutput "发现版本冲突:" "Red"
        Write-Host $conflicts
        return $true
    } else {
        Write-ColorOutput "✅ 无版本冲突" "Green"
        return $false
    }
}

# 清理 Cargo.lock
function Remove-CargoLock {
    if (Test-Path "Cargo.lock") {
        if ($DryRun) {
            Write-ColorOutput "🔍 [DRY RUN] 将删除 Cargo.lock" "Yellow"
        } else {
            Write-ColorOutput "🗑️ 删除 Cargo.lock..." "Yellow"
            Remove-Item "Cargo.lock" -Force
            Write-ColorOutput "✅ Cargo.lock 已删除" "Green"
        }
    }
}

# 更新依赖
function Update-Dependencies {
    if ($DryRun) {
        Write-ColorOutput "🔍 [DRY RUN] 将更新依赖" "Yellow"
    } else {
        Write-ColorOutput "📦 更新依赖..." "Yellow"
        cargo update
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ 依赖更新完成" "Green"
        } else {
            Write-ColorOutput "❌ 依赖更新失败" "Red"
            return $false
        }
    }
    return $true
}

# 检查编译状态
function Test-Compilation {
    if ($DryRun) {
        Write-ColorOutput "🔍 [DRY RUN] 将检查编译状态" "Yellow"
        return $true
    }
    
    Write-ColorOutput "🔨 检查编译状态..." "Yellow"
    cargo check --quiet
    if ($LASTEXITCODE -eq 0) {
        Write-ColorOutput "✅ 编译通过" "Green"
        return $true
    } else {
        Write-ColorOutput "❌ 编译失败" "Red"
        return $false
    }
}

# 主执行流程
function Main {
    Write-ColorOutput "🚀 开始依赖版本冲突修复..." "Cyan"
    
    # 检查 cargo
    if (-not (Test-Cargo)) {
        exit 1
    }
    
    # 检查版本冲突
    $hasConflicts = Get-VersionConflicts
    
    if (-not $hasConflicts -and -not $Clean) {
        Write-ColorOutput "✅ 未发现版本冲突，无需修复" "Green"
        exit 0
    }
    
    # 清理 Cargo.lock
    if ($Clean) {
        Remove-CargoLock
    }
    
    # 更新依赖
    if (-not (Update-Dependencies)) {
        exit 1
    }
    
    # 检查编译状态
    if (-not (Test-Compilation)) {
        if (-not $Force) {
            Write-ColorOutput "❌ 编译失败，请检查错误信息" "Red"
            Write-ColorOutput "💡 使用 -Force 参数强制继续" "Yellow"
            exit 1
        } else {
            Write-ColorOutput "⚠️ 编译失败，但强制继续" "Yellow"
        }
    }
    
    # 最终检查
    Write-ColorOutput "🔍 最终检查..." "Yellow"
    $finalConflicts = Get-VersionConflicts
    
    if (-not $finalConflicts) {
        Write-ColorOutput "🎉 依赖版本冲突修复完成！" "Green"
    } else {
        Write-ColorOutput "⚠️ 仍存在版本冲突，可能需要手动处理" "Yellow"
    }
}

# 执行主流程
Main
