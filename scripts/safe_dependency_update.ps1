# PowerShell脚本：安全依赖更新
# 用于安全地更新Rust项目依赖，包含回滚机制

param(
    [switch]$DryRun,
    [switch]$SkipTests,
    [string]$LogFile = "dependency_update.log"
)

# 设置错误处理
$ErrorActionPreference = "Stop"

# 日志函数
function Write-Log {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "[$timestamp] [$Level] $Message"
    Write-Host $logMessage
    Add-Content -Path $LogFile -Value $logMessage
}

# 检查命令是否存在
function Test-Command {
    param([string]$Command)
    try {
        Get-Command $Command -ErrorAction Stop | Out-Null
        return $true
    }
    catch {
        return $false
    }
}

# 备份文件
function Backup-Files {
    Write-Log "创建备份文件..."
    if (Test-Path "Cargo.lock") {
        Copy-Item "Cargo.lock" "Cargo.lock.backup" -Force
        Write-Log "已备份 Cargo.lock"
    }
    if (Test-Path "Cargo.toml") {
        Copy-Item "Cargo.toml" "Cargo.toml.backup" -Force
        Write-Log "已备份 Cargo.toml"
    }
}

# 回滚函数
function Restore-Backup {
    Write-Log "回滚到备份状态..." -Level "WARN"
    if (Test-Path "Cargo.lock.backup") {
        Copy-Item "Cargo.lock.backup" "Cargo.lock" -Force
        Write-Log "已恢复 Cargo.lock"
    }
    if (Test-Path "Cargo.toml.backup") {
        Copy-Item "Cargo.toml.backup" "Cargo.toml" -Force
        Write-Log "已恢复 Cargo.toml"
    }
}

# 执行cargo命令
function Invoke-CargoCommand {
    param([string]$Command, [string]$Description)
    
    Write-Log "执行: $Description"
    Write-Log "命令: cargo $Command"
    
    if ($DryRun) {
        Write-Log "模拟执行: cargo $Command" -Level "INFO"
        return $true
    }
    
    try {
        $result = Invoke-Expression "cargo $Command" 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Log "✅ $Description 成功"
            return $true
        } else {
            Write-Log "❌ $Description 失败: $result" -Level "ERROR"
            return $false
        }
    }
    catch {
        Write-Log "❌ $Description 异常: $($_.Exception.Message)" -Level "ERROR"
        return $false
    }
}

# 检查编译
function Test-Compilation {
    Write-Log "检查编译状态..."
    return Invoke-CargoCommand "check" "编译检查"
}

# 运行测试
function Test-Tests {
    if ($SkipTests) {
        Write-Log "跳过测试" -Level "WARN"
        return $true
    }
    
    Write-Log "运行测试..."
    return Invoke-CargoCommand "test" "单元测试"
}

# 主函数
function Main {
    Write-Log "=== Rust 依赖安全更新脚本 ==="
    Write-Log "开始时间: $(Get-Date)"
    Write-Log "日志文件: $LogFile"
    
    if ($DryRun) {
        Write-Log "运行模式: 模拟执行" -Level "WARN"
    }
    
    # 检查cargo是否可用
    if (-not (Test-Command "cargo")) {
        Write-Log "错误: cargo 命令不可用" -Level "ERROR"
        exit 1
    }
    
    # 检查是否在Rust项目目录
    if (-not (Test-Path "Cargo.toml")) {
        Write-Log "错误: 当前目录不是Rust项目" -Level "ERROR"
        exit 1
    }
    
    # 创建备份
    Backup-Files
    
    # 阶段1: 安全更新
    Write-Log "=== 阶段1: 安全更新 ==="
    
    $safeUpdates = @(
        @{Command = "update rustls tokio-rustls rustls-webpki rustls-pemfile"; Description = "更新rustls相关依赖"},
        @{Command = "update rand rand_chacha rand_core"; Description = "更新rand系列依赖"},
        @{Command = "update http http-body http-body-util"; Description = "更新http相关依赖"},
        @{Command = "update bytes"; Description = "更新bytes库"},
        @{Command = "update tokio tokio-util tokio-stream"; Description = "更新tokio相关依赖"}
    )
    
    foreach ($update in $safeUpdates) {
        if (-not (Invoke-CargoCommand $update.Command $update.Description)) {
            Write-Log "安全更新失败，回滚更改" -Level "ERROR"
            Restore-Backup
            exit 1
        }
    }
    
    # 测试编译
    if (-not (Test-Compilation)) {
        Write-Log "编译失败，回滚更改" -Level "ERROR"
        Restore-Backup
        exit 1
    }
    
    # 阶段2: 功能更新
    Write-Log "=== 阶段2: 功能更新 ==="
    
    $featureUpdates = @(
        @{Command = "update hickory-proto hickory-resolver"; Description = "更新DNS相关库"},
        @{Command = "update lru"; Description = "更新LRU缓存库"},
        @{Command = "update serde serde_json serde_yaml"; Description = "更新序列化库"},
        @{Command = "update tracing tracing-subscriber"; Description = "更新日志库"}
    )
    
    foreach ($update in $featureUpdates) {
        if (-not (Invoke-CargoCommand $update.Command $update.Description)) {
            Write-Log "功能更新失败，回滚更改" -Level "ERROR"
            Restore-Backup
            exit 1
        }
    }
    
    # 测试编译
    if (-not (Test-Compilation)) {
        Write-Log "编译失败，回滚更改" -Level "ERROR"
        Restore-Backup
        exit 1
    }
    
    # 阶段3: 高风险更新（需要特别测试）
    Write-Log "=== 阶段3: 高风险更新 ==="
    
    $riskyUpdates = @(
        @{Command = "update generic-array"; Description = "更新generic-array (0.14 -> 1.x)"},
        @{Command = "update base64"; Description = "更新base64库"},
        @{Command = "update url"; Description = "更新URL库"}
    )
    
    foreach ($update in $riskyUpdates) {
        Write-Log "执行高风险更新: $($update.Description)" -Level "WARN"
        if (-not (Invoke-CargoCommand $update.Command $update.Description)) {
            Write-Log "高风险更新失败，回滚更改" -Level "ERROR"
            Restore-Backup
            exit 1
        }
        
        # 每个高风险更新后都测试
        if (-not (Test-Compilation)) {
            Write-Log "高风险更新后编译失败，回滚更改" -Level "ERROR"
            Restore-Backup
            exit 1
        }
    }
    
    # 最终测试
    Write-Log "=== 最终测试 ==="
    
    if (-not (Test-Compilation)) {
        Write-Log "最终编译测试失败，回滚更改" -Level "ERROR"
        Restore-Backup
        exit 1
    }
    
    if (-not (Test-Tests)) {
        Write-Log "最终测试失败，回滚更改" -Level "ERROR"
        Restore-Backup
        exit 1
    }
    
    # 生成报告
    Write-Log "=== 生成更新报告 ==="
    
    if (-not $DryRun) {
        Invoke-CargoCommand "outdated" "检查剩余过时依赖"
        Invoke-CargoCommand "tree --duplicates" "检查依赖冲突"
        Invoke-CargoCommand "audit" "安全审计"
    }
    
    Write-Log "✅ 依赖更新完成！"
    Write-Log "结束时间: $(Get-Date)"
    
    # 清理备份文件（可选）
    $cleanup = Read-Host "是否删除备份文件？(y/N)"
    if ($cleanup -eq "y" -or $cleanup -eq "Y") {
        Remove-Item "Cargo.lock.backup" -ErrorAction SilentlyContinue
        Remove-Item "Cargo.toml.backup" -ErrorAction SilentlyContinue
        Write-Log "已清理备份文件"
    } else {
        Write-Log "备份文件已保留"
    }
}

# 显示帮助信息
function Show-Help {
    Write-Host @"
Rust 依赖安全更新脚本

用法: .\safe_dependency_update.ps1 [选项]

选项:
    -DryRun      模拟执行，不实际更新依赖
    -SkipTests   跳过测试阶段
    -LogFile     指定日志文件路径 (默认: dependency_update.log)

示例:
    .\safe_dependency_update.ps1                    # 正常更新
    .\safe_dependency_update.ps1 -DryRun           # 模拟执行
    .\safe_dependency_update.ps1 -SkipTests        # 跳过测试
    .\safe_dependency_update.ps1 -LogFile update.log # 自定义日志文件

注意事项:
    1. 脚本会自动创建备份文件
    2. 如果更新失败会自动回滚
    3. 建议在更新前提交当前更改到git
    4. 更新后请运行完整的测试套件
"@
}

# 检查参数
if ($args -contains "-h" -or $args -contains "--help") {
    Show-Help
    exit 0
}

# 执行主函数
try {
    Main
}
catch {
    Write-Log "脚本执行异常: $($_.Exception.Message)" -Level "ERROR"
    Restore-Backup
    exit 1
}
