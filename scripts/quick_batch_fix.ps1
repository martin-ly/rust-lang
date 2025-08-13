Param(
    [Parameter(Mandatory=$true, Position=0)]
    [string]$TargetDir,

    [switch]$DryRun,
    [switch]$NoBackup
)

$ErrorActionPreference = "Stop"

function Write-Info($msg) { Write-Host "[INFO] $msg" -ForegroundColor Cyan }
function Write-Success($msg) { Write-Host "[SUCCESS] $msg" -ForegroundColor Green }
function Write-WarningMsg($msg) { Write-Host "[WARNING] $msg" -ForegroundColor Yellow }
function Write-ErrorMsg($msg) { Write-Host "[ERROR] $msg" -ForegroundColor Red }

if (-not (Test-Path $TargetDir)) {
    Write-ErrorMsg "目标目录不存在: $TargetDir"
    exit 1
}

Write-Info "开始快速批量修复..."
Write-Info "目标目录: $TargetDir"
Write-Info "试运行: $($DryRun.IsPresent)"
Write-Info "备份: $(-not $NoBackup.IsPresent)"

# 编译工具
Write-Info "编译修正工具..."
Push-Location tools
try {
    cargo build --release | Write-Output
}
catch {
    Pop-Location
    Write-ErrorMsg "工具编译失败: $_"
    exit 1
}
Pop-Location

$terminologyFixer = Join-Path (Join-Path tools target\release) "terminology_fixer.exe"
$structureChecker = Join-Path (Join-Path tools target\release) "structure_checker.exe"

if (-not (Test-Path $terminologyFixer)) {
    Write-ErrorMsg "术语修正工具未找到: $terminologyFixer"
    exit 1
}
if (-not (Test-Path $structureChecker)) {
    Write-ErrorMsg "结构检查工具未找到: $structureChecker"
    exit 1
}

# 构建参数
$termArgs = @()
if ($DryRun) { $termArgs += "--dry-run" }
if ($NoBackup) { $termArgs += "--no-backup" }

# 执行术语修正
Write-Info "步骤1: 执行术语标准化..."
& $terminologyFixer $TargetDir @termArgs
Write-Success "术语修正完成!"

# 执行结构检查
Write-Info "步骤2: 执行结构检查..."
& $structureChecker $TargetDir
Write-Success "结构检查完成!"

# 汇总报告
$termReport = Join-Path $TargetDir "terminology_fix_report.md"
$structReport = Join-Path $TargetDir "structure_check_report.md"
$comprehensive = Join-Path $TargetDir "quick_batch_fix_report.md"

"# 快速批量修复综合报告`n" +
"执行时间: $(Get-Date) `n" +
"目标目录: $TargetDir `n" +
"试运行: $($DryRun.IsPresent) `n" +
"备份: $(-not $NoBackup.IsPresent) `n`n" +
"## 术语修正`n" +
"报告: $termReport `n`n" +
"## 结构检查`n" +
"报告: $structReport `n" |
    Set-Content -Path $comprehensive -Encoding UTF8

Write-Success "综合报告已生成: $comprehensive"

Write-Host ""
Write-Success "快速批量修复执行完成!" 