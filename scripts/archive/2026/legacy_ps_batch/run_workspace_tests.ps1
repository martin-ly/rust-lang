# 全工作区测试脚本 - 用于达成「狭义 100%」
# 使用独立 target 目录，避免与 IDE/其它 Cargo 进程争用主 target
# 默认优先使用 %TEMP%\rust-lang-test（更不易被 IDE/杀软/权限策略影响）；必要时回退到项目内 target_run_tests
# 用法: 在项目根目录执行 .\scripts\run_workspace_tests.ps1

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
if (-not (Test-Path (Join-Path $root "Cargo.toml"))) {
    $root = $PSScriptRoot
    while ($root -and -not (Test-Path (Join-Path $root "Cargo.toml"))) { $root = Split-Path -Parent $root }
}
if (-not $root -or -not (Test-Path (Join-Path $root "Cargo.toml"))) {
    Write-Host "错误: 未在 scripts 的上级目录找到 Cargo.toml，请于仓库根目录执行。" -ForegroundColor Red
    exit 1
}

$targetInRepo = Join-Path $root "target_run_tests"
$targetTEMP = if ($env:TEMP) { Join-Path $env:TEMP "rust-lang-test" } else { $null }

# 若用户已显式设置 CARGO_TARGET_DIR，则尊重用户设置
if ($env:CARGO_TARGET_DIR) {
    $targetDir = $env:CARGO_TARGET_DIR
} else {
    # 默认优先用 TEMP（更不易被 IDE/杀软/权限策略影响）；每次运行使用独立子目录，降低锁冲突
    $stamp = Get-Date -Format "yyyyMMdd-HHmmss"
    $preferredBase = if ($targetTEMP) { $targetTEMP } else { $targetInRepo }
    $fallbackBase = if ($targetTEMP) { $targetInRepo } else { $null }

    $targetDir = Join-Path $preferredBase $stamp
    try {
        if (-not (Test-Path $preferredBase)) { New-Item -ItemType Directory -Path $preferredBase -Force | Out-Null }
        if (-not (Test-Path $targetDir)) { New-Item -ItemType Directory -Path $targetDir -Force | Out-Null }
        if ($preferredBase -eq $targetTEMP) {
            Write-Host "使用 TEMP 目录: $targetDir" -ForegroundColor Yellow
        }
    } catch {
        if (-not $fallbackBase) { throw }
        $targetDir = Join-Path $fallbackBase $stamp
        if (-not (Test-Path $fallbackBase)) { New-Item -ItemType Directory -Path $fallbackBase -Force | Out-Null }
        if (-not (Test-Path $targetDir)) { New-Item -ItemType Directory -Path $targetDir -Force | Out-Null }
        Write-Host "使用仓库目录: $targetDir" -ForegroundColor Yellow
    }

    $env:CARGO_TARGET_DIR = $targetDir
}
Push-Location $root
try {
    Write-Host "CARGO_TARGET_DIR=$targetDir" -ForegroundColor Cyan
    Write-Host "执行: cargo test --workspace --tests --locked" -ForegroundColor Cyan
    cargo test --workspace --tests --locked
    $exit = $LASTEXITCODE
    if ($exit -eq 0) {
        Write-Host "全部测试通过。狭义 100% 已达成。" -ForegroundColor Green
    } else {
        Write-Host "存在失败用例，请按输出修正后重试。" -ForegroundColor Yellow
    }
    exit $exit
} finally {
    Pop-Location
}
