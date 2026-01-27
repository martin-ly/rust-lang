# 全工作区测试脚本 - 用于达成「狭义 100%」
# 使用独立 target 目录，避免与 IDE/其它 Cargo 进程争用主 target
# 若项目内 target_run_tests 不可写，自动改用 %TEMP%\rust-lang-test
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
$targetTEMP = Join-Path $env:TEMP "rust-lang-test"
# 优先用项目内目录；若不存在则创建，创建失败则用 TEMP
$targetDir = $targetInRepo
try {
    if (-not (Test-Path $targetInRepo)) { New-Item -ItemType Directory -Path $targetInRepo -Force | Out-Null }
} catch {
    $targetDir = $targetTEMP
    if (-not (Test-Path $targetTEMP)) { New-Item -ItemType Directory -Path $targetTEMP -Force | Out-Null }
    Write-Host "使用 TEMP 目录: $targetDir" -ForegroundColor Yellow
}
$env:CARGO_TARGET_DIR = $targetDir
Push-Location $root
try {
    Write-Host "CARGO_TARGET_DIR=$targetDir" -ForegroundColor Cyan
    Write-Host "执行: cargo test --workspace --tests" -ForegroundColor Cyan
    cargo test --workspace --tests
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
