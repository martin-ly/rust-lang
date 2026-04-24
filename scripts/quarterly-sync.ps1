<#
.SYNOPSIS
    每季度权威来源同步辅助脚本
.DESCRIPTION
    自动收集 Rust 生态更新信息，生成季度同步检查表填充数据。
    辅助维护者完成 QUARTERLY_SYNC_CHECKLIST.md 的填写。
#>
[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Resolve-Path (Join-Path $scriptDir "..")
Set-Location $projectRoot

$year = Get-Date -Format "yyyy"
$quarter = [Math]::Ceiling((Get-Date).Month / 3)
$reportName = "quarterly-sync-data-${year}-Q${quarter}.md"
$reportPath = Join-Path $projectRoot "target" $reportName

New-Item -ItemType Directory -Force -Path (Split-Path $reportPath) | Out-Null

$lines = [System.Collections.Generic.List[string]]::new()

function Add-Line($text) { $lines.Add($text) }

Add-Line "# 📅 季度同步数据 - ${year} Q${quarter}"
Add-Line ""
Add-Line "> 自动生成时间: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
Add-Line "> 此文件为辅助数据，请维护者核对后填入 QUARTERLY_SYNC_CHECKLIST.md"
Add-Line ""

# ===== 1. Rust 工具链信息 =====
Add-Line "## 🔧 Rust 工具链信息"
Add-Line ""
try {
    $rustc = rustc --version 2>$null
    $cargo = cargo --version 2>$null
    Add-Line "- **rustc:** $rustc"
    Add-Line "- **cargo:** $cargo"
} catch {
    Add-Line "- ⚠️ 无法获取 Rust 版本信息"
}
Add-Line ""

# ===== 2. 依赖状态 =====
Add-Line "## 📦 依赖状态"
Add-Line ""

# cargo outdated
$hasOutdated = [bool](Get-Command cargo-outdated -ErrorAction SilentlyContinue)
if ($hasOutdated) {
    Add-Line "### 过期依赖 (cargo outdated -R)"
    Add-Line "```"
    try {
        cargo outdated -R 2>&1 | ForEach-Object { Add-Line ($_.ToString()) }
    } catch { Add-Line "cargo outdated 执行失败" }
    Add-Line "```"
} else {
    Add-Line "⚠️ 未安装 cargo-outdated，跳过过期依赖检查。"
    Add-Line ""
    Add-Line '安装命令: cargo install cargo-outdated --locked'
}
Add-Line ""

# cargo audit
$hasAudit = [bool](Get-Command cargo-audit -ErrorAction SilentlyContinue)
if ($hasAudit) {
    Add-Line "### 安全审计 (cargo audit)"
    Add-Line "```"
    try {
        cargo audit 2>&1 | ForEach-Object { Add-Line ($_.ToString()) }
    } catch { Add-Line "cargo audit 执行失败" }
    Add-Line "```"
} else {
    Add-Line "⚠️ 未安装 cargo-audit，跳过安全审计。"
    Add-Line ""
    Add-Line '安装命令: cargo install cargo-audit --locked'
}
Add-Line ""

# ===== 3. 项目编译状态 =====
Add-Line "## 🔨 项目编译状态"
Add-Line ""
Add-Line "### Workspace 编译"
Add-Line "```"
try {
    cargo check --workspace --all-features 2>&1 | ForEach-Object { Add-Line ($_.ToString()) }
} catch { Add-Line "cargo check 执行失败" }
Add-Line "```"
Add-Line ""

Add-Line "### Clippy 检查"
Add-Line "```"
try {
    cargo clippy --workspace --all-features -- -D warnings 2>&1 | ForEach-Object { Add-Line ($_.ToString()) }
} catch { Add-Line "cargo clippy 执行失败或存在警告" }
Add-Line "```"
Add-Line ""

# ===== 4. 测试状态 =====
Add-Line "## 🧪 测试状态"
Add-Line ""
Add-Line "```"
try {
    cargo test --workspace --all-features 2>&1 | ForEach-Object { Add-Line ($_.ToString()) }
} catch { Add-Line "cargo test 执行失败" }
Add-Line "```"
Add-Line ""

# ===== 5. 文档构建 =====
Add-Line "## 📚 文档构建状态"
Add-Line ""
Add-Line "```"
try {
    cargo doc --workspace --no-deps --all-features 2>&1 | ForEach-Object { Add-Line ($_.ToString()) }
} catch { Add-Line "cargo doc 执行失败" }
Add-Line "```"
Add-Line ""

# ===== 6. 统计信息 =====
Add-Line "## 📊 项目统计"
Add-Line ""

# 统计 crates 数量
$crateCount = 0
if (Test-Path "crates") {
    $crateCount = (Get-ChildItem -Directory -Path "crates" | Where-Object { $_.Name -notmatch "^\." }).Count
}
Add-Line "- **Crates 数量:** $crateCount"

# 统计文档数量
$docCount = 0
if (Test-Path "docs") {
    $docCount = (Get-ChildItem -Recurse -File -Path "docs" -Filter "*.md" -ErrorAction SilentlyContinue).Count
}
Add-Line "- **文档文件数:** $docCount"

# 统计代码行数
$rsLines = 0
$rsFiles = 0
if (Test-Path "crates") {
    $rsFiles = (Get-ChildItem -Recurse -File -Path "crates" -Filter "*.rs" -ErrorAction SilentlyContinue).Count
    $rsLines = (Get-ChildItem -Recurse -File -Path "crates" -Filter "*.rs" -ErrorAction SilentlyContinue | Get-Content | Measure-Object -Line).Lines
}
Add-Line "- **Rust 源文件数:** $rsFiles"
Add-Line "- **Rust 代码行数:** $rsLines"
Add-Line ""

# ===== 7. 外部链接检查提示 =====
Add-Line "## 🔗 外部链接检查"
Add-Line ""
Add-Line "请手动运行以下命令检查文档链接有效性:"
Add-Line ""
Add-Line "```powershell"
Add-Line "# PowerShell"
Add-Line ".\scripts\check_links.ps1"
Add-Line "```"
Add-Line ""
Add-Line "```bash"
Add-Line "# Bash (Linux CI)"
Add-Line "./scripts/check_links.sh  # 如果存在"
Add-Line "```"
Add-Line ""

# ===== 8. 下季度待办提示 =====
Add-Line "## 📋 下季度关注提示"
Add-Line ""
Add-Line "请维护者关注以下事项:"
Add-Line ""
Add-Line "1. [Rust 官方博客](https://blog.rust-lang.org/) 新特性发布"
Add-Line "2. [This Week in Rust](https://this-week-in-rust.org/) 社区动态"
Add-Line "3. [RUSTSEC](https://rustsec.org/advisories/) 安全公告"
Add-Line "4. [Rust RFC 仓库](https://github.com/rust-lang/rfcs) 新合并的 RFC"
Add-Line "5. [Rust Reference](https://doc.rust-lang.org/reference/) 文档更新"
Add-Line ""

# 保存报告
$lines | Out-File -FilePath $reportPath -Encoding UTF8

Write-Host "========================================"
Write-Host "季度同步数据已生成"
Write-Host "文件: $reportPath"
Write-Host "========================================"
