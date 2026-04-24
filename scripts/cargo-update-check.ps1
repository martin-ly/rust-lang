<#
.SYNOPSIS
    Cargo update automation check script
.DESCRIPTION
    Runs cargo update, generates report, and optionally runs cargo audit.
    Supports --dry-run mode.
.PARAMETER DryRun
    Show packages that would be updated without applying changes
#>
[CmdletBinding()]
param([switch]$DryRun)

$ErrorActionPreference = "Stop"
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Resolve-Path (Join-Path $scriptDir "..")
Set-Location $projectRoot

$report = [System.Collections.Generic.List[string]]::new()
function Add-ReportLine($Line) {
    $report.Add($Line)
    Write-Host $Line
}

Add-ReportLine "========================================"
Add-ReportLine "Cargo Update Check Report"
Add-ReportLine "Date: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
Add-ReportLine "Project: $projectRoot"
Add-ReportLine "Mode: $(if ($DryRun) { 'DRY-RUN' } else { 'LIVE' })"
Add-ReportLine "========================================"

# Verify cargo
try {
    $cv = cargo --version 2>$null
    Add-ReportLine "Cargo: $cv"
} catch {
    Write-Error "cargo not found"
    exit 1
}

# Outdated check
$hasOutdated = [bool](Get-Command cargo-outdated -ErrorAction SilentlyContinue)
if ($hasOutdated) {
    Add-ReportLine ""
    Add-ReportLine "--- Outdated Packages ---"
    try {
        $out = cargo outdated -R 2>&1
        $out | ForEach-Object { Add-ReportLine "$_" }
    } catch { Add-ReportLine "cargo outdated failed: $_" }
} else {
    Add-ReportLine "Note: cargo-outdated not installed"
}

# Cargo update
Add-ReportLine ""
Add-ReportLine "--- cargo update $(if ($DryRun) { '--dry-run' }) ---"
$updateArgs = @("update"); if ($DryRun) { $updateArgs += "--dry-run" }
$updateOutput = & cargo @updateArgs 2>&1
$updated = @()
$locked = @()
foreach ($line in $updateOutput) {
    $s = "$line"
    if ($s -match '^\s+Updating\s+(\S+)\s+v?([\d\.\-+a-zA-Z]+)\s+->\s+v?([\d\.\-+a-zA-Z]+)') {
        $updated += [PSCustomObject]@{ Package=$matches[1]; Old=$matches[2]; New=$matches[3] }
    } elseif ($s -match '^\s+Locking\s') { $locked += $s.Trim() }
}
if ($updated.Count -gt 0) {
    Add-ReportLine "Packages Updated:"
    $updated | ForEach-Object { Add-ReportLine ("  {0,-40} {1,-20} -> {2}" -f $_.Package, $_.Old, $_.New) }
} else {
    Add-ReportLine "No packages were updated."
}
if ($locked.Count -gt 0) {
    Add-ReportLine "Locked/Unchanged count: $($locked.Count)"
}

# Audit
Add-ReportLine ""
Add-ReportLine "--- Security Audit ---"
$hasAudit = [bool](Get-Command cargo-audit -ErrorAction SilentlyContinue)
if ($hasAudit) {
    try {
        $aout = cargo audit 2>&1
        $aout | ForEach-Object { Add-ReportLine "$_" }
    } catch { Add-ReportLine "cargo audit failed: $_" }
} else {
    Add-ReportLine "Note: cargo-audit not installed"
}

# Recommendations
Add-ReportLine ""
Add-ReportLine "--- Recommendations ---"
Add-ReportLine "  libp2p  - verify hickory-resolver compatibility before upgrading to 0.56+"
Add-ReportLine "  dioxus  - check for stable releases when upgrading from RC"
Add-ReportLine "  sea-orm - 2.0.0 is still in RC; verify API stability before upgrading"
Add-ReportLine "  bincode - keep pinned at 2.0.1 until 3.0 stable is released"

Add-ReportLine ""
Add-ReportLine "========================================"
Add-ReportLine "Report Complete"
Add-ReportLine "========================================"

$outFile = Join-Path $projectRoot "target" "cargo-update-report-$(Get-Date -Format 'yyyyMMdd-HHmmss').txt"
New-Item -ItemType Directory -Force -Path (Split-Path $outFile) | Out-Null
$report | Out-File -FilePath $outFile -Encoding UTF8
Add-ReportLine ""
Add-ReportLine "Report saved to: $outFile"
