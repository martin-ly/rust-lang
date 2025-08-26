# Pre-commit hook for navigation block injection
# Usage: Copy this to .git/hooks/pre-commit and make it executable

param(
    [string]$RepoRoot = (Get-Location).Path
)

Write-Host "Running navigation block pre-commit hook..."

# Check if navigation injector script exists
$scriptPath = Join-Path $RepoRoot "scripts\navigation_injector.ps1"
if (-not (Test-Path $scriptPath)) {
    Write-Host "Navigation injector script not found: $scriptPath"
    exit 1
}

# Get staged files that are .md or .rs
$stagedFiles = git diff --cached --name-only --diff-filter=A | Where-Object {
    $ext = [System.IO.Path]::GetExtension($_).ToLowerInvariant()
    $ext -eq '.md' -or $ext -eq '.rs'
}

if ($stagedFiles.Count -eq 0) {
    Write-Host "No new .md or .rs files staged. Skipping navigation injection."
    exit 0
}

Write-Host "Found $($stagedFiles.Count) new files that may need navigation blocks:"
$stagedFiles | ForEach-Object { Write-Host "  - $_" }

# Run navigation injector on staged files
try {
    $result = & $scriptPath -Root $RepoRoot 2>&1
    $exitCode = $LASTEXITCODE
    
    if ($exitCode -eq 0) {
        Write-Host "Navigation blocks injected successfully."
        
        # Re-stage files that were modified
        $modifiedFiles = $result | Where-Object { $_ -match "已更新:" }
        if ($modifiedFiles) {
            Write-Host "Re-staging modified files..."
            git add $stagedFiles
        }
        
        exit 0
    } else {
        Write-Host "Navigation injection failed with exit code: $exitCode"
        Write-Host "Output: $result"
        exit 1
    }
} catch {
    Write-Host "Error running navigation injector: $_"
    exit 1
}
