#requires -RunAsAdministrator
param(
    [switch]$WithNpcap = $true,
    [switch]$InstallNasm = $false,
    [switch]$WithNpcapSdk = $true,
    [string]$NpcapSdkUrl = "https://npcap.com/dist/npcap-sdk-1.13.zip"
)

Write-Host "[c10] Windows 环境准备: CMake / VS Build Tools / Npcap / NASM (可选)" -ForegroundColor Cyan

function Ensure-Winget {
    if (!(Get-Command winget -ErrorAction SilentlyContinue)) {
        Write-Error "未检测到 winget，请更新到 Windows 11 或安装 App Installer 后重试。"
        exit 1
    }
}

function Install-IfMissing($id, $name) {
    Write-Host "[c10] 检查: $name" -ForegroundColor Yellow
    $exists = winget list --id $id 2>$null | Select-String $id
    if (!$exists) {
        Write-Host "[c10] 安装: $name" -ForegroundColor Green
        winget install --id $id --accept-source-agreements --accept-package-agreements -h
    } else {
        Write-Host "[c10] 已安装: $name" -ForegroundColor Green
    }
}

function Install-ChocoIfMissing {
    if (!(Get-Command choco -ErrorAction SilentlyContinue)) {
        Write-Host "[c10] 安装 Chocolatey" -ForegroundColor Yellow
        Set-ExecutionPolicy Bypass -Scope Process -Force
        [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072
        Invoke-Expression ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))
    }
}

Ensure-Winget

# 1) CMake
Install-IfMissing -id "Kitware.CMake" -name "CMake"

# 2) VS Build Tools（含 C++）
Install-IfMissing -id "Microsoft.VisualStudio.2022.BuildTools" -name "VS Build Tools 2022"

# 3) Npcap（可交互/静默），使用官方安装器
if ($WithNpcap) {
    $npcapUrl = "https://npcap.com/dist/npcap-1.79.exe"
    $tmp = Join-Path $env:TEMP "npcap.exe"
    if (!(Test-Path $tmp)) {
        Write-Host "[c10] 下载 Npcap..." -ForegroundColor Yellow
        Invoke-WebRequest -Uri $npcapUrl -OutFile $tmp
    }
    Write-Host "[c10] 安装 Npcap (WinPcap 兼容, 安装驱动需要管理员)..." -ForegroundColor Yellow
    & $tmp /S /winpcap_mode=yes | Out-Null
}

# 4) NASM（可选）
if ($InstallNasm) {
    Install-ChocoIfMissing
    choco install nasm -y
}

# 5) Npcap SDK（用于链接 Packet.lib/wpcap.lib）
if ($WithNpcapSdk) {
    try {
        $sdkRoot = Join-Path ${env:ProgramFiles} "Npcap-SDK"
        if (!(Test-Path $sdkRoot)) {
            New-Item -ItemType Directory -Force -Path $sdkRoot | Out-Null
        }
        $zipPath = Join-Path $env:TEMP "npcap-sdk.zip"
        Write-Host "[c10] 下载 Npcap SDK..." -ForegroundColor Yellow
        Invoke-WebRequest -Uri $NpcapSdkUrl -OutFile $zipPath
        Write-Host "[c10] 解压 Npcap SDK 至 $sdkRoot" -ForegroundColor Yellow
        Add-Type -AssemblyName System.IO.Compression.FileSystem
        [System.IO.Compression.ZipFile]::ExtractToDirectory($zipPath, $sdkRoot, $true)
        Remove-Item $zipPath -Force -ErrorAction SilentlyContinue

        # SDK 常见结构：Include、Lib\x64
        $includeDir = Join-Path $sdkRoot "Include"
        $libDir = Join-Path (Join-Path $sdkRoot "Lib") "x64"
        if (Test-Path $includeDir -and (Test-Path $libDir)) {
            Write-Host "[c10] 设置系统环境变量 NPCAP_DIR/INCLUDE/LIB" -ForegroundColor Green
            [Environment]::SetEnvironmentVariable("NPCAP_DIR", $sdkRoot, "Machine")
            # 追加 INCLUDE / LIB（保留现有值）
            $curInc = [Environment]::GetEnvironmentVariable("INCLUDE", "Machine")
            $curLib = [Environment]::GetEnvironmentVariable("LIB", "Machine")
            $newInc = if ($curInc) { "$includeDir;$curInc" } else { $includeDir }
            $newLib = if ($curLib) { "$libDir;$curLib" } else { $libDir }
            [Environment]::SetEnvironmentVariable("INCLUDE", $newInc, "Machine")
            [Environment]::SetEnvironmentVariable("LIB", $newLib, "Machine")
        } else {
            Write-Warning "未在 $sdkRoot 下发现 Include/Lib\\x64，请检查 SDK 包结构或版本。"
        }
    } catch {
        Write-Warning "Npcap SDK 安装失败：$($_.Exception.Message)"
    }
}

# 6) 清理潜在干扰变量
if ($env:AWS_LC_SYS_NO_ASM -eq '1') {
    Write-Host "[c10] 检测到 AWS_LC_SYS_NO_ASM=1，建议清除后重开终端。" -ForegroundColor Yellow
}

Write-Host "[c10] 完成。请重启管理员 PowerShell 确保环境变量生效。" -ForegroundColor Cyan


