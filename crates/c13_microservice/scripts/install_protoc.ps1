# PowerShell脚本：安装Protocol Buffers编译器
# 用于Windows系统

Write-Host "正在安装Protocol Buffers编译器..." -ForegroundColor Green

# 检查是否已安装chocolatey
if (!(Get-Command choco -ErrorAction SilentlyContinue)) {
    Write-Host "正在安装Chocolatey包管理器..." -ForegroundColor Yellow
    Set-ExecutionPolicy Bypass -Scope Process -Force
    [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072
    Invoke-Expression ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))
}

# 安装protoc
Write-Host "正在安装protoc..." -ForegroundColor Yellow
choco install protoc -y

# 验证安装
Write-Host "验证protoc安装..." -ForegroundColor Yellow
protoc --version

Write-Host "Protocol Buffers编译器安装完成！" -ForegroundColor Green
Write-Host "现在可以运行 'cargo build' 来构建gRPC功能" -ForegroundColor Cyan
