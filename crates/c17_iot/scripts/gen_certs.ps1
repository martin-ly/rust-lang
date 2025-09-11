param(
  [string]$CN = "localhost"
)

$ErrorActionPreference = "Stop"
$root = Join-Path (Split-Path $MyInvocation.MyCommand.Path -Parent) "..\examples\certs"
New-Item -ItemType Directory -Force -Path $root | Out-Null
Push-Location $root

# 生成 CA
openssl genrsa -out ca.key 2048
openssl req -x509 -new -nodes -key ca.key -subj "/CN=$CN CA" -days 3650 -out ca.crt

# 生成服务器证书
openssl genrsa -out server.key 2048
openssl req -new -key server.key -subj "/CN=$CN" -out server.csr
openssl x509 -req -in server.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out server.crt -days 825 -sha256

# 生成客户端证书
openssl genrsa -out client.key 2048
openssl req -new -key client.key -subj "/CN=client" -out client.csr
openssl x509 -req -in client.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out client.crt -days 825 -sha256

Pop-Location
Write-Output "certs generated at $root"


