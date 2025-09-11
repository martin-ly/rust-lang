#!/usr/bin/env bash
set -euo pipefail

CN="${1:-localhost}"
ROOT="$(dirname "$0")/../examples/certs"
mkdir -p "$ROOT"
cd "$ROOT"

# CA
openssl genrsa -out ca.key 2048
openssl req -x509 -new -nodes -key ca.key -subj "/CN=${CN} CA" -days 3650 -out ca.crt

# Server
openssl genrsa -out server.key 2048
openssl req -new -key server.key -subj "/CN=${CN}" -out server.csr
openssl x509 -req -in server.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out server.crt -days 825 -sha256

# Client
openssl genrsa -out client.key 2048
openssl req -new -key client.key -subj "/CN=client" -out client.csr
openssl x509 -req -in client.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out client.crt -days 825 -sha256

echo "certs generated at ${ROOT}"


