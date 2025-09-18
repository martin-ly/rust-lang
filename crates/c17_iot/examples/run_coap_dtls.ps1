$ErrorActionPreference = "Stop"
Push-Location "$PSScriptRoot\..\..\.."
try {
  cargo run -p c17_iot --example coap_dtls
} finally {
  Pop-Location
}

