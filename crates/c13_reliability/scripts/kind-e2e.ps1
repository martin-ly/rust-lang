param(
  [string]$ClusterName = "c13-kind",
  [string]$Namespace = "default"
)

function Exec($cmd) {
  Write-Host "==> $cmd"
  Invoke-Expression $cmd
}

Exec "kind create cluster --name $ClusterName"
Exec "kubectl cluster-info --context kind-$ClusterName"
Exec "kubectl apply -n $Namespace -f ..\deploy\k8s\c13-demo-pod.yaml"
Exec "kubectl wait --for=condition=ready pod/c13-demo -n $Namespace --timeout=120s"
Exec "kubectl get pods -n $Namespace -o wide"
Write-Host "E2E succeeded."

