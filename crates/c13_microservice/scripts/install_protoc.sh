#!/bin/bash
# Bash脚本：安装Protocol Buffers编译器
# 用于Linux/macOS系统

echo "正在安装Protocol Buffers编译器..."

# 检测操作系统
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    # Linux
    if command -v apt-get &> /dev/null; then
        # Ubuntu/Debian
        sudo apt-get update
        sudo apt-get install -y protobuf-compiler
    elif command -v yum &> /dev/null; then
        # CentOS/RHEL
        sudo yum install -y protobuf-compiler
    elif command -v dnf &> /dev/null; then
        # Fedora
        sudo dnf install -y protobuf-compiler
    else
        echo "不支持的Linux发行版，请手动安装protoc"
        exit 1
    fi
elif [[ "$OSTYPE" == "darwin"* ]]; then
    # macOS
    if command -v brew &> /dev/null; then
        brew install protobuf
    else
        echo "请先安装Homebrew，然后运行: brew install protobuf"
        exit 1
    fi
else
    echo "不支持的操作系统: $OSTYPE"
    exit 1
fi

# 验证安装
echo "验证protoc安装..."
protoc --version

echo "Protocol Buffers编译器安装完成！"
echo "现在可以运行 'cargo build' 来构建gRPC功能"
