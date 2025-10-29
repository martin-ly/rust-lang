#!/usr/bin/env python3
"""
生成 mdBook 所需的占位符文件
"""

import os
from pathlib import Path

# 定义模块结构
modules = {
    "c01_ownership": {
        "name": "所有权与借用",
        "description": "Rust 最核心的特性 - 内存安全的基石",
        "files": ["01_overview.md", "02_master_index.md", "03_faq.md", "04_glossary.md", "05_quick_start.md"],
        "tiers": {
            "tier1": ["README.md", "01_ownership_basics.md", "02_borrowing.md", "03_lifetimes.md"],
            "tier2": ["README.md"],
            "tier3": ["README.md"],
            "tier4": ["README.md"],
        }
    },
    "c02_type_system": {
        "name": "类型系统",
        "description": "强大的类型系统和 Trait",
        "files": ["01_overview.md", "02_master_index.md", "03_faq.md", "04_glossary.md"],
        "tiers": {
            "tier1": ["README.md", "01_type_basics.md", "02_traits.md", "03_generics.md"],
            "tier2": ["README.md"],
            "tier3": ["README.md"],
            "tier4": ["README.md"],
        }
    },
    "c03_control_fn": {
        "name": "控制流与函数",
        "description": "程序流程控制和函数式编程",
        "files": ["01_overview.md", "02_master_index.md"],
        "tiers": {
            "tier1": ["README.md", "01_conditionals.md", "02_pattern_matching.md", "03_loops.md", "04_functions.md", "05_closures.md"],
        }
    },
    "c04_generic": {
        "name": "泛型编程",
        "description": "高级泛型和抽象",
        "files": ["01_overview.md", "02_master_index.md"],
        "tiers": {
            "tier1": ["README.md", "01_associated_types.md", "02_higher_ranked_traits.md", "03_gats.md"],
        }
    },
    "c05_threads": {
        "name": "线程与并发",
        "description": "安全的并发编程",
        "files": ["01_overview.md", "02_master_index.md"],
        "tiers": {
            "tier1": ["README.md", "01_threads.md", "02_shared_state.md", "03_message_passing.md", "04_atomics.md"],
        }
    },
    "c06_async": {
        "name": "异步编程",
        "description": "现代异步编程范式",
        "files": ["01_overview.md", "02_master_index.md"],
        "tiers": {
            "tier1": ["README.md", "01_async_await.md", "02_futures.md", "03_runtime.md", "04_ecosystem.md"],
        }
    },
    "c07_process": {
        "name": "进程管理",
        "description": "系统级进程管理",
        "files": ["01_overview.md", "02_master_index.md"],
        "tiers": {
            "tier1": ["README.md", "01_process_creation.md", "02_ipc.md", "03_signals.md"],
        }
    },
    "c08_algorithms": {
        "name": "算法与数据结构",
        "description": "高性能算法实现",
        "files": ["01_overview.md", "02_master_index.md"],
        "tiers": {
            "tier1": ["README.md", "01_sorting.md", "02_searching.md", "03_graphs.md", "04_dynamic_programming.md"],
        }
    },
    "c09_design_pattern": {
        "name": "设计模式",
        "description": "Rust 中的设计模式",
        "files": ["01_overview.md", "02_master_index.md"],
        "tiers": {
            "tier1": ["README.md", "01_creational.md", "02_structural.md", "03_behavioral.md"],
            "tier2": ["README.md"],
        }
    },
    "c10_networks": {
        "name": "网络编程",
        "description": "网络应用开发",
        "files": ["01_overview.md", "02_master_index.md"],
        "tiers": {
            "tier1": ["README.md", "01_tcp_udp.md", "02_http.md", "03_websocket.md"],
            "tier2": ["README.md", "01_axum.md", "02_actix.md"],
        }
    },
    "c11_macro": {
        "name": "宏系统",
        "description": "元编程和宏",
        "files": ["01_overview.md", "02_master_index.md", "03_faq.md", "04_glossary.md"],
        "tiers": {
            "tier1": ["README.md", "01_macro_basics.md", "02_pattern_matching.md", "03_repetition.md"],
            "tier2": ["README.md", "01_derive_macros.md", "02_attribute_macros.md", "03_function_like_macros.md"],
            "tier3": ["README.md"],
        }
    },
}

# 附录文件
appendix_files = {
    "learning_paths.md": "学习路径指南",
    "cross_module.md": "跨模块学习资源",
    "references.md": "参考资料",
    "glossary.md": "术语总表",
    "contributing.md": "贡献指南",
    "changelog.md": "更新日志",
}


def create_placeholder(file_path, title, description=""):
    """创建占位符文件"""
    content = f"# {title}\n\n"
    if description:
        content += f"> {description}\n\n"
    content += "**正在建设中...**\n\n"
    content += "本文档正在从现有内容迁移，敬请期待！\n"
    
    os.makedirs(os.path.dirname(file_path), exist_ok=True)
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(content)
    print(f"Created: {file_path}")


def main():
    base_dir = Path("book/src")
    
    # 生成模块文件
    for module_id, module_info in modules.items():
        module_dir = base_dir / module_id
        
        # 创建模块根文件
        for file_name in module_info.get("files", []):
            file_path = module_dir / file_name
            if not file_path.exists():
                create_placeholder(
                    str(file_path),
                    file_name.replace('.md', '').replace('_', ' ').title(),
                    module_info["description"]
                )
        
        # 创建 tier 文件
        for tier_name, tier_files in module_info.get("tiers", {}).items():
            tier_dir = module_dir / tier_name
            for file_name in tier_files:
                file_path = tier_dir / file_name
                if not file_path.exists():
                    create_placeholder(
                        str(file_path),
                        file_name.replace('.md', '').replace('_', ' ').title(),
                        f"{module_info['name']} - {tier_name.upper()}"
                    )
    
    # 生成附录文件
    appendix_dir = base_dir / "appendix"
    for file_name, title in appendix_files.items():
        file_path = appendix_dir / file_name
        if not file_path.exists():
            create_placeholder(
                str(file_path),
                title,
                "重要参考资料"
            )
    
    print("\n✅ 所有占位符文件创建完成！")
    print(f"📁 总计创建了大量文件在 {base_dir}")


if __name__ == "__main__":
    main()

