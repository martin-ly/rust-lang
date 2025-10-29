#!/usr/bin/env python3
"""
Rust 知识库 - 知识图谱生成器
生成模块间的依赖关系图，使用 Graphviz 可视化
"""

import re
from pathlib import Path
from collections import defaultdict
import sys

class KnowledgeGraphGenerator:
    def __init__(self, project_root):
        self.project_root = Path(project_root)
        self.links = defaultdict(list)
        self.modules = set()
        
    def extract_links_from_file(self, md_file):
        """从Markdown文件中提取内部链接"""
        try:
            with open(md_file, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # 提取Markdown链接: [text](path)
            pattern = r'\[([^\]]+)\]\(([^)]+)\)'
            matches = re.findall(pattern, content)
            
            internal_links = []
            for text, link in matches:
                # 过滤外部链接
                if not link.startswith(('http://', 'https://', 'mailto:')):
                    # 只保留.md文件的链接
                    if '.md' in link or link.startswith('../'):
                        internal_links.append((text, link))
            
            return internal_links
        except Exception as e:
            print(f"Warning: Could not process {md_file}: {e}", file=sys.stderr)
            return []
    
    def detect_module(self, file_path):
        """从文件路径检测模块名"""
        path_str = str(file_path)
        
        # 检测 crates/cXX_name 模式
        match = re.search(r'crates/(c\d+_[\w_]+)', path_str)
        if match:
            return match.group(1)
        
        # 检测 docs/ 区域
        if 'docs/' in path_str:
            if 'quick_reference' in path_str:
                return 'quick_reference'
            elif 'research_notes' in path_str:
                return 'research_notes'
            else:
                return 'docs'
        
        return 'other'
    
    def scan_repository(self):
        """扫描整个代码库，构建知识图谱"""
        print("🔍 扫描代码库...")
        
        # 扫描所有Markdown文件
        md_files = list(self.project_root.rglob('*.md'))
        
        # 过滤掉一些目录
        excluded = ['node_modules', '.git', 'target', 'book']
        md_files = [f for f in md_files if not any(ex in str(f) for ex in excluded)]
        
        print(f"📄 找到 {len(md_files)} 个Markdown文件")
        
        for md_file in md_files:
            source_module = self.detect_module(md_file)
            self.modules.add(source_module)
            
            links = self.extract_links_from_file(md_file)
            
            for text, link in links:
                # 尝试解析目标模块
                target_module = self.detect_module_from_link(link, md_file)
                if target_module and target_module != source_module:
                    self.modules.add(target_module)
                    self.links[source_module].append({
                        'target': target_module,
                        'label': text[:30]  # 限制标签长度
                    })
        
        print(f"📊 识别出 {len(self.modules)} 个模块")
        print(f"🔗 发现 {sum(len(v) for v in self.links.values())} 条链接")
    
    def detect_module_from_link(self, link, source_file):
        """从链接路径推测目标模块"""
        # 尝试解析相对路径
        try:
            source_dir = source_file.parent
            target_path = (source_dir / link).resolve()
            return self.detect_module(target_path)
        except:
            # 如果无法解析，尝试从链接字符串匹配
            match = re.search(r'c\d+_[\w_]+', link)
            if match:
                return match.group(0)
            return None
    
    def generate_dot(self):
        """生成Graphviz DOT格式"""
        dot = """digraph RustKnowledgeGraph {
    // 图形设置
    rankdir=LR;
    node [shape=box, style="rounded,filled", fillcolor=lightblue, fontname="Arial"];
    edge [fontname="Arial", fontsize=10];
    
    // 模块节点
"""
        
        # 按类型分组模块
        core_modules = sorted([m for m in self.modules if m.startswith('c0') or m.startswith('c1')])
        other_modules = sorted([m for m in self.modules if m not in core_modules])
        
        # 核心模块（特殊颜色）
        for module in core_modules:
            label = module.replace('_', '\\n')
            dot += f'    "{module}" [label="{label}", fillcolor="#FFE6CC"];\n'
        
        # 其他模块
        for module in other_modules:
            label = module.replace('_', '\\n')
            dot += f'    "{module}" [label="{label}"];\n'
        
        dot += "\n    // 连接关系\n"
        
        # 去重链接
        seen_links = set()
        for source, targets in self.links.items():
            for target_info in targets:
                target = target_info['target']
                link_key = (source, target)
                if link_key not in seen_links:
                    seen_links.add(link_key)
                    # 只添加第一个标签
                    label = target_info['label'].replace('"', '\\"')
                    dot += f'    "{source}" -> "{target}";\n'
        
        dot += "}\n"
        return dot
    
    def save_graph(self, output_file='knowledge_graph.dot'):
        """保存图谱到文件"""
        dot_content = self.generate_dot()
        
        output_path = self.project_root / output_file
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(dot_content)
        
        print(f"\n✅ 知识图谱已保存: {output_path}")
        print(f"\n📊 可视化命令:")
        print(f"   dot -Tpng {output_file} -o knowledge_graph.png")
        print(f"   dot -Tsvg {output_file} -o knowledge_graph.svg")
        print(f"   dot -Tpdf {output_file} -o knowledge_graph.pdf")
        
        # 生成统计摘要
        self.generate_summary()
    
    def generate_summary(self):
        """生成统计摘要"""
        print(f"\n📈 知识图谱统计:")
        print(f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        print(f"  模块总数: {len(self.modules)}")
        print(f"  连接总数: {sum(len(v) for v in self.links.values())}")
        
        # 最活跃的模块（出度最高）
        if self.links:
            most_linked = max(self.links.items(), key=lambda x: len(x[1]))
            print(f"  最活跃模块: {most_linked[0]} ({len(most_linked[1])} 条出链)")
        
        # 核心模块列表
        core = [m for m in self.modules if m.startswith('c0') or m.startswith('c1')]
        print(f"  核心模块: {len(core)} 个")
        for m in sorted(core):
            count = len(self.links.get(m, []))
            print(f"    - {m}: {count} 条链接")

def main():
    import os
    
    # 获取项目根目录
    script_dir = Path(__file__).parent
    project_root = script_dir.parent
    
    print("🌐 Rust 知识库 - 知识图谱生成器")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n")
    
    generator = KnowledgeGraphGenerator(project_root)
    generator.scan_repository()
    generator.save_graph()
    
    print(f"\n🎉 完成！")

if __name__ == '__main__':
    main()

