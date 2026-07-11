#!/usr/bin/env python3
"""修复 00_meta/ 和 README.md 等元文件的低质量英文摘要。"""

import glob
import re
import os

META_DESC = {
    'concept_index': 'Global concept index providing cross-layer navigation and topic lookup.',
    'learning_guide': 'Structured learning path from beginner to expert Rust concepts.',
    'LEARNING_MVP_PATH': 'Minimum viable learning path for rapid Rust skill acquisition.',
    'audit_checklist': 'Quality assurance checklist for maintaining knowledge base consistency.',
    'concept_audit_guide': 'Guide to auditing concept files for accuracy and completeness.',
    'self_assessment': 'Self-assessment quizzes to gauge Rust proficiency across Bloom levels.',
    'quick_reference': 'Quick-reference cards for Rust syntax, patterns, and standard library.',
    'methodology': 'Methodology for knowledge representation and structural organization.',
    'sources': 'Authoritative source mapping and citation management for Rust concepts.',
    'todos': 'Global task tracking and content development roadmap.',
    'inter_layer_map': 'Cross-layer knowledge graph mapping concept dependencies.',
    'semantic_space': 'Semantic expressiveness analysis and representation space mapping.',
    'semantic_bridge_algorithms_patterns': 'Semantic bridge connecting algorithms to design patterns.',
    'boundary_extension_tree': 'Safety boundary extension reasoning and risk compensation analysis.',
    'career_landscape': 'Rust career market analysis: salaries, roles, and skill demand.',
    'cognitive_dimension_matrix': 'Cognitive dimension matrix mapping Bloom to Krathwohl taxonomies.',
    'competency_graph': 'Competency graph modeling skill dependencies and progression paths.',
    'cross_reference_matrix': 'Cross-reference matrix tracking inter-file concept links.',
    'authority_source_map': 'Map of authoritative sources for Rust language and ecosystem.',
    'bloom_taxonomy': 'Bloom taxonomy adaptation for Rust cognitive skill assessment.',
    'expressiveness_multiview': 'Multi-view analysis of Rust language expressiveness.',
    'fault_tree_analysis_collection': 'Collection of fault tree analyses for Rust safety.',
    'grading_system': 'Four-level content grading system for audience-targeted documentation.',
    'kg_ontology': 'Knowledge graph ontology for Rust concept relationships.',
    'knowledge_mindmap': 'Visual mindmap of the Rust knowledge base structure.',
    'navigation': 'Navigation guide for the layered concept knowledge base.',
    'paradigm_transition_matrix': 'Matrix mapping paradigm transitions across language generations.',
    'problem_graph': 'Problem-solution graph for Rust learning and troubleshooting.',
    'quality_dashboard_v2': 'Quality dashboard v2 for tracking documentation health metrics.',
    'rustbelt_predicate_map': 'Predicate mapping for RustBelt formal verification.',
    'decidability_spectrum': 'Decidability spectrum of Rust type system and borrow checker.',
    'comprehensive_rust_mapping': 'Comprehensive mapping of Rust concepts to learning outcomes.',
    'inter_layer_topology': 'Topology of inter-layer concept relationships and flows.',
    'intra_layer_model_map': 'Intra-layer model map showing concept clustering within layers.',
    'asp_marking_guide': 'A/S/P three-dimensional cognitive marking specification.',
    '00_before_formal': 'Cognitive cliff buffer guiding readers before entering formal methods.',
}

def fix_summary(path, content):
    summary_match = re.search(r'(\*\*Summary\*\*:\s*)(.+?)(?=\n>|\n#|\Z)', content, re.DOTALL)
    if not summary_match:
        return None, "no summary"
    
    summary_val = summary_match.group(2).strip()
    if 'Core Rust concept:' not in summary_val and 'Core Rust concept: README' not in summary_val:
        return None, "not bad format"
    
    base = os.path.basename(path).replace('.md', '')
    
    # 检查 META_DESC
    desc = META_DESC.get(base)
    
    # README.md 特殊处理
    if base == 'README':
        parent = os.path.basename(os.path.dirname(path))
        layer_names = {
            '00_meta': 'Meta layer',
            '01_foundation': 'L1 Foundation layer',
            '02_intermediate': 'L2 Intermediate layer',
            '03_advanced': 'L3 Advanced layer',
            '04_formal': 'L4 Formal methods layer',
            '05_comparative': 'L5 Comparative analysis layer',
            '06_ecosystem': 'L6 Ecosystem layer',
            '07_future': 'L7 Future trends layer',
        }
        layer = layer_names.get(parent, parent)
        desc = f'{layer} overview and navigation hub.'
    
    if not desc:
        # 尝试从第一段正文提取前 10 个词
        body = re.search(r'\n##?\s+(.+?)(?=\n##|\Z)', content, re.DOTALL)
        if body:
            first_line = body.group(1).strip().split('\n')[0]
            first_line = re.sub(r'[#\*\`\|\[\]\(\)]', '', first_line)
            words = first_line.split()[:12]
            if len(words) >= 5:
                desc = ' '.join(words) + '.'
    
    if not desc:
        # 回退：基于文件名生成
        clean = base.replace('_', ' ').replace('-', ' ').title()
        desc = f'Guide to {clean}.'
    
    # 提取 EN 字段或主题
    en_match = re.search(r'\*\*EN\*\*:\s*(.+?)(?=\n>|\n#)', content)
    topic = en_match.group(1).strip() if en_match else base.replace('_', ' ').title()
    topic = topic.split('（')[0].strip()
    
    new_summary = f'{topic}. {desc}'
    
    prefix = summary_match.group(1)
    old_block = summary_match.group(0)
    new_block = prefix + new_summary
    
    new_content = content.replace(old_block, new_block, 1)
    return new_content, new_summary

def main():
    files = glob.glob('concept/**/*.md', recursive=True)
    files = [f for f in files if 'archive' not in f]
    
    fixed = 0
    skipped = 0
    
    for path in files:
        try:
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            new_content, msg = fix_summary(path, content)
            if new_content:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(new_content)
                fixed += 1
                if fixed <= 3:
                    print(f"[FIXED] {path}")
                    print(f"        → {msg}")
            else:
                skipped += 1
        except Exception as e:
            print(f"ERROR {path}: {e}")
    
    print(f"\nFixed: {fixed}, Skipped: {skipped}")

if __name__ == '__main__':
    main()
