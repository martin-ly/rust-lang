//! # 模块系统改进 / Module System Improvements
//!
//! Rust 1.89 在模块系统方面进行了重要改进，包括更好的模块解析、
//! 改进的模块可见性和更灵活的模块组织。
//!
//! Rust 1.89 has made important improvements in the module system, including
//! better module resolution, improved module visibility, and more flexible module organization.

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

/// 模块解析器 / Module Resolver
///
/// 提供模块解析和加载功能。
/// Provides module resolution and loading functionality.
pub struct ModuleResolver {
    module_cache: HashMap<String, Arc<Module>>,
    search_paths: Vec<String>,
    resolution_strategy: ResolutionStrategy,
}

/// 模块 / Module
#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub path: String,
    pub visibility: ModuleVisibility,
    pub dependencies: Vec<ModuleDependency>,
    pub exports: Vec<ModuleExport>,
    pub imports: Vec<ModuleImport>,
    pub metadata: ModuleMetadata,
}

/// 模块可见性 / Module Visibility
#[derive(Debug, Clone, PartialEq)]
pub enum ModuleVisibility {
    /// 公开 / Public
    Public,
    /// 私有 / Private
    Private,
    /// 受限 / Restricted
    Restricted(Vec<String>),
    /// 内部 / Internal
    Internal,
}

/// 模块依赖 / Module Dependency
#[derive(Debug, Clone)]
pub struct ModuleDependency {
    pub name: String,
    pub version: String,
    pub dependency_type: DependencyType,
    pub is_optional: bool,
}

/// 依赖类型 / Dependency Type
#[derive(Debug, Clone, PartialEq)]
pub enum DependencyType {
    /// 直接依赖 / Direct Dependency
    Direct,
    /// 传递依赖 / Transitive Dependency
    Transitive,
    /// 开发依赖 / Development Dependency
    Development,
    /// 构建依赖 / Build Dependency
    Build,
}

/// 模块导出 / Module Export
#[derive(Debug, Clone)]
pub struct ModuleExport {
    pub name: String,
    pub export_type: ExportType,
    pub visibility: ModuleVisibility,
    pub documentation: Option<String>,
}

/// 导出类型 / Export Type
#[derive(Debug, Clone, PartialEq)]
pub enum ExportType {
    /// 函数 / Function
    Function,
    /// 结构体 / Struct
    Struct,
    /// 枚举 / Enum
    Enum,
    /// 特征 / Trait
    Trait,
    /// 类型别名 / Type Alias
    TypeAlias,
    /// 常量 / Constant
    Constant,
    /// 静态变量 / Static Variable
    Static,
    /// 模块 / Module
    Module,
}

/// 模块导入 / Module Import
#[derive(Debug, Clone)]
pub struct ModuleImport {
    pub name: String,
    pub source_module: String,
    pub import_type: ImportType,
    pub alias: Option<String>,
}

/// 导入类型 / Import Type
#[derive(Debug, Clone, PartialEq)]
pub enum ImportType {
    /// 完全导入 / Full Import
    Full,
    /// 部分导入 / Partial Import
    Partial(Vec<String>),
    /// 重命名导入 / Renamed Import
    Renamed(String),
    /// 通配符导入 / Wildcard Import
    Wildcard,
}

/// 模块元数据 / Module Metadata
#[derive(Debug, Clone)]
pub struct ModuleMetadata {
    pub author: Option<String>,
    pub version: Option<String>,
    pub description: Option<String>,
    pub license: Option<String>,
    pub repository: Option<String>,
    pub documentation: Option<String>,
    pub keywords: Vec<String>,
    pub categories: Vec<String>,
}

/// 解析策略 / Resolution Strategy
#[derive(Debug, Clone, PartialEq)]
pub enum ResolutionStrategy {
    /// 严格解析 / Strict Resolution
    Strict,
    /// 宽松解析 / Loose Resolution
    Loose,
    /// 智能解析 / Smart Resolution
    Smart,
    /// 自定义解析 / Custom Resolution
    Custom(String),
}

impl ModuleResolver {
    /// 创建新的模块解析器 / Create new module resolver
    pub fn new() -> Self {
        Self {
            module_cache: HashMap::new(),
            search_paths: Vec::new(),
            resolution_strategy: ResolutionStrategy::Smart,
        }
    }

    /// 添加搜索路径 / Add search path
    pub fn add_search_path(&mut self, path: String) {
        if !self.search_paths.contains(&path) {
            self.search_paths.push(path);
        }
    }

    /// 设置解析策略 / Set resolution strategy
    pub fn set_resolution_strategy(&mut self, strategy: ResolutionStrategy) {
        self.resolution_strategy = strategy;
    }

    /// 解析模块 / Resolve module
    pub fn resolve_module(
        &mut self,
        module_name: &str,
    ) -> Result<Arc<Module>, ModuleResolutionError> {
        // 检查缓存 / Check cache
        if let Some(module) = self.module_cache.get(module_name) {
            return Ok(module.clone());
        }

        // 解析模块 / Resolve module
        let module = self.resolve_module_from_paths(module_name)?;

        // 缓存模块 / Cache module
        self.module_cache
            .insert(module_name.to_string(), module.clone());

        Ok(module)
    }

    /// 从路径解析模块 / Resolve module from paths
    fn resolve_module_from_paths(
        &self,
        module_name: &str,
    ) -> Result<Arc<Module>, ModuleResolutionError> {
        for search_path in &self.search_paths {
            let module_path = Path::new(search_path).join(format!("{}.rs", module_name));

            if module_path.exists() {
                return self.load_module_from_file(&module_path, module_name);
            }
        }

        Err(ModuleResolutionError::ModuleNotFound(
            module_name.to_string(),
        ))
    }

    /// 从文件加载模块 / Load module from file
    fn load_module_from_file(
        &self,
        path: &Path,
        name: &str,
    ) -> Result<Arc<Module>, ModuleResolutionError> {
        // 简化的模块加载 / Simplified module loading
        let module = Module {
            name: name.to_string(),
            path: path.to_string_lossy().to_string(),
            visibility: ModuleVisibility::Public,
            dependencies: Vec::new(),
            exports: Vec::new(),
            imports: Vec::new(),
            metadata: ModuleMetadata {
                author: None,
                version: None,
                description: None,
                license: None,
                repository: None,
                documentation: None,
                keywords: Vec::new(),
                categories: Vec::new(),
            },
        };

        Ok(Arc::new(module))
    }

    /// 获取模块依赖 / Get module dependencies
    pub fn get_module_dependencies(
        &self,
        module_name: &str,
    ) -> Result<Vec<ModuleDependency>, ModuleResolutionError> {
        let module = self
            .module_cache
            .get(module_name)
            .ok_or_else(|| ModuleResolutionError::ModuleNotFound(module_name.to_string()))?;

        Ok(module.dependencies.clone())
    }

    /// 获取模块导出 / Get module exports
    pub fn get_module_exports(
        &self,
        module_name: &str,
    ) -> Result<Vec<ModuleExport>, ModuleResolutionError> {
        let module = self
            .module_cache
            .get(module_name)
            .ok_or_else(|| ModuleResolutionError::ModuleNotFound(module_name.to_string()))?;

        Ok(module.exports.clone())
    }

    /// 清除缓存 / Clear cache
    pub fn clear_cache(&mut self) {
        self.module_cache.clear();
    }
}

/// 模块解析错误 / Module Resolution Error
#[derive(Debug, thiserror::Error)]
pub enum ModuleResolutionError {
    #[error("模块未找到 / Module not found: {0}")]
    ModuleNotFound(String),

    #[error("循环依赖 / Circular dependency: {0}")]
    CircularDependency(String),

    #[error("版本冲突 / Version conflict: {0}")]
    VersionConflict(String),

    #[error("权限不足 / Insufficient permissions: {0}")]
    InsufficientPermissions(String),

    #[error("解析失败 / Resolution failed: {0}")]
    ResolutionFailed(String),
}

/// 模块管理器 / Module Manager
pub struct ModuleManager {
    resolver: ModuleResolver,
    loaded_modules: HashMap<String, Arc<Module>>,
    module_graph: ModuleGraph,
}

/// 模块图 / Module Graph
#[derive(Debug, Clone)]
pub struct ModuleGraph {
    pub nodes: HashMap<String, ModuleNode>,
    pub edges: Vec<ModuleEdge>,
}

/// 模块节点 / Module Node
#[derive(Debug, Clone)]
pub struct ModuleNode {
    pub name: String,
    pub module: Arc<Module>,
    pub dependencies: Vec<String>,
    pub dependents: Vec<String>,
}

/// 模块边 / Module Edge
#[derive(Debug, Clone)]
pub struct ModuleEdge {
    pub from: String,
    pub to: String,
    pub edge_type: EdgeType,
}

/// 边类型 / Edge Type
#[derive(Debug, Clone, PartialEq)]
pub enum EdgeType {
    /// 依赖关系 / Dependency
    Dependency,
    /// 导入关系 / Import
    Import,
    /// 导出关系 / Export
    Export,
    /// 继承关系 / Inheritance
    Inheritance,
}

impl ModuleManager {
    /// 创建新的模块管理器 / Create new module manager
    pub fn new() -> Self {
        Self {
            resolver: ModuleResolver::new(),
            loaded_modules: HashMap::new(),
            module_graph: ModuleGraph {
                nodes: HashMap::new(),
                edges: Vec::new(),
            },
        }
    }

    /// 加载模块 / Load module
    pub fn load_module(&mut self, module_name: &str) -> Result<Arc<Module>, ModuleResolutionError> {
        // 检查是否已加载 / Check if already loaded
        if let Some(module) = self.loaded_modules.get(module_name) {
            return Ok(module.clone());
        }

        // 解析模块 / Resolve module
        let module = self.resolver.resolve_module(module_name)?;

        // 加载模块 / Load module
        self.loaded_modules
            .insert(module_name.to_string(), module.clone());

        // 更新模块图 / Update module graph
        self.update_module_graph(&module);

        Ok(module)
    }

    /// 更新模块图 / Update module graph
    fn update_module_graph(&mut self, module: &Module) {
        let node = ModuleNode {
            name: module.name.clone(),
            module: Arc::new(module.clone()),
            dependencies: module.dependencies.iter().map(|d| d.name.clone()).collect(),
            dependents: Vec::new(),
        };

        self.module_graph.nodes.insert(module.name.clone(), node);

        // 添加依赖边 / Add dependency edges
        for dependency in &module.dependencies {
            let edge = ModuleEdge {
                from: module.name.clone(),
                to: dependency.name.clone(),
                edge_type: EdgeType::Dependency,
            };

            self.module_graph.edges.push(edge);
        }
    }

    /// 获取模块图 / Get module graph
    pub fn get_module_graph(&self) -> &ModuleGraph {
        &self.module_graph
    }

    /// 检查循环依赖 / Check for circular dependencies
    pub fn check_circular_dependencies(&self) -> Result<(), ModuleResolutionError> {
        let mut visited = std::collections::HashSet::new();
        let mut rec_stack = std::collections::HashSet::new();

        for node_name in self.module_graph.nodes.keys() {
            if !visited.contains(node_name) {
                if self.dfs_check_cycle(node_name, &mut visited, &mut rec_stack) {
                    return Err(ModuleResolutionError::CircularDependency(format!(
                        "Circular dependency detected involving {}",
                        node_name
                    )));
                }
            }
        }

        Ok(())
    }

    /// 深度优先搜索检查循环 / DFS check for cycles
    fn dfs_check_cycle(
        &self,
        node_name: &str,
        visited: &mut std::collections::HashSet<String>,
        rec_stack: &mut std::collections::HashSet<String>,
    ) -> bool {
        visited.insert(node_name.to_string());
        rec_stack.insert(node_name.to_string());

        if let Some(node) = self.module_graph.nodes.get(node_name) {
            for dependency in &node.dependencies {
                if !visited.contains(dependency) {
                    if self.dfs_check_cycle(dependency, visited, rec_stack) {
                        return true;
                    }
                } else if rec_stack.contains(dependency) {
                    return true;
                }
            }
        }

        rec_stack.remove(node_name);
        false
    }

    /// 获取模块拓扑排序 / Get module topological sort
    pub fn get_topological_sort(&self) -> Result<Vec<String>, ModuleResolutionError> {
        self.check_circular_dependencies()?;

        let mut visited = std::collections::HashSet::new();
        let mut stack = Vec::new();

        for node_name in self.module_graph.nodes.keys() {
            if !visited.contains(node_name) {
                self.dfs_topological_sort(node_name, &mut visited, &mut stack);
            }
        }

        stack.reverse();
        Ok(stack)
    }

    /// 深度优先搜索拓扑排序 / DFS topological sort
    fn dfs_topological_sort(
        &self,
        node_name: &str,
        visited: &mut std::collections::HashSet<String>,
        stack: &mut Vec<String>,
    ) {
        visited.insert(node_name.to_string());

        if let Some(node) = self.module_graph.nodes.get(node_name) {
            for dependency in &node.dependencies {
                if !visited.contains(dependency) {
                    self.dfs_topological_sort(dependency, visited, stack);
                }
            }
        }

        stack.push(node_name.to_string());
    }
}

/// 模块工具函数 / Module Utility Functions
pub mod utils {
    use super::*;

    /// 验证模块名称 / Validate module name
    pub fn validate_module_name(name: &str) -> bool {
        !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_')
    }

    /// 规范化模块路径 / Normalize module path
    pub fn normalize_module_path(path: &str) -> String {
        path.replace("::", "/")
            .replace("\\", "/")
            .trim_start_matches('/')
            .to_string()
    }

    /// 解析模块路径 / Parse module path
    pub fn parse_module_path(path: &str) -> Vec<String> {
        path.split("::")
            .filter(|s| !s.is_empty())
            .map(|s| s.to_string())
            .collect()
    }

    /// 构建模块路径 / Build module path
    pub fn build_module_path(parts: &[String]) -> String {
        parts.join("::")
    }

    /// 检查模块可见性 / Check module visibility
    pub fn check_module_visibility(module: &Module, requester: &str) -> bool {
        match &module.visibility {
            ModuleVisibility::Public => true,
            ModuleVisibility::Private => false,
            ModuleVisibility::Restricted(allowed) => allowed.contains(&requester.to_string()),
            ModuleVisibility::Internal => true, // 简化的内部可见性检查 / Simplified internal visibility check
        }
    }

    /// 生成模块文档 / Generate module documentation
    pub fn generate_module_documentation(module: &Module) -> String {
        let mut doc = String::new();

        doc.push_str(&format!("# Module: {}\n\n", module.name));

        if let Some(description) = &module.metadata.description {
            doc.push_str(&format!("{}\n\n", description));
        }

        if !module.exports.is_empty() {
            doc.push_str("## Exports\n\n");
            for export in &module.exports {
                doc.push_str(&format!("- `{}`: {:?}\n", export.name, export.export_type));
            }
            doc.push_str("\n");
        }

        if !module.dependencies.is_empty() {
            doc.push_str("## Dependencies\n\n");
            for dependency in &module.dependencies {
                doc.push_str(&format!(
                    "- `{}` (v{})\n",
                    dependency.name, dependency.version
                ));
            }
            doc.push_str("\n");
        }

        doc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_resolver() {
        let mut resolver = ModuleResolver::new();
        resolver.add_search_path("/test/path".to_string());
        resolver.set_resolution_strategy(ResolutionStrategy::Strict);

        assert_eq!(resolver.search_paths.len(), 1);
        assert_eq!(resolver.resolution_strategy, ResolutionStrategy::Strict);
    }

    #[test]
    fn test_module_manager() {
        let manager = ModuleManager::new();

        // 测试循环依赖检查 / Test circular dependency check
        let result = manager.check_circular_dependencies();
        assert!(result.is_ok());
    }

    #[test]
    fn test_module_utils() {
        assert!(utils::validate_module_name("test_module"));
        assert!(!utils::validate_module_name("test-module"));

        let normalized = utils::normalize_module_path("::test::module::");
        assert_eq!(normalized, "test/module");

        let parts = utils::parse_module_path("test::module::submodule");
        assert_eq!(parts, vec!["test", "module", "submodule"]);

        let path = utils::build_module_path(&["test".to_string(), "module".to_string()]);
        assert_eq!(path, "test::module");
    }

    #[test]
    fn test_module_visibility() {
        let module = Module {
            name: "test_module".to_string(),
            path: "/test/path".to_string(),
            visibility: ModuleVisibility::Public,
            dependencies: Vec::new(),
            exports: Vec::new(),
            imports: Vec::new(),
            metadata: ModuleMetadata {
                author: None,
                version: None,
                description: None,
                license: None,
                repository: None,
                documentation: None,
                keywords: Vec::new(),
                categories: Vec::new(),
            },
        };

        assert!(utils::check_module_visibility(&module, "any_requester"));
    }
}
