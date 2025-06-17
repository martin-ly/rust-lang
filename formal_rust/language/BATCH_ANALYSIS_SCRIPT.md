# Rust语言形式化文档批量分析脚本

## 分析目标
系统性地分析 `/crates` 目录下所有子目录的 `docs` 文件夹内容，重构到 `/formal_rust/language` 目录下。

## 分析范围
- c01_ownership_borrow_scope/docs/
- c02_type_system/docs/
- c03_control_fn/docs/
- c04_generic/docs/
- c05_threads/docs/
- c06_async/docs/
- c07_process/docs/
- c08_algorithms/docs/
- c09_design_pattern/docs/
- c10_networks/docs/
- c11_frameworks/docs/
- c12_middlewares/docs/
- c13_microservice/docs/
- c14_workflow/docs/
- c15_blockchain/docs/
- c16_webassembly/docs/
- c17_iot/docs/
- c18_model/docs/

## 分析策略
1. **内容提取**: 读取所有markdown文件
2. **主题识别**: 识别核心知识点
3. **相关性分析**: 建立知识关联
4. **去重合并**: 消除重复内容
5. **形式化处理**: 添加数学证明
6. **重构输出**: 生成规范文档

## 执行顺序
1. 分析c01-c06 (核心语言特性)
2. 分析c07-c12 (高级特性)
3. 分析c13-c18 (应用领域)
4. 统一格式化和链接

## 质量控制
- 数学形式化证明
- 严格的逻辑推理
- 完整的代码示例
- 清晰的图表说明
- 统一的markdown格式
- 严格的目录编号
- 一致的命名规范
- 完整的内部链接

## 进度跟踪
- [ ] c01_ownership_borrow_scope
- [ ] c02_type_system
- [ ] c03_control_fn
- [ ] c04_generic
- [ ] c05_threads
- [ ] c06_async
- [ ] c07_process
- [ ] c08_algorithms
- [ ] c09_design_pattern
- [ ] c10_networks
- [ ] c11_frameworks
- [ ] c12_middlewares
- [ ] c13_microservice
- [ ] c14_workflow
- [ ] c15_blockchain
- [ ] c16_webassembly
- [ ] c17_iot
- [ ] c18_model

## 上下文保持
- 保存分析状态
- 记录已完成工作
- 标记待处理内容
- 维护依赖关系图 