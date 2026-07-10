# OWL 2 一致性检查报告

- 生成时间：2026-07-10T10:56:51
- 知识图谱：E:\_src\rust-lang\concept\00_meta\kg_data_v2.json
- 实体总数：21

## 总体结果：❌ 失败

| 检查项 | 状态 | 说明 |
| --- | --- | --- |
| mutexWith 对称性 | ✅ | 0 条违反 |
| mutexWith 反自反性 | ✅ | 0 条违反 |
| dependsOn 无环性 | ✅ | 0 个环 |
| equivalentTo 对称性 | ❌ | 4 条违反 |
| equivalentTo 传递性 | ✅ | 0 条缺失 |
| 关系端点存在性 | ✅ | 0 条悬空 |

## mutexWith 对称性违反

✅ 无问题。

## mutexWith 反自反性违反

✅ 无问题。

## dependsOn 循环依赖

✅ 未发现 dependsOn 循环依赖。

## equivalentTo 对称性违反

- Generics equivalentTo SystemF 缺少反向边
- Lifetimes equivalentTo RegionTypes 缺少反向边
- Borrowing equivalentTo SeparationLogic 缺少反向边
- Ownership equivalentTo AffineLogic 缺少反向边

## equivalentTo 传递性缺失

✅ 无问题。

## 关系端点悬空

✅ 无问题。

## 检查方法说明

1. **对称性**：对每条 `A R B`，检查是否存在 `B R A`。
2. **反自反性**：检查是否存在 `A R A` 的自环。
3. **传递性**：计算传递闭包，检查所有 `A R C` 是否已在图中显式声明。
4. **无环性**：使用 DFS 检测有向图中的环。
5. **端点存在性**：检查关系的主体/客体是否都在实体列表中。
