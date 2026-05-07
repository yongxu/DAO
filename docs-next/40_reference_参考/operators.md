# 算子参考

本页是算子系统的人读入口。机器事实以 `../_generated/operator-index.md` 和 Lean 源为准；本页不维护总数、分组数量或完整表格。

## 主要来源

| 来源 | 用途 |
|---|---|
| `../_generated/operator-index.md` | 当前算子索引、分组和 code/id |
| `wenyan-operators.md` | 人工长表与文字说明 |
| `formal/SSBX/Text/WenyanOperators.lean` | 算子数据源 |
| `formal/SSBX/Text/OperatorReadings.lean` | 读法登记 |
| `formal/SSBX/Text/OperatorSignatures.lean` | 签名和形态 |
| `formal/SSBX/Text/OperatorCellMap.lean` | 单元映射 |
| `formal/SSBX/Foundation/Wen/Operators.lean` | Wen 层算子接口 |

## 读表方法

每个算子至少有四个层面：

| 层面 | 问题 | 审计入口 |
|---|---|---|
| 文字 | 这个字或短语如何写 | `wenyan-operators.md` |
| code/id | 它在表中如何定位 | `../_generated/operator-index.md` |
| 签名 | 它怎样接收和产生结构 | `OperatorSignatures.lean` |
| 语义 | 它在候选 cell 或 family 中怎样解释 | `Operator*Semantics.lean` |

## 分组口径

算子分组是阅读与审计工具，不是宣称传统文献天然如此分类。常见组别包括关系、容纳、转化、流动、起止、量词、因果、模态、否定、同异、句法、核心义理、墨经、名家、时间副词等。完整 group 列表以生成索引为准。

## 与义理的关系

- `义理/D_算子代数.md` 和 `义理/G_完整算子系统_八卦互通与归一.md` 是旧解释入口。
- 新版义理只摘要结构，不复制长表。
- 若旧别名表与生成索引冲突，先信任生成索引，再回到 Lean 源确认。
- 算子出现于图或 claim 时，仍需查对应 theorem 或 registry 状态。

## 维护规则

- 不在本页手写完整算子清单。
- 不把同字复用自动解释为同一语义；复用要看 id、group 和 reading。
- 不把 operator table complete 误读成所有自然语言句子可解析。
- 新增算子后应重新生成 `../_generated/operator-index.md`，再检查本页是否需要补充入口。
