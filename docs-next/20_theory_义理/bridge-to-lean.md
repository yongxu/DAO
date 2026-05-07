# 义理到 Lean

本页说明如何把义理命题接到形式层。原则很简单：义理页负责读法，生成索引负责当前事实，Lean 源码负责可检查定义与证明，信任边界负责说明哪里还依赖公理、部分函数或 opaque 常量。

必查索引：

- [../_generated/markdown-index.md](../_generated/markdown-index.md)：文档和旧入口位置。
- [../_generated/lean-index.md](../_generated/lean-index.md)：Lean 模块、声明数量、集群。
- [../_generated/operator-index.md](../_generated/operator-index.md)：文言算子表。
- [../_generated/claim-index.md](../_generated/claim-index.md)：claim 类型与状态。
- [../_generated/trust-boundary.md](../_generated/trust-boundary.md)：`partial def`、`axiom`、`opaque` 等边界。

## 五级强度

| 强度 | 可写语气 | 检查入口 |
|---|---|---|
| 导览 | 可读作、可作为入口 | markdown index |
| 结构映射 | 对应、同构候选、接口 | markdown index、operator index |
| 模块存在 | 已有形式文件承载 | lean index |
| 机器检查 | 已有 theorem、registry 或计算结果 | lean index、claim index |
| 公理依赖 | 在账本或公理下成立 | claim index、trust boundary |

不要把低一级语气写成高一级语气。尤其是“模块存在”不等于“自然语言命题已证”。

## 义理命题落点流程

1. 找旧文或新页：用 markdown index 确认命题来源，不凭记忆。
2. 判断命题类型：定义、类比、同构、案例、定理、价值公理、审计规则。
3. 找形式入口：在 lean index 搜索对应 cluster 或模块。
4. 查 claim 状态：若命题涉及“真、善、开、闭、仁、义、道、对齐”等强词，查 claim index。
5. 查边界：若涉及自指、运行、绝对、微核、递归，查 trust-boundary。
6. 回写文档语气：只写索引支持的强度。

## 常见桥接

| 义理域 | 可能模块 | 说明 |
|---|---|---|
| 八卦代数 | `Foundation/Bagua` | 八卦、算子、不变量、192、不完备 |
| 核心生成 | `Foundation/Core` | 元、对齐、演化、仁类、真道 claim 接口 |
| 八衍 | `Foundation/Eight`、`Foundation/Modern` | 数、推、测、形、映、行、识、象 |
| 间与本体 | `Foundation/Jian` | 间、本体三联、极简性、桥接 |
| 文言与微核 | `Foundation/Wen`、`Text` | 文言算子、parser、eval、自释、自举 |
| 真理账本 | `Truth`、`Model` | claim ledger、语义充分性、模型案例 |

## Claim 状态读法

[../_generated/claim-index.md](../_generated/claim-index.md) 中的状态应这样读：

| 状态 | 义理写法 |
|---|---|
| `machineChecked` | 可写“形式层已检查某项声明”，但仍要说明对象 |
| `modelComputed` | 可写“模型案例给出计算结果”，不泛化为普遍定理 |
| `ledgerDependent` | 可写“依赖账本、公理或接口”，不写成无条件证明 |

若一个旧文标题含“证明报告”，也要回到 claim index 或 Lean index 查实际状态。

## 信任边界读法

[../_generated/trust-boundary.md](../_generated/trust-boundary.md) 是防止过度宣称的最短清单。出现以下情况时，义理页必须降语气：

| 边界 | 文档语气 |
|---|---|
| `partial def` | 运行或函数有部分性，不能写成全域完备 |
| `axiom` | 结论依赖外加承诺，不能写成零假设证明 |
| `opaque` | 定义内部被隐藏，不能假装已展开 |

这不是削弱系统，而是让读者知道证明在哪里结束、承诺从哪里开始。

## 文言算子桥

算子相关命题优先查 [../_generated/operator-index.md](../_generated/operator-index.md)。该索引给出 code、group、title 和 id。义理页可解释“化、变、反、复、合、分”等常用词，但完整表不应手工复制。

写作建议：

| 情况 | 写法 |
|---|---|
| 只解释词义 | “可读作……” |
| 对应算子表 | “operator index 中列有……” |
| 对应 Lean 定义 | “Lean index 中有相关 Text 或 Wen 模块……” |
| 声称完备 | 必须同时查 claim index 的完备项 |

## 史料冻结

Lean 桥接不改变史料。传统来源、古代源流、经典出处只在旧目录或归档指针中保留。本区可以说“该旧文作为入口”，不能在此补写新考据或改动冻结材料。

## 最小引用格式

在义理页中推荐使用短引用：

- “索引入口见 `../_generated/lean-index.md`。”
- “claim 强度见 `../_generated/claim-index.md`。”
- “信任边界见 `../_generated/trust-boundary.md`。”

避免把 generated 文件内容整段复制到人工页；索引会重建，人工页只保留稳定路径和读法。
