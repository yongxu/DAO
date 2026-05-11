# Root Language Tree 1023 — R0-R8 分层审阅包

> 状态：draft v0.1 (2026-05-11)
> 角色：这是 `R0..R8` root language tree 的 1023-entry 审阅包。它把 1 个未分根与每一层每个 root 的 `cell` / `operator` 两种 interface reading 全部列出，让后续可以逐字审定“文言 / 中文 / English / formal logic”的命名方案。
> 父文档：[../r8-root-language-tree.md](../r8-root-language-tree.md)
> Lean 锚点：[`RootLanguageTree.lean`](../../../formal/SSBX/Foundation/Hierarchy/RootLanguageTree.lean) — 证明 `511 / 1021 / 1022 / 1023` 计数与 root role 读法；[`RootRuleKernel.lean`](../../../formal/SSBX/Foundation/Wen/RootRuleKernel.lean) — 证明 12 条 root rule 的 R8-visible 程序核。

## 计数

本文档组采用用户要求的 `1023` 审名口径：

```text
1 未分根 + 1022 interface readings = 1023 review entries
```

其中 `1022` interface 口径仍为：

```text
2 × (|R0| + |R1| + ... + |R8|)
= 2 × (1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 + 256)
= 2 × 511
= 1022
```

注意：父文档推荐的本体口径是 `1021 = R0 + 2 × (R1..R8)`，因为 R0 在 cell/operator 分化之前。这里为了完整审阅接口，故意把 R0 也列成两项，并额外列 1 个“未分根”作为总审名锚。

## 文件

| 层 | entries | 文件 |
|---|---:|---|
| 总表 | 1023 | [all-1023.md](all-1023.md) |
| 未分根 | 1 | [manifest.md](manifest.md#pre-root-entry) |
| R0 | 2 | [layers/R0.md](layers/R0.md) |
| R1 | 4 | [layers/R1.md](layers/R1.md) |
| R2 | 8 | [layers/R2.md](layers/R2.md) |
| R3 | 16 | [layers/R3.md](layers/R3.md) |
| R4 | 32 | [layers/R4.md](layers/R4.md) |
| R5 | 64 | [layers/R5.md](layers/R5.md) |
| R6 | 128 | [layers/R6.md](layers/R6.md) |
| R7 | 256 | [layers/R7.md](layers/R7.md) |
| R8 | 512 | [layers/R8.md](layers/R8.md) |
| **interface subtotal** | **1022** |  |
| **审名合计** | **1023** |  |

## 审阅字段

每行字段：

| 字段 | 含义 |
|---|---|
| `id` | 稳定审阅 id：`R<n>-<ox>-<role>` |
| `ox` | R-layer bitstring；R0 用 `ε` |
| `role` | `cell` 或 `operator` |
| `文言候选` | 最短古文/经典/文言风格候选；没有稳定字时回退 ox |
| `中文候选` | 现代中文解释 |
| `English` | 英文读法 |
| `formal logic` | 形式逻辑读法：cell 为 carrier element，operator 为 XOR mask action |
| `scheme` | 当前方案分类 |
| `备选与理由` | 为什么这么定；有什么备选；哪些 provisional |

## 当前原则

1. 有 canonical 字时先用 canonical，例如 R3 八卦、R6 六十四卦、R8 Shi V4。
2. 没有稳定字时不强造，文言列保留 `ox`。
3. operator 不再手写万行 transform；每个 operator row 都是 `lambda s, mask xor s` 的 interface reading。
4. 遗留 operator catalogue 属于解释、别名、corpus 或审稿材料，不进入本组 root count。
5. 这组文件是审字草案，不是最终定本；最终定字后再回写到 `LayerCharacterMap` / Lean。

## 配套说明

- [naming-scheme.md](naming-scheme.md)：层级命名原则、备选及理由。
- [all-1023.md](all-1023.md)：1023 条审名总表。
- [manifest.md](manifest.md)：1023 审名计数清单。
- [r8-64/](r8-64/)：R8 按 Shi 拆成 4×64 的审名工作表。
- [../r8-root-language-tree.md](../r8-root-language-tree.md)：root language tree 的理论总纲。
- [../root-native-operators.md](../root-native-operators.md)：root-native operator 与 legacy catalogue quarantine。

## Lean 验证入口

```bash
lake build SSBX.Foundation.Hierarchy.RootLanguageTree
lake build SSBX.Foundation.Wen.RootRuleKernel
lake build SSBX.Foundation.Wen.RootOperator
```

当前 summary theorem：

```lean
root_language_tree_summary
root_rule_kernel_summary
```
