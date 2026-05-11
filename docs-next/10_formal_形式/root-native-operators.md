# Root-Native Operators — 根算子、投影与目录隔离

> 状态：draft v0.1 (2026-05-12)
> 前置：[`r8-root-language-tree.md`](r8-root-language-tree.md) · [`cell256-algebra.md`](cell256-algebra.md) · [`../50_maintenance/legacy-catalogue-quarantine.md`](../50_maintenance/legacy-catalogue-quarantine.md)
> Lean 锚点：[`RootOperator.lean`](../../formal/SSBX/Foundation/Wen/RootOperator.lean) — `root_operator_summary`。

---

## 0. Claim

> **v3 的 operator 不以历史目录行数为本体。一个 root-native operator 只能来自四种结构：R8 mask、root-rule program、带 loss ledger 的 projection、或指向前述三者的 alias。遗留 catalogue 可以被审计为 alias、corpus、evidence note 或 delete，但其目录大小不进入 root ontology。**

这把“算”从目录统计中抽出来，接回 R8-root language tree：

```text
root operator
= mask | program | projection | alias
```

目录只能问：

```text
this legacy row maps to which root operator?
this row contributes an example corpus?
this row is only an evidence note?
this row should be deleted?
```

不能问：

```text
how many catalogue rows prove completeness?
```

---

## 1. Lean 结构

`RootOperator.lean` 固定四类 root-native source：

| constructor | meaning | semantics |
|---|---|---|
| `mask c` | R8 XOR mask | `.path [c]` |
| `program e` | root-rule `CoreForm` | `CoreForm.eval emptyEnv e` |
| `projection c loss` | richer carrier projected to R8 | `.projected c loss` |
| `alias name target` | name for existing root operator | same visible / loss as target |

关键 theorem：

```lean
RootOperator.every_operator_has_visible_projection
RootOperator.every_operator_has_loss_ledger
RootOperator.alias_visible
RootOperator.alias_loss
RootOperator.duplicated_mask_returns_origin
root_operator_summary
```

它们只证明结构边界：

```text
每个 root operator 都有 R8-visible projection。
每个 root operator 都有 loss ledger。
alias 不新增行为，只继承 target。
```

---

## 2. Legacy catalogue role

遗留目录行进入 quarantine 后只有四种合法角色：

| role | can enter root ontology? | required action |
|---|---|---|
| `alias` | no, but must point to a root target | 给出 root mask / program / projection target |
| `corpus` | no | 迁入例句、测试或文义材料 |
| `evidenceNote` | no | 保留为审稿证据，不进入主 claim |
| `delete` | no | 说明删除理由 |

Lean 里对应：

```lean
LegacyCatalogueRole.requiresRootTarget
LegacyCatalogueRole.isOntologyCount
LegacyCatalogueRole.no_legacy_role_is_ontology_count
```

其中 `isOntologyCount role = false` 对所有 role 成立。

---

## 3. 边界声明

本文件已经关闭：

| closed | theorem |
|---|---|
| root operator 四类 carrier | `RootOperatorKind`, `RootOperator` |
| 每个 root operator 可投影到 R8 | `every_operator_has_visible_projection` |
| 每个 root operator 有 loss ledger | `every_operator_has_loss_ledger` |
| alias 不新增行为 | `alias_visible`, `alias_loss` |
| legacy role 不作为本体计数 | `no_legacy_role_is_ontology_count` |

未纳入本轮：

| outside | reason |
|---|---|
| 完整自然语言语义 | 需要 parser / interpreter / corpus |
| 每个遗留行的逐条归档 | 由 quarantine audit 执行 |
| 领域物理 / 数学 claim 的真值 | 仍走 truth-status ledger |

---

## 4. 验证

```bash
lake build SSBX.Foundation.Wen.RootOperator
```
