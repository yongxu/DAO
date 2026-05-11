# Legacy Catalogue Quarantine

> 状态：draft v0.1 (2026-05-12)
> 目标：把历史 operator catalogue 从结构主张中隔离出来，只作为可审计迁移材料。
> 形式锚点：[`RootOperator.lean`](../../formal/SSBX/Foundation/Wen/RootOperator.lean) — `LegacyCatalogueRole` 与 `root_operator_summary`。

---

## 0. Rule

> **任何遗留 catalogue 条目都不能凭“在目录中”进入 root ontology。它必须被标注为 alias、corpus、evidence note 或 delete。只有 alias 需要给出 root-native target；其余三类都不产生 root operator。**

这条规则替代“目录优先”的旧路线。

---

## 1. Allowed Roles

| role | definition | required evidence |
|---|---|---|
| `alias` | 旧名可解释为已有 root operator 的名字 | root mask / root program / projection target |
| `corpus` | 旧条目只提供例句、语料、文义测试 | source line / example / expected reading |
| `evidenceNote` | 旧条目暂作审稿材料 | why it is not root-native yet |
| `delete` | 旧条目不保留 | reason and replacement if any |

禁止角色：

| forbidden | reason |
|---|---|
| completeness count | 目录大小不是本体不变量 |
| exact-by-row | 行存在不等于 root rule 证明 |
| semantic-complete | 有名称不等于有领域语义 |
| second ontology | catalogue 不是 R8-root 之外的新本体空间 |

---

## 2. Audit Record

建议每条迁移记录使用：

```text
legacyId:
surface:
role: alias | corpus | evidenceNote | delete
rootTarget: only if role = alias
source:
reason:
status: proposed | accepted | rejected
```

`rootTarget` 只能是：

```text
mask(...)
program(...)
projection(...)
alias(...)
```

即 [`root-native-operators.md`](../10_formal_形式/root-native-operators.md) 定义的四类。

---

## 3. Entrypoint Policy

入口文档只允许这样说：

```text
legacy operator catalogue is quarantined migration material.
```

入口文档不再把目录大小、operator-cell grid 大小、exact row 分组写成当前 claim、roadmap 阶段或 completeness 证据。

若必须引用旧目录实现，例如 CLI 或历史文档，应加边界：

```text
implementation inventory, not ontology.
```

---

## 4. Migration Order

| step | action |
|---|---|
| 1 | 清入口：README / formal README / roadmap 不再目录优先 |
| 2 | 建 root-native target：mask / program / projection / alias |
| 3 | 审旧条目：alias / corpus / evidenceNote / delete |
| 4 | 只把 accepted alias 接入 root operator |
| 5 | corpus 进入例句测试；evidence note 留维护文档；delete 移出入口 |

---

## 5. Validation

```bash
lake build SSBX.Foundation.Wen.RootOperator
rg -n "目录大小|coverage grid|complete semantics" README.md README.en.md README.formal.md docs-next/00_start docs-next/10_formal_形式 docs-next/50_maintenance
```
