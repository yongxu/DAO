# 维护手册

本节记录 docs-next 与形式层同步时的最低维护口径。它不替代脚本、CI 或 Lean 构建；机器事实优先来自目标构建、`lake build SSBX`、审计脚本与 `../_generated/`。

## 构建检查

推荐顺序：

```bash
/Users/ren/.elan/bin/lake build
/Users/ren/.elan/bin/lake build SSBX
rg -n "\\bsorry\\b|\\badmit\\b|\\bunsafe\\b|#allow_unsafe" formal
rg -n "\\baxiom\\b|\\bopaque\\b|partial def" formal
```

期望口径：

- live `sorry/admit/unsafe` 为 `0`。
- axiom 只允许 `kleene_recursion_axiom`。
- opaque 只允许 `theOne`。
- `partial def` 只允许 `YiState.run`，且记录为执行边界。

## 文档同步

- 形式事实以 Lean 源和生成索引为准，docs-next 只解释口径。
- 涉及数量统计时，引用 `../_generated/`，不要在人工文档中重复维护易过期数字。
- 若 `formal/SSBX/notes/` 与 docs-next 叙述冲突，先核对 Lean 源，再更新两边文档。
- 修改 trust boundary 时，必须同步更新 `docs-next/10_formal_形式/trust-boundaries.md`。
- 修改图类别或图源时，必须同步更新 `docs-next/30_crosswalk_互证/diagrams.md`。

## 专题维护页

| 需求 | 入口 |
|---|---|
| 文档分层契约 | [docs-contract.md](docs-contract.md) |
| 生成索引流程 | [generation-pipeline.md](generation-pipeline.md) |
| 发布前检查 | [release-checklist.md](release-checklist.md) |
| 归档与替代 | [archive-policy.md](archive-policy.md) |

## 生成资产

已有脚本负责 DAG 与图渲染：

- `scripts/generate_concept_dag.py`
- `scripts/generate_monad_dag.py`
- `scripts/generate_monad_tree.py`
- `scripts/render_concept_dag.sh`
- `scripts/render_monad_dag.sh`
- `scripts/render_construction_dag.sh`
- `scripts/render_attention.sh`
- `scripts/render_human_alignment.sh`

维护原则：脚本和 Lean 源是生产者，docs-next 是消费者。不要为修正文档而手改生成图的渲染产物。

## 合作边界

多人同时改写时，先看 `git status --short`。不要回滚别人对 Lean、脚本、web、README 或其他 docs-next 分区的修改。本文档分区只维护形式、互证图索引与维护说明。
