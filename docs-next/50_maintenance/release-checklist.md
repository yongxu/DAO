# 发布检查表

本表用于 docs-next 或形式层同步前的最低检查。它不替代 CI。

## 构建

- `lake build` 通过。
- `python3 scripts/docs_next.py build` 通过。
- `../_generated/` 已刷新。
- 没有意外改动生成文件以外的区域。

## 信任边界

- `../_generated/trust-boundary.md` 与 `../10_formal_形式/trust-boundaries.md` 口径一致。
- axiom、opaque、partial 的变化已被明确解释。
- 依赖 `kleene_recursion_axiom` 的说明仍带条件。
- `theOne` 未被写成可展开构造。
- `YiState.run` 未被写成 theorem-level total evaluator。

## Claim 与状态

- `../_generated/claim-index.md` 已检查。
- 新增或变更 claim 的 status 没有被人工页夸大。
- pending interface 仍标为 pending。
- modelComputed 与 machineChecked 在叙述中区分清楚。

## 参考与互证

- 新增图已进入 `diagram-index`。
- 新增算子已进入 `operator-index`。
- 新增名册项已进入 `registry-index`。
- 新增文档已进入 `markdown-index`。
- 互证页只写指针和口径，不复制生成表。

## 史料与归档

- `史料/` 未被无意改写。
- 旧义理未被大段复制进新版。
- 归档指针仍指向真实路径。
- 已替代内容标清「旧入口」和「当前读法」。

## 合作

- `git status --short` 已查看。
- 未回滚他人改动。
- 只提交本次任务范围内文件。
