# 生成流程

本页记录 docs-next 生成资产的消费流程。脚本细节以仓库脚本为准；本文只说明维护顺序和检查点。

## 常规顺序

1. 修改 Lean、旧文或人工 docs。
2. 运行 Lean 构建，确认形式层可检查。
3. 运行 docs-next 生成脚本，刷新 `docs-next/_generated/`。
4. 检查生成索引是否反映预期变化。
5. 更新人工页中的入口、读法或状态说明。

## 推荐命令

```bash
/Users/ren/.elan/bin/lake build
python3 scripts/docs_next.py build
```

必要时再运行审计搜索：

```bash
rg -n "\\bsorry\\b|\\badmit\\b|\\bunsafe\\b|#allow_unsafe" formal
rg -n "\\baxiom\\b|\\bopaque\\b|partial def" formal
```

## 生成文件读法

| 文件 | 用途 |
|---|---|
| `_manifest.json` | 生成批次和产物清单 |
| `lean-index.md/json` | Lean 模块、cluster、路径和声明统计 |
| `claim-index.md/json` | claim ledger 状态 |
| `operator-index.md/json` | 文言算子索引 |
| `registry-index.md/json` | 名册 kind 和 pending |
| `diagram-index.md/json` | Mermaid 图和 SVG 对照 |
| `crossrefs.md/json` | Markdown 与 Lean path/symbol 交叉引用 |
| `markdown-index.md/json` | 文档路径和标题索引 |
| `trust-boundary.md/json` | axiom、opaque、partial 扫描 |

## 人工检查点

- 新增文档是否进入 `markdown-index`。
- 新增 Lean module 是否进入 `lean-index`。
- claim 状态是否符合预期，特别是 ledgerDependent 是否被误写。
- trust boundary 是否仍与 `../10_formal_形式/trust-boundaries.md` 一致。
- 图源更新后，diagram index 是否同步。

## 不做的事

- 不手改 `docs-next/_generated/`。
- 不为通过文档检查而改 Lean 语义。
- 不把生成统计复制到人工页长期维护。
