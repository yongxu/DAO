# WenSurface 路线状态

本页记录 `wenyan-surface` 的实现边界。它是 `ziwen-spec.md` 的可执行子集前端，不宣称覆盖完整 Ziwen v0：当前没有 layout token、语句块、函数定义、match、数字/树等通用语言结构。

## 当前定义

完整在这里的含义是：

- 371 个 `OperatorId` 全部可登记、可查 signature、可诊断支持状态。
- 82 个 surface / 193 个 reading 可被 resolver 说明或报告歧义。
- 只有 theorem-backed registry 中的 12 个 operator 进入 evaluator。
- catalogue-only operator 在 CLI 中报告 `known-not-executable`，不伪造结果。
- `baguaWen` 的 22-token 受控 IL parser 仍独立冻结。

## 里程碑状态

| Milestone | 状态 | 现态 |
|---|---|---|
| M0 基线合流 | done | `WenSurface` CLI、operator readings/signatures/cell map 已接入；`baguaWen` 未改。 |
| M1 语法前端重构 | done | `SurfaceExpr`、`parseSurface`、显式 `之` marker、尾随 `之` 错误。 |
| M2 表驱动 resolver | done | runtime 走 `allSurfaceReadings` / operator forms / executable registry；`resolveStdlibOp` 仅作 legacy witness。 |
| M3 字面值扩展 | done | `一` + 64 卦名 + conservative 繁简 alias；未 promotion gap 只诊断。 |
| M4 核心语法能力 | done for Hex | `者 甲 E`、`凡 甲 E`、`令 甲 V E` 支持 Hex binder；Bool binder 留后续。 |
| M5 可执行语义扩展 | done for current subset | 12 个 executable：早期 8 个 + `错/錯`、`综/綜`、`互`、`反`。 |
| M6 全目录覆盖 | done as catalogue coverage | 371 operator 全部 registry/signature 可查；359 个当前 known-not-executable。 |
| M7 CLI 产品化 | done | `--tokens`、`--resolve`、`--ast`、`--typecheck`、`--json`、`--explain`、`--operator`、`--operators`、`--coverage`；失败返回非零。 |

## 验收命令

```bash
lake build
lake build wenyan-surface
scripts/check_wenyan_surface_cli.py
```

`scripts/check_wenyan_surface_cli.py` 覆盖 JSON run、负例诊断、inspect modes、operator catalogue listing。

## 边界

- `known-not-executable` 不是错误的 catalogue 行；它表示签名/读法存在但没有 theorem-backed denotation。
- `unsupported` 仅保留作 CLI filter/phase 的兼容词，产品语义以 `known-not-executable` 为准。
- `推/益/损/損` 等可在 `WenDefEval` 求值，不代表都能 compile 到 L0 `YiInstr`；`WenDefCompile` 的 cuo-equivariance ceiling 仍有效。
- 完整 Ziwen v0 仍以 `ziwen-spec.md` 为未来目标，不由 WenSurface 当前子集承诺。

## 下一阶段语法设计

括号、优先级、infix/operator mixfix 的设计合同见
`formal/SSBX/notes/wensurface-syntax-spec.md`。该 spec 保持 catalogue coverage
与 theorem-backed evaluator 分离，目标是用表驱动 Pratt parser 扩展当前
prefix-only 前端。S1 已落地：`（ E ）` 与 `( E )` 可 token/parse 为 grouped
AST，并在 elaboration 时透明求值。
