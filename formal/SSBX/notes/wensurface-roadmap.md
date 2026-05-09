# WenSurface 路线状态

本页记录 `wenyan-surface` 的实现边界。它是 `ziwen-spec.md` 的可执行子集前端，不宣称覆盖完整 Ziwen v0：当前没有 layout token、语句块、函数定义、match、数字/树等通用语言结构。

## 当前定义

完整在这里的含义是：

- 371 个 `OperatorId` 全部可登记、可查 signature、可诊断支持状态。
- 82 个 surface / 193 个 reading 可被 resolver 说明或报告歧义。
- 371 个 `OperatorId` 全部进入 evaluator：367 个 exact/theorem-backed rows，
  4 个 structural catalogue normal forms。
- structural catalogue operator 返回 `Catalogue[...]` result，可 type-check / evaluate，但不伪装成 exact Hex/Bool 文本专义 denotation。
- `baguaWen` 的 22-token 受控 IL parser 仍独立冻结。

## 里程碑状态

| Milestone | 状态 | 现态 |
|---|---|---|
| M0 基线合流 | done | `WenSurface` CLI、operator readings/signatures/cell map 已接入；`baguaWen` 未改。 |
| M1 语法前端重构 | done | `SurfaceExpr`、`parseSurface`、显式 `之` marker、尾随 `之` 错误。 |
| M2 表驱动 resolver | done | runtime 走 `allSurfaceReadings` / operator forms / executable registry；`resolveStdlibOp` 仅作 legacy witness。 |
| M3 字面值扩展 | done | `一` + 64 卦名 + conservative 繁简 alias；未 promotion gap 只诊断。 |
| M4 核心语法能力 | done | `者 甲 E`、`凡 甲 E`、`令 甲 V E` 支持 Hex；`者`/`令` 已支持 Bool 与常用函数域推断。 |
| M5 可执行语义扩展 | done | 367 个 exact/theorem-backed executable：早期 Hex/Bool 核心、exact Hex transforms、逻辑/恒等/量词 aliases、context application、state/process edge carriers、carrier rows 等。 |
| M6 全目录覆盖 | done | 371 operator 全部 registry/signature 可查、可执行；4 个非 exact row 只落为 structural catalogue normal form；0 个 known-not-executable。剩余 4 个已按 signature kind 入账：2 state-transition、2 trajectory。 |
| M7 CLI 产品化 | done | `--tokens`、`--resolve`、`--ast`、`--typecheck`、`--json`、`--explain`、`--operator`、`--operators`、`--coverage`；失败返回非零。 |

## 验收命令

```bash
lake build
lake build wenyan-surface
scripts/check_wenyan_surface_cli.py
```

`scripts/check_wenyan_surface_cli.py` 覆盖 JSON run、负例诊断、inspect modes、operator catalogue listing。

## 边界

- `known-not-executable` / `unsupported` filter 仅保留作 CLI 兼容词；当前 operator catalogue 返回 0 行。
- 非 exact row 的 evaluator 语义是 structural catalogue normal form，仍不承诺 exact Hex/Bool denotation。
- 多义 surface 不因某个 reading 已有 evaluator 语义而自动消歧；除保留的 v1 核心 surface 外，
  只有候选语义完全同体时才自动选择，否则返回 ambiguity。
- `而`/S-2 已有 exact `Hex → Hex` endomap composition 语义；支持显式 `者` lambda，
  也支持 theorem-backed exact function section，如 `而 推 損 一`。它仍是 Hex endomap composition，
  不是多态 Bool/function compose。
- `同`/`比` 支持受控 relation infix：`A 同 B`、`A 比 B` desugar 为既有 prefix
  application；关系链如 `一 同 一 同 一` 作为 non-associative syntax error。
- `者` binder 无显式类型标注；parser/elaborator 只在有限候选域中推断
  `Hex`、`Bool`、`Hex → Hex`、`Hex → Bool`、`Bool → Bool`、`Bool → Hex`。
  `凡` 仍是 Hex universe quantifier，不是多态 forall。
- `推/益/损/損` 等可在 `WenDefEval` 求值，不代表都能 compile 到 L0 `YiInstr`；`WenDefCompile` 的 cuo-equivariance ceiling 仍有效。
- 完整 Ziwen v0 仍以 `ziwen-spec.md` 为未来目标，不由 WenSurface 当前子集承诺。

## 下一阶段语法设计

括号、优先级、infix/operator mixfix 的设计合同见
`formal/SSBX/notes/wensurface-syntax-spec.md`。该 spec 保持 catalogue coverage
与 theorem-backed evaluator 分离，目标是用表驱动 Pratt parser 扩展当前
prefix-first 前端。S1 已落地：`（ E ）` 与 `( E )` 可 token/parse 为 grouped
AST，并在 elaboration 时透明求值。另已完成 binder 正规化与 relation infix：
Bool binder、函数值 binder、exact operator 所需 predicate/function 参数位置的 `者`
解析、以及 `同`/`比` infix 均可运行。
