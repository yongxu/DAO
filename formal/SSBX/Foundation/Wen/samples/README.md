# Wenyan samples

样本分两层，对应 Wen 语言栈之两个表面：

| 层 | 表面 | 样本 | 入口 |
|---|---|---|---|
| **Bagua-ISA** | 22-token 汇编 (`«终» «推» «翻爻»`…) | `hello.wen` / `daoJudge.wen` / `microKernel.wen` | `wenyan` CLI binary |
| **WenSurface** | 文言级 prose (`推 之 一` / `凡 甲 同 甲 甲`) | `wenSurfaceProse.wen` | `wenyanInterp` / `wenyanInterpBool` (Lean) |

两层并非并行宇宙：WenSurface 经 `theoremBackedSemanticsFor?` desugar 落到与 Bagua-ISA 同一组 `WenDef.Tm` builtin (推=`tuiBody` / 同=`tongBody` …), 在 R₈ 投影上汇合.

> **Canonical user evaluator** (2026-05-17): `WenDefEval.denoteHex` (Tm→Value) 与 `WenEval.wenEval` (String→R8). `RootRuleDemoInterpreter` 已 `@[deprecated]`, 仅作教学示例保留, 不应在新代码中复用.

## Inventory

### Bagua-ISA samples (runnable via `wenyan` CLI)

| File | Description | Source |
|---|---|---|
| `hello.wen` | Halt immediately | hand-written |
| `daoJudge.wen` | Roster.lean §「道判之程」: classify hexagram as 天道 (y3=y4 → 已) or 心道 (otherwise → 未) | generated via `wenyan print daoJudge` |
| `microKernel.wen` | 微核源 — Tier 2 self-host kernel, 64 instructions traversing all 12 wenyan ops | generated via `wenyan print microKernel` |

### WenSurface samples (round-trip pinned via Lean `native_decide`)

| File | Description | Lean mirror |
|---|---|---|
| `wenSurfaceProse.wen` | 7-行文言级 prose, 演示 S-组虚词 之/而/凡/令/者 同走 desugar 至 22 核 builtin | `SSBX.Foundation.Wen.WenSurface.ProseSample` |

## Regenerate the generated samples

```bash
wenyan print daoJudge    > daoJudge.wen
wenyan print microKernel > microKernel.wen
```

## Run

### Bagua-ISA (CLI)

```bash
wenyan run hello.wen
wenyan run daoJudge.wen --init 111111   # 乾 → expect halted with cur.shi = 已
wenyan run daoJudge.wen --init 111100   # y3=1, y4=0 → expect halted with cur.shi = 未
wenyan run microKernel.wen               # default 乾 init, expect halted within fuel
```

### WenSurface (Lean)

```bash
lake build SSBX.Foundation.Wen.WenSurface.ProseSample
```

`wenSurfaceProse.wen` 自身仅作文档展示; 实际 round-trip 在 ProseSample.lean 中由 `theorem proseSurface_endToEnd` 见证.
