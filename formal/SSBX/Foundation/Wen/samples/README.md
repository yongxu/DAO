# Wenyan samples

样本分两层，对应 Wen 语言栈之两个表面：

| 层 | 表面 | 样本 | 入口 |
|---|---|---|---|
| **Bagua-ISA** | 22-token 汇编 (`«终» «推» «翻爻»`…) | `hello.wen` / `daoJudge.wen` / `microKernel.wen` | `wenyan` CLI binary |
| **WenSurface** | 文言级 prose (`推 之 一` / `凡 甲 同 甲 甲`) | `wenSurfaceProse.wen` | `wenyanInterp` / `wenyanInterpBool` (Lean) |

两层并非并行宇宙：

1. **WenSurface → WenDef.Tm**：`wenyanCompile` 经 `theoremBackedSemanticsFor?` desugar 把 371 个 catalogue 算子（88% 已接电）落到 22 个 builtin（推=`tuiBody` / 同=`tongBody` …）。
2. **WenDef.Tm → Bagua-ISA**：`compileHexFunCertified?` (in `WenDefCompile.lean`) 把 complement-equivariant 之 Hex→Hex 子集编译到 YiInstr 程序，由 `runHexProg` 或 `wenyan run` CLI 执行。

故 Bagua-ISA 是 WenDef.Tm 之**后端目标**而非另一表面，两条表面在 Tm 处汇合。**「错等变」约束** (`f(h.complement) = (f h).complement`) 是 YiInstr 之代数刚性 — 故 `推`/`损`/`生` 等非 equivariant 项不可桥（这是结构性界限，不是工程缺口）。

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
| `wenSurfaceISABridge.wen` | 文言 → Bagua-ISA 桥之 5 个可桥例 (错/综/互/而 反 综/再 反) + 3 个反例 (推/損/同 — non-equivariant)；演示二层在 Tm 处汇合 | `SSBX.Foundation.Wen.WenSurface.ISABridge` |

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
lake build SSBX.Foundation.Wen.WenSurface.ProseSample   # 7 行文言 → Tm denotation
lake build SSBX.Foundation.Wen.WenSurface.ISABridge     # 8 行文言 → YiInstr 桥 + 64-Hex agreement
```

`.wen` 文件自身仅作文档展示；实际 round-trip 在对应 Lean 模块中由 `theorem proseSurface_endToEnd` / `theorem isaBridge_endToEnd` 见证。
