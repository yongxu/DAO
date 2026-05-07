# Wenyan samples

Sample wenyan / YiInstr programs runnable by the `wenyan` CLI binary.

## Inventory

| File | Description | Source |
|---|---|---|
| `hello.wen` | Halt immediately | hand-written |
| `daoJudge.wen` | Roster.lean §「道判之程」: classify hexagram as 天道 (y3=y4 → 已) or 心道 (otherwise → 未) | generated via `wenyan print daoJudge` |
| `microKernel.wen` | 微核源 — Tier 2 self-host kernel, 64 instructions traversing all 12 wenyan ops | generated via `wenyan print microKernel` |

## Regenerate the generated samples

```bash
wenyan print daoJudge    > daoJudge.wen
wenyan print microKernel > microKernel.wen
```

## Run

```bash
wenyan run hello.wen
wenyan run daoJudge.wen --init 111111   # 乾 → expect halted with cur.shi = 已
wenyan run daoJudge.wen --init 111100   # y3=1, y4=0 → expect halted with cur.shi = 未
wenyan run microKernel.wen               # default 乾 init, expect halted within fuel
```
