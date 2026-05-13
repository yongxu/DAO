# Root512 / V4 Power Plan

> Status: implemented first carrier and WenScript bridge.
> Lean anchor: [`Root512.lean`](../../formal/SSBX/Foundation/Wen/V4Kernel/Root512.lean).

## Purpose

The current root grammar should not depend on a historical operator catalogue
count. The root structure is generated from the v3 R-axis:

```text
R_n = (Z/2)^n
```

Even layers group canonically into V4 powers:

```text
R2 = V4
R4 = V4^2
R6 = V4^3 = Word64
R8 = V4^4 = Cell256
```

The root interface at R8 has two readings:

```text
Root512 = R8 x {cell, operator}
```

The factor from 256 to 512 is a reading role, not a ninth ontology bit and not
another V4 factor.

## Plan

### Phase 1 — Carrier

Implement the finite root carrier:

```text
RootCell256 = Word64 x V4 = V4^4
RootReading = RootCell256 x {cell, operator}
```

Prove:

- `RootCell256` has 256 generated cells.
- `RootReading` has 512 generated readings.
- the 64-word surface is the `temporal = dao`, `role = cell` fiber, hence one
  eighth of `Root512`.
- `R8` can be presented as `Mode16 x Mode16`, i.e. `(V4 x V4) x (V4 x V4)`.

### Phase 2 — Root Operator Reading

Define root operator application structurally:

```text
operatorReading(mask) applied to reading(cell)
  = reading(cell xor mask)
```

This only covers root XOR operators. Other semantic operators may later enter
as root-rule programs or projections with loss ledgers.

### Phase 3 — Controlled WenScript Bridge

Add a small root-native alias set:

| surface | root reading |
|---|---|
| `恒` / `恆` | origin operator |
| `印` | temporal trace-bit toggle |
| `投` | temporal projection-bit toggle |
| `印投` | temporal compound toggle |
| `非` / `不` | 64-word complement mask at temporal origin |

These names are direct root readings, not catalogue rows. The parser reports
their execution separately as `rootApplications`.

### Phase 4 — Boundary

The V4 action words `道/错/综/错综` remain V4 actions over the 64-word layer.
They are not all reducible to R8 XOR masks: `综` is a frame permutation, not a
constant XOR mask. This is why the bridge keeps `v4Actions` and
`rootApplications` separate.

## Current Boundary

Implemented now:

- `Root512` carrier and counts.
- `Mode16 x Mode16` presentation.
- root XOR application.
- WenScript recognition of root-native aliases.
- CLI trace for root applications.

Not claimed:

- all classical Chinese grammar has executable semantics;
- every text-layer operator is already mapped;
- catalogue cardinality is an ontology count;
- recursive macros or VM/meta-interpreter self-hosting.

## Example

```bash
lake exe wen-lisp prove examples/wen-lisp/demo-root512-operators.wen --trace
```

Expected shape:

```text
rootApplications=6
rootApplication[0] 恒 之 乾 :: .../operator applied to .../cell => .../cell
```
