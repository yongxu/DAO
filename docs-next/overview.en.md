# Shengsheng Buxi Documentation — v3 Overview (English)

> Status: v3 final (2026-05-11) — Cell256 / V₄ Klein Shi / strict-uniform R₀..R₈
> As of: 2026-05-11. Lean build: `lake build SSBX` 3656 jobs, 0 sorry, 0 warning.

This directory is the staging area for a rebuilt documentation set. It does not yet replace the repository root documents; it is meant to become the single replacement once generated indexes and links are stable.

## Thesis (one paragraph)

The minimal algebraic kernel of *Yi* (易) is the strict (Z/2)ⁿ uniform R₀..R₈ ladder — each layer Rₙ has size 2ⁿ for n = 0..8 — carrying its own (Z/2)⁸ Cayley regular representation. The V₄ Klein four-group of *Shi* {dao, ji, jin, wei} ≅ (YinBit × GuoBit) ∈ Bool² emerges only at R₈ as the joint of the seventh (因, *yīn*, past-trace) and eighth (果, *guǒ*, future-projection) binary axes; **dao = (0, 0) is simultaneously the V₄ identity, the chosen origin of the (Z/2)⁸ torsor, the no-op operator, and the always-true anchor cell — a single 8-character string carrying five identities**. R₈ = 256 is the natural 8-bit closure isomorphic in cardinality to the ASCII byte; this framework is the *self-describing-system* GUT, not a physical one. As of v3 (2026-05-10/11), the legacy Cell192 / Z/3 cyclic Shi has been deleted; Cell256 / V₄ Shi is the sole ontology, with the `R8_complete` bundle depending only on `propext` + `native_decide` (no project-defined axiom).

## R₀..R₈ ladder

| R-index | size = 2ⁿ | Name (CN) | Name (EN) | New atom this layer | Lean carrier |
|---|---|---|---|---|---|
| R₀ | 1 | 太极 | Taiji | (Unit) | (Lean stdlib `Unit`) |
| R₁ | 2 | 爻 / 两仪 | Yao | neg (mask `x`) | [`Yi.lean`](../formal/SSBX/Foundation/Atlas/YiLegacy/Yi.lean) |
| R₂ | 4 | 四象 | SiXiang | (lift R₁) | [`BaguaAlgebra.lean`](../formal/SSBX/Foundation/Atlas/YiLegacy/Bagua/BaguaAlgebra.lean) |
| R₃ | 8 | 八卦 | Trigram | dong/hua/bian + cuo/zong/hu | [`Yi.lean`](../formal/SSBX/Foundation/Atlas/YiLegacy/Yi.lean) |
| R₄ | 16 | 面 (Mian) | Mian = Ben × Zheng | 4-th binary axis | [`BenZheng.lean`](../formal/SSBX/Foundation/Atlas/YiLegacy/Bagua/BenZheng.lean) |
| R₅ | 32 | 五爻 (provisional) | Wuyao | 5-th binary axis | [`R5_Wuyao.lean`](../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) |
| R₆ | 64 | 重卦 | Hexagram | outer 3 yao flips + outer V₄ | [`Yi.lean`](../formal/SSBX/Foundation/Atlas/YiLegacy/Yi.lean) |
| R₇ | 128 | 因卦 (Cell128) | YinHex | 因 (yīn) bit + 印 toggle | [`Cell128.lean`](../formal/SSBX/Foundation/Atlas/YiLegacy/Bagua/Cell128.lean) |
| R₈ | 256 | 果卦 (Cell256) | GuoHex | 果 (guǒ) bit + 投 + Shi V₄ emerge | [`Cell256.lean`](../formal/SSBX/Foundation/Atlas/YiLegacy/Bagua/Cell256.lean) |

Anchors: [`yi-RO-hierarchy.md`](10_formal_形式/yi-RO-hierarchy.md) §3 (definitive). Each Rₙ is exactly 2ⁿ — strict uniform, no jumps, no gaps. The R-index naming alias shims (`R0_Taiji.lean` .. `R8_GuoHex.lean`) and umbrella ([`RHierarchy.lean`](../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)) provide reader-friendly navigation.

## V₄ Shi structure (R₈ emergence)

| Shi | (yin, guo) | mask last 2 bits | V₄ element | Phenomenology | Cell with 乾 |
|---|---|---|---|---|---|
| **dao (道)** | (0, 0) | `oo` | identity *e* | always-true / cross-temporal / no-op | `oooooooo` |
| **ji (已)** | (1, 0) | `xo` | σ_P | past closed (parity-like) | `ooooooxo` |
| **wei (未)** | (0, 1) | `ox` | σ_T | future open (T-like) | `ooooooox` |
| **jin (今)** | (1, 1) | `xx` | σ_PT | present (PT, causation flow point) | `ooooooxx` |

The Shi V₄ is **not** an R₇ or R₈ single-layer atom — it is the **double-axis emergence** at R₈ from the joint of R₇'s 因 axis and R₈'s 果 axis. Encoding it as Z/3 cyclic (the legacy Cell192 path) loses the V₄ identity (i.e., loses `dao` as first-class) and breaks (Z/2)ⁿ self-similarity.

## Five identities of dao (一字五身)

`oooooooo` = dao = V₄ identity = origin of (Z/2)⁸ = no-op operator = always-true anchor cell — one 8-character string carrying five identities.

## Lean infrastructure pointers

- **R-index alias / umbrella**: [`RHierarchy.lean`](../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)
- **Algebraic spine**: Cell{128, 256} carry Add / Zero / Neg / Sub + SMul; Cayley ι/ε homomorphism; origin = (qian, dao) = V₄ identity.
- **Operators**: atomic XOR subgroup ([`Operators/Atomic.lean`](../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)), V₄ outer permutations ([`Operators/V4Outer.lean`](../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)).
- **Lift / Project uniform API**: [`LiftProject.lean`](../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) (8 R-layer pairs, each with `proj_lift_id_Rn` retract lemma).
- **OX 8-char literal macro**: [`OXNotation.lean`](../formal/SSBX/Foundation/Notation/OXNotation.lean) provides `OX["xxxxxxxx"]` (8-char `o`/`x` string → Cell256).
- **Self-description witness**: [`SelfDescription.lean`](../formal/SSBX/Truth/SelfDescription.lean) — `Cell256OperatorComplete` (the V₄ extension of the legacy 192-cell version).
- **R₈ closure bundle**: `R8_complete` in [`Cell256Stratify.lean`](../formal/SSBX/Foundation/Atlas/YiLegacy/Bagua/Cell256Stratify.lean) — depends only on `propext` + `native_decide`.

## Current verification policy

- `lake build SSBX` completes cleanly: 3656 jobs, 0 errors, 0 warnings, 0 sorry, 0 admit, 0 unsafe.
- Live trust-boundary facts are generated in [_generated/trust-boundary.md](./_generated/trust-boundary.md):
  - One live axiom: `kleene_recursion_axiom` (used in MetaInterp / Kleene closure, not in R-hierarchy);
  - One opaque sealed witness: `theOne`;
  - One top-level partial executable boundary: `YiState.run`;
  - No live `sorry`, `admit`, or `unsafe` declarations.
- Machine-readable indexes live in [_generated](./_generated/). Authored documents should explain; generated indexes should carry counts, status, and source locations.

## Pointers to v3 docs

- [v3 quick map (final-theory.md)](00_start/final-theory.md) — one-page summary
- [yi-RO-hierarchy.md](10_formal_形式/yi-RO-hierarchy.md) — R₀..R₈ definitive
- [yi-calculus-theorem.md](10_formal_形式/yi-calculus-theorem.md) — Theorems A–K
- [yi-as-meta-framework.md](10_formal_形式/yi-as-meta-framework.md) — meta-framework
- [old-to-new.md](30_crosswalk_互证/old-to-new.md) — Cell192 → Cell256 transition record
- [core-framework.md](20_theory_义理/core-framework.md) — theory entry (R₀..R₈ updated)
- [formal layer README](10_formal_形式/README.md) · [theory layer README](20_theory_义理/README.md) · [archive pointers](archive-pointers.md)

## Key history

| Date | Commit | Content |
|---|---|---|
| 2026-05-11 | `1c76a55` | Phase C: 9 R-index alias files + `RHierarchy.lean` umbrella |
| 2026-05-10 | `8e4406e` | Phase F.6 + G + B.1: delete `Cell192.lean`, doc sync, YinBit dedup |
| 2026-05-10 | `0003224` | Phase F.x.5: Modern/* cardinality cascade 192 → 256 |
| 2026-05-10 | `7de5064` | Phase A–F: doctrinal alignment — Cell192 → Cell256, V₄ Klein Shi |
