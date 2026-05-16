# wen-substrate — split into a folder (2026-05-16)

> The single-file form of `wen-substrate.md` has been replaced by a navigable, multi-chapter folder. See [`wen-substrate/00-README.md`](wen-substrate/00-README.md) for the reading map and the anchor migration table.

The substantive claim is unchanged: **R-Family is the universal formal substrate. R-Family is what "formal" means.**

## Where to read

| topic | file |
|---|---|
| reading map, per-chapter abstract, anchor migration table | [`wen-substrate/00-README.md`](wen-substrate/00-README.md) |
| definitions D1–D6, necessary properties P1–P7, R-Family emergence, R-tower cosmology | [`wen-substrate/01-foundations.md`](wen-substrate/01-foundations.md) |
| parametric R-Family-over-k; encoding (T1) vs articulation (T2); Hilbert is R-Family-over-ℂ | [`wen-substrate/02-parametric.md`](wen-substrate/02-parametric.md) |
| operation monism + distinction monism — the Σ operator below the base; the primitive `o` / `x` below the operator (Spencer-Brown / Bateson / Wheeler / yi-jing); 一元 distinct from substance-monism; 道家 reading | [`wen-substrate/03-operation-monism.md`](wen-substrate/03-operation-monism.md) |
| `PartialCell N` algebra; Wen.Core ISA; codim filtration; constraint composition | [`wen-substrate/04-partialcell.md`](wen-substrate/04-partialcell.md) |
| coverage of formal domains (mathematics, language, computation, physics, spacetime, cognition, phenomenology, decidability, informational-physical, formality) | [`wen-substrate/05-coverage.md`](wen-substrate/05-coverage.md) |
| universal grammar — classical UG mapping + X²-256 conditional form (existence + uniqueness discharged in Lean) | [`wen-substrate/06-universal-grammar.md`](wen-substrate/06-universal-grammar.md) |
| comparison with alternative foundations; seven standing objections; the direct claim; Claim Z + falsification | [`wen-substrate/07-claim.md`](wen-substrate/07-claim.md) |
| proof obligations — T0, D1–D6, T1–T8, Phase 0 sub-theorems, three-phase roadmap, complete version history | [`wen-substrate/08-obligations.md`](wen-substrate/08-obligations.md) |

## Why the split

The single-file form grew to ~4,200 lines across 11 versions (v0.6 → v1.4). The accretion was appended rather than re-architected: sub-sections that now warrant their own chapter (operation monism, distinction monism, X²-256 conditional UG, PartialCell substrate) were buried inside Part III / Part IV, and cross-section patches and version-correction prose were scattered in-place. The new folder is a complete rewrite from the framework's current understanding — not a re-paste of the old layout. Operation monism and distinction monism (the v1.4 substrate-most-primitive layer) live together in chapter 03; universal grammar gets its own chapter; v0.x → v1.x patch trail is folded into clean current-form exposition with the version trajectory consolidated in chapter 08; the V₄ marquee is dropped in favour of R₂'s underlying algebra.

## Anchor migration

The legacy `§X.Y` anchors of the single-file form are mapped to their new chapters in [`wen-substrate/00-README.md`](wen-substrate/00-README.md). External references — 89 Lean docstring cites across 18 files plus ~100 markdown hrefs across the D-series companion docs in this directory — currently name old `§X.Y` anchors; their mechanical rewrite is a follow-up pass. The anchor migration table is the input to that pass.

## Backup

The legacy single-file form is preserved at `wen-substrate.md.legacy-backup-2026-05-16` for reference; the canonical material is now in `wen-substrate/`.
