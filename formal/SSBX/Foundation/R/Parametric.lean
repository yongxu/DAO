/-
# Foundation.R.Parametric — parametric R-Family over an arbitrary base `k`

Documentation companion: `docs-next/10_formal_形式/r-family-parametric-bases.md`
(D3 companion to `wen-substrate.md` v1.0.2+ §3.6).

This module sketches the **parametric R-Family** structure. Per
wen-substrate §3.6:

    R-Family-over-k = { R_N^{(k)} }_{N ∈ ℕ},   R_N^{(k)} := k^N.

The **minimum instance** is R-Family-over-`Bool` ≅ R-Family-over-$\mathbb{F}_2$,
which is fully formalized in `Foundation/R/Basic.lean` as

    def R (N : ℕ) : Type := Fin N → Bool.

This file:

* Defines `RFamily k N := Fin N → k` for arbitrary `k`.
* Confirms `R N := RFamily Bool N` is a definitional equality
  (the `Bool ≅ F_2` minimum specialization).
* Inherits `Fintype` when `k` is finite (e.g., `Bool`, `ZMod p`).
* Carries the pointwise scalar action by `k` when `k` is a `Mul`-monoid
  (sketch — full module structure deferred to per-base instances).

Per-instance specialization to ℝ, ℂ, ℤ_p, ℚ_p, ℂ_p is **deferred** to
Mathlib bridges (wen-substrate §3.6.7 "code vs theory"). The role of this
file is structural: making the parametric type **available** in the
codebase, so future Mathlib-bridge work can refer to it.

## Doctrinal anchor

* `wen-substrate.md` v1.0.2+ §3.6.1 (Layer A / Layer B split),
  §3.6.2 (instantiation table), §3.6.7 (code vs theory).
* `r-family-parametric-bases.md` (this file's documentation companion).
-/

import SSBX.Foundation.R.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi

namespace SSBX.Foundation.R

/-! ## § 1 The parametric R-Family carrier

`RFamily k N` is the N-fold product of `k`, i.e. `k^N`. This is the
**parametric R-Family carrier** over base `k`. The minimum instance is
`k = Bool`, recovering the canonical `R N` (≅ R-Family-over-F_2).

Per wen-substrate v1.0.2+ §3.6.1 (Layer A structural pattern). -/

/-- Parametric R-Family carrier over base `k`. The minimum instance is
    `k = Bool ≅ F_2`, recovering the canonical `R N` from
    `Foundation/R/Basic.lean`. -/
def RFamily (k : Type _) (N : ℕ) : Type _ := Fin N → k

namespace RFamily

variable {k : Type _}

/-! ## § 2 F_2-specialization: `RFamily Bool N` recovers `R N`

The minimum-base specialization `k = Bool` recovers the canonical R-Family
over `F_2` formalized in `Foundation/R/Basic.lean`. This identity is a
definitional equality. -/

/-- The `F_2`-specialization: `RFamily Bool N` is **definitionally**
    `R N`. This anchors the parametric form to the existing canonical
    R-Family over `Bool`. -/
example (N : ℕ) : RFamily Bool N = R N := rfl

/-- Restate the previous example as a named theorem for downstream use. -/
theorem rfamily_bool_eq_R (N : ℕ) : RFamily Bool N = R N := rfl

/-! ## § 3 Basic structure instances (parametric)

These instances lift automatically from the `Fin N → k` definition via
the `Pi`-type machinery. They cover the minimum amount of structure
needed to talk about R-Family-over-`k` carriers uniformly. -/

/-- When `k` is finite, `RFamily k N` is finite. Cardinality
    `|RFamily k N| = |k|^N` (proof inherited from `Fintype.card_fun`,
    not restated here). -/
instance instFintype (k : Type _) [Fintype k] (N : ℕ) :
    Fintype (RFamily k N) :=
  inferInstanceAs (Fintype (Fin N → k))

/-- Decidable equality of `RFamily k N` when `k` has decidable equality.
    Matches the `R N` instance from `Foundation/R/Basic.lean`. -/
instance instDecidableEq (k : Type _) [DecidableEq k] (N : ℕ) :
    DecidableEq (RFamily k N) :=
  inferInstanceAs (DecidableEq (Fin N → k))

/-- When `k` is inhabited, so is `RFamily k N`. -/
instance instInhabited (k : Type _) [Inhabited k] (N : ℕ) :
    Inhabited (RFamily k N) :=
  ⟨fun _ => default⟩

/-! ## § 4 Coordinate read

Per wen-substrate §3.6.1: the bit-pattern (here: the coordinate
function `Fin N → k`) is the primary identity of every element. -/

/-- Coordinate read: `coord v i = v i`. Mirrors `R.coord` from
    `Foundation/R/Basic.lean`. -/
@[reducible] def coord {k : Type _} {N : ℕ} (v : RFamily k N) (i : Fin N) :
    k := v i

/-! ## § 5 Boundary — what is NOT in this file

Detailed P1–P7 statements parametric in `k` (direct sum, Hom-as-content,
squaring tower, bilinear/quadratic relational structure, M_2(k) atomic
operations) are deferred to per-instance bridges. Specifically:

* For `k = Bool` (the F_2 instance), the full P1–P7 content lives in
  `Foundation/R/{Basic, DirectSum, Tensor, Hom, Bilinear, Aut,
  Phantom, DirectDecomp, BeyondR8, Squaring, SubTower}.lean`.

* For other bases (`ℝ`, `ℂ`, `ℤ_p`, `ℚ_p`, `ℂ_p`, …), per-instance
  files would bridge Mathlib's existing field / module / matrix
  machinery to the R-Family pattern. These are **future work**
  per the three-phase proof programme (wen-substrate §8.9).

This file commits only to the **carrier-level parametric structure** —
the minimum scaffolding to make `RFamily k N` available in the namespace
without disrupting the existing `R N` definition or its proofs. -/

end RFamily

end SSBX.Foundation.R
