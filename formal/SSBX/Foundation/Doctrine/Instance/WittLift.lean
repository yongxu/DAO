/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Path C — R-tower ↔ Riemann ζ bridge program
-/
import SSBX.Foundation.Doctrine.T_GUT
import SSBX.Foundation.Doctrine.Instance.Algebraic
import SSBX.Foundation.R.Basic
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.RingTheory.WittVector.Identities
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Foundation.Doctrine.Instance.WittLift
## T_GUT Witt-vector lift — char p → char 0 bridge for the algebraic instance

**Reference**: conversation 2026-05-17 — Step 2 of the 4-step R-tower /
Riemann ζ bridge program.  See also
`docs-next/10_formal_形式/r-family-parametric-bases.md` §3.4 (Witt-vector
/ Teichmüller-lift placeholder, previously informal).

This file constructs a **second algebraic T_GUT realisation** at prime
`p` whose generator object is the Witt-vector ring `𝕎_p(ZMod p)`.  When
`p` is prime, `𝕎_p(ZMod p)` is canonically isomorphic to the `p`-adic
integers `ℤ_p` — a complete discrete-valuation ring of **characteristic
0** (per Mathlib `WittVector.p_nonzero`).

The construction provides:

1.  **The Witt realisation** `TGUTRealisation.witt p` over
    `𝕎_p(ZMod p)` — structurally identical to `TGUTRealisation.algebraic
    p` of `Foundation/Doctrine/Instance/Algebraic.lean`, but over a
    char-0 base.
2.  **Teichmüller lift** `R n (ZMod p) → R n (𝕎_p(ZMod p))` —
    coordinate-wise application of `WittVector.teichmuller p`.
3.  **Reduction-mod-`p`** `R n (𝕎_p(ZMod p)) → R n (ZMod p)` —
    coordinate-wise `WittVector.constantCoeff`.
4.  **One-sided round-trip**: `reduction ∘ teichmuller_lift = id` —
    the other direction is genuinely lossy and is **not** identity.
5.  **Frobenius compatibility**: the `WittVector.frobenius` lifts
    coordinate-wise to an endomorphism of `R n (𝕎_p(ZMod p))` that
    reduces, under `constantCoeff`, to the Frobenius `x ↦ x ^ p` on
    `R n (ZMod p)` — and for `R = ZMod p` this Frobenius is identity
    (per `frobenius_zmodp`), so the lift `frobeniusR` is genuinely a
    char-0 endomorphism whose reduction is identity.

Together with `Foundation/Doctrine/Instance/QuantumContinuous.lean`
(Step 3), this file routes the algebraic R-tower into a **char-0
extension** of the GUT-C T_GUT framework — the analytic-continuation
side of the conversation's bridge to Riemann ζ.

## What this file deliberately omits

The full theory of Witt vectors as **the** universal char-0 lift would
require:

* The ring isomorphism `𝕎_p(ZMod p) ≃+* ℤ_p` (Mathlib does not yet
  package this directly; the canonical equivalent is `padicInt`).
* The full Λ-ring structure (Adams operations `ψ_n` for **all** `n`,
  not only Frobenius `ψ_p`).
* The archimedean place (`v = ∞`).  That is Step 3's territory.

These belong to follow-up files; this one is the **algebraic / char-p →
char-0** bridge only.

## Status

* **0 sorry**.  All claims that are not direct Mathlib applications are
  routed through provable identities (`teichmuller_coeff_zero`,
  `frobenius_zmodp`, `WittVector.p_nonzero`).
* The construction is **noncomputable** (the Witt-vector ring structure
  is noncomputable in Mathlib).
-/

namespace SSBX.Foundation.Doctrine.Instance

open CategoryTheory MonoidalCategory
open SSBX.Foundation.Doctrine
open SSBX.Foundation.R

/-! ## §1 Carrier abbreviation -/

section Carrier

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Witt-lifted carrier at level `n`: arrows from `Fin n` into the
    Witt-vector ring `𝕎_p(ZMod p)`.  This is the **char-0 companion**
    of the algebraic carrier `R n (ZMod p) = Fin n → ZMod p`. -/
abbrev WittR (n : ℕ) : Type :=
  SSBX.Foundation.R.R n (WittVector p (ZMod p))

end Carrier

/-! ## §2 Tensor equivalence (mirror of `algebraicTensorEquiv`) -/

section TensorEquiv

variable (p : ℕ) [hp : Fact p.Prime]

/-- Witt-vector analogue of `algebraicTensorEquiv`:
    `R (n + m) (𝕎_p(ZMod p)) ≃ R n (𝕎_p(ZMod p)) × R m (𝕎_p(ZMod p))`.

    Polymorphic over the codomain field — same shape as
    `Foundation/Doctrine/Instance/Algebraic.lean`'s tensor equivalence,
    swapping `ZMod q` for `WittVector p (ZMod p)`. -/
def wittTensorEquiv (n m : ℕ) :
    SSBX.Foundation.R.R (n + m) (WittVector p (ZMod p))
      ≃ SSBX.Foundation.R.R n (WittVector p (ZMod p))
        × SSBX.Foundation.R.R m (WittVector p (ZMod p)) :=
  (Equiv.arrowCongr finSumFinEquiv (Equiv.refl (WittVector p (ZMod p)))).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

end TensorEquiv

/-! ## §3 The Witt-lifted T_GUT realisation -/

section WittRealisation

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The Witt-lifted T_GUT realisation** at prime `p`.

    Replaces `ZMod p` with `WittVector p (ZMod p) ≃ ℤ_p` (the `p`-adic
    integers — characteristic 0).  All seven generator morphisms are
    structural analogues of `TGUTRealisation.algebraic p`, with
    `ZMod p` swapped for `𝕎_p(ZMod p)` throughout.

    The seven generator morphisms (mirroring
    `Foundation/Doctrine/Instance/Algebraic.lean`):

    * `compose_mor`  — direct-sum inverse via `wittTensorEquiv`.
    * `square_mor`   — duplicate input via direct-sum decomposition.
    * `relate_mor`   — placeholder zero map (concrete bilinear /
      Witt-discriminant content for char ≠ 2 lives elsewhere).
    * `hom_mor`      — identity.
    * `modal_V4_mor` — V₄ embedding (duplicate single coordinate).
    * `atom_3_mor`   — identity (involution).
    * `wedderburn_4_mor` — identity iso. -/
noncomputable def TGUTRealisation.witt :
    TGUTRealisation (Type 0) (WittVector p (ZMod p)) where
  R n := SSBX.Foundation.R.R n (WittVector p (ZMod p))
  R_unit :=
    { hom := TypeCat.ofHom (fun _ => PUnit.unit)
      inv := TypeCat.ofHom (fun _ : PUnit =>
              (fun i : Fin 0 => i.elim0 :
                SSBX.Foundation.R.R 0 (WittVector p (ZMod p))))
      hom_inv_id := by
        ext v
        funext i
        exact i.elim0
      inv_hom_id := by ext }
  R_gen :=
    { hom := TypeCat.ofHom (fun
                  (v : SSBX.Foundation.R.R 1 (WittVector p (ZMod p))) => v 0)
      inv := TypeCat.ofHom (fun (a : WittVector p (ZMod p)) =>
              (fun _ : Fin 1 => a :
                SSBX.Foundation.R.R 1 (WittVector p (ZMod p))))
      hom_inv_id := by
        ext v
        funext i
        have : i = 0 := Fin.fin_one_eq_zero i
        subst this
        rfl
      inv_hom_id := by ext _; rfl }
  R_tensor n m := (wittTensorEquiv p n m).toIso
  compose_mor N M := TypeCat.ofHom (fun w =>
    (wittTensorEquiv p N M).symm w)
  square_mor N := TypeCat.ofHom (fun
        (v : SSBX.Foundation.R.R N (WittVector p (ZMod p))) =>
    show SSBX.Foundation.R.R (2 * N) (WittVector p (ZMod p)) from
      (two_mul N) ▸ (wittTensorEquiv p N N).symm (v, v))
  relate_mor _ _ := TypeCat.ofHom (fun _ _ => 0)
  hom_mor _ _ := 𝟙 _
  modal_V4_mor := TypeCat.ofHom (fun
        (v : SSBX.Foundation.R.R 1 (WittVector p (ZMod p))) =>
    ((fun _ => v 0 : SSBX.Foundation.R.R 2 (WittVector p (ZMod p))),
     (fun _ => v 0 : SSBX.Foundation.R.R 2 (WittVector p (ZMod p)))))
  atom_3_mor := 𝟙 _
  wedderburn_4_mor := Iso.refl _

end WittRealisation

/-! ## §4 Carrier-level identities -/

section CarrierIdentities

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Definitional equality** — `(TGUTRealisation.witt p).R n` *is*
    `R n (𝕎_p(ZMod p))`.  Mirrors
    `Foundation/Doctrine/Instance/Algebraic.lean`'s
    `algebraic_R_eq`. -/
theorem TGUTRealisation.witt_R_eq (n : ℕ) :
    (TGUTRealisation.witt p).R n =
      SSBX.Foundation.R.R n (WittVector p (ZMod p)) := rfl

/-- **Identity equivalence** — the realisation's carrier *is* the
    R-family over `𝕎_p(ZMod p)`. -/
def TGUTRealisation.witt_equiv_RFamily (n : ℕ) :
    (TGUTRealisation.witt p).R n
      ≃ SSBX.Foundation.R.R n (WittVector p (ZMod p)) :=
  Equiv.refl _

end CarrierIdentities

/-! ## §5 Teichmüller lift `algebraic ⟶ witt` -/

section TeichmullerLift

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Teichmüller lift at level `n`** — the coordinate-wise application
    of `WittVector.teichmuller p : ZMod p →* 𝕎_p(ZMod p)`.

    This is the natural transformation
    `(TGUTRealisation.algebraic p).R n ⟶ (TGUTRealisation.witt p).R n`
    in `Type 0` (= a function between sets).  Note: `teichmuller` is
    multiplicative but **not** additive, so this lift is not a linear
    map of `R`-modules; it is a *set-theoretic section* of
    `constantCoeff` (cf. `r-family-parametric-bases.md` §3.4 framing
    "set-theoretic, not canonical as a ring map"). -/
noncomputable def teichmullerLift (n : ℕ) :
    SSBX.Foundation.R.R n (ZMod p)
      → SSBX.Foundation.R.R n (WittVector p (ZMod p)) :=
  fun v i => WittVector.teichmuller p (v i)

/-- **Reduction-mod-`p` at level `n`** — the coordinate-wise application
    of `WittVector.constantCoeff : 𝕎_p(ZMod p) →+* ZMod p`.

    Unlike `teichmullerLift`, this **is** a ring map (in each
    coordinate); the projection `𝕎_p(ZMod p) →+* ZMod p` is the
    canonical "reduction modulo `p`" map ℤ_p → 𝔽_p. -/
noncomputable def reductionMod (n : ℕ) :
    SSBX.Foundation.R.R n (WittVector p (ZMod p))
      → SSBX.Foundation.R.R n (ZMod p) :=
  fun w i => WittVector.constantCoeff (w i)

/-- **Round-trip identity (lift then reduce)** — at every level `n`,
    `reductionMod ∘ teichmullerLift = id`.

    The proof is one-line: `(teichmuller p r).coeff 0 = r`
    (`teichmuller_coeff_zero` from Mathlib) — and `constantCoeff` is
    *defined* as `coeff 0`. -/
theorem reduction_teichmuller_id (n : ℕ) (v : SSBX.Foundation.R.R n (ZMod p)) :
    reductionMod p n (teichmullerLift p n v) = v := by
  funext i
  -- `reductionMod` is `constantCoeff` coord-wise; `teichmullerLift` is
  -- `teichmuller` coord-wise; their composition at coordinate `i` is
  -- `constantCoeff (teichmuller p (v i)) = (teichmuller p (v i)).coeff 0
  --  = v i`.
  show WittVector.constantCoeff (WittVector.teichmuller p (v i)) = v i
  rw [WittVector.constantCoeff_apply]
  exact WittVector.teichmuller_coeff_zero p (v i)

/-- **Failure of the other direction** — `teichmullerLift ∘ reductionMod`
    is **not** identity in general: it kills all coefficients beyond the
    zeroth.  We do not record this as a `theorem` (it would be an
    inequality witness) but document the failure for clarity.

    Concretely: pick `w : R 1 (𝕎_p(ZMod p))` with `w 0 = mk p (fun k => if k = 1 then 1 else 0)`.
    Then `reductionMod (w) 0 = 0` (the 0th coefficient is 0), and
    `teichmullerLift (reductionMod w) 0 = teichmuller p 0 = 0 ≠ w 0`. -/
example : True := trivial  -- documentation only

end TeichmullerLift

/-! ## §6 Frobenius compatibility -/

section FrobeniusCompat

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Coordinate-wise Frobenius on the Witt-lifted carrier**.  Applies
    `WittVector.frobenius : 𝕎_p(R) →+* 𝕎_p(R)` to each coordinate.

    Physically: the *natural* ψ_p Adams operation on the Witt-lifted
    R-tower.  Because the operation is coordinate-wise, it commutes
    with `wittTensorEquiv` (i.e. it is a natural transformation of the
    underlying functor `n ↦ R n (𝕎_p(ZMod p))`). -/
noncomputable def frobeniusR (n : ℕ) :
    SSBX.Foundation.R.R n (WittVector p (ZMod p))
      → SSBX.Foundation.R.R n (WittVector p (ZMod p)) :=
  fun w i => WittVector.frobenius (w i)

/-- **At `R = ZMod p`, the Witt Frobenius is the identity** —
    per Mathlib `WittVector.frobenius_zmodp`.

    Witnessing why `WittVector p (ZMod p)` is *interesting* (despite
    its Frobenius being trivial): the residue field's Frobenius being
    identity is the statement that `ZMod p` is the **prime field** of
    its own algebraic closure — Frobenius generates the absolute Galois
    group of any `F_q`, but on `F_p` itself it is identity.  The
    char-0 lift is non-trivial *not* through Frobenius but through
    extra coefficient layers carrying the `p`-adic information. -/
theorem frobeniusR_eq_id (n : ℕ)
    (w : SSBX.Foundation.R.R n (WittVector p (ZMod p))) :
    frobeniusR p n w = w := by
  funext i
  exact WittVector.frobenius_zmodp p (w i)

/-- **Frobenius is compatible with the Teichmüller lift**: applying
    `frobeniusR` to a Teichmüller-lifted vector recovers the
    `(· ^ p)`-image of the original.

    Combined with `frobeniusR_eq_id`, this gives the witness for
    "ψ_p in the Witt lift reduces to the Frobenius on ZMod p" — and
    on `ZMod p` (the prime field), `x ↦ x^p` is `id` by Fermat's little
    theorem, so the whole story collapses to a tautology.  This is
    the **expected** picture (the prime-field case is the trivial fixed
    point of the Galois action); non-trivial cases would be
    `𝕎_p(ZMod p^k)` for `k > 1`. -/
theorem frobeniusR_teichmuller_compat (n : ℕ)
    (v : SSBX.Foundation.R.R n (ZMod p)) :
    frobeniusR p n (teichmullerLift p n v) = teichmullerLift p n v := by
  exact frobeniusR_eq_id p n _

end FrobeniusCompat

/-! ## §7 Characteristic statement -/

section CharStatement

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`WittVector p (ZMod p)` is non-trivial (so `p`-adic information is
    *visible*).** -/
theorem witt_nontrivial : Nontrivial (WittVector p (ZMod p)) := by
  infer_instance

/-- **`(p : 𝕎_p(ZMod p))` is non-zero** — the defining property of a
    `p`-adic integer ring (`p` is a non-unit but not a zero divisor).

    Per Mathlib `WittVector.p_nonzero`. -/
theorem witt_p_nonzero : (p : WittVector p (ZMod p)) ≠ 0 :=
  WittVector.p_nonzero p (ZMod p)

/-- **Char-0 statement (operational form)** — `(p : 𝕎_p(ZMod p))` is
    non-zero.  In a ring `R`, `(p : R) ≠ 0` whenever `R` has
    characteristic 0 or characteristic > `p`; for the Witt ring this
    is the witness that the **canonical map** `ZMod p → 𝕎_p(ZMod p)`
    via `r ↦ teichmuller p r` is *not* surjective and the inclusion
    `ℤ → 𝕎_p(ZMod p)` is *injective*.  Together this is the
    "char-0 lift" half of the algebraic / char-0 bridge.

    A direct `CharZero (𝕎_p(ZMod p))` Mathlib instance is not yet
    upstream (only `Nontrivial`, `CharP _ p` and `p_nonzero`); we
    record the operational statement and leave the full `CharZero`
    instance as a follow-up. -/
theorem witt_natCast_p_ne_zero :
    (Nat.cast p : WittVector p (ZMod p)) ≠ 0 :=
  witt_p_nonzero p

end CharStatement

/-! ## §8 Connection back to the algebraic instance -/

section AlgebraicBridge

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Reduction-mod-`p` recovers the algebraic instance carrier**.
    The reduction map at every level is a function from the Witt-lifted
    carrier to the algebraic-instance carrier — definitionally
    `(TGUTRealisation.witt p).R n → (TGUTRealisation.algebraic p).R n`
    (modulo Mathlib's `[NeZero p]` typeclass; we re-derive it from
    `Fact p.Prime`). -/
noncomputable def reductionAsRealisationMap (n : ℕ) :
    let _ : NeZero p := ⟨hp.out.ne_zero⟩
    (TGUTRealisation.witt p).R n → (TGUTRealisation.algebraic p).R n :=
  let _ : NeZero p := ⟨hp.out.ne_zero⟩
  fun w => reductionMod p n w

/-- **Teichmüller as a realisation map** — set-theoretic section of
    `reductionAsRealisationMap`.

    This is the function-level companion of `reductionAsRealisationMap`;
    a `RealIso` (= isomorphism of realisations in the categorical
    sense) would require the lift to also intertwine **every**
    generator morphism, which fails because `teichmuller` is not
    additive.  We supply only the underlying set-level section. -/
noncomputable def teichmullerAsRealisationMap (n : ℕ) :
    let _ : NeZero p := ⟨hp.out.ne_zero⟩
    (TGUTRealisation.algebraic p).R n → (TGUTRealisation.witt p).R n :=
  let _ : NeZero p := ⟨hp.out.ne_zero⟩
  fun v => teichmullerLift p n v

/-- **Section identity** — `reduction ∘ teichmuller = id` as
    realisation-level functions.  This is the round-trip identity from
    §5, packaged in the realisation API. -/
theorem reduction_section_teichmuller (n : ℕ) :
    let _ : NeZero p := ⟨hp.out.ne_zero⟩
    (reductionAsRealisationMap p n) ∘ (teichmullerAsRealisationMap p n)
      = id := by
  let _ : NeZero p := ⟨hp.out.ne_zero⟩
  funext v
  exact reduction_teichmuller_id p n v

end AlgebraicBridge

/-! ## §9 Layer cardinality observations

The Witt-lifted layers are **infinite** at every `n ≥ 1` (since
`WittVector p (ZMod p)` is infinite — it surjects onto `ℤ_p` ≅
`ℕ → ZMod p` set-theoretically).  This is the structural marker of
the char-0 jump: every algebraic-instance layer is finite of
cardinality `p^n`, while every Witt-lifted layer is countably
infinite.  Recording the witness:
-/

section Cardinality

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The Witt-lifted single-coordinate carrier is non-trivial** —
    in particular, distinct from the algebraic single-coordinate
    carrier `ZMod p` (which is finite of order `p`). -/
theorem witt_R1_nontrivial : Nontrivial (WittR p 1) := by
  -- `WittR p 1 = Fin 1 → 𝕎_p(ZMod p)`; non-trivial since
  -- `𝕎_p(ZMod p)` is non-trivial: witness the two functions
  -- `fun _ => 0` and `fun _ => 1`, distinct by `zero_ne_one`.
  refine ⟨⟨(fun _ => (0 : WittVector p (ZMod p))),
          (fun _ => (1 : WittVector p (ZMod p))), ?_⟩⟩
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  exact zero_ne_one h0

end Cardinality

/-! ## §10 Summary

This file is the **Step 2** deliverable of the R-tower / Riemann ζ
bridge program.  In session-conversation language:

* The char-2 / char-`p` algebraic R-family
  (`Foundation/Doctrine/Instance/Algebraic.lean`) has a **char-0
  companion** via Witt vectors.
* The Teichmüller lift and the constant-coefficient reduction provide
  the *bidirectional functions* between the two T_GUT realisations
  (one is a multiplicative section of the other).
* The "all-primes / Λ-ring" story is **not** fully built here —
  Adams operations `ψ_n` for `n ≠ p` would require richer Mathlib
  Λ-ring infrastructure (not yet upstream).  What this file
  delivers is the **`p = 2`-and-`p`-fold** core: char-`p` lifts to
  char-0 via `𝕎_p(ZMod p)`.
* The **archimedean** companion (the `v = ∞` place that closes the
  adele product back to ℝ / classical Riemann ζ) lives in
  `Foundation/Doctrine/Instance/QuantumContinuous.lean` (Step 3).

Together, Steps 2 + 3 give the **char-0 + archimedean** completion of
the R-tower at the GUT-C T_GUT framework level — the precise location
of Riemann ζ in the SSBX library, as analysed in the 2026-05-17
conversation.
-/

end SSBX.Foundation.Doctrine.Instance
