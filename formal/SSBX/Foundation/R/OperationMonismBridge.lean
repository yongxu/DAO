/-
# Foundation.R.OperationMonismBridge — RTower Bool ≃ R (2^k)

Per `docs-next/10_formal_形式/wen-substrate.md` v1.2 §3.7.6
("Implications for D2, cuo-equivariance, and Lean code") and §3.7.3
("Carrier as fixed-point of the composition graph").

This module **bridges** the operation-monism iteration
(`Foundation/R/OperationMonism.lean`) to the canonical F₂ carrier
family (`Foundation/R/Basic.lean`):

    RTower Bool k  ≃  R (2^k)

In §3.7.6 we claim that *carriers are theorems, not definitions* —
the carrier family `{R N}` is derivative of the operator iteration
`Σ^k`.  This file makes that claim **real**: the canonical R-Family
carrier at squaring-tower level `2^k` is, up to equivalence, exactly
the `k`-th iterate of the squaring functor `Σ X := X × X` seeded at
`Bool`.

No new axioms, no `sorry`.  The bridge uses only:

* `RTower Bool (k+1) = RTower Bool k × RTower Bool k` (definitional,
  from `OperationMonism.RTower_succ`).
* `R (N + N) ≃ R N × R N` (existing `R.squaringEquiv` from
  `Foundation/R/Squaring.lean`, ultimately `directSumEquiv`).
* `2^(k+1) = 2^k + 2^k` (Mathlib `pow_succ` + `two_mul`).

## Doctrinal anchor

* `wen-substrate.md` v1.2 §3.7.3 (Carrier as fixed-point).
* `wen-substrate.md` v1.2 §3.7.6 (Carriers are theorems, not definitions).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Squaring
import SSBX.Foundation.R.OperationMonism

namespace SSBX.Foundation.R.OperationMonism

open SSBX.Foundation.R

/-! ## § 1 Base case: `RTower Bool 0 ≃ R 1`

`RTower Bool 0 = Bool` by definition.  `R 1 = Fin 1 → Bool` is iso to
`Bool` by evaluation at `0`.  Their composition gives the base case of
the bridge induction. -/

/-- `R 1 ≃ Bool` — the canonical 1-bit carrier identifies with `Bool`
    via evaluation at the unique coordinate.  This is the `N = 1`
    instance of `R N = Fin N → Bool` seen as a singleton-domain
    function space. -/
def R1EquivBool : R 1 ≃ Bool where
  toFun f := f 0
  invFun b := fun _ => b
  left_inv f := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    cases hi
    rfl
  right_inv b := rfl

/-- **Base case of the bridge** : `RTower Bool 0 ≃ R 1`.

    `RTower Bool 0` is definitionally `Bool`; `R 1` is `Fin 1 → Bool`.
    The equivalence is `R1EquivBool` flipped. -/
def rtower_bool_zero : RTower Bool 0 ≃ R 1 :=
  R1EquivBool.symm

/-! ## § 2 Successor case: `RTower Bool (k+1) ≃ RTower Bool k × RTower Bool k`

This is `rfl` by `RTower_succ`. -/

/-- **Successor case of the bridge** : `RTower Bool (k+1)` is
    definitionally `RTower Bool k × RTower Bool k`. -/
def rtower_bool_succ (k : ℕ) :
    RTower Bool (k + 1) ≃ (RTower Bool k × RTower Bool k) :=
  Equiv.refl _

/-! ## § 3 Main bridge: `RTower Bool k ≃ R (2^k)`

The substantive theorem.  By induction on `k`:

* `k = 0`: `RTower Bool 0 ≃ Bool ≃ R 1 = R (2^0)`.
* `k+1`: `RTower Bool (k+1) ≃ RTower Bool k × RTower Bool k`
  (by `rtower_bool_succ`)
  `≃ R (2^k) × R (2^k)` (by IH on both sides)
  `≃ R (2^k + 2^k)` (by `R.squaringEquiv` reversed)
  `= R (2^(k+1))` (by `pow_succ` + `two_mul`).
-/

/-- A cast helper: `R N ≃ R M` whenever `N = M`. -/
def R.castEquiv {N M : ℕ} (h : N = M) : R N ≃ R M := by
  subst h
  exact Equiv.refl _

/-- **The main bridge** : `RTower Bool k ≃ R (2^k)`.

    The operator iteration `Σ^k Bool` (no algebraic structure on the
    seed) reconstructs the canonical F₂ carrier `R (2^k)` of the
    squaring sub-tower.  Per wen-substrate §3.7.6: "carriers are
    theorems, not definitions" — and here is the theorem. -/
def rtowerBoolEquiv : ∀ k, RTower Bool k ≃ R (2^k)
  | 0 => by
    -- RTower Bool 0 = Bool, R (2^0) = R 1, R 1 ≃ Bool
    have h : (2 : ℕ)^0 = 1 := rfl
    exact rtower_bool_zero.trans (R.castEquiv h.symm)
  | k + 1 => by
    -- RTower Bool (k+1) ≃ RTower Bool k × RTower Bool k
    --                  ≃ R (2^k) × R (2^k)
    --                  ≃ R (2^k + 2^k)
    --                  = R (2^(k+1))
    have ih : RTower Bool k ≃ R (2^k) := rtowerBoolEquiv k
    have hpow : (2 : ℕ)^(k+1) = 2^k + 2^k := by
      show 2 ^ k * 2 = 2^k + 2^k
      rw [Nat.mul_two]
    refine (rtower_bool_succ k).trans ?_
    refine (ih.prodCongr ih).trans ?_
    exact (R.squaringEquiv (2^k)).symm.trans (R.castEquiv hpow.symm)

/-! ## § 4 Cardinality corollary

The Fintype-cardinality of `RTower Bool k` is `2^(2^k)` — i.e., the
squaring-tower cardinality table `2, 4, 16, 256, 65536, …` at
`k = 0, 1, 2, 3, 4, …` — derived purely from the operator iteration,
with no algebraic structure on the seed. -/

/-- `RTower Bool k` is a `Fintype` for every `k`, by induction on `k`. -/
instance instFintypeRTowerBool : ∀ k, Fintype (RTower Bool k)
  | 0       => (inferInstance : Fintype Bool)
  | (k + 1) =>
    let _ : Fintype (RTower Bool k) := instFintypeRTowerBool k
    (inferInstance : Fintype (RTower Bool k × RTower Bool k))

/-- **F₂ cardinality table from the operator iteration** :
    `|RTower Bool k| = 2^(2^k)`.

    For `k = 0, 1, 2, 3, 4`: cardinalities `2, 4, 16, 256, 65536`,
    matching `|R 1|, |R 2|, |R 4|, |R 8|, |R 16|`.  Per wen-substrate
    §3.6 / §3.7: this is the F₂ cardinality, derived from the squaring
    law alone, with no algebraic structure assumed on the seed. -/
theorem rtowerBool_card (k : ℕ) :
    Fintype.card (RTower Bool k) = 2 ^ (2 ^ k) := by
  rw [Fintype.card_congr (rtowerBoolEquiv k), R.card_eq]

end SSBX.Foundation.R.OperationMonism
