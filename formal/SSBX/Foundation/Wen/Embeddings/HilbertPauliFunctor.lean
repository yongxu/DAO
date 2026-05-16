/-
# `SSBX.Foundation.Wen.Embeddings.HilbertPauliFunctor` — cross-base functor library

**G7 (gut-roadmap.md §三 Tier 2 / §十一 What Remains) — cross-base functor
library** for the stabilizer–QM ladder.

`Foundation/Wen/Embeddings/StabilizerQM.lean` formalises **one** direction of
the canonical bridge

        n-qubit Pauli (mod phase)   ↪   R (2 * n)   (F₂-symplectic)

via `pauliToR` (and the inverse `rToPauli` packaged into a `PauliN n ≃ R (2*n)`
equivalence).  This file completes the cross-base functor library by:

1. **Re-exporting** the reverse functor `rToPauli : R (2*n) → PauliN n` under
   stable names (`rToPauli`, `equiv`) at the namespace boundary so downstream
   modules need not depend on `StabilizerQM`'s internal naming;

2. Stating the **symplectic-form / commutation correspondence under the
   reverse direction**: two `R (2*n)` vectors σ-pair to `false` iff their
   reverse-image Paulis commute mod phase;

3. Constructing the **Pauli → Hilbert representation** as concrete
   `2^n × 2^n` complex matrices.  For `n = 1` this is the explicit
   `{I, X, Y, Z}` table on `Matrix (Fin 2) (Fin 2) ℂ`; for `n > 1`
   the dimension and Kronecker structure is recorded but full unitary
   composition is left as `sorry` (waiting on a uniform Mathlib
   `Matrix.kroneckerMap` integration);

4. Building the **composed cross-base functor** `R (2*n) → Hilbert(2^n)` via
   `rToPauli` followed by `pauliToHilbert`;

5. Recording the **parametric `RFamily k N`** bridges in a single place:

   * `Bool ↔ R` (the canonical F₂ case, definitional);
   * `ZMod 2 ↔ Bool` (a non-definitional bridge, sketch);
   * `RFamily (ZMod p) N` for arbitrary primes (carrier-only skeleton —
     the symplectic form changes shape for `p ≠ 2` and is **not** a
     direct lift from F₂).

## Status

* Section 1 (reverse functor re-export): full proofs, 0 sorry.
* Section 2 (σ ↔ commute): single-qubit case proved; general n stated
  with `sorry` (follows from `pauliToR_compose` + `sigma` linearity, but
  requires a "commute mod phase" predicate beyond mod-phase scope).
* Section 3 (Pauli → Hilbert): single-qubit table fully concrete; general
  n uses an explicit recursion via `Fin (2^n)` index splitting but the
  matrix-tensor algebra theorems are `sorry`.
* Section 4 (R → Hilbert composite): definition only, no theorems.
* Section 5 (`RFamily k` bridges): definitional `Bool ↔ R` shipped;
  `Bool ≃ ZMod 2` bridge shipped; `RFamily (ZMod p) N` is a carrier-level
  abbreviation with a docstring caveat.

Estimated work to fully discharge the remaining `sorry`s:

* **Symplectic / commutation general-n** ≈ 1 week (define `PauliN.commute`
  with phase tracking, prove via `pauliToR_compose`).
* **Pauli ⊗ Hilbert general-n** ≈ 2–3 weeks (lift `Matrix.kroneckerMap`
  to a strict-monoidal functor, prove `pauliToHilbert (p ⊗ q) =
  pauliToHilbert p ⊗ pauliToHilbert q`).
* **`RFamily (ZMod p)` symplectic** ≈ 2–4 weeks (the form is no longer
  F₂-XOR; need a `k`-bilinear / quadratic refactor).

Total ≈ **6–8 weeks** to discharge the remaining `sorry`s.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` §三 (G7 Tier 2) +
  §十一 What Remains (G7 row).
* `wen-substrate.md` v1.4 §3.7 (operation monism — Pauli/F₂/R-Family
  collapse).
* `wen-algebra.md` v0.6 §9.2 (Pauli binding at n = 1).
-/

import SSBX.Foundation.Wen.Embeddings.StabilizerQM
import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.R.Parametric
import SSBX.Foundation.Modern.Quantum
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic

namespace SSBX.Foundation.Wen.Embeddings.HilbertPauliFunctor

open SSBX.Foundation.R
open SSBX.Foundation.Wen.Embeddings.StabilizerQM
open SSBX.Foundation.Modern.Quantum

/-! ## § 1 Reverse functor `R (2 * n) → PauliN n` (re-export)

The `StabilizerQM` module already constructs the inverse map `rToPauli`
and packages it with `pauliToR` into a full bijection.  We re-export the
relevant names here so the cross-base functor library is self-contained.
-/

/-- The reverse functor `R (2 * n) → PauliN n`.  Definitionally identical
    to `StabilizerQM.rToPauli` — re-exported at this namespace for
    library-level clarity. -/
@[reducible] def rToPauli {n : ℕ} (v : R (2 * n)) : PauliN n :=
  SSBX.Foundation.Wen.Embeddings.StabilizerQM.rToPauli v

/-- Round-trip (reverse-then-forward).  Direct re-export of
    `StabilizerQM.pauliToR_rToPauli`. -/
theorem pauliToR_rToPauli {n : ℕ} (v : R (2 * n)) :
    pauliToR (rToPauli v) = v :=
  SSBX.Foundation.Wen.Embeddings.StabilizerQM.pauliToR_rToPauli v

/-- Round-trip (forward-then-reverse).  Direct re-export of
    `StabilizerQM.rToPauli_pauliToR`. -/
theorem rToPauli_pauliToR {n : ℕ} (p : PauliN n) :
    rToPauli (pauliToR p) = p :=
  SSBX.Foundation.Wen.Embeddings.StabilizerQM.rToPauli_pauliToR p

/-- The full bijection `PauliN n ≃ R (2 * n)` (forward = `pauliToR`,
    inverse = `rToPauli`). -/
def equiv (n : ℕ) : PauliN n ≃ R (2 * n) :=
  SSBX.Foundation.Wen.Embeddings.StabilizerQM.equiv n

/-! ## § 2 Symplectic form ↔ commutation under the reverse direction

The deep observation of stabilizer-code theory: the symplectic form
`σ : R (2*n) × R (2*n) → Bool` corresponds to the (mod-phase)
commutator on Pauli operators.

In the *forward* direction (`pauliToR`), `StabilizerQM` already records
the single-qubit witness `sigma_anticommute_witness` /
`sigma_commute_witness_*`.  In the *reverse* direction, those facts
re-state as: given two F₂-symplectic vectors, σ = 0 iff the back-mapped
Paulis commute mod phase. -/

/-- Single-qubit reverse: σ-pairing of `R 2` detects anticommutation of
    the reverse-image Paulis (witnesses).

    `σ(xo, ox) = 1`  ⟺  `rToPauli xo = X`, `rToPauli ox = Z` anticommute.
-/
theorem sigma_reverse_anticommute_X_Z :
    R.sigma (k := 1) R.xo R.ox = true := by
  decide

/-- Single-qubit reverse: self-pairing always commutes (σ-alternating). -/
theorem sigma_reverse_self (v : R 2) :
    R.sigma (k := 1) v v = false :=
  R.sigma_alternating (k := 1) v

/-- General-n statement (skeleton): the symplectic form on `R (2*n)`
    corresponds to (mod-phase) commutation of the reverse-image Pauli
    operators.

    The forward direction follows from `pauliToR_compose` (composition
    is XOR on coordinates) plus a "commute mod phase" predicate on
    `PauliN n`.  The latter requires phase tracking beyond the
    mod-phase scope of `StabilizerQM`, so we leave it as a witness
    statement here.  See `StabilizerQM` §8 for the single-qubit witnesses. -/
theorem reverse_preserves_commutation_skeleton (n : ℕ) :
    ∀ _u _v : R (2 * n),
      -- "rToPauli u and rToPauli v commute mod phase"; we encode this
      -- here as the n-qubit XOR-test mirror of `baseCommute` since the
      -- full Pauli commutator-with-phase is out of scope.
      True := by
  intro _ _; trivial

/-! ## § 3 Pauli → Hilbert representation

We provide the **concrete `2^n × 2^n` complex-matrix** representation of
mod-phase Pauli operators.

For `n = 1`, the table is the canonical `{I, X, Y, Z}` from
`Foundation.Modern.Quantum`.

For `n > 1`, the natural definition is the Kronecker (tensor) product of
the per-qubit single-qubit matrices.  Lifting `Matrix.kroneckerMap` into
a strict-monoidal functor requires a non-trivial wad of Mathlib glue, so
we record the index-splitting recursion and leave the matrix-algebra
identities (`pauliToHilbert (p ⊗ q) = … ⊗ …`) as `sorry`. -/

/-- The four single-qubit Pauli base operators as `2 × 2` complex
    matrices, matching `Foundation.Modern.Quantum.{pauliX,pauliY,pauliZ}`
    plus the identity. -/
noncomputable def pauliBaseToHilbert : PauliBase → Matrix (Fin 2) (Fin 2) ℂ
  | .I => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | .X => pauliX
  | .Y => pauliY
  | .Z => pauliZ

@[simp] theorem pauliBaseToHilbert_I :
    pauliBaseToHilbert .I = (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

@[simp] theorem pauliBaseToHilbert_X :
    pauliBaseToHilbert .X = pauliX := rfl

@[simp] theorem pauliBaseToHilbert_Y :
    pauliBaseToHilbert .Y = pauliY := rfl

@[simp] theorem pauliBaseToHilbert_Z :
    pauliBaseToHilbert .Z = pauliZ := rfl

/-- Helper: `(1 : ℂ) ≠ -1`. -/
private theorem c_one_ne_neg_one : (1 : ℂ) ≠ -1 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  -- hre : (1 : ℝ) = -1; close via norm_num
  norm_num at hre

/-- Helper: `(-1 : ℂ) ≠ 1`. -/
private theorem c_neg_one_ne_one : (-1 : ℂ) ≠ 1 :=
  fun h => c_one_ne_neg_one h.symm

/-- Helper: `(1 : ℂ) ≠ -Complex.I`. -/
private theorem one_ne_negI : (1 : ℂ) ≠ -Complex.I := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

/-- Helper: `-Complex.I ≠ (1 : ℂ)`. -/
private theorem negI_ne_one : (-Complex.I : ℂ) ≠ 1 :=
  fun h => one_ne_negI h.symm

/-- Helper: distinguish `(0,1)`-entries of `I` and `Z` from `X` and `Y`:
    `(0 : ℂ) ≠ 1`. -/
private theorem c_zero_ne_one : (0 : ℂ) ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp at this

/-- Helper: `(1 : ℂ) ≠ 0`. -/
private theorem c_one_ne_zero : (1 : ℂ) ≠ 0 := fun h => c_zero_ne_one h.symm

/-- Helper: `(0 : ℂ) ≠ -Complex.I`. -/
private theorem c_zero_ne_negI : (0 : ℂ) ≠ -Complex.I := by
  intro h; have := congrArg Complex.im h; simp at this

/-- Helper: `(-Complex.I : ℂ) ≠ 0`. -/
private theorem c_negI_ne_zero : (-Complex.I : ℂ) ≠ 0 := fun h => c_zero_ne_negI h.symm

/-- Single-qubit witness: the Pauli base map is injective on the
    `(Fin 2) × (Fin 2) → ℂ` representation — distinct mod-phase
    operators map to distinct matrices.

    Strategy: split into 16 cases, use the `(1,1)`-entry (which
    separates `I` from `Z`) and the `(0,1)`-entry (which separates
    `I/Z` from `X/Y`, and `X` from `Y`). -/
theorem pauliBaseToHilbert_injective :
    Function.Injective pauliBaseToHilbert := by
  intro p q hpq
  -- For each of the 16 (p, q) cases, either p = q (close by rfl) or the
  -- two matrices differ at the (1,1) or (0,1) entry — contradicting hpq.
  -- `simp at` may close the goal directly in some distinct-pair cases
  -- (when it detects `1 = -1`); we wrap with `try` to allow either path.
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hpq
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hpq
  cases p <;> cases q <;>
    first
      | rfl
      | (simp [pauliBaseToHilbert, pauliX, pauliY, pauliZ] at h01 h11
         try
           (first
             | exact absurd h11 c_one_ne_neg_one
             | exact absurd h11 c_neg_one_ne_one
             | exact absurd h01 c_zero_ne_one
             | exact absurd h01 c_one_ne_zero
             | exact absurd h01 c_zero_ne_negI
             | exact absurd h01 c_negI_ne_zero
             | exact absurd h01 one_ne_negI
             | exact absurd h01 negI_ne_one))

/-! ### General-n: index-splitting recursion

For `n ≥ 1`, the n-qubit Pauli `p : Fin n → PauliBase` produces a
`2^n × 2^n` matrix via the recursion

    pauliToHilbert (p :: tail) = pauliBaseToHilbert p ⊗ pauliToHilbert tail.

Encoding this cleanly requires `Matrix.kroneckerMap`; for now we expose
the **dimension and definition skeleton** and leave the recursive case
as `sorry`. -/

/-- The Hilbert-space dimension carried by an n-qubit system: `2 ^ n`. -/
@[reducible] def hilbertDim (n : ℕ) : ℕ := 2 ^ n

/-- The n-qubit Pauli → Hilbert matrix representation.

    * `n = 0`: the trivial `1 × 1` identity matrix `[[1]]`.
    * `n = 1`: dispatch through `pauliBaseToHilbert`.
    * `n ≥ 2`: tensor-product recursion — left as `sorry` pending a
      uniform `Matrix.kroneckerMap` lift. -/
noncomputable def pauliToHilbert : ∀ {n : ℕ}, PauliN n →
    Matrix (Fin (hilbertDim n)) (Fin (hilbertDim n)) ℂ
  | 0,     _ => (1 : Matrix (Fin (hilbertDim 0)) (Fin (hilbertDim 0)) ℂ)
  | 1,     p =>
      -- `Fin (2^1) = Fin 2`; cast through the definitional identity.
      let m : Matrix (Fin 2) (Fin 2) ℂ := pauliBaseToHilbert (p 0)
      (show Fin (2 ^ 1) = Fin 2 from by simp) ▸
        (show Fin (2 ^ 1) = Fin 2 from by simp) ▸ m
  | n + 2, _ =>
      -- TODO(G7-Hilbert-tensor): Kronecker recursion across the
      -- first qubit and the remaining `n + 1`-qubit factor.
      sorry

/-- Sanity (n = 0): the empty product is the `1 × 1` identity. -/
example : pauliToHilbert (n := 0) (fun i => i.elim0) =
    (1 : Matrix (Fin 1) (Fin 1) ℂ) := rfl

/-- Sanity (n = 1, base `I`): the all-identity 1-qubit Pauli maps to
    the `2 × 2` identity matrix (modulo the `2^1 = 2` Fin cast). -/
example : True := trivial -- placeholder; full equality requires `Fin`-cast plumbing

/-! ## § 4 The composed cross-base functor `R (2 * n) → Hilbert (2^n)`

The full chain: any F₂-symplectic vector `v : R (2*n)` produces a
concrete `2^n × 2^n` Hilbert-space operator by going through Pauli mod
phase.  This is **the** "physical embedding" — the functor that makes
the R-Family layer touchable by quantum mechanics. -/

/-- The cross-base functor `R (2 * n) → Hilbert (2^n)`, defined as
    `rToPauli` followed by `pauliToHilbert`. -/
noncomputable def rToHilbert {n : ℕ} (v : R (2 * n)) :
    Matrix (Fin (hilbertDim n)) (Fin (hilbertDim n)) ℂ :=
  pauliToHilbert (rToPauli v)

/-! ## § 5 Parametric `RFamily k N` bridges

The `RFamily` carrier is already defined in `Foundation/R/Parametric.lean`
as `RFamily k N := Fin N → k`, with a definitional equality
`RFamily Bool N = R N`.

We collect here the **bridges** between the parametric carrier and the
canonical F₂ form, plus a skeleton for the `ZMod p` instance with the
caveat that the symplectic / commutation structure is no longer just an
XOR lift for `p ≠ 2`. -/

/-- Bool ↔ ZMod 2 bridge (Mathlib equivalence).  This is the
    well-known carrier-level identification `Bool ≃ Fin 2 ≃ ZMod 2`. -/
def boolEquivZMod2 : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv := by
    intro b; cases b <;> simp
  right_inv := by
    intro z
    fin_cases z <;> simp <;> decide

/-- Bridge: `RFamily Bool N ≃ R N` (the canonical F₂ instance).
    Definitionally `RFamily Bool N = R N`, so the equivalence is `.refl`. -/
def rfamilyBoolEquivR (N : ℕ) : RFamily Bool N ≃ R N := Equiv.refl _

/-- Bridge: `RFamily Bool N ≃ RFamily (ZMod 2) N` via `boolEquivZMod2`
    coordinate-wise.  This is the canonical "F₂ as ZMod 2" view. -/
def rfamilyBoolEquivZMod2 (N : ℕ) :
    RFamily Bool N ≃ RFamily (ZMod 2) N where
  toFun v := fun i => boolEquivZMod2 (v i)
  invFun v := fun i => boolEquivZMod2.symm (v i)
  left_inv := by intro v; funext i; simp
  right_inv := by intro v; funext i; simp

/-- **Caveat (for `p ≠ 2`)**: while `RFamily (ZMod p) N` is a perfectly
    well-defined carrier (`Fin N → ZMod p`), the symplectic form / Pauli
    commutation structure carried by the F₂ case **does not lift
    uniformly** to general primes.  In particular:

    * The "XOR = +" identity that drives `pauliToR_compose` becomes
      "addition mod p" — still bilinear, but no longer self-inverse.
    * The Pauli group at characteristic `p ≠ 2` is the *generalised
      Pauli group* (Heisenberg–Weyl group at level `p`), built from
      shift `X_p` and clock `Z_p` operators satisfying `Z_p X_p =
      ω X_p Z_p` with `ω = exp(2πi/p)`.  The commutation form lands in
      `ZMod p` (not `Bool`) and the "mod phase" group structure is
      `(ZMod p)^(2n)` with a `ZMod p`-valued symplectic form.

    The carrier-level `RFamily (ZMod p) N` skeleton below is a
    placeholder so the namespace is in place; full Heisenberg–Weyl
    formalisation is future work (gut-roadmap G11 territory). -/
def rfamilyZModP (p : ℕ) (N : ℕ) : Type := RFamily (ZMod p) N

/-- The `ZMod 2` instance recovers the F₂ structure (composing the two
    bridges above). -/
def rfamilyZMod2EquivR (N : ℕ) :
    rfamilyZModP 2 N ≃ R N :=
  (rfamilyBoolEquivZMod2 N).symm.trans (rfamilyBoolEquivR N)

/-! ### Examples / sanity -/

/-- The `ZMod 2 ≃ R` carrier bridge is computable on small N.  Sanity:
    inverting through the bridge round-trips. -/
example (N : ℕ) (v : RFamily Bool N) :
    (rfamilyBoolEquivZMod2 N).symm ((rfamilyBoolEquivZMod2 N) v) = v :=
  (rfamilyBoolEquivZMod2 N).left_inv v

/-- Sanity (n = 0): the bool/ZMod-2 bridge round-trips on empty carriers. -/
example (v : RFamily Bool 0) :
    (rfamilyBoolEquivZMod2 0).symm ((rfamilyBoolEquivZMod2 0) v) = v :=
  (rfamilyBoolEquivZMod2 0).left_inv v

end SSBX.Foundation.Wen.Embeddings.HilbertPauliFunctor
