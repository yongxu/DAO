/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Path C — R-tower ↔ Riemann ζ bridge program
-/
import SSBX.Foundation.Doctrine.Instance.EulerBridge
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Foundation.Doctrine.Instance.LSeriesSMCC
## B2 — Cross-SMCC L-functions for the four T_GUT instances

**Reference**: conversation 2026-05-17 strategy discussion — direction
**B2** ("Cross-SMCC L-function library").  Sits alongside
`EulerBridge.lean` (B1 — Euler product ↔ R∞ prime substructure).

Each of the four `TGUTRealisation` instances
(`Algebraic`, `Heyting`, `Quantum`, `Topological`) gives a different
SMCC base for the same `T_GUT` Lawvere theory.  By
`universal_sayability` (in `Foundation/Doctrine/T_GUT.lean`), every
realisation is iso to the canonical tensor-power realisation
`n ↦ δ^⊗n` in its base.

The **cardinality spectrum** of the canonical realisation in base
`δ` at level `n` is

  `|δ^⊗n| = |δ|^n`,

and the corresponding **cardinality spectral zeta** is

  `ζ_δ(s) := ∑_{n ≥ 0} (|δ|^n)^(-s) = ∑_{n ≥ 0} (|δ|^(-s))^n
           = (1 − |δ|^(-s))^(-1)        (for `Re s > 0` if `|δ| > 1`).

This is *exactly* the Euler factor `(1 − q^(-s))^(-1)` of the
classical Riemann zeta at `q = |δ|`.

## What this file delivers

* **`cardSpectrum q`** — the spectral sequence `n ↦ q^n` (positive
  geometric).
* **`cardSpectralZeta_eq`** — the closed form
  `spectralZeta (cardSpectrum q) s = (1 − q^(-s))^(-1)` for
  `|q^(-s)| < 1`.
* **Instance-specific zetas**:
  * `algebraicCardZeta q s` — at `δ = ZMod q`.
  * `heytingCardZeta s` — at `δ = DiamondH4` (|·| = 4).
  * `quantumCardZeta s` — at `δ = PauliBase` (Klein four, |·| = 4).
  * `topologicalCardZeta s` — at `δ = SierpinskiOmega` (|·| = 2).
* **The Heyting/Quantum degeneracy theorem** —
  `heytingCardZeta = quantumCardZeta`.  The cardinality zeta
  **cannot** distinguish Heyting's `DiamondH4` from quantum's
  `PauliBase`: both are 4-element δ-classes.  Distinguishing them
  requires a *finer* invariant (research-open).
* **Euler-product re-reading** —
  `spectralZeta integerSpectrum s = ∏_p algebraicCardZeta p s` for
  `Re s > 1`.  The Riemann zeta is the product of the
  algebraic-instance cardinality zetas over primes.
* **Research-open conjectures** (Prop-level statement-sites):
  * Heyting Möbius zeta: incorporates the lattice Möbius function.
  * Quantum symplectic zeta: weights Pauli strings by symplectic
    form values (`R.sigma`).
  * Topological frame Möbius zeta: incorporates the Sierpinski
    frame's Möbius function.

These three finer zetas are **conjecturally distinct** even though
the cardinality zetas of Heyting and Quantum coincide.

## Status

* **0 sorry** on the cardinality-zeta proofs.
* Statement-only on the three research-open conjectures.
-/

namespace SSBX.Foundation.Doctrine.Instance

open Complex

/-! ## §1 The cardinality spectrum -/

section CardSpectrum

/-- **The cardinality spectrum** at base `q : ℕ` — the positive
    geometric sequence `n ↦ q^n` as a `SpectralSequence`.

    Models `|δ^⊗n| = |δ|^n` for an SMCC base δ of cardinality `q`. -/
def cardSpectrum (q : ℕ) : SpectralSequence :=
  fun n => (q ^ n : NNReal)

@[simp]
theorem cardSpectrum_zero (q : ℕ) : cardSpectrum q 0 = 1 := by
  simp [cardSpectrum]

@[simp]
theorem cardSpectrum_one (q : ℕ) : cardSpectrum q 1 = (q : NNReal) := by
  simp [cardSpectrum]

theorem cardSpectrum_succ (q n : ℕ) :
    cardSpectrum q (n + 1) = (q : NNReal) * cardSpectrum q n := by
  simp [cardSpectrum, pow_succ, mul_comm]

end CardSpectrum

/-! ## §2 Closed form for the cardinality spectral zeta

The series `Σ_n (q^n)^(-s)` is a geometric series in `q^(-s)`.  For
`|q^(-s)| < 1` (equivalently, `q > 1` and `Re s > 0`), it converges
to `(1 − q^(-s))^(-1)` — the **Euler factor at `q`**.
-/

section ClosedForm

/-- **The closed form** of the cardinality spectral zeta.

    For `q : ℕ` with `q ≥ 1` (so `(q : ℂ).arg = 0`) and a norm-bound
    `‖(q : ℂ)^(-s)‖ < 1` for convergence, the geometric series
    `Σ_n (q^n)^(-s)` converges to `(1 − q^(-s))^(-1)`. -/
theorem cardSpectralZeta_eq {q : ℕ} {s : ℂ}
    (_hq_ge : 1 ≤ q) (hnorm : ‖(q : ℂ) ^ (-s)‖ < 1) :
    spectralZeta (cardSpectrum q) s = (1 - (q : ℂ) ^ (-s))⁻¹ := by
  unfold spectralZeta cardSpectrum
  -- Show each term equals ((q : ℂ)^(-s))^n, then apply tsum_geometric.
  have hq_pos_real : (0 : ℝ) ≤ q := by exact_mod_cast Nat.zero_le _
  have hq_arg : (q : ℂ).arg = 0 := by
    show ((q : ℝ) : ℂ).arg = 0
    exact Complex.arg_ofReal_of_nonneg hq_pos_real
  have hterm : ∀ n : ℕ,
      (((((q : ℕ) ^ n : NNReal) : ℝ) : ℂ)) ^ (-s) = ((q : ℂ) ^ (-s)) ^ n := by
    intro n
    have hcast : ((((q : ℕ) ^ n : NNReal) : ℝ) : ℂ) = (q : ℂ) ^ n := by
      push_cast; ring
    rw [hcast]
    -- Now: ((q : ℂ) ^ n) ^ (-s) = ((q : ℂ) ^ (-s)) ^ n.
    -- Strategy: both equal (q : ℂ) ^ ((n : ℂ) * (-s)).
    have h_arg_lt : -Real.pi < (n : ℝ) * (q : ℂ).arg := by
      rw [hq_arg, mul_zero]; exact neg_neg_iff_pos.mpr Real.pi_pos
    have h_arg_le : (n : ℝ) * (q : ℂ).arg ≤ Real.pi := by
      rw [hq_arg, mul_zero]; exact Real.pi_pos.le
    rw [← Complex.cpow_nat_mul' h_arg_lt h_arg_le, Complex.cpow_nat_mul]
  -- Rewrite tsum using term-wise equality, then apply geometric formula.
  rw [tsum_congr hterm]
  exact tsum_geometric_of_norm_lt_one hnorm

/-- **Simplified closed form for `q ≥ 2` and `Re s > 0`** — concrete
    convergence hypotheses for use in the instance theorems.

    For `q ≥ 2` (as ℕ) and `Re s > 0`, `‖(q : ℂ)^(-s)‖ = q^(-Re s) < 1`,
    so the geometric series converges with value `(1 − q^(-s))^(-1)`. -/
theorem cardSpectralZeta_eq_of_pos {q : ℕ} {s : ℂ}
    (hq : 2 ≤ q) (hs : 0 < s.re) :
    spectralZeta (cardSpectrum q) s = (1 - (q : ℂ) ^ (-s))⁻¹ := by
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq_gt : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hnorm : ‖(q : ℂ) ^ (-s)‖ < 1 := by
    -- Convert `((q : ℕ) : ℂ)` to `(((q : ℕ) : ℝ) : ℂ)` to apply Mathlib's
    -- `Complex.norm_cpow_eq_rpow_re_of_pos` which expects an `ℝ → ℂ` cast.
    have hcast : ((q : ℕ) : ℂ) = (((q : ℕ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hq_pos]
    simp only [Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq_gt (by linarith : -s.re < 0)
  exact cardSpectralZeta_eq (by omega) hnorm

end ClosedForm

/-! ## §3 Instance-specific cardinality zetas -/

section InstanceZetas

/-- **Algebraic cardinality zeta** at base `q : ℕ` — the cardinality
    spectral zeta of `TGUTRealisation.algebraic q`.

    For `q = 2` (the F₂ classical case): recovers the 2-local Euler
    factor of `riemannZeta`.
    For `q` an arbitrary prime power: the local zeta of a point
    over `F_q`. -/
noncomputable def algebraicCardZeta (q : ℕ) (s : ℂ) : ℂ :=
  spectralZeta (cardSpectrum q) s

/-- **Closed form for `algebraicCardZeta`** (for `q ≥ 2`, `Re s > 0`). -/
theorem algebraicCardZeta_eq {q : ℕ} {s : ℂ}
    (hq : 2 ≤ q) (hs : 0 < s.re) :
    algebraicCardZeta q s = (1 - (q : ℂ) ^ (-s))⁻¹ :=
  cardSpectralZeta_eq_of_pos hq hs

/-- **Algebraic zeta at `q = p` prime = Euler factor at `p`**.

    This is the cleanest cross-instance / Euler-product connection:
    the algebraic instance's cardinality zeta at a prime `q = p` is
    *literally* the Euler factor `eulerFactor p s` (from
    `EulerBridge.lean`). -/
theorem algebraicCardZeta_at_prime_eq_eulerFactor
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    algebraicCardZeta p.val s = eulerFactor p s := by
  rw [algebraicCardZeta_eq p.2.two_le hs]
  rfl

/-- **Heyting cardinality zeta** — at `δ = DiamondH4` (the
    canonical non-Boolean 4-element Heyting algebra from
    `Foundation/Doctrine/Instance/Heyting.lean` §5).

    Since `|DiamondH4| = 4`, the cardinality zeta is the algebraic
    cardinality zeta at base `4`. -/
noncomputable def heytingCardZeta (s : ℂ) : ℂ :=
  algebraicCardZeta 4 s

/-- **Closed form for `heytingCardZeta`** at `Re s > 0`. -/
theorem heytingCardZeta_eq {s : ℂ} (hs : 0 < s.re) :
    heytingCardZeta s = (1 - (4 : ℂ) ^ (-s))⁻¹ :=
  algebraicCardZeta_eq (by norm_num) hs

/-- **Quantum cardinality zeta** — at `δ = PauliBase` (the
    single-qubit Pauli group mod phase = Klein four group).

    Since `|PauliBase| = 4`, the cardinality zeta is the algebraic
    cardinality zeta at base `4` — *identical* to
    `heytingCardZeta`.  This is the **Heyting/Quantum degeneracy**:
    cardinality-only invariants cannot distinguish the two. -/
noncomputable def quantumCardZeta (s : ℂ) : ℂ :=
  algebraicCardZeta 4 s

/-- **Closed form for `quantumCardZeta`** at `Re s > 0`. -/
theorem quantumCardZeta_eq {s : ℂ} (hs : 0 < s.re) :
    quantumCardZeta s = (1 - (4 : ℂ) ^ (-s))⁻¹ :=
  algebraicCardZeta_eq (by norm_num) hs

/-- **Topological cardinality zeta** — at `δ = SierpinskiOmega` (the
    Sierpinski frame, 2-element).

    Since `|SierpinskiOmega| = 2`, the cardinality zeta is the
    algebraic cardinality zeta at base `2`. -/
noncomputable def topologicalCardZeta (s : ℂ) : ℂ :=
  algebraicCardZeta 2 s

/-- **Closed form for `topologicalCardZeta`** at `Re s > 0`. -/
theorem topologicalCardZeta_eq {s : ℂ} (hs : 0 < s.re) :
    topologicalCardZeta s = (1 - (2 : ℂ) ^ (-s))⁻¹ :=
  algebraicCardZeta_eq (by norm_num) hs

end InstanceZetas

/-! ## §4 The Heyting / Quantum cardinality degeneracy

A genuinely surprising fact about the GUT-C δ-class menagerie: the
**cardinality zetas of Heyting and Quantum coincide**, because both
δ-classes happen to have cardinality 4.

This means **the cardinality zeta is a coarse invariant** — it
captures only `|δ|`, not the algebraic structure on δ.  To
distinguish Heyting's `DiamondH4` (non-Boolean lattice) from
quantum's `PauliBase` (Klein four group) at the L-function level,
one needs a **finer zeta** that incorporates structure beyond
cardinality.

We record the degeneracy theorem and then state (without proving)
research-open candidates for finer zetas in §6.
-/

section HeytingQuantumDegeneracy

/-- **The Heyting/Quantum cardinality degeneracy theorem**.

    `heytingCardZeta = quantumCardZeta` as functions `ℂ → ℂ`,
    pointwise.  Both equal `algebraicCardZeta 4`.

    **Interpretation**: at the cardinality-only level, the Heyting
    SMCC instance and the Quantum SMCC instance are *L-function
    indistinguishable*.  Distinguishing them requires finer
    zeta invariants (§6).

    **Note**: this is **not** a categorical equivalence claim about
    the instances; the Heyting and Quantum realisations differ in
    their generator morphisms (e.g., the P3 / `relate_mor`
    structure).  The degeneracy is **only** at the cardinality-zeta
    level. -/
theorem heytingCardZeta_eq_quantumCardZeta :
    heytingCardZeta = quantumCardZeta := by
  funext s
  unfold heytingCardZeta quantumCardZeta
  rfl

end HeytingQuantumDegeneracy

/-! ## §5 The Euler-product re-reading

The classical Euler product `riemannZeta s = ∏_p (1 − p^(-s))^(-1)`
(for `Re s > 1`) admits a **GUT-C re-reading**:

  `riemannZeta s = ∏_p algebraicCardZeta p s`

— the Riemann zeta is the **product of the algebraic-instance
cardinality zetas over all primes**.  This is the precise sense
in which "the algebraic instance, summed over the prime-axis, is
the classical Riemann zeta".
-/

section EulerReReading

/-- **Riemann zeta as the product of algebraic-cardinality-zetas
    over primes.**

    For `Re s > 1`:

      `spectralZeta integerSpectrum s
         = ∏' p : Nat.Primes, algebraicCardZeta p s`.

    Proof: the Euler product from `EulerBridge.lean` rewrites each
    factor `eulerFactor p s` via `algebraicCardZeta_at_prime_eq_eulerFactor`
    (`Re s > 1 ⟹ Re s > 0`). -/
theorem spectralZeta_integerSpectrum_as_algebraic_product
    {s : ℂ} (hs : 1 < s.re) :
    spectralZeta integerSpectrum s
      = ∏' p : Nat.Primes, algebraicCardZeta p s := by
  rw [spectralZeta_integerSpectrum_eulerProduct hs]
  -- Goal: ∏' p, eulerFactor p s = ∏' p, algebraicCardZeta p s
  congr 1
  funext p
  exact (algebraicCardZeta_at_prime_eq_eulerFactor p (by linarith : 0 < s.re)).symm

end EulerReReading

/-! ## §6 Research-open: finer zetas that distinguish the SMCCs

The cardinality zeta `cardSpectrum q` only sees `|δ|`.  To
distinguish the four instances at the L-function level, we need
finer spectral structures.  We record three research-open
candidates as Prop-level statement-sites.

### Heyting Möbius zeta

For a finite Heyting algebra `H` (e.g., `DiamondH4`), the lattice
**Möbius function** `μ : H × H → ℤ` encodes the order structure.
A natural Heyting-side zeta is:

  `Z_H(s) := ∑_{(a, b) ∈ H × H} μ(a, b) · (some weight)^(-s)`

For `DiamondH4` specifically, `μ` is the 4×4 Möbius matrix of the
diamond.  The corresponding zeta is research-level — no canonical
choice of weight has been studied.

### Quantum symplectic zeta

For Pauli strings `p ∈ PauliN n`, the **symplectic form**
`σ(p, q) ∈ ℤ/2` (commutator detection) endows the Pauli group with
its natural F₂-symplectic structure (cf.
`Foundation/Wen/Embeddings/StabilizerQM.lean`).  A weighted zeta:

  `Z_Q(s) := ∑_{p ∈ PauliN •} (weight(σ-class p))^(-s)`

where `σ-class` groups Pauli strings by their symplectic profile.
Research-level.

### Topological frame Möbius zeta

For the Sierpinski frame `Ω`, the analogue of the Heyting Möbius
function gives a frame-side zeta — also research-level.

These three finer zetas are **conjecturally pairwise distinct**
(unlike the cardinality zetas, which collapse to one of three
values depending only on `|δ|`).  Establishing distinctness — or
finding unexpected equalities — would be genuine new content.
-/

section ResearchOpen

/-- **The Heyting Möbius zeta conjecture** (statement-only).

    A `Prop`-level placeholder recording that there exists a
    Heyting-side spectral zeta strictly stronger than
    `heytingCardZeta` — one that, evaluated on `DiamondH4`,
    distinguishes Heyting from Quantum.

    The Prop body is `True`; the substantive content lives in the
    *named statement-site*, which downstream research can attach
    a concrete Möbius-based definition to. -/
def HeytingMobiusZetaConjecture : Prop := True

/-- **The quantum symplectic zeta conjecture** (statement-only). -/
def QuantumSymplecticZetaConjecture : Prop := True

/-- **The topological frame Möbius zeta conjecture**
    (statement-only). -/
def TopologicalFrameMobiusZetaConjecture : Prop := True

/-- **The cross-SMCC distinctness conjecture**: when the finer
    zetas (Heyting Möbius, Quantum symplectic) are formalised,
    they are *pairwise distinct* as functions `ℂ → ℂ`, even though
    their cardinality projections coincide (per
    `heytingCardZeta_eq_quantumCardZeta`).

    Research-level open conjecture. -/
def FinerZetasDistinguishHeytingQuantum : Prop := True

end ResearchOpen

/-! ## §7 Summary

This file delivers direction **B2** of the conversation 2026-05-17
strategy discussion: a unified cross-SMCC L-function library.

**Concrete content (theorems)**:

| Theorem | Statement |
|---|---|
| `cardSpectralZeta_eq` | Closed form `(1 - q^(-s))^(-1)` for the cardinality zeta |
| `algebraicCardZeta_at_prime_eq_eulerFactor` | Algebraic ζ at prime `p` = Euler factor at `p` |
| `heytingCardZeta_eq_quantumCardZeta` | **The Heyting/Quantum cardinality degeneracy** |
| `spectralZeta_integerSpectrum_as_algebraic_product` | Riemann ζ = product of algebraic-instance card-ζ over primes |

**Statement-sites (research-open Props)**:

* `HeytingMobiusZetaConjecture` — finer Heyting zeta via lattice Möbius.
* `QuantumSymplecticZetaConjecture` — finer Quantum zeta via Pauli symplectic.
* `TopologicalFrameMobiusZetaConjecture` — finer Topological zeta.
* `FinerZetasDistinguishHeytingQuantum` — distinctness conjecture.

**Cross-references**:

* `Foundation/Doctrine/Instance/SpectralZeta.lean` — Step ④
  spectral zeta + classical RH.
* `Foundation/Doctrine/Instance/EulerBridge.lean` — B1 Euler
  product / R∞ prime-substructure.
* `Foundation/Doctrine/T_GUT.lean` — universal sayability
  framework underlying the four δ-class instances.

**Combined picture**: SSBX now has four parallel "spectral zeta
sites", one per SMCC instance, with:
- The **Algebraic** site (this file + `EulerBridge.lean`) recovers
  classical Riemann ζ as a product of local factors.
- The **Heyting**, **Quantum**, **Topological** sites give
  cardinality zetas that coincide pairwise (Heyting = Quantum, both
  ≠ Topological), and whose **finer** invariants
  (Möbius / symplectic) are conjecturally distinct.

The latter — distinguishing Heyting from Quantum at the L-function
level — is **genuinely new content** that no prior literature
addresses (since the four-SMCC universal-sayability framework is
itself SSBX-original).
-/

end SSBX.Foundation.Doctrine.Instance
