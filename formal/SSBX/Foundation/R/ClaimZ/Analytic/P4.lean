/-
# Foundation.R.ClaimZ.Analytic.P4 — D1 ⟹ P4 (squaring tower self-similarity)

**GUT roadmap Phase 1 Stream A4** (per
`docs-next/10_formal_形式/gut-roadmap.md`):

This file discharges the **analytic step** `D1 ⟹ P4` for the
F₂-Boolean realisation of the R-Family.  Per
`docs-next/10_formal_形式/wen-substrate/01-foundations.md`:

> **P4** says the substrate is **self-similar under squaring** —
> `R (2N) ≃ R N × R N`.  The R-tower {R 0, R 1, R 2, R 4, R 8, ...}
> arises as `R 1 → R 2 → R 4 → R 8 → ...` via iterated squaring.

For the canonical F₂-Boolean instance, this becomes the concrete
isomorphism

    R (2 * N) ≃ R N × R N              (analytic P4_F2)

witnessed via the existing direct-sum equivalence
`R.directSumEquiv (N := N) (M := N) : R (N + N) ≃ R N × R N` from
`Foundation/R/DirectSum.lean`, plus the `Nat.two_mul` arithmetic
identity `2 * N = N + N`.  This is the **direct-sum form** of the
squaring step (per `wen-algebra` v0.6 §1.3): cardinality doubling
via XOR-direct-sum, not tensor.

The squaring tower (`R 1 → R 2 → R 4 → R 8 → ...`) is the *sub-tower
view* of this equivalence: setting `N` to 1, 2, 4 instantiates the
three non-trivial squaring steps at the R-Family root layers.

## What this file delivers

* `D1_implies_P4_F2 : (N : ℕ) → R (2 * N) ≃ R N × R N` — the named
  analytic-step theorem (the `2 * N` form via `Nat.two_mul`).
* `D1_implies_P4_F2_add_form : (N : ℕ) → R (N + N) ≃ R N × R N` — the
  arithmetic-direct form (= `R.squaringEquiv`); both are exposed for
  downstream callers that prefer one shape over the other.
* `D1_implies_P4_R2_squaring : R 4 ≃ R 2 × R 2` — the canonical
  R 2 → R 4 squaring step (the first non-trivial one in the tower).
* `D1_implies_P4_R4_squaring : R 8 ≃ R 4 × R 4` — the
  R 4 → R 8 squaring step (the ceiling-reaching one).
* `D1_implies_P4_R1_squaring : R 2 ≃ R 1 × R 1` — the atomic
  R 1 → R 2 squaring step.
* `D1_implies_P4_tower : ∀ k, R (2 ^ (k + 1)) ≃ R (2 ^ k) × R (2 ^ k)`
  — the **self-similar tower** statement: the doubling step at the
  squaring-tower indices `1, 2, 4, 8, 16, ...`.
* `D1_implies_P4_F2_card` — cardinality corollary
  `|R (2 * N)| = |R N|^2`.

## Strength of the statement

Two readings are delivered:

1. **Per-`N` form** `R (2 * N) ≃ R N × R N` — the analytic content of
   P4 at every layer index `N`.  This is the **strongest purely-set-
   level form** at δ = Bool (any stronger structure-preservation —
   e.g., the group iso form — follows from this together with the
   `R.append_add` / `R.append_zero` lemmas in `DirectSum.lean`).
2. **Self-similar tower form** `R (2^{k+1}) ≃ R (2^k) × R (2^k)` —
   the **squaring sub-tower** specialisation, used in `Foundation/R/
   OperationMonismBridge.lean` § 3 to relate `RTower Bool k ≃ R (2^k)`.

The bijection is moreover **structure-preserving**: `R.directSumEquiv`
satisfies `append_add` and `append_zero` (proved in DirectSum.lean),
so the F₂-vector-space structure on `R (2 * N)` matches the direct-sum
of the F₂-vector-space structures on the two factors `R N`.

## Relation to other Phase 1 streams

* **A2 (D1 ⟹ P2, direct-sum composition)** — *not used*.  At
  the time of writing, `formal/SSBX/Foundation/R/ClaimZ/Analytic/
  P2.lean` does not exist (A2 is `in_progress`).  This file is
  therefore **stand-alone**: it uses `R.directSumEquiv` directly from
  `Foundation/R/DirectSum.lean`, not via any A2 packaging.  If A2
  is later added and exports a generalised `R (N + M) ≃ R N × R M`
  theorem, P4 could be re-derived as the `M = N` specialisation; that
  refactor is purely cosmetic.
* **A5 (D1 ⟹ P5, Hom-as-content)** — depends on P4 (P5 at `R 4` uses
  the fact that `R 4 ≃ R 2 × R 2`).  This file's
  `D1_implies_P4_R2_squaring` is the squaring witness consumed by A5's
  T_P7b anchor at `N = M = 2`.
* **A8 (D1 ⟹ P7b, T_P7b)** — depends transitively on P4 (the analytic
  chain D1 ⟹ P4 ⟹ P5 ⟹ P7b documented in `P7b.lean` § 1).

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` (Phase 1 Stream A4).
* `docs-next/10_formal_形式/wen-substrate/01-foundations.md` (P4
  statement: self-similar under squaring).
* `wen-substrate.md` v1.2 §2.4 (P4 closure condition), §7.8.3
  (D1 ⟹ P4 analytic mapping: D1.6 recur ⟹ P4).
* `wen-algebra.md` v0.6 §1.3 (squaring tower step is direct sum, not
  tensor).
* `Foundation/R/Squaring.lean` — the `R.squaringEquiv` infrastructure
  this file packages under the analytic label.
* `Foundation/R/DirectSum.lean` — the underlying `R.directSumEquiv`.
* `Foundation/R/OperationMonismBridge.lean` § 3 — the
  `rtowerBoolEquiv` self-similar tower used in operation-monism.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R.Squaring
import SSBX.Foundation.R.ClaimZ

namespace SSBX.Foundation.R.ClaimZ.Analytic

open SSBX.Foundation.R
open SSBX.Foundation.R.R

/-! ## § 1 The analytic-step equivalence at general layer index `N`

The direct-sum form `R (N + N) ≃ R N × R N` is the existing
`R.squaringEquiv N` from `Foundation/R/Squaring.lean`.  The `2 * N`
form is obtained via `Nat.two_mul : 2 * N = N + N` and the
`R.castEquiv`-style cast.
-/

/-- **D1 ⟹ P4 (F₂-Boolean analytic step, additive form) —
    `R (N + N) ≃ R N × R N`**.

    The direct-sum reading of the squaring step (per `wen-algebra`
    v0.6 §1.3): cells of size `N + N` decompose as a pair of
    `N`-cells.  At δ = Bool this is the XOR-direct-sum, witnessed by
    `R.directSumEquiv` (= `R.squaringEquiv N`). -/
def D1_implies_P4_F2_add_form (N : ℕ) : R (N + N) ≃ R N × R N :=
  R.squaringEquiv N

/-- **D1 ⟹ P4 (F₂-Boolean analytic step, Phase 1 Stream A4) —
    `R (2 * N) ≃ R N × R N`**.

    The standard "2N" form of the squaring step.  Obtained from
    `D1_implies_P4_F2_add_form N : R (N + N) ≃ R N × R N` by
    transporting along `Nat.two_mul N : 2 * N = N + N`.

    This is the named theorem; the proof is a `Nat.two_mul`-cast of
    `R.squaringEquiv`.  (Declared as `def` rather than `theorem`
    because `Equiv` is a `Type`-valued bundle, not a `Prop`.  The
    propositional shadow `Nonempty (R (2 * N) ≃ R N × R N)` is
    recorded immediately below as `D1_implies_P4_F2_prop`.) -/
def D1_implies_P4_F2 (N : ℕ) : R (2 * N) ≃ R N × R N := by
  have h : 2 * N = N + N := Nat.two_mul N
  -- Transport `R (N + N) ≃ R N × R N` along `h.symm : N + N = 2 * N`
  -- reversed.
  exact (h ▸ R.squaringEquiv N)

/-- The propositional shadow: `Nonempty (R (2 * N) ≃ R N × R N)`.
    Useful when downstream code wants a `Prop`-valued conjunct of
    P-closure rather than the data-bearing `Equiv`. -/
theorem D1_implies_P4_F2_prop (N : ℕ) :
    Nonempty (R (2 * N) ≃ R N × R N) :=
  ⟨D1_implies_P4_F2 N⟩

/-! ## § 2 Cardinality corollary

The cardinality identity `|R (2 * N)| = |R N|^2 = (2^N)^2 = 2^(2*N)`
is the *counting shadow* of `D1_implies_P4_F2`.  Already proved in
`Foundation/R/Squaring.lean` as `squaringEquiv_card` (in the `N + N`
form); we re-export the `2 * N` form under the P4 name. -/

/-- |R (2 * N)| = |R N|^2.  The cardinality shadow of P4. -/
theorem D1_implies_P4_F2_card (N : ℕ) :
    Fintype.card (R (2 * N)) = Fintype.card (R N) * Fintype.card (R N) := by
  rw [Fintype.card_congr (D1_implies_P4_F2 N), Fintype.card_prod]

/-! ## § 3 Concrete squaring witnesses at the R-tower

The three non-trivial squaring steps at the R-tower indices
`{1, 2, 4}`.  These specialise `D1_implies_P4_F2_add_form` (which is
the `+ +` form, i.e., `R 2 = R (1+1)`, `R 4 = R (2+2)`, `R 8 = R
(4+4)`) and match the existing witnesses `R2_eq_R1_sq`,
`R4_eq_R2_sq`, `R8_eq_R4_sq` from `Foundation/R/Squaring.lean`.
-/

/-- The atomic squaring step `R 2 ≃ R 1 × R 1`.

    Re-exports `R.R2_eq_R1_sq` under the analytic-direction label.
    Per P4 at `N = 1`: the bit-pair `R 2` decomposes as two bits. -/
def D1_implies_P4_R1_squaring : R 2 ≃ R 1 × R 1 :=
  R.R2_eq_R1_sq

/-- The first non-trivial squaring step `R 4 ≃ R 2 × R 2`.

    Re-exports `R.R4_eq_R2_sq` under the analytic-direction label.
    Per P4 at `N = 2`: the Klein-four-doubled `R 4` decomposes as two
    Klein-four-groups.  This is the witness consumed by A5's T_P7b
    anchor at `N = M = 2`. -/
def D1_implies_P4_R2_squaring : R 4 ≃ R 2 × R 2 :=
  R.R4_eq_R2_sq

/-- The ceiling-reaching squaring step `R 8 ≃ R 4 × R 4`.

    Re-exports `R.R8_eq_R4_sq` under the analytic-direction label.
    Per P4 at `N = 4`: the byte-cell `R 8` decomposes as two nibble-
    cells.  Used in `Foundation/R8/Squaring.lean` for the R₈-level
    tensor / direct-sum decomposition. -/
def D1_implies_P4_R4_squaring : R 8 ≃ R 4 × R 4 :=
  R.R8_eq_R4_sq

/-! ## § 4 Self-similar tower statement

The squaring tower `R 1 → R 2 → R 4 → R 8 → ...` has indices
`{2^0, 2^1, 2^2, 2^3, ...} = {1, 2, 4, 8, ...}`.  The "self-similar"
clause of P4 is the statement that this index sequence is closed
under the squaring step `n ↦ 2 * n` — equivalently, `2 * 2^k =
2^(k+1)` so `R (2^(k+1)) ≃ R (2^k) × R (2^k)`.

This is the **tower-view** of P4: rather than fixing an arbitrary
`N`, we fix the iteration depth `k` and watch the cardinality double
at each step.  This view is used in
`Foundation/R/OperationMonismBridge.lean` § 3 to relate `RTower Bool
k ≃ R (2^k)` (the operator-iteration tower and the R-Family tower
agree on cardinalities and structure).
-/

/-- **D1 ⟹ P4 (self-similar tower form)** — the squaring step at the
    R-tower indices `2^k`: `R (2 ^ (k + 1)) ≃ R (2 ^ k) × R (2 ^ k)`.

    At `k = 0`: `R 2 ≃ R 1 × R 1` (= `D1_implies_P4_R1_squaring`).
    At `k = 1`: `R 4 ≃ R 2 × R 2` (= `D1_implies_P4_R2_squaring`).
    At `k = 2`: `R 8 ≃ R 4 × R 4` (= `D1_implies_P4_R4_squaring`).
    At `k = 3`: `R 16 ≃ R 8 × R 8`, etc. -/
def D1_implies_P4_tower (k : ℕ) : R (2 ^ (k + 1)) ≃ R (2 ^ k) × R (2 ^ k) := by
  -- 2^(k+1) = 2^k + 2^k, so this is `R.squaringEquiv (2^k)` cast.
  have h : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by
    show 2 ^ k * 2 = 2 ^ k + 2 ^ k
    rw [Nat.mul_two]
  exact (h ▸ R.squaringEquiv (2 ^ k))

/-- The propositional shadow of the tower form. -/
theorem D1_implies_P4_tower_prop (k : ℕ) :
    Nonempty (R (2 ^ (k + 1)) ≃ R (2 ^ k) × R (2 ^ k)) :=
  ⟨D1_implies_P4_tower k⟩

/-! ## § 5 Cardinality shadow of the self-similar tower

`|R (2^(k+1))| = |R (2^k)|^2`.  The counting view of the tower: the
cardinality of the `k`-th rung is `2^(2^k)`, doubling-in-exponent at
each step. -/

/-- |R (2^(k+1))| = |R (2^k)|^2.  Cardinality at the squaring-tower
    indices. -/
theorem D1_implies_P4_tower_card (k : ℕ) :
    Fintype.card (R (2 ^ (k + 1)))
      = Fintype.card (R (2 ^ k)) * Fintype.card (R (2 ^ k)) := by
  rw [Fintype.card_congr (D1_implies_P4_tower k), Fintype.card_prod]

/-! ## § 6 Interface-level analytic step `D1.6 ⟹ P4`

Per `Foundation/R/ClaimZ.lean` § 3, the analytic step is factored
through per-item entailments `h4 : S.recur → P.p4` (D1.6 recursive
expressibility ⟹ P4 squaring tower).  This file delivers that
entailment as a named theorem for the canonical F₂-Boolean instance,
and packages the interface-level analytic step.
-/

/-- **D1 ⟹ P4 (interface-level analytic step, Phase 1 Stream A4)** —
    given a `D1Articulation` `S` together with the per-item analytic
    entailment `h4 : S.recur → P.p4` and the D1.6 witness `h_rec`,
    the P4 closure conjunct `P.p4` holds.

    This is the *Lean-checked combinator* form of the §7.8.3
    D1.6 ⟹ P4 mapping: the entailment hypothesis `h4` is the
    *substantive content* (saying "recursion forces squaring tower"),
    and this theorem witnesses that the combination yields `P.p4`.
    Concrete instantiations (e.g., R-Family-over-F₂ via
    `D1_implies_P4_for_F2`) supply `h4` together with a concrete
    `P.p4 := Nonempty (R (2 * N) ≃ R N × R N)` for some chosen N. -/
theorem D1_implies_P4
    (S : ClaimZ.D1Articulation)
    (P : ClaimZ.PClosure)
    (h4 : S.recur → P.p4)
    (h_rec : S.recur) : P.p4 :=
  h4 h_rec

/-- **D1 ⟹ P4 (F₂-Boolean) at `N = 2`** — closure at the
    R 2 → R 4 squaring step.

    The P4 closure conjunct is realised as `Nonempty (R 4 ≃ R 2 × R
    2)`, which is proved directly by `D1_implies_P4_R2_squaring` (=
    `R.R4_eq_R2_sq`).  Independent of any further D1-articulation
    content beyond `S.recur`. -/
theorem D1_implies_P4_for_F2_at_2 :
    ∀ (S : ClaimZ.D1Articulation), S.recur →
      Nonempty (R 4 ≃ R 2 × R 2) := by
  intro _ _
  exact ⟨D1_implies_P4_R2_squaring⟩

/-- **D1 ⟹ P4 (F₂-Boolean) at arbitrary `N`** — closure for every
    layer index `N`.

    The P4 closure conjunct is realised as `∀ N, Nonempty (R (2 * N)
    ≃ R N × R N)`, which is the **universal** form of P4 at δ = Bool.
    Proved by `D1_implies_P4_F2_prop`. -/
theorem D1_implies_P4_for_F2 :
    ∀ (S : ClaimZ.D1Articulation), S.recur →
      ∀ N : ℕ, Nonempty (R (2 * N) ≃ R N × R N) := by
  intro _ _ N
  exact D1_implies_P4_F2_prop N

/-- **D1 ⟹ P4 (F₂-Boolean, tower form) at arbitrary depth `k`** —
    closure at the squaring-tower indices.

    The P4 closure conjunct in the tower form: `∀ k, Nonempty (R
    (2^(k+1)) ≃ R (2^k) × R (2^k))`.  This is the **self-similar**
    reading of P4 at δ = Bool. -/
theorem D1_implies_P4_for_F2_tower :
    ∀ (S : ClaimZ.D1Articulation), S.recur →
      ∀ k : ℕ, Nonempty (R (2 ^ (k + 1)) ≃ R (2 ^ k) × R (2 ^ k)) := by
  intro _ _ k
  exact D1_implies_P4_tower_prop k

/-! ## § 7 Summary witness

A single bundled lemma recording that P4 is closed at every canonical
witness — general `N`, the three concrete R-tower steps `R 1 → R 2`,
`R 2 → R 4`, `R 4 → R 8`, and the self-similar tower form — and that
the interface-level analytic step `D1.6 ⟹ P4` is fully realised.
-/

/-- **Phase 1 Stream A4 summary witness** — the analytic step
    `D1 ⟹ P4` is fully closed at:

    * `R (2 * N) ≃ R N × R N` for every `N` (universal form, via
      `D1_implies_P4_F2`)
    * `R 2 ≃ R 1 × R 1` (atomic step, via `D1_implies_P4_R1_squaring`)
    * `R 4 ≃ R 2 × R 2` (first non-trivial, via
      `D1_implies_P4_R2_squaring`)
    * `R 8 ≃ R 4 × R 4` (ceiling-reaching, via
      `D1_implies_P4_R4_squaring`)
    * `R (2^(k+1)) ≃ R (2^k) × R (2^k)` (self-similar tower form, via
      `D1_implies_P4_tower`)

    No `sorry`, no new axiom.  The interface-level analytic step
    `D1_implies_P4` consumes the per-item entailment as a hypothesis,
    matching the `ClaimZ.d1_implies_P` combinator pattern.

    Per `gut-roadmap.md` Phase 1 Stream A4, this discharges the
    **D1 ⟹ P4 analytic obligation** for the F₂-Boolean scope. -/
theorem A4_summary_witness :
    -- General form
    (∀ N : ℕ, Nonempty (R (2 * N) ≃ R N × R N)) ∧
    -- Atomic R-tower step
    Nonempty (R 2 ≃ R 1 × R 1) ∧
    -- First non-trivial R-tower step
    Nonempty (R 4 ≃ R 2 × R 2) ∧
    -- Ceiling-reaching R-tower step
    Nonempty (R 8 ≃ R 4 × R 4) ∧
    -- Self-similar tower form
    (∀ k : ℕ, Nonempty (R (2 ^ (k + 1)) ≃ R (2 ^ k) × R (2 ^ k))) ∧
    -- Interface-level: D1.6 recur ⟹ P4 at chosen P.p4
    (∀ (S : ClaimZ.D1Articulation), S.recur →
        ∀ N : ℕ, Nonempty (R (2 * N) ≃ R N × R N)) :=
  ⟨ D1_implies_P4_F2_prop
  , ⟨D1_implies_P4_R1_squaring⟩
  , ⟨D1_implies_P4_R2_squaring⟩
  , ⟨D1_implies_P4_R4_squaring⟩
  , D1_implies_P4_tower_prop
  , D1_implies_P4_for_F2 ⟩

end SSBX.Foundation.R.ClaimZ.Analytic
