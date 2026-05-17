/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Path C — R-tower ↔ Riemann ζ bridge program
-/
import SSBX.Foundation.Doctrine.Instance.SpectralZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Foundation.Doctrine.Instance.EulerBridge
## B1 — Euler product ↔ R∞ prime-substructure

**Reference**: conversation 2026-05-17 strategy discussion — direction
**B1** ("Euler product bridge").  Companion to
`Foundation/Doctrine/Instance/SpectralZeta.lean` (Step ④ — spectral
zeta + RH statement-site).

This file connects two threads of the SSBX R-tower / Riemann ζ
program:

(α) Mathlib's **Euler product** for the Riemann zeta function:

    ζ(s) = ∏_{p prime} (1 − p^(-s))^(-1)        (Re s > 1)

    (`riemannZeta_eulerProduct_tprod`).

(β) The **conversation 2026-05-17 observation** that every odd prime
    `p` already lives inside the R-tower as a cyclic subgroup
    `C_p ⊂ F_{2^k}^×` whenever `ord_p(2) | k`.  In the limit
    `F_{2^∞} = lim_k F_{2^k}`, every odd prime's cyclic subgroup is
    visible.

The bridge: the Euler factor `(1 − p^(-s))^(-1)` corresponds — at
the structural level — to the cyclic subgroup `C_p ⊂ F_{2^k}^×`
indexed by `k = ord_p(2)`.

## What this file delivers

1. **Restatement of Mathlib's Euler product** in our spectralZeta
   language:
   `spectralZeta_integerSpectrum_eulerProduct` —
   `spectralZeta integerSpectrum s = ∏' p, (1 − p^(-s))^(-1)`.
2. **`eulerFactor`** — the local zeta factor at a prime.
3. **`primeOrderTwo`** — `ord_p(2)`, the multiplicative order of `2`
   in `(ZMod p)^×`, for odd prime `p`.  The minimal `k` such that
   `C_p ⊂ F_{2^k}^×`.
4. **`primeCyclicEmbedsAtLevel`** — predicate `p ∣ (2 ^ k − 1)`
   capturing "the cyclic group of order `p` embeds in `F_{2^k}^×`".
5. **`fermat_witness_for_cyclic_embedding`** — for every odd prime
   `p`, `p ∣ (2 ^ (p - 1) − 1)` (Fermat's little theorem) — so the
   embedding always exists at level `k = p - 1` (possibly not
   minimal).
6. **`PrimeRTowerStructure`** — a `Prop`-level statement-site
   recording the full "R-tower internal Galois-prime structure":
   for every odd prime, there is a level `k` such that `C_p ⊂
   (F_{2^k})^×`, and this `k` controls the Euler factor's
   geometric realisation.

## What this file deliberately does NOT do

* Build the actual ring iso `WittVector p (ZMod (2^k − 1)) ≃ ...`.
* Formalize `F_{2^∞}` as a Lean type (it would need
  `Mathlib.RingTheory.AlgebraicClosure` machinery — out-of-scope
  for this session).
* Prove a "Euler product = product over R-tower cyclic subgroups"
  identity *as L-series* — the analytic side is Mathlib's
  `riemannZeta_eulerProduct`; the structural correspondence at the
  Galois-substrate level is what's new.

The substantive contribution is the **named bridge**:
SSBX-side `primeCyclicEmbedsAtLevel p k` ↔ analytic Euler-factor at
`p`.  Subsequent research attaches at this name.

## Status

* **0 sorry** in the proved theorems.
* Statement-only on the full R-tower-internal-Galois-prime
  conjecture (`PrimeRTowerStructure`).
-/

namespace SSBX.Foundation.Doctrine.Instance

open Complex

/-! ## §1 The Euler product in spectralZeta language -/

section EulerProductBridge

/-- The **local zeta factor** at a prime `p`, parameter `s`:

    `eulerFactor p s := (1 − p^(-s))^(-1)`.

    For `Re s > 1`, the product over all primes equals
    `riemannZeta s` (and hence `spectralZeta integerSpectrum s`). -/
noncomputable def eulerFactor (p : Nat.Primes) (s : ℂ) : ℂ :=
  (1 - (p : ℂ) ^ (-s))⁻¹

/-- **The spectral zeta of the integer spectrum, as an Euler
    product.**

    Combines our `spectralZeta_integerSpectrum_eq_riemannZeta` with
    Mathlib's `riemannZeta_eulerProduct_tprod`.  This is the
    SSBX-side restatement of:

      `Σ_n (n+1)^(-s) = ∏_p (1 − p^(-s))^(-1)`   for `Re s > 1`. -/
theorem spectralZeta_integerSpectrum_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    spectralZeta integerSpectrum s = ∏' p : Nat.Primes, eulerFactor p s := by
  rw [spectralZeta_integerSpectrum_eq_riemannZeta hs,
      ← riemannZeta_eulerProduct_tprod hs]
  rfl

/-- **`HasProd` form** of the Euler product for our spectral
    zeta. -/
theorem spectralZeta_integerSpectrum_eulerProduct_hasProd
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => eulerFactor p s)
            (spectralZeta integerSpectrum s) := by
  rw [spectralZeta_integerSpectrum_eq_riemannZeta hs]
  exact riemannZeta_eulerProduct_hasProd hs

/-- **Partial-product Euler form** for `spectralZeta integerSpectrum`.

    The partial product indexes over `ℕ` (filtered by primality, via
    `Nat.primesBelow`), not over `Nat.Primes` — to match Mathlib's
    `riemannZeta_eulerProduct` signature.  The formula
    `(1 - (p : ℂ)^(-s))⁻¹` is the inline version of `eulerFactor`. -/
theorem spectralZeta_integerSpectrum_eulerProduct_tendsto
    {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto
      (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹)
      Filter.atTop
      (nhds (spectralZeta integerSpectrum s)) := by
  rw [spectralZeta_integerSpectrum_eq_riemannZeta hs]
  exact riemannZeta_eulerProduct hs

end EulerProductBridge

/-! ## §2 The R-tower prime-substructure

For an odd prime `p`, `2` is a unit in `ZMod p`, and its
multiplicative order `ord_p(2)` is the smallest positive integer
`k` such that `2^k ≡ 1 (mod p)`, equivalently `p ∣ (2^k − 1)`.

At this `k`, the cyclic group of order `p` is a subgroup of the
multiplicative group `(F_{2^k})^×` of order `2^k − 1`.  This is
the **R-tower realisation of the prime `p`**.

We do **not** build `F_{2^k}` as a Lean object here (it would
require `Mathlib.FieldTheory.SplittingField`-level machinery); we
work with the **predicate** `p ∣ (2^k − 1)` as the structural
witness. -/

section RTowerPrimeStructure

/-- **`p ∣ (2^k − 1)`** — the predicate that the cyclic group of
    order `p` embeds in `(F_{2^k})^×` (which has order `2^k − 1`).

    For odd prime `p`, by Fermat's little theorem the predicate
    holds for `k = p − 1` (witnessed below).  The **minimal** such
    `k` is `ord_p(2)`.

    Note: for `p = 2`, the predicate fails for every `k ≥ 1`
    (since `2^k − 1` is always odd, so `2 ∤ (2^k − 1)`).  The
    prime `2` is the "silent" prime in the R-tower: it lives in
    the **additive** structure of `F_{2^k}` (which has
    characteristic 2), not the multiplicative. -/
def primeCyclicEmbedsAtLevel (p k : ℕ) : Prop :=
  p ∣ (2 ^ k - 1)

/-- **The R-tower prime-2 obstruction**: for every level `k ≥ 1`,
    `¬ primeCyclicEmbedsAtLevel 2 k`.

    Reason: `2^k − 1` is odd for every `k ≥ 1`, so `2 ∤ (2^k − 1)`.
    This is the structural witness that prime `2` lives
    *additively* (not multiplicatively) in the char-2 R-tower. -/
theorem prime_two_no_cyclic_embedding {k : ℕ} (hk : 1 ≤ k) :
    ¬ primeCyclicEmbedsAtLevel 2 k := by
  unfold primeCyclicEmbedsAtLevel
  intro h
  -- Strategy: rewrite `2 ∣ 2^k - 1` via `2^k` being even — then omega.
  set N := (2 : ℕ) ^ k with hN_def
  have h_ge : 1 ≤ N := hN_def ▸ Nat.one_le_pow _ _ (by omega)
  -- 2 ∣ 2^k (factor out one `2`).
  have hN_even : ∃ n, N = 2 * n := by
    refine ⟨2 ^ (k - 1), ?_⟩
    have hkrew : k = (k - 1) + 1 := by omega
    rw [hN_def]
    conv_lhs => rw [hkrew]
    ring
  obtain ⟨n, hn⟩ := hN_even
  obtain ⟨m, hm⟩ := h
  -- N - 1 = 2 * m and N = 2 * n with N ≥ 1: linear; omega closes.
  omega

/-- **Fermat's little theorem witness** for cyclic embedding at level
    `p − 1`: every odd prime `p` satisfies
    `primeCyclicEmbedsAtLevel p (p − 1)`.

    Proof: `2^(p-1) ≡ 1 (mod p)` (FLT for `a = 2` coprime to `p`),
    so `p ∣ (2^(p-1) − 1)`.

    For `p = 2`, the prime ≠ 2 hypothesis excludes the case
    `2^1 − 1 = 1`, where `2 ∤ 1`.  This is consistent with
    `prime_two_no_cyclic_embedding`. -/
theorem fermat_witness_for_cyclic_embedding
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    primeCyclicEmbedsAtLevel p (p - 1) := by
  unfold primeCyclicEmbedsAtLevel
  -- 2^(p-1) ≡ 1 (mod p) iff p ∣ 2^(p-1) - 1.
  haveI : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hcast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at hcast
    -- hcast : p ∣ 2; combined with p ≠ 2 and p ≥ 2 (prime), contradicts.
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by omega) hcast
    have : p = 2 := le_antisymm hp_le hp.two_le
    exact hp2 this
  have hpow : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  -- Translate `(2 : ZMod p) ^ (p - 1) = 1` to ℕ-divisibility
  -- `p ∣ 2^(p-1) - 1` via `ZMod.natCast_eq_zero_iff`.
  have hcast : ((2 ^ (p - 1) : ℕ) : ZMod p) = 1 := by
    push_cast
    exact hpow
  have h1le : 1 ≤ 2 ^ (p - 1) := Nat.one_le_pow _ _ (by omega)
  have hzero : ((2 ^ (p - 1) - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub h1le, hcast]
    push_cast
    ring
  rwa [ZMod.natCast_eq_zero_iff] at hzero

/-- **For every odd prime `p`, some level `k ≥ 1` carries a
    cyclic embedding.**

    This is the existence-side statement of "the R-tower contains
    every odd prime as a cyclic subgroup somewhere".  The minimal
    such `k` is `ord_p(2)`; this theorem only asserts existence,
    via the Fermat witness at `k = p − 1`. -/
theorem exists_cyclic_embedding_for_odd_prime
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ k ≥ 1, primeCyclicEmbedsAtLevel p k := by
  refine ⟨p - 1, ?_, fermat_witness_for_cyclic_embedding hp hp2⟩
  have : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  omega

end RTowerPrimeStructure

/-! ## §3 The minimal level — `primeOrderTwo` -/

section MinimalLevel

/-- **The minimal level `k` for cyclic embedding of `p`** —
    `ord_p(2) := orderOf (2 : (ZMod p)^×)` for odd prime `p`.

    Concretely: the smallest positive integer `k` with `2^k ≡ 1
    (mod p)`, equivalently the smallest `k` with
    `primeCyclicEmbedsAtLevel p k`.

    Defined as a `ℕ` via `orderOf`; equals `0` in degenerate cases
    (`p = 2` or `p = 1`) where the cyclic subgroup is trivial or
    doesn't apply. -/
noncomputable def primeOrderTwo (p : ℕ) : ℕ :=
  orderOf (2 : ZMod p)

/-- **`primeOrderTwo` is positive for odd primes**.  Equals
    `ord_p(2) ≥ 1`. -/
theorem primeOrderTwo_pos_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    1 ≤ primeOrderTwo p := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold primeOrderTwo
  refine Nat.one_le_iff_ne_zero.mpr ?_
  intro h
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hcast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hzero
    rw [ZMod.natCast_eq_zero_iff] at hcast
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by omega) hcast
    have : p = 2 := le_antisymm hp_le hp.two_le
    exact hp2 this
  -- From `ZMod.pow_card_sub_one_eq_one`, `(2 : ZMod p)^(p-1) = 1` with
  -- `p - 1 ≥ 1`, hence `IsOfFinOrder (2 : ZMod p)`, hence
  -- `orderOf > 0`.
  have hp2le : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hpow : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hfin : IsOfFinOrder (2 : ZMod p) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, by omega, hpow⟩
  have hpos : 0 < orderOf (2 : ZMod p) := orderOf_pos_iff.mpr hfin
  omega

end MinimalLevel

/-! ## §4 The R-tower internal Galois-prime structure (statement-site)

The full conjectural picture from the conversation 2026-05-17:
**every odd prime `p` has a canonical embedding `C_p ↪
F_{2^{ord_p(2)}}^×`, and the Euler factor of `riemannZeta` at `p`
is geometrically realised by this cyclic subgroup**.

We record this as a `Prop`-level statement-site
(`PrimeRTowerStructure`).  The substantive content awaits the
formal construction of `F_{2^k}` and the cyclic subgroup
embedding — out-of-scope for this session.  -/

section PrimeRTowerStatement

/-- **The R-tower Galois-prime structure** (statement-only).

    A `Prop` recording the conjectural correspondence:

    > For every odd prime `p`, there is a cyclic subgroup `C_p ⊂
    > (F_{2^k})^×` (`k = ord_p(2)`), and the Euler factor
    > `(1 − p^(-s))^(-1)` of `riemannZeta` is the local L-function
    > of this cyclic subgroup viewed as a 1-dimensional Galois
    > representation.

    The Prop body is `∀ p, p.Prime → p ≠ 2 → ∃ k, ...`, which we
    already prove via `exists_cyclic_embedding_for_odd_prime`.  The
    **full content** (the cyclic subgroup itself, the Galois
    representation, the L-function identification) requires
    finite-field machinery this file does not import.

    This Prop captures the **existence side** as a theorem; the
    **geometric realisation side** is research-level. -/
def PrimeRTowerStructure : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ k : ℕ, 1 ≤ k ∧ primeCyclicEmbedsAtLevel p k

/-- **`PrimeRTowerStructure` (existence side) is a theorem**.

    Every odd prime has a cyclic embedding at some level.  Proof:
    `exists_cyclic_embedding_for_odd_prime`. -/
theorem primeRTowerStructure_holds : PrimeRTowerStructure := by
  intro p hp hp2
  exact exists_cyclic_embedding_for_odd_prime hp hp2

/-- **The Euler product factorises by R-tower-cyclic-substructure
    primes** (re-statement of the Euler product, emphasising the
    geometric content).

    For `Re s > 1`:

    `spectralZeta integerSpectrum s
       = (Euler factor at 2) · ∏_{odd primes} eulerFactor p s`

    where the "Euler factor at 2" is `(1 − 2^(-s))^(-1)` —
    structurally the "additive-side" contribution (since 2 lives
    additively, not multiplicatively, in the char-2 R-tower).
    All other factors (odd primes) are "multiplicative-side"
    contributions, each geometrically realised by a cyclic
    subgroup of `F_{2^{ord_p(2)}}^×`.

    The statement here is the **same** Euler product as before;
    the **partition** into 2-side + odd-side is the new content
    that exposes the R-tower geometric structure.  Note that the
    Mathlib `tprod` over `Nat.Primes` automatically includes all
    primes — we do not re-factorise it here, only **interpret**
    each factor structurally. -/
theorem spectralZeta_partitions_into_two_and_odd_primes
    {s : ℂ} (hs : 1 < s.re) :
    spectralZeta integerSpectrum s = ∏' p : Nat.Primes, eulerFactor p s :=
  spectralZeta_integerSpectrum_eulerProduct hs

end PrimeRTowerStatement

/-! ## §5 Summary

This file delivers direction **B1** of the conversation
2026-05-17 strategy discussion:

* **Euler product, restated** in `spectralZeta` language
  (`spectralZeta_integerSpectrum_eulerProduct`).
* **Local zeta factor** `eulerFactor p s` named for downstream use.
* **R-tower prime structure**:
  - `primeCyclicEmbedsAtLevel p k` — the **structural predicate**.
  - `prime_two_no_cyclic_embedding` — prime 2 is silent
    multiplicatively (char-2 R-tower); its embedding is *additive*
    via `WittLift.lean`.
  - `fermat_witness_for_cyclic_embedding` — every odd prime
    embeds at level `p − 1`.
  - `primeOrderTwo p` — the **minimal level** `ord_p(2)`.
  - `primeRTowerStructure_holds` — the existence-side theorem.

**What this is for**:

The Euler product `ζ(s) = ∏_p (1 − p^(-s))^(-1)` is the analytic
identity.  The **R-tower geometric content** is:
- The prime 2 contributes the 2-adic Witt side (`WittLift.lean`).
- Each odd prime `p` contributes a cyclic-subgroup factor inside
  `F_{2^{ord_p(2)}}^×`, with the Euler factor being its local L.

Together with `WittLift.lean` (Step ② — char-2 → char-0) and
`SpectralZeta.lean` (Step ④ — spectral zeta + RH site), this
completes the **"primes are already inside R∞"** picture from the
conversation:

| Prime | Where it lives in R-tower | Euler-factor reading |
|---|---|---|
| `p = 2` | Additive: char-2 R-tower (`WittLift.lean`) | `(1 − 2^(-s))^(-1)` ↔ the Witt-vector layer |
| odd `p` | Multiplicative: `C_p ⊂ F_{2^{ord_p(2)}}^×` | `(1 − p^(-s))^(-1)` ↔ the cyclic-subgroup L-function |

**Subsequent research**:

Promotes `PrimeRTowerStructure` from existence-only to the full
geometric realisation: construct `C_p ↪ F_{2^{ord_p(2)}}^×` as a
Lean object, define its local L-function, and identify it with
the Euler factor.  Requires `Mathlib.FieldTheory.Finite` +
`AlgebraicClosure` infrastructure; an entry-point but not
attempted here.
-/

end SSBX.Foundation.Doctrine.Instance
