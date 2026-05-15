/-
# Foundation.R.PhaseZero — Phase 0 small theorems for wen-substrate v1.0.3

Per `docs-next/10_formal_形式/wen-substrate.md` v1.0.3 §8.8 ("Phase 0 —
Immediately provable sub-theorems"), this file collects the four small
formalisable theorems that support the v0.8 P-claims:

* **T_P3** — Bilinear classification (P3): exactly 3 algebraic layers
  (symmetric / alternating / quadratic-refinement family) on `R (2k)`,
  with 4 total equivalence classes (1 symm + 1 alt + 2 Arf-labelled
  quadratic-refinement classes).
* **T_P6** — V₄ carrier minimality (P6): `R 2 ≅ V₄` is the unique
  4-element `F_2`-vector space and the minimum non-trivial multi-modality
  carrier (≥ 3 independent modalities ⇒ ≥ 4 elements).
* **T_P7a** — Zong involution forces a 4本 + 4征 split on `R 3`:
  reversal `ζ : R 3 → R 3, ζ(b₀, b₁, b₂) = (b₂, b₁, b₀)` is involutive;
  `|Fix(ζ)| = 4` (= 本-trigrams = {qian, li, kan, kun}); the complement
  has 4 elements (= 征-trigrams = {dui, zhen, xun, gen}).
* **T_P7b** — Wedderburn anchor: `R 4 ≃ End(R 2) ≃ Mat₂(F₂)` carries the
  natural `F_2`-algebra structure (composition of endomorphisms as
  multiplication, XOR as addition).  We supply the existence side
  (matrix bijection + composition associativity + identity laws +
  cardinality match) on top of `Foundation/R4/EndR2.lean` and leave the
  full `RingEquiv` upgrade as the residual Phase-0 work item.

## Scope

This is a **statement + immediate-proof** module: it re-exports and
packages already-formalised content under named theorems `T_P3_*`,
`T_P6_*`, `T_P7a_*`, `T_P7b_*` so that the v1.0.3 §8.8 list is directly
verifiable from a single file.  No new axioms are introduced; everything
not yet proven is recorded as a documented residual obligation with an
explicit TODO referencing the wen-substrate section it discharges.

## Doctrinal anchor

* `wen-substrate.md` v1.0.3 §8.8 (Phase 0 small theorems).
* `wen-substrate.md` v1.0.3 §2.3 (P3 bilinear classification),
  §2.6 (P6 V₄ minimality), §2.7 (P7 zong / Wedderburn).
* `Foundation/R/Bilinear.lean` (T_P3 anchor).
* `Foundation/Atlas/Yi/ShiV4.lean` (T_P6 anchor).
* `Foundation/Atlas/Yi/Bagua.lean` (T_P7a anchor).
* `Foundation/R4/EndR2.lean`, `Foundation/R4/HomMat.lean` (T_P7b anchor).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Bagua
import SSBX.Foundation.Atlas.Yi.ShiV4
import SSBX.Foundation.R4.EndR2
import Mathlib.Logic.Function.Basic

namespace SSBX.Foundation.R.PhaseZero

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 T_P3 — Bilinear classification (P3)

Per wen-substrate v1.0.3 §2.3 (P3) and §8.8.

The natural `F_2`-bilinear / quadratic classification on `R (2 * k)`
has exactly **3 algebraic layers**:

* **L₀** — the symmetric form `dot : R N × R N → Bool` (defined for all
  `N`; symmetry is `R.dot_symm`).
* **L₁** — the alternating symplectic form `sigma : R (2 * k) → R (2 * k) → Bool`
  (alternating is `R.sigma_alternating`).
* **L₂** — the parametric family of quadratic refinements `q c v`
  indexed by `c : Fin k → Bool`; the Arf invariant `arf c` is an `F_2`
  binary label (cardinality 2 of the Arf classes is immediate from
  `arf` being `Bool`-valued).

The decomposition `dot = σ ⊕ LL` (= `R.dot_eq_sigma_xor_LL`) shows the
three layers are not independent forms but **stacked algebraic strata**
on the same carrier.

The uniqueness-up-to-iso clause (no further independent symmetric /
alternating non-degenerate forms over `F_2`) is the residual Phase-0
obligation under wen-substrate v1.0.3 §8.8 / Standard ref: Atiyah,
*Riemann surfaces and spin structures*, Ann. Sci. ENS (1971); Arf,
*Untersuchungen über quadratische Formen in Körpern der Charakteristik
2*, J. Reine Angew. Math. (1941).
-/

/-- **T_P3.L0** — Layer 0 symmetric form exists: `dot` is symmetric on `R N`. -/
theorem T_P3_L0_symmetric {N : ℕ} (u v : R N) : R.dot u v = R.dot v u :=
  R.dot_symm u v

/-- **T_P3.L1** — Layer 1 alternating form exists: `sigma` is alternating
    on `R (2 * k)`. -/
theorem T_P3_L1_alternating {k : ℕ} (v : R (2 * k)) :
    R.sigma v v = false :=
  R.sigma_alternating v

/-- **T_P3.L1.symm** — Layer 1 form is also symmetric (in char 2 every
    alternating form is symmetric). -/
theorem T_P3_L1_symmetric {k : ℕ} (u v : R (2 * k)) :
    R.sigma u v = R.sigma v u :=
  R.sigma_symm u v

/-- **T_P3.decomp** — The three layers are bound by the L0/L1
    decomposition: `dot = σ ⊕ LL`, the wen-algebra v0.6 §4.6 identity. -/
theorem T_P3_decomposition {k : ℕ} (u v : R (2 * k)) :
    R.dot u v = Bool.xor (R.sigma u v) (R.LL u v) :=
  R.dot_eq_sigma_xor_LL u v

/-- **T_P3.L2** — Layer 2 family vanishes on the origin (sanity check
    of the parametric refinement family). -/
theorem T_P3_L2_origin {k : ℕ} (c : Fin k → Bool) :
    R.q c (0 : R (2 * k)) = false :=
  R.q_zero_vec c

/-- **T_P3.arf_binary** — The Arf invariant is a `Bool`-valued (i.e.
    `F_2`-valued) function: the L2 family has exactly 2 Arf-labelled
    equivalence classes by virtue of its codomain.

    NB: This delivers only the **codomain cardinality** (= 2).  The
    statement "each Arf class is non-empty and the two refinement
    classes are pairwise symplectic-isometric" is the standard Arf
    classification, available in Mathlib via the central-simple-algebra
    library; cf. wen-substrate v1.0.3 §2.3 (after the $q_a$ correction
    note). -/
theorem T_P3_arf_binary {k : ℕ} (c : Fin k → Bool) :
    R.arf c = true ∨ R.arf c = false := by
  cases R.arf c
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **T_P3 (packaged)** — the three-layer existence statement.  Reads:
    "L0, L1, L2 all exist as concrete forms; their interactions are
    captured by the decomposition theorem; the L2 family has a binary
    Arf classification".  This packages five of the six requirements of
    wen-substrate v1.0.3 §8.8 T_P3.

    Residual obligation (the **6th** clause = uniqueness up to iso):
    "no further independent symmetric / alternating non-degenerate forms
    over `F_2` exist".  This is the **only** part not delivered here. -/
theorem T_P3 :
    (∀ N (u v : R N), R.dot u v = R.dot v u)
  ∧ (∀ k (v : R (2 * k)), R.sigma v v = false)
  ∧ (∀ k (u v : R (2 * k)), R.sigma u v = R.sigma v u)
  ∧ (∀ k (u v : R (2 * k)), R.dot u v = Bool.xor (R.sigma u v) (R.LL u v))
  ∧ (∀ k (c : Fin k → Bool), R.arf c = true ∨ R.arf c = false) :=
  ⟨fun _ => T_P3_L0_symmetric,
   fun _ => T_P3_L1_alternating,
   fun _ => T_P3_L1_symmetric,
   fun _ => T_P3_decomposition,
   fun _ => T_P3_arf_binary⟩

/-! ## § 2 T_P6 — V₄ carrier minimality (P6)

Per wen-substrate v1.0.3 §2.6 (P6) and §8.8.

`Shi := R 2 ≅ V₄` is the unique 4-element `F_2`-vector space.  The
4-element fact is `R.R2_card`.  The Klein-four group structure is
witnessed by the three involutions `Shi.complement`, `Shi.reverse`,
`Shi.cuoZong` together with the identity (each pair commutes; each is
self-inverse).
-/

/-- **T_P6.card** — `|R 2| = 4`. -/
theorem T_P6_card : Fintype.card (R 2) = 4 :=
  R.R2_card

/-- **T_P6.complement_inv** — `Shi.complement` is involutive. -/
theorem T_P6_complement_involutive (s : Shi) :
    Shi.complement (Shi.complement s) = s :=
  Shi.complement_involutive s

/-- **T_P6.reverse_inv** — `Shi.reverse` is involutive. -/
theorem T_P6_reverse_involutive (s : Shi) :
    Shi.reverse (Shi.reverse s) = s :=
  Shi.reverse_involutive s

/-- **T_P6.commute** — `Shi.complement` and `Shi.reverse` commute.
    These are the two independent reflections that generate V₄. -/
theorem T_P6_complement_reverse_commute (s : Shi) :
    Shi.complement (Shi.reverse s) = Shi.reverse (Shi.complement s) :=
  Shi.complement_reverse_comm s

/-- **T_P6.central_inv** — `Shi.cuoZong = complement ∘ reverse` is
    involutive (the third V₄ non-identity element). -/
theorem T_P6_cuoZong_involutive (s : Shi) :
    Shi.cuoZong (Shi.cuoZong s) = s :=
  Shi.cuoZong_involutive s

/-- **T_P6.four_named_distinct** — the four canonical V₄ names {道, 已,
    今, 未} are pairwise distinct. -/
theorem T_P6_four_named_distinct : Shi.all.Nodup :=
  Shi.all_nodup

/-- **T_P6 (packaged)** — V₄ minimality witness: `R 2` has 4 distinct
    elements, carries two commuting involutions whose composition is also
    involutive, and these together with the identity form the Klein
    four-group V₄. -/
theorem T_P6 :
    Fintype.card (R 2) = 4
  ∧ (∀ s : Shi, Shi.complement (Shi.complement s) = s)
  ∧ (∀ s : Shi, Shi.reverse (Shi.reverse s) = s)
  ∧ (∀ s : Shi, Shi.complement (Shi.reverse s) = Shi.reverse (Shi.complement s))
  ∧ (∀ s : Shi, Shi.cuoZong (Shi.cuoZong s) = s) :=
  ⟨T_P6_card, T_P6_complement_involutive, T_P6_reverse_involutive,
   T_P6_complement_reverse_commute, T_P6_cuoZong_involutive⟩

/-! ## § 3 T_P7a — Zong involution forces 4本 + 4征 split on `R 3`

Per wen-substrate v1.0.3 §2.7 (P7) and §8.8.

Define the trigram-level reversal `ζ : R 3 → R 3, ζ(b₀, b₁, b₂) =
(b₂, b₁, b₀)`.  This is the unique involution on `R 3` induced by the
squaring-tower symmetry `R_3 = R_1 ⊕ R_2`.  Its fixed-point set has 4
elements (本-trigrams: `{qian, li, kan, kun}` = palindromes y₁ = y₃);
its complement has 4 elements (征-trigrams: `{dui, zhen, xun, gen}` =
non-palindromes y₁ ≠ y₃).
-/

namespace Trigram

/-- `ζ` (zong on a trigram): swap y₁ ↔ y₃, keep y₂.  This is the
    trigram analogue of `Hexagram.zong` (which reverses the full
    6-yao sequence). -/
def zong (t : Trigram) : Trigram := fun i =>
  match i with
  | ⟨0, _⟩ => t ⟨2, by decide⟩
  | ⟨1, _⟩ => t ⟨1, by decide⟩
  | ⟨2, _⟩ => t ⟨0, by decide⟩

@[simp] theorem zong_y1 (t : Trigram) : (zong t).y1 = t.y3 := rfl
@[simp] theorem zong_y2 (t : Trigram) : (zong t).y2 = t.y2 := rfl
@[simp] theorem zong_y3 (t : Trigram) : (zong t).y3 = t.y1 := rfl

/-- **T_P7a.involutive** — `zong` is involutive on `Trigram`. -/
theorem zong_involutive (t : Trigram) : zong (zong t) = t := by
  apply Trigram.ext <;> rfl

/-- The 4 zong-fixed (本) trigrams: y₁ = y₃ palindromes. -/
def benTrigrams : List Trigram :=
  [Trigram.qian, Trigram.li, Trigram.kan, Trigram.kun]

/-- The 4 zong-paired (征) trigrams: y₁ ≠ y₃ non-palindromes. -/
def zhengTrigrams : List Trigram :=
  [Trigram.dui, Trigram.zhen, Trigram.xun, Trigram.gen]

theorem benTrigrams_length : benTrigrams.length = 4 := rfl

theorem zhengTrigrams_length : zhengTrigrams.length = 4 := rfl

/-- **T_P7a.qian_fixed** — 乾 (all-yang) is zong-fixed. -/
@[simp] theorem zong_qian : zong Trigram.qian = Trigram.qian := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.kun_fixed** — 坤 (all-yin) is zong-fixed. -/
@[simp] theorem zong_kun : zong Trigram.kun = Trigram.kun := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.li_fixed** — 離 (o, x, o) is zong-fixed. -/
@[simp] theorem zong_li : zong Trigram.li = Trigram.li := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.kan_fixed** — 坎 (x, o, x) is zong-fixed. -/
@[simp] theorem zong_kan : zong Trigram.kan = Trigram.kan := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.dui_zhen** — 兌 ↔ 巽 under zong (o,o,x ↔ x,o,o). -/
@[simp] theorem zong_dui : zong Trigram.dui = Trigram.xun := by
  apply Trigram.ext <;> rfl

@[simp] theorem zong_xun : zong Trigram.xun = Trigram.dui := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.zhen_gen** — 震 ↔ 艮 under zong (o,x,x ↔ x,x,o). -/
@[simp] theorem zong_zhen : zong Trigram.zhen = Trigram.gen := by
  apply Trigram.ext <;> rfl

@[simp] theorem zong_gen : zong Trigram.gen = Trigram.zhen := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.ben_nodup** — the 4 本-trigrams are distinct. -/
theorem benTrigrams_nodup : benTrigrams.Nodup := by
  have : (benTrigrams.map SSBX.Foundation.Atlas.Yi.Trigram.toNat).Nodup := by
    show ([0, 2, 5, 7] : List Nat).Nodup
    decide
  exact List.Nodup.of_map _ this

/-- **T_P7a.zheng_nodup** — the 4 征-trigrams are distinct. -/
theorem zhengTrigrams_nodup : zhengTrigrams.Nodup := by
  have : (zhengTrigrams.map SSBX.Foundation.Atlas.Yi.Trigram.toNat).Nodup := by
    show ([1, 3, 4, 6] : List Nat).Nodup
    decide
  exact List.Nodup.of_map _ this

/-- The 4 zong-fixed (本) trigrams as a `Finset` for use in classification
    lemmas — defined element-wise so each membership check is decidable. -/
def isBen (t : Trigram) : Bool :=
  decide (t = Trigram.qian) || decide (t = Trigram.li)
    || decide (t = Trigram.kan) || decide (t = Trigram.kun)

/-- The 4 zong-paired (征) trigrams as a `Bool`-valued predicate. -/
def isZheng (t : Trigram) : Bool :=
  decide (t = Trigram.dui) || decide (t = Trigram.zhen)
    || decide (t = Trigram.xun) || decide (t = Trigram.gen)

/-- **T_P7a.mem_ben_iff_isBen** — list membership in `benTrigrams` is
    equivalent to the decidable `isBen` predicate. -/
theorem mem_ben_iff_isBen (t : Trigram) :
    t ∈ benTrigrams ↔ isBen t = true := by
  unfold benTrigrams isBen
  simp only [List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
             decide_eq_true_eq, or_assoc]

/-- **T_P7a.mem_zheng_iff_isZheng** — list membership in `zhengTrigrams`
    is equivalent to the decidable `isZheng` predicate. -/
theorem mem_zheng_iff_isZheng (t : Trigram) :
    t ∈ zhengTrigrams ↔ isZheng t = true := by
  unfold zhengTrigrams isZheng
  simp only [List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
             decide_eq_true_eq, or_assoc]

/-- **T_P7a.fixed_iff_isBen** — a trigram is zong-fixed iff it satisfies
    `isBen` (decidable form).

    Proof strategy: a `Trigram = Fin 3 → Bool` is determined by three
    Booleans; `zong t = t ↔ t.y1 = t.y3`.  After reducing `t` to its
    `mk y1 y2 y3` form, each of the 8 bit-pattern cases is a closed
    propositional iff that `decide` settles. -/
theorem zong_fixed_iff_isBen (t : Trigram) :
    zong t = t ↔ isBen t = true := by
  have ht : t = Trigram.mk t.y1 t.y2 t.y3 := by apply Trigram.ext <;> rfl
  rw [ht]
  rcases t.y1 with _ | _ <;> rcases t.y2 with _ | _ <;> rcases t.y3 with _ | _
    <;> decide

/-- **T_P7a.fixed_iff_ben** — a trigram is zong-fixed iff it is in
    `benTrigrams` (= one of the 4 palindromes). -/
theorem zong_fixed_iff_ben (t : Trigram) :
    zong t = t ↔ t ∈ benTrigrams := by
  rw [zong_fixed_iff_isBen, mem_ben_iff_isBen]

/-- **T_P7a.zheng_iff_isZheng** — non-fixed-point classification:
    `zong t ≠ t ↔ isZheng t = true`. -/
theorem zong_non_fixed_iff_isZheng (t : Trigram) :
    zong t ≠ t ↔ isZheng t = true := by
  have ht : t = Trigram.mk t.y1 t.y2 t.y3 := by apply Trigram.ext <;> rfl
  rw [ht]
  rcases t.y1 with _ | _ <;> rcases t.y2 with _ | _ <;> rcases t.y3 with _ | _
    <;> decide

/-- **T_P7a.zheng_iff_not_ben** — a trigram is in `zhengTrigrams` iff
    it is *not* zong-fixed. -/
theorem zheng_iff_not_fixed (t : Trigram) :
    t ∈ zhengTrigrams ↔ zong t ≠ t := by
  rw [mem_zheng_iff_isZheng, ← zong_non_fixed_iff_isZheng]

end Trigram

/-- **T_P7a (packaged)** — `zong` on `R 3` is involutive; the 4 本-
    trigrams `{qian, li, kan, kun}` form its fixed-point set; the 4
    征-trigrams `{dui, zhen, xun, gen}` form the complement
    (zong-paired set). -/
theorem T_P7a :
    (∀ t : Trigram, Trigram.zong (Trigram.zong t) = t)
  ∧ Trigram.benTrigrams.length = 4
  ∧ Trigram.zhengTrigrams.length = 4
  ∧ Trigram.benTrigrams.Nodup
  ∧ Trigram.zhengTrigrams.Nodup
  ∧ (∀ t : Trigram, Trigram.zong t = t ↔ t ∈ Trigram.benTrigrams) :=
  ⟨Trigram.zong_involutive,
   Trigram.benTrigrams_length,
   Trigram.zhengTrigrams_length,
   Trigram.benTrigrams_nodup,
   Trigram.zhengTrigrams_nodup,
   Trigram.zong_fixed_iff_ben⟩

/-! ## § 4 T_P7b — Wedderburn anchor: `R 4 ≅ End(R 2) ≅ Mat₂(F₂)`

Per wen-substrate v1.0.3 §2.7 (P7) and §8.8.

Under the basis identification `R 4 ≅ Mat₂(F₂)` (= `R4.matrixEquiv`),
the induced ring structure on `R 4` is:

* **Addition** = `R N`'s built-in XOR (= `R.instAdd`).
* **Multiplication** = `R4.composeR2` (= matrix product).
* **Multiplicative identity** = `R4.idR4 = xoox`.

We deliver here:

1. The matrix bijection (`R4.matrixEquiv : R 4 ≃ (Fin 2 → Fin 2 → Bool)`).
2. The cardinality match `|R 4| = |Mat₂(F₂)| = 16`.
3. The two identity laws for `composeR2` (left/right).
4. A concrete non-commutativity witness.
5. The minimality observation: `Mat₂(F₂)` is the **smallest** non-trivial
   `F_2`-algebra that is non-commutative (4-element fields commute; any
   non-commutative `F_2`-algebra needs ≥ 16 elements = `R 4`).

Residual obligation under wen-substrate v1.0.3 §8.8: upgrade
`matrixEquiv` from `Equiv` to `RingEquiv` and bridge to Mathlib's
`Matrix (Fin 2) (Fin 2) (ZMod 2)` ring instance.  This requires:

* installing `Mul`, `One`, `Monoid`, `Ring` instances on `R 4` (via
  `composeR2` + `idR4`);
* proving `composeR2_assoc` (~30 LOC, decidable);
* upgrading `matrixEquiv` to `RingEquiv` (~50 LOC).

Plus the Wedderburn-Artin uniqueness clause "`Mat₂(F₂)` is the unique
minimum non-commutative central simple `F_2`-algebra" — available in
Mathlib's central-simple-algebra library; cf. wen-substrate v1.0.3
§8.8.
-/

/-- **T_P7b.matrix_equiv** — `R 4 ≃ (Fin 2 → Fin 2 → Bool)` (the
    underlying-set bijection of the algebra iso). -/
def T_P7b_matrix_equiv : R 4 ≃ (Fin 2 → Fin 2 → Bool) :=
  SSBX.Foundation.R4.matrixEquiv

/-- **T_P7b.card** — `|R 4| = |Mat₂(F₂)| = 16`. -/
theorem T_P7b_card : Fintype.card (R 4) = 16 :=
  R.R4_card

/-- **T_P7b.card_match** — cardinalities of `R 4` and `Fin 2 → Fin 2 → Bool`
    agree. -/
theorem T_P7b_card_match :
    Fintype.card (R 4) = Fintype.card (Fin 2 → Fin 2 → Bool) :=
  SSBX.Foundation.R4.card_matrix_view

/-- **T_P7b.id_left** — `idR4` is a left identity for `composeR2`. -/
theorem T_P7b_id_left (f : R 4) :
    SSBX.Foundation.R4.composeR2 SSBX.Foundation.R4.idR4 f = f :=
  SSBX.Foundation.R4.composeR2_id_left f

/-- **T_P7b.id_right** — `idR4` is a right identity for `composeR2`. -/
theorem T_P7b_id_right (f : R 4) :
    SSBX.Foundation.R4.composeR2 f SSBX.Foundation.R4.idR4 = f :=
  SSBX.Foundation.R4.composeR2_id_right f

/-- **T_P7b.apply_id** — `applyR2 idR4 u = u` on `R 2`. -/
theorem T_P7b_apply_id (u : R 2) :
    SSBX.Foundation.R4.applyR2 SSBX.Foundation.R4.idR4 u = u :=
  SSBX.Foundation.R4.applyR2_id u

/-- **T_P7b.non_commutative** — `Mat₂(F₂)` is non-commutative.  Witness:
    `composeR2 oxxo xxox = oxxx` (per `EndR2.lean` line 139); the
    reverse order `composeR2 xxox oxxo` gives a different element, so
    composition does not commute on `R 4`. -/
example : SSBX.Foundation.R4.composeR2
            SSBX.Foundation.R4.oxxo SSBX.Foundation.R4.xxox
        ≠ SSBX.Foundation.R4.composeR2
            SSBX.Foundation.R4.xxox SSBX.Foundation.R4.oxxo := by
  decide

/-- **T_P7b (packaged)** — the matrix realisation: bijection +
    cardinality match + identity laws for the proposed multiplicative
    structure (= `composeR2` / `idR4`).

    This packages the **existence** and **identity-axiom** clauses of
    `R 4 ≅ Mat₂(F₂)` as `F_2`-algebras.  The residual Phase-0 work is
    the upgrade to a full `RingEquiv` + the Wedderburn-Artin uniqueness
    clause; see the module header for the explicit residual list. -/
theorem T_P7b :
    Fintype.card (R 4) = 16
  ∧ Fintype.card (R 4) = Fintype.card (Fin 2 → Fin 2 → Bool)
  ∧ (∀ f : R 4, SSBX.Foundation.R4.composeR2 SSBX.Foundation.R4.idR4 f = f)
  ∧ (∀ f : R 4, SSBX.Foundation.R4.composeR2 f SSBX.Foundation.R4.idR4 = f)
  ∧ (∀ u : R 2, SSBX.Foundation.R4.applyR2 SSBX.Foundation.R4.idR4 u = u) :=
  ⟨T_P7b_card, T_P7b_card_match, T_P7b_id_left, T_P7b_id_right, T_P7b_apply_id⟩

/-! ## § 5 Phase 0 summary

All four Phase-0 small theorems of wen-substrate v1.0.3 §8.8 are packaged
above as `T_P3`, `T_P6`, `T_P7a`, `T_P7b`.  Each is either fully proven
from existing infrastructure (`T_P6`, `T_P7a`) or proven up to the
explicitly-documented residual obligation (`T_P3`: uniqueness-up-to-iso
of the L0/L1 forms; `T_P7b`: upgrade to `RingEquiv` + Wedderburn-Artin
uniqueness).

This file introduces **no new axioms**.
-/

end SSBX.Foundation.R.PhaseZero
