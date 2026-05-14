/-
# Wen.Xiang.Quadratic — Layer 2 of the Xiang kernel: q-refinements + Arf

Per `wen-algebra` v0.4 §5.7, in characteristic 2 the alternating
bilinear form σ (`Symplectic.lean`) does not determine the geometry
uniquely — a **quadratic refinement** `q : Image → F₂` satisfying

    q(u · v) = q(u) ⊕ q(v) ⊕ σ(u, v)         (and  q(1) = 0)

provides the missing data, and the **Arf invariant**

    Arf(q) := q(e_α) ∧ q(e_β)

classifies q modulo σ-preserving change of basis.  On `Image` (= V₄)
there are exactly two non-trivial canonical refinements:

| Lean alias | formula                              | atom values               | Arf |
|------------|--------------------------------------|---------------------------|-----|
| `q0`       | `v_α · v_β`                          | (0, 0, 0, 1)              |  0  |
| `q1`       | `L(v) ⊕ q0 v` = `v_α + v_β + v_α·v_β`| (0, 1, 1, 1)              |  1  |

`q0` singles out **错综** (Compound-Flip) as the exceptional atom;
`q1` singles out **道** (Identity).  Together they sit in the two
Arf-classes of v0.4 §5.7.4 and provide the Layer 2 distinction
between "compound is exceptional" vs "identity is exceptional"
quadratic geometries.

## Tower lift

A choice vector `c : Fin n → Bool` selects `q_{c i}` at each image
coordinate, producing a quadratic refinement `qC c` on `X n`.
Per v0.4 §5.7.5 the total Arf invariant is the **parity** of `c`:

    Arf(qC c) = popcount(c) mod 2 = ⊕ᵢ cᵢ.

There are `2^(n-1)` Arf-0 refinements and `2^(n-1)` Arf-1 refinements
on `X n`, classifying the n-fold quadratic-refinement family modulo
symplectic equivalence.

## Doctrinal anchor

Per v0.4 §5.7.6, Layer 2 is opt-in: the Xiang kernel default is
Layer 0 (`Dot.lean`).  Layer 1 (`Symplectic.lean`) and Layer 2 (this
file) are the necessary substrate for Pauli n-qubit groups, stabilizer
codes, and the {道-exceptional vs 错综-exceptional} semantic split.
-/

import SSBX.Foundation.Wen.Xiang.Image
import SSBX.Foundation.Wen.Xiang.X
import SSBX.Foundation.Wen.Xiang.Dot
import SSBX.Foundation.Wen.Xiang.Symplectic
import Mathlib.Data.Fin.Tuple.Basic

namespace SSBX.Foundation.Wen.Xiang

namespace Image

/-! ## § 1 The two canonical quadratic refinements (v0.4 §5.7.2) -/

/-- Quadratic refinement of σ with **错综 as the unique 1-point**
    (`q0(错综) = 1`, all others `0`).  Defined by
    `q0(v) := v_α · v_β`.  Per v0.4 §5.7.2, this is the canonical
    Arf-0 refinement on `Image`. -/
def q0 (v : Image) : Bit := Bool.and v.alpha v.beta

@[simp] theorem q0_oo : q0 .oo = false := rfl
@[simp] theorem q0_xo : q0 .xo = false := rfl
@[simp] theorem q0_ox : q0 .ox = false := rfl
@[simp] theorem q0_xx : q0 .xx = true  := rfl

/-- Quadratic refinement of σ with **道 as the unique 0-point**
    (`q1(道) = 0`, all others `1`).  Defined by
    `q1(v) := L(v) ⊕ q0(v) = v_α + v_β + v_α · v_β`.  Per v0.4 §5.7.2
    this is the canonical Arf-1 refinement on `Image`. -/
def q1 (v : Image) : Bit := Bool.xor (L v) (q0 v)

@[simp] theorem q1_oo : q1 .oo = false := rfl
@[simp] theorem q1_xo : q1 .xo = true  := rfl
@[simp] theorem q1_ox : q1 .ox = true  := rfl
@[simp] theorem q1_xx : q1 .xx = true  := rfl

/-- The pointwise relation `q1 = L ⊕ q0` (v0.4 §5.7.2). -/
theorem q1_eq_L_xor_q0 (v : Image) : q1 v = Bool.xor (L v) (q0 v) := rfl

/-! ## § 2 Polarisation: each `qᵢ` polarises to σ (v0.4 §5.7.1) -/

/-- Polarisation identity for `q0`: per v0.4 §5.7.1, `q0` is a
    quadratic refinement of σ in the precise sense

      q0(u · v) = q0 u ⊕ q0 v ⊕ σ(u, v).

    The proof is a direct case split on the four V₄ atoms in each
    argument (so `decide` proves all 16 cases at once). -/
theorem q0_polarizes_symplectic (u v : Image) :
    q0 (u * v) = Bool.xor (Bool.xor (q0 u) (q0 v)) (symplectic u v) := by
  cases u <;> cases v <;> rfl

/-- Polarisation identity for `q1`: same shape as `q0_polarizes`,
    proven the same way (16-element decide). -/
theorem q1_polarizes_symplectic (u v : Image) :
    q1 (u * v) = Bool.xor (Bool.xor (q1 u) (q1 v)) (symplectic u v) := by
  cases u <;> cases v <;> rfl

/-- The two refinements vanish on the V₄ identity (preconditions of
    quadratic refinement; per v0.4 §5.7.1). -/
@[simp] theorem q0_one : q0 (1 : Image) = false := rfl
@[simp] theorem q1_one : q1 (1 : Image) = false := rfl

/-! ## § 3 The Arf invariant (v0.4 §5.7.3) -/

/-- Arf invariant of a quadratic refinement `q` on `Image`, computed
    against the canonical symplectic basis `(.xo, .ox) = (e_α, e_β)`:

      Arf(q) := q(e_α) ∧ q(e_β).

    Per v0.4 §5.7.3, this is the σ-equivariant invariant that
    classifies q modulo basis change. -/
def arf (q : Image → Bit) : Bit := Bool.and (q .xo) (q .ox)

/-- `Arf(q0) = 0` — q0 sits in the Arf-0 class.  (v0.4 §5.7.3) -/
@[simp] theorem arf_q0 : arf q0 = false := rfl

/-- `Arf(q1) = 1` — q1 sits in the Arf-1 class.  (v0.4 §5.7.3) -/
@[simp] theorem arf_q1 : arf q1 = true := rfl

/-! ## § 4 Zero-loci and the §3.5 sub-tower correspondence (v0.4 §5.7.7) -/

/-- `q0` zero locus (v0.4 §5.7.7): exactly `{道, 错, 综}` — every atom
    except 错综. -/
theorem q0_zero_locus (v : Image) :
    q0 v = false ↔ v = .oo ∨ v = .xo ∨ v = .ox := by
  cases v <;> simp [q0]

/-- `q1` zero locus (v0.4 §5.7.7): exactly `{道}` — every other atom
    is the unique exception. -/
theorem q1_zero_locus (v : Image) :
    q1 v = false ↔ v = .oo := by
  cases v <;> simp [q1, L, q0]

end Image

/-! ## § 5 Lifting to the `X n` tower (v0.4 §5.7.5) -/

namespace X

/-- The choice vector for a `qC`-refinement: `c i = false` selects
    `q0` at coordinate `i`; `c i = true` selects `q1`. -/
abbrev Choice (n : Nat) : Type := Fin n → Bool

/-- Pick the atomic refinement at one coordinate per the choice
    vector. -/
@[inline] def pickQ (c : Bool) : Image → Bit :=
  if c then Image.q1 else Image.q0

@[simp] theorem pickQ_false : pickQ false = Image.q0 := rfl
@[simp] theorem pickQ_true  : pickQ true  = Image.q1 := rfl

/-- The Layer-2 quadratic refinement on `X n` selected by choice
    vector `c`:

      qC c U := ⊕ᵢ q_{cᵢ}(uᵢ).

    Per v0.4 §5.7.5 every quadratic refinement on `X n` agreeing with
    σⁿ on polarisation is of this form for some `c`. -/
def qC : ∀ {n : Nat}, Choice n → X n → Bit
  | 0,     _, _ => false
  | _ + 1, c, U =>
      Bool.xor (pickQ (c 0) (U 0))
               (qC (Fin.tail c) (Fin.tail U))

@[simp] theorem qC_zero (c : Choice 0) (U : X 0) : qC c U = false := rfl

theorem qC_succ {n : Nat} (c : Choice (n + 1)) (U : X (n + 1)) :
    qC c U = Bool.xor (pickQ (c 0) (U 0))
                      (qC (Fin.tail c) (Fin.tail U)) := rfl

/-- `qC` vanishes on the origin (preconditions of quadratic
    refinement, lifted). -/
@[simp] theorem qC_origin {n : Nat} (c : Choice n) :
    qC c (origin n) = false := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [qC_succ]
    have h0 : (origin (k + 1)) 0 = Image.oo := rfl
    rw [h0]
    have h_q : pickQ (c 0) Image.oo = false := by
      cases c 0 <;> rfl
    rw [h_q]
    have h_tail : Fin.tail (origin (k + 1)) = origin k := rfl
    rw [h_tail, ih (Fin.tail c)]
    rfl

/-! ## § 6 Polarisation on the tower (v0.4 §5.7.5) -/

private theorem pickQ_polarizes (c : Bool) (u v : Image) :
    pickQ c (u * v) =
      Bool.xor (Bool.xor (pickQ c u) (pickQ c v)) (Image.symplectic u v) := by
  cases c
  · exact Image.q0_polarizes_symplectic u v
  · exact Image.q1_polarizes_symplectic u v

/-- Polarisation on `X n`: the lifted refinement `qC c` polarises to σⁿ.

      qC c (U * V) = qC c U ⊕ qC c V ⊕ σⁿ(U, V).

    Proof is induction on `n`, using `pickQ_polarizes` componentwise
    plus a `Bool.xor` rearrangement at each step. -/
theorem qC_polarizes_symplectic {n : Nat} (c : Choice n) (U V : X n) :
    qC c (U * V) = Bool.xor (Bool.xor (qC c U) (qC c V)) (symplectic U V) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hmul : (U * V) 0 = U 0 * V 0 := rfl
    have htail : Fin.tail (U * V) = Fin.tail U * Fin.tail V := rfl
    rw [qC_succ, hmul, htail, pickQ_polarizes,
        ih (Fin.tail c) (Fin.tail U) (Fin.tail V),
        qC_succ, qC_succ, symplectic_succ]
    cases pickQ (c 0) (U 0) <;>
      cases pickQ (c 0) (V 0) <;>
      cases Image.symplectic (U 0) (V 0) <;>
      cases qC (Fin.tail c) (Fin.tail U) <;>
      cases qC (Fin.tail c) (Fin.tail V) <;>
      cases symplectic (Fin.tail U) (Fin.tail V) <;> rfl

/-! ## § 7 Total Arf invariant on `X n` (v0.4 §5.7.5)

The total Arf of `qC c` is the **parity** of the choice vector `c`:

    Arf(qC c) = ⊕ᵢ cᵢ.

This identifies the `2^n` quadratic refinements on `X n` with the two
Arf-classes (`2^(n-1)` each) by choice-vector parity. -/

/-- XOR-fold of a `Choice n` vector — its F₂ "popcount". -/
def Choice.parity : ∀ {n : Nat}, Choice n → Bit
  | 0,     _ => false
  | _ + 1, c => Bool.xor (c 0) (Choice.parity (Fin.tail c))

@[simp] theorem Choice.parity_zero (c : Choice 0) : Choice.parity c = false := rfl

theorem Choice.parity_succ {n : Nat} (c : Choice (n + 1)) :
    Choice.parity c = Bool.xor (c 0) (Choice.parity (Fin.tail c)) := rfl

/-- Total Arf invariant on `X n`, computed against the canonical
    symplectic basis `(basisAlpha i, basisBeta i)ᵢ` from `Dot.lean`.
    Per v0.4 §5.7.5,

      arfTotal(qC c) = ⊕ᵢ qC c (basisAlpha i) ∧ qC c (basisBeta i)
                     = ⊕ᵢ cᵢ
                     = Choice.parity c.

    The `arfTotal` definition follows the literal Arf formula; the
    main theorem `arfTotal_qC` reduces it to `Choice.parity`.  We use
    `List.finRange n` (in canonical order) as the iteration carrier so
    that `arfTotal` and `Choice.parity` share the same fold shape. -/
def arfTotal {n : Nat} (q : X n → Bit) : Bit :=
  ((List.finRange n).map
    (fun i => Bool.and (q (basisAlpha i)) (q (basisBeta i)))).foldr
    Bool.xor false

/-! ### Atomic-coordinate evaluation of `qC c` on basis vectors

`qC c` evaluated on `basisAlpha i` (resp. `basisBeta i`) reduces to
`pickQ (c i) Image.xo` (resp. `Image.ox`), since every other coordinate
is `Image.oo` and `pickQ _ Image.oo = false`. -/

private theorem qC_basisAlpha_aux {n : Nat} (c : Choice n) (i : Fin n) :
    qC c (basisAlpha i) = c i := by
  induction n with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [qC_succ, basisAlpha_self, tail_basisAlpha_zero, qC_origin]
      cases c 0 <;> rfl
    · rw [qC_succ, basisAlpha_other (Fin.succ_ne_zero j),
          tail_basisAlpha_succ, ih (Fin.tail c) j]
      have h : pickQ (c 0) Image.oo = false := by cases c 0 <;> rfl
      rw [h]
      show Bool.xor false (c j.succ) = c j.succ
      cases c j.succ <;> rfl

private theorem qC_basisBeta_aux {n : Nat} (c : Choice n) (i : Fin n) :
    qC c (basisBeta i) = c i := by
  induction n with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [qC_succ, basisBeta_self, tail_basisBeta_zero, qC_origin]
      cases c 0 <;> rfl
    · rw [qC_succ, basisBeta_other (Fin.succ_ne_zero j),
          tail_basisBeta_succ, ih (Fin.tail c) j]
      have h : pickQ (c 0) Image.oo = false := by cases c 0 <;> rfl
      rw [h]
      show Bool.xor false (c j.succ) = c j.succ
      cases c j.succ <;> rfl

/-- `qC c (basisAlpha i) = c i`. -/
@[simp] theorem qC_basisAlpha {n : Nat} (c : Choice n) (i : Fin n) :
    qC c (basisAlpha i) = c i := qC_basisAlpha_aux c i

/-- `qC c (basisBeta i) = c i`. -/
@[simp] theorem qC_basisBeta {n : Nat} (c : Choice n) (i : Fin n) :
    qC c (basisBeta i) = c i := qC_basisBeta_aux c i

/-- `Choice.parity` equals the XOR-foldr of the choice values along
    `List.finRange n`.  This re-expresses the recursive `Choice.parity`
    as a list fold, so it composes with `arfTotal`'s list-fold shape. -/
private theorem parity_eq_foldr_finRange {n : Nat} (c : Choice n) :
    Choice.parity c
      = ((List.finRange n).map (fun i => c i)).foldr Bool.xor false := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Choice.parity_succ, ih (Fin.tail c)]
    rw [List.finRange_succ]
    simp [List.map_cons, List.foldr_cons, List.map_map, Fin.tail]
    rfl

/-- The total Arf invariant of `qC c` is the parity of `c`.

    Combined with `qC_polarizes_symplectic` this identifies the `2^n`
    quadratic refinements `qC c` modulo σⁿ with the two Arf-classes
    (`2^(n-1)` each), realising v0.4 §5.7.5. -/
theorem arfTotal_qC {n : Nat} (c : Choice n) :
    arfTotal (qC c) = Choice.parity c := by
  unfold arfTotal
  have hAndSelf : ∀ b : Bool, Bool.and b b = b := by intro b; cases b <;> rfl
  have hMapEq :
      (List.finRange n).map
          (fun i => Bool.and (qC c (basisAlpha i)) (qC c (basisBeta i)))
        = (List.finRange n).map (fun i => c i) := by
    apply List.map_congr_left
    intro i _
    rw [qC_basisAlpha, qC_basisBeta, hAndSelf]
  rw [hMapEq, ← parity_eq_foldr_finRange]

end X

end SSBX.Foundation.Wen.Xiang
