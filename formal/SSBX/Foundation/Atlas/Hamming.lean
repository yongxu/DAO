/-
# Foundation.Atlas.Hamming — R 7 Hamming(7, 4) perfect code

Per `wen-algebra` v0.6 §9.2 and `v4-foundation` v0.5 §15.7:

    R 7  ⊇  Hamming(7, 4)  (4-dimensional F_2 subspace, 16 codewords)

The Hamming(7, 4) code is the unique [7, 4, 3] linear code over `F_2`:

- block length 7 = 2^3 - 1
- 4 information bits, 3 parity bits
- minimum Hamming distance 3 (corrects any single-bit error)
- |code| = 16 codewords (a 4-dim F_2 subspace of `R 7`)

This file gives the parity-check description of the code:

    c ∈ Code  ⇔  H · c = 0  (over F_2)

where `H : Fin 3 → Fin 7 → Bool` is the standard parity-check matrix
whose 7 columns are the 7 non-zero binary vectors of length 3.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §1.2 (R 7 = Hamming).
* `v4-foundation.md` v0.5 §15.7 (Hamming(7, 4), Steane code).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Atlas.Hamming

open SSBX.Foundation.R

/-! ## § 1 The parity-check matrix H -/

/-- The standard Hamming(7, 4) parity-check matrix.

    `H i j` is bit `i` of the column index `(j+1)` in binary.  This
    arrangement gives:

    | column j     | 0 (001) | 1 (010) | 2 (011) | 3 (100) | 4 (101) | 5 (110) | 6 (111) |
    |--------------|---------|---------|---------|---------|---------|---------|---------|
    | H 0 (high)   | 0       | 0       | 0       | 1       | 1       | 1       | 1       |
    | H 1          | 0       | 1       | 1       | 0       | 0       | 1       | 1       |
    | H 2 (low)    | 1       | 0       | 1       | 0       | 1       | 0       | 1       |

    The 7 columns are exactly the 7 non-zero binary vectors of length 3,
    so the resulting code corrects any single-bit error. -/
def H : Fin 3 → Fin 7 → Bool := fun i j =>
  -- bit `(2 - i.val)` of `(j.val + 1)` (high bit first)
  decide (((j.val + 1) >>> (2 - i.val)) % 2 = 1)

/-- One parity check at row `i`: the XOR of the 7 products `H i j ∧ c j`. -/
def syndromeBit (i : Fin 3) (c : R 7) : Bool :=
  let p (j : Fin 7) : Bool := H i j && c j
  Bool.xor (Bool.xor (Bool.xor (Bool.xor (Bool.xor (Bool.xor
    (p ⟨0, by decide⟩) (p ⟨1, by decide⟩))
    (p ⟨2, by decide⟩)) (p ⟨3, by decide⟩))
    (p ⟨4, by decide⟩)) (p ⟨5, by decide⟩)) (p ⟨6, by decide⟩)

/-- The full syndrome vector `H · c ∈ R 3`. -/
def syndrome (c : R 7) : R 3 := fun i => syndromeBit i c

/-! ## § 2 The Hamming code = kernel of H -/

/-- A `c : R 7` is a codeword iff every parity check vanishes. -/
def isCodeword (c : R 7) : Prop := syndrome c = 0

instance instDecidableIsCodeword (c : R 7) : Decidable (isCodeword c) := by
  unfold isCodeword
  infer_instance

/-- The Hamming(7, 4) code as a finset. -/
def Code : Finset (R 7) :=
  Finset.univ.filter isCodeword

/-! ## § 3 Cardinality: |Code| = 16

The proof is by `decide`: there are 128 elements in `R 7` and the
codeword predicate is decidable, so the kernel can be counted
exhaustively.  -/

/-- The Hamming(7, 4) code has exactly 16 codewords. -/
theorem code_card : Code.card = 16 := by
  unfold Code
  decide

/-! ## § 4 Minimum distance 3

The minimum Hamming distance of the code equals the minimum weight
of any non-zero codeword.  We show that every non-zero codeword has
weight ≥ 3 by an exhaustive check over `R 7`. -/

/-- Hamming weight of `v : R 7` — sum of its 7 boolean coordinates as
    naturals.  Specialised to length 7 so that `decide` can evaluate
    weight on every `R 7` element without recursion blowups. -/
def weight7 (v : R 7) : ℕ :=
  (if v ⟨0, by decide⟩ then 1 else 0)
  + (if v ⟨1, by decide⟩ then 1 else 0)
  + (if v ⟨2, by decide⟩ then 1 else 0)
  + (if v ⟨3, by decide⟩ then 1 else 0)
  + (if v ⟨4, by decide⟩ then 1 else 0)
  + (if v ⟨5, by decide⟩ then 1 else 0)
  + (if v ⟨6, by decide⟩ then 1 else 0)

/-- The minimum weight of any non-zero codeword is at least 3. -/
theorem min_distance_ge_three :
    ∀ c : R 7, isCodeword c → c ≠ 0 → weight7 c ≥ 3 := by
  native_decide

/-- The minimum distance is achieved: there is a codeword of weight 3. -/
theorem min_distance_eq_three :
    ∃ c : R 7, isCodeword c ∧ c ≠ 0 ∧ weight7 c = 3 := by
  native_decide

/-! ## § 5 Linearity (closure under addition)

The Hamming code is closed under addition (XOR).  The syndrome map
is F_2-linear, so the codewords (its kernel) form a subspace.

The proof works by abstracting `syndromeBit` as a 7-fold XOR of a
generic function `g : Fin 7 → Bool`, then showing this fold is
additive in `g`. -/

/-- A generic 7-fold XOR.  Used to abstract `syndromeBit` for the
    linearity proof below. -/
private def xor7 (g : Fin 7 → Bool) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (Bool.xor (Bool.xor (Bool.xor
    (g ⟨0, by decide⟩) (g ⟨1, by decide⟩))
    (g ⟨2, by decide⟩)) (g ⟨3, by decide⟩))
    (g ⟨4, by decide⟩)) (g ⟨5, by decide⟩)) (g ⟨6, by decide⟩)

/-- `syndromeBit i c = xor7 (fun j => H i j ∧ c j)`. -/
private theorem syndromeBit_eq_xor7 (i : Fin 3) (c : R 7) :
    syndromeBit i c = xor7 (fun j => H i j && c j) := rfl

/-- Boolean distributivity: `a ∧ (b ⊕ c) = (a ∧ b) ⊕ (a ∧ c)`. -/
private theorem and_xor_distrib (a b c : Bool) :
    (a && Bool.xor b c) = Bool.xor (a && b) (a && c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Boolean XOR is associative. -/
private theorem xor_assoc (a b c : Bool) :
    Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Boolean XOR is commutative. -/
private theorem xor_comm (a b : Bool) : Bool.xor a b = Bool.xor b a := by
  cases a <;> cases b <;> rfl

/-- Algebraic XOR pair rearrangement: `(a₁ ⊕ b₁) ⊕ (a₂ ⊕ b₂) = (a₁ ⊕ a₂) ⊕ (b₁ ⊕ b₂)`. -/
private theorem xor_swap (a1 a2 b1 b2 : Bool) :
    Bool.xor (Bool.xor a1 b1) (Bool.xor a2 b2)
    = Bool.xor (Bool.xor a1 a2) (Bool.xor b1 b2) := by
  rw [xor_assoc a1 b1, ← xor_assoc b1 a2 b2, xor_comm b1 a2,
      xor_assoc a2 b1 b2, ← xor_assoc a1 a2 (Bool.xor b1 b2)]

/-- `xor7` is additive: `xor7 (g + h) = xor7 g ⊕ xor7 h`.

    Proven by Boolean associativity/commutativity rearrangement (no
    exponential case split). -/
private theorem xor7_add (g h : Fin 7 → Bool) :
    xor7 (fun j => Bool.xor (g j) (h j)) = Bool.xor (xor7 g) (xor7 h) := by
  unfold xor7
  -- Abbreviate
  set g0 := g ⟨0, by decide⟩
  set g1 := g ⟨1, by decide⟩
  set g2 := g ⟨2, by decide⟩
  set g3 := g ⟨3, by decide⟩
  set g4 := g ⟨4, by decide⟩
  set g5 := g ⟨5, by decide⟩
  set g6 := g ⟨6, by decide⟩
  set h0 := h ⟨0, by decide⟩
  set h1 := h ⟨1, by decide⟩
  set h2 := h ⟨2, by decide⟩
  set h3 := h ⟨3, by decide⟩
  set h4 := h ⟨4, by decide⟩
  set h5 := h ⟨5, by decide⟩
  set h6 := h ⟨6, by decide⟩
  -- The identity to prove:
  --   ((((((g0⊕h0) ⊕ (g1⊕h1)) ⊕ (g2⊕h2)) ⊕ (g3⊕h3)) ⊕ (g4⊕h4)) ⊕ (g5⊕h5)) ⊕ (g6⊕h6)
  -- = ((((((g0⊕g1) ⊕ g2) ⊕ g3) ⊕ g4) ⊕ g5) ⊕ g6) ⊕ ((((((h0⊕h1) ⊕ h2) ⊕ h3) ⊕ h4) ⊕ h5) ⊕ h6)
  --
  -- Iteratively pull the h-terms across using xor_swap.
  rw [xor_swap g0 g1 h0 h1]  -- pair up (g0,g1) and (h0,h1)
  -- LHS becomes: ((g0⊕g1) ⊕ (h0⊕h1)) ⊕ (g2⊕h2) ⊕ ...
  rw [xor_swap (Bool.xor g0 g1) g2 (Bool.xor h0 h1) h2]
  rw [xor_swap (Bool.xor (Bool.xor g0 g1) g2) g3 (Bool.xor (Bool.xor h0 h1) h2) h3]
  rw [xor_swap _ g4 _ h4]
  rw [xor_swap _ g5 _ h5]
  rw [xor_swap _ g6 _ h6]

/-- Pointwise lemma: `syndromeBit i (u + v) = syndromeBit i u ⊕ syndromeBit i v`. -/
theorem syndromeBit_add (i : Fin 3) (u v : R 7) :
    syndromeBit i (u + v) = Bool.xor (syndromeBit i u) (syndromeBit i v) := by
  rw [syndromeBit_eq_xor7, syndromeBit_eq_xor7, syndromeBit_eq_xor7]
  -- Rewrite `H i j ∧ (u + v) j` as a XOR of two products and apply xor7_add
  have h : (fun j => H i j && (u + v) j)
         = (fun j => Bool.xor (H i j && u j) (H i j && v j)) := by
    funext j
    rw [R.add_apply]
    exact and_xor_distrib _ _ _
  rw [h, xor7_add]

/-- The Hamming code is closed under XOR (it is an F_2-subspace). -/
theorem code_add_closed (u v : R 7) :
    isCodeword u → isCodeword v → isCodeword (u + v) := by
  intro hu hv
  unfold isCodeword syndrome at *
  funext i
  rw [syndromeBit_add]
  have h0u : syndromeBit i u = false := by
    have := congrFun hu i; simpa using this
  have h0v : syndromeBit i v = false := by
    have := congrFun hv i; simpa using this
  rw [h0u, h0v]; rfl

/-- The all-zero vector is a codeword. -/
theorem zero_isCodeword : isCodeword (0 : R 7) := by decide

end SSBX.Foundation.Atlas.Hamming
