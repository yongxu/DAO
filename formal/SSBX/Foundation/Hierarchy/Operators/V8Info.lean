/-
# Operators · V8Info -- lightweight V8 information preservation kernel

This sidecar module keeps the Phase 4 V8 argument local: V8 states are
eight Boolean coordinates, subgroups are XOR-mask predicates, and linear
queries are F2 parity masks.
-/

import SSBX.Foundation.Wen.Layered.Bridges.V4Time

namespace SSBX.Foundation.Hierarchy.Operators

/-! ## V8 carrier and XOR masks -/

/-- V8 information states: eight Boolean coordinates. -/
abbrev V8 : Type := Fin 8 → Bool

namespace V8Info

def xor (a b : V8) : V8 :=
  fun i => Bool.xor (a i) (b i)

def zero : V8 :=
  fun _ => false

/-- A finite V8 subgroup, represented by its carrier predicate. -/
structure Subgroup where
  carrier : V8 → Prop
  zero_mem : carrier zero
  xor_mem : ∀ {a b : V8}, carrier a → carrier b → carrier (xor a b)

def bit (n : Nat) (h : n < 8) : Fin 8 :=
  ⟨n, h⟩

def y7 : Fin 8 := bit 6 (by decide)
def y8 : Fin 8 := bit 7 (by decide)

def single (i : Fin 8) : V8 :=
  fun j => decide (j = i)

def parityMask : V8 :=
  xor (single y7) (single y8)

/-! ## Linear query evaluation -/

def andBit (q x : V8) (i : Fin 8) : Bool :=
  q i && x i

def bxor8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Bool :=
  Bool.xor b0
    (Bool.xor b1
      (Bool.xor b2
        (Bool.xor b3
          (Bool.xor b4
            (Bool.xor b5
              (Bool.xor b6 b7))))))

/-- F2 dot product of a query mask and a V8 state. -/
def evalQuery (q x : V8) : Bool :=
  bxor8
    (andBit q x (bit 0 (by decide)))
    (andBit q x (bit 1 (by decide)))
    (andBit q x (bit 2 (by decide)))
    (andBit q x (bit 3 (by decide)))
    (andBit q x (bit 4 (by decide)))
    (andBit q x (bit 5 (by decide)))
    (andBit q x y7)
    (andBit q x y8)

/-- A query is invariant under a subgroup when every allowed XOR mask preserves
its evaluation on every state. -/
def isInvariant (H : Subgroup) (q : V8) : Prop :=
  ∀ x g : V8, H.carrier g → evalQuery q (xor x g) = evalQuery q x

/-- Orbit of a state under subgroup XOR masks. -/
def orbit (H : Subgroup) (x y : V8) : Prop :=
  ∃ g : V8, H.carrier g ∧ y = xor x g

theorem evalQuery_constant_on_orbit
    {H : Subgroup} {q x y : V8}
    (hq : isInvariant H q) (hy : orbit H x y) :
    evalQuery q y = evalQuery q x := by
  rcases hy with ⟨g, hg, rfl⟩
  exact hq x g hg

/-- Public information-preservation theorem: an invariant query has the same
value at every state in the subgroup orbit of a root. -/
theorem info_preservation
    (q : V8) (H : Subgroup) (root y : V8)
    (hq : isInvariant H q) (hy : orbit H root y) :
    evalQuery q y = evalQuery q root :=
  evalQuery_constant_on_orbit hq hy

/-! ## Concrete Phase 4 masks -/

def timeY7Mask : V8 := single y7
def timeY8Mask : V8 := single y8

/-- The two-coordinate time plane: only y7/y8 may be nonzero. -/
def offTimeZero (g : V8) : Prop :=
  ∀ i : Fin 8, i ≠ y7 → i ≠ y8 → g i = false

def v4TimeCarrier (g : V8) : Prop :=
  offTimeZero g

/-- The full V4 time subgroup on y7/y8 toggles. -/
def v4Time : Subgroup where
  carrier := v4TimeCarrier
  zero_mem := by
    intro i _ _
    rfl
  xor_mem := by
    intro a b ha hb i hi7 hi8
    unfold xor
    rw [ha i hi7 hi8, hb i hi7 hi8]
    rfl

def daoJinCarrier (g : V8) : Prop :=
  offTimeZero g ∧ g y7 = g y8

/-- The `{dao, jin}` subgroup toggles y7 and y8 together. -/
def daoJin : Subgroup where
  carrier := daoJinCarrier
  zero_mem := by
    constructor
    · intro i _ _
      rfl
    · rfl
  xor_mem := by
    intro a b ha hb
    constructor
    · intro i hi7 hi8
      unfold xor
      rw [ha.1 i hi7 hi8, hb.1 i hi7 hi8]
      rfl
    · unfold xor
      rw [ha.2, hb.2]

theorem evalQuery_parityMask_zero :
    evalQuery parityMask zero = false := rfl

theorem evalQuery_parityMask_parityMask :
    evalQuery parityMask parityMask = false := rfl

theorem evalQuery_parityMask (x : V8) :
    evalQuery parityMask x = Bool.xor (x y7) (x y8) := by
  unfold evalQuery bxor8 andBit parityMask xor single y7 y8 bit
  cases x ⟨6, by decide⟩ <;> cases x ⟨7, by decide⟩ <;> rfl

theorem daoJin_preserves_parity :
    isInvariant daoJin parityMask := by
  intro x g hg
  rw [evalQuery_parityMask, evalQuery_parityMask]
  unfold xor
  rw [hg.2]
  cases x y7 <;> cases x y8 <;> cases g y8 <;> rfl

theorem full_v4_time_does_not_preserve_parity :
    ¬ isInvariant v4Time parityMask := by
  intro h
  have hmem : v4Time.carrier timeY7Mask := by
    intro i hi7 _hi8
    unfold timeY7Mask single
    simp [hi7]
  have hflip := h zero timeY7Mask hmem
  rw [evalQuery_parityMask, evalQuery_parityMask] at hflip
  unfold xor zero timeY7Mask single y7 y8 bit at hflip
  contradiction

/-! ## Checklist compatibility names -/

/-- Compatibility alias for the checklist name `{道, 今}`. -/
def dao_jin_subgroup : Subgroup := daoJin

/-- Compatibility alias for the checklist query `y7 ⊕ y8`. -/
def parity_y7_y8 : V8 := parityMask

theorem dao_jin_preserves_parity :
    isInvariant dao_jin_subgroup parity_y7_y8 :=
  daoJin_preserves_parity

theorem V4_does_not_preserve_parity :
    ¬ isInvariant v4Time parity_y7_y8 :=
  full_v4_time_does_not_preserve_parity

/-! ## Phase 8 layered compatibility anchors -/

abbrev LayeredV8 : Type :=
  SSBX.Foundation.Wen.Layered.V4Time.TimeSpace

def layeredEvalQuery :
    LayeredV8 → LayeredV8 → Bool :=
  SSBX.Foundation.Wen.Layered.V4Time.evalQuery

theorem layered_evalQuery_parityMask (x : V8) :
    SSBX.Foundation.Wen.Layered.V4Time.evalQuery
        SSBX.Foundation.Wen.Layered.V4Time.parityMask x =
      evalQuery parityMask x := by
  rw [SSBX.Foundation.Wen.Layered.V4Time.evalQuery_parityMask,
    evalQuery_parityMask]
  rfl

theorem layered_daoJin_preserves_parity :
    SSBX.Foundation.Wen.Layered.BitSpace.isInvariant
      SSBX.Foundation.Wen.Layered.V4Time.daoJin
      (SSBX.Foundation.Wen.Layered.V4Time.evalQuery
        SSBX.Foundation.Wen.Layered.V4Time.parityMask) :=
  SSBX.Foundation.Wen.Layered.V4Time.daoJin_preserves_parity

theorem layered_full_v4_time_does_not_preserve_parity :
    ¬ SSBX.Foundation.Wen.Layered.BitSpace.isInvariant
      SSBX.Foundation.Wen.Layered.V4Time.v4Time
      (SSBX.Foundation.Wen.Layered.V4Time.evalQuery
        SSBX.Foundation.Wen.Layered.V4Time.parityMask) :=
  SSBX.Foundation.Wen.Layered.V4Time.full_v4_time_does_not_preserve_parity

theorem layered_v8info_summary :
    (∀ x : V8,
      SSBX.Foundation.Wen.Layered.V4Time.evalQuery
          SSBX.Foundation.Wen.Layered.V4Time.parityMask x =
        evalQuery parityMask x)
    ∧ SSBX.Foundation.Wen.Layered.BitSpace.isInvariant
      SSBX.Foundation.Wen.Layered.V4Time.daoJin
      (SSBX.Foundation.Wen.Layered.V4Time.evalQuery
        SSBX.Foundation.Wen.Layered.V4Time.parityMask)
    ∧ ¬ SSBX.Foundation.Wen.Layered.BitSpace.isInvariant
      SSBX.Foundation.Wen.Layered.V4Time.v4Time
      (SSBX.Foundation.Wen.Layered.V4Time.evalQuery
        SSBX.Foundation.Wen.Layered.V4Time.parityMask) :=
  ⟨layered_evalQuery_parityMask, layered_daoJin_preserves_parity,
   layered_full_v4_time_does_not_preserve_parity⟩

end V8Info

end SSBX.Foundation.Hierarchy.Operators
