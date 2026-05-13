/-
# Wen.Layered.Runtime.VnRn -- BitVec runtime Vn/Rn facade

Runtime operations are spec-lifted through `toSpec/ofSpec`; raw optimized
BitVec implementations can replace these definitions later behind the same
theorems.
-/

import SSBX.Foundation.Wen.Layered.VnRn
import SSBX.Foundation.Wen.Layered.Runtime.BitSpace

namespace SSBX.Foundation.Wen.Layered.Runtime

/-- Runtime R-layer state space: packed `n`-bit cells. -/
abbrev Rn (n : Nat) : Type := Cell n

/-- Runtime V-layer translation masks: packed `n`-bit cells. -/
abbrev Vn (n : Nat) : Type := Cell n

namespace Vn

def zero {n : Nat} : Vn n := Runtime.zero

def xor {n : Nat} (a b : Vn n) : Vn n := Runtime.xor a b

def act {n : Nat} (g : Vn n) (x : Rn n) : Rn n :=
  Runtime.xor g x

def toSpecV {n : Nat} (g : Vn n) : SSBX.Foundation.Wen.Layered.Vn n :=
  Runtime.toSpec g

def toSpecR {n : Nat} (x : Rn n) : SSBX.Foundation.Wen.Layered.Rn n :=
  Runtime.toSpec x

def ofSpecV {n : Nat} (g : SSBX.Foundation.Wen.Layered.Vn n) : Vn n :=
  Runtime.ofSpec g

def ofSpecR {n : Nat} (x : SSBX.Foundation.Wen.Layered.Rn n) : Rn n :=
  Runtime.ofSpec x

@[simp] theorem toSpecV_ofSpecV {n : Nat}
    (g : SSBX.Foundation.Wen.Layered.Vn n) :
    toSpecV (ofSpecV g) = g := by
  simp [toSpecV, ofSpecV]

@[simp] theorem ofSpecV_toSpecV {n : Nat} (g : Vn n) :
    ofSpecV (toSpecV g) = g := by
  simp [toSpecV, ofSpecV]

@[simp] theorem toSpecR_ofSpecR {n : Nat}
    (x : SSBX.Foundation.Wen.Layered.Rn n) :
    toSpecR (ofSpecR x) = x := by
  simp [toSpecR, ofSpecR]

@[simp] theorem ofSpecR_toSpecR {n : Nat} (x : Rn n) :
    ofSpecR (toSpecR x) = x := by
  simp [toSpecR, ofSpecR]

@[simp] theorem toSpec_zero {n : Nat} :
    toSpecV (zero : Vn n) = SSBX.Foundation.Wen.Layered.Vn.zero := by
  simp [toSpecV, zero, SSBX.Foundation.Wen.Layered.Vn.zero]

@[simp] theorem toSpec_xor {n : Nat} (a b : Vn n) :
    toSpecV (xor a b) =
      SSBX.Foundation.Wen.Layered.Vn.xor (toSpecV a) (toSpecV b) := by
  simp [toSpecV, xor, SSBX.Foundation.Wen.Layered.Vn.xor]

@[simp] theorem toSpec_act {n : Nat} (g : Vn n) (x : Rn n) :
    toSpecR (act g x) =
      SSBX.Foundation.Wen.Layered.Vn.act (toSpecV g) (toSpecR x) := by
  simp [toSpecR, toSpecV, act, SSBX.Foundation.Wen.Layered.Vn.act]

@[simp] theorem act_zero {n : Nat} (x : Rn n) :
    act (zero : Vn n) x = x := by
  apply Runtime.eq_of_toSpec_eq
  change toSpecR (act (zero : Vn n) x) = toSpecR x
  rw [toSpec_act, toSpec_zero]
  exact SSBX.Foundation.Wen.Layered.Vn.act_zero (toSpecR x)

theorem act_xor {n : Nat} (g h : Vn n) (x : Rn n) :
    act (xor g h) x = act g (act h x) := by
  apply Runtime.eq_of_toSpec_eq
  change toSpecR (act (xor g h) x) = toSpecR (act g (act h x))
  rw [toSpec_act, toSpec_act, toSpec_act, toSpec_xor]
  exact SSBX.Foundation.Wen.Layered.Vn.act_mul
    (toSpecV g) (toSpecV h) (toSpecR x)

theorem runtime_vnrn_summary (n : Nat) :
    (∀ g : SSBX.Foundation.Wen.Layered.Vn n, toSpecV (ofSpecV g) = g)
    ∧ (∀ g : Vn n, ofSpecV (toSpecV g) = g)
    ∧ (∀ x : SSBX.Foundation.Wen.Layered.Rn n, toSpecR (ofSpecR x) = x)
    ∧ (∀ x : Rn n, ofSpecR (toSpecR x) = x)
    ∧ toSpecV (zero : Vn n) = SSBX.Foundation.Wen.Layered.Vn.zero
    ∧ (∀ g h : Vn n,
        toSpecV (xor g h) =
          SSBX.Foundation.Wen.Layered.Vn.xor (toSpecV g) (toSpecV h))
    ∧ (∀ g : Vn n, ∀ x : Rn n,
        toSpecR (act g x) =
          SSBX.Foundation.Wen.Layered.Vn.act (toSpecV g) (toSpecR x))
    ∧ (∀ x : Rn n, act (zero : Vn n) x = x)
    ∧ (∀ g h : Vn n, ∀ x : Rn n,
        act (xor g h) x = act g (act h x)) :=
  ⟨toSpecV_ofSpecV, ofSpecV_toSpecV,
   toSpecR_ofSpecR, ofSpecR_toSpecR,
   toSpec_zero,
   toSpec_xor,
   toSpec_act,
   act_zero,
   act_xor⟩

end Vn

end SSBX.Foundation.Wen.Layered.Runtime
