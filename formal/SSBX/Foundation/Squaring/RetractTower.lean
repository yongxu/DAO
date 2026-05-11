/-
# Retract tower inside L₁

This file lifts the existing R₈ carrier into the first squaring layer and
records the generic product-retract pattern used by later layers.
-/
import SSBX.Foundation.Squaring.L1
import SSBX.Foundation.Hierarchy.LiftProject

namespace SSBX.Foundation.Squaring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Hierarchy.LiftProject

namespace RetractTower

def liftR8toL1 : R8 → L1 := L1.diag
def projL1toR8 : L1 → R8 := L1.proj1

theorem proj_lift_id_L1 (c : R8) : projL1toR8 (liftR8toL1 c) = c := rfl

def projL1toR7 (l : L1) : R7 := projR8toR7 (projL1toR8 l)
def projL1toR6 (l : L1) : R6 := projR7toR6 (projL1toR7 l)
def projL1toR5 (l : L1) : R5 := projR6toR5 (projL1toR6 l)
def projL1toR4 (l : L1) : R4 := projR5toR4 (projL1toR5 l)
def projL1toR3 (l : L1) : R3 := projR4toR3 (projL1toR4 l)
def projL1toR2 (l : L1) : R2 := projR3toR2 (projL1toR3 l)
def projL1toR1 (l : L1) : R1 := projR2toR1 (projL1toR2 l)
def projL1toR0 (l : L1) : R0 := projR1toR0 (projL1toR1 l)

def squareRetract {α β : Type} (lift : α → β) : α × α → β × β
  | (a₁, a₂) => (lift a₁, lift a₂)

def squareProj {α β : Type} (proj : β → α) : β × β → α × α
  | (b₁, b₂) => (proj b₁, proj b₂)

theorem squareProj_squareRetract {α β : Type}
    (lift : α → β) (proj : β → α) (h : ∀ a, proj (lift a) = a) :
    ∀ aa : α × α, squareProj proj (squareRetract lift aa) = aa := by
  intro aa
  rcases aa with ⟨a₁, a₂⟩
  simp [squareRetract, squareProj, h]

def liftR7toL1 (c : R7) : L1 := liftR8toL1 (liftR7toR8 c false)
def liftR6toL1 (h : R6) : L1 := liftR7toL1 (liftR6toR7 h false)
def liftR5toL1 (w : R5) : L1 := liftR6toL1 (liftR5toR6 w Yao.yang)
def liftR4toL1 (m : R4) : L1 := liftR5toL1 (liftR4toR5 m false)
def liftR3toL1 (t : R3) : L1 := liftR4toL1 (liftR3toR4 t Yao.yang)
def liftR2toL1 (s : R2) : L1 := liftR3toL1 (liftR2toR3 s Yao.yang)
def liftR1toL1 (y : R1) : L1 := liftR2toL1 (liftR1toR2 y Yao.yang)
def liftR0toL1 (r : R0) : L1 := liftR1toL1 (liftR0toR1 r Yao.yang)

theorem proj_liftR0toL1 (r : R0) : projL1toR0 (liftR0toL1 r) = r := by
  simp [projL1toR0, projL1toR1, projL1toR2, projL1toR3, projL1toR4, projL1toR5,
    projL1toR6, projL1toR7, projL1toR8, liftR0toL1, liftR1toL1, liftR2toL1,
    liftR3toL1, liftR4toL1, liftR5toL1, liftR6toL1, liftR7toL1, liftR8toL1,
    L1.diag, L1.proj1, proj_lift_id_R7, proj_lift_id_R6, proj_lift_id_R5, proj_lift_id_R4,
    proj_lift_id_R3, proj_lift_id_R2, proj_lift_id_R1]

theorem proj_liftR1toL1 (y : R1) : projL1toR1 (liftR1toL1 y) = y := by
  simp [projL1toR1, projL1toR2, projL1toR3, projL1toR4, projL1toR5,
    projL1toR6, projL1toR7, projL1toR8, liftR1toL1, liftR2toL1,
    liftR3toL1, liftR4toL1, liftR5toL1, liftR6toL1, liftR7toL1, liftR8toL1,
    L1.diag, L1.proj1, proj_lift_id_R7, proj_lift_id_R6, proj_lift_id_R5, proj_lift_id_R4,
    proj_lift_id_R3, proj_lift_id_R2, proj_lift_id_R1]

theorem proj_liftR2toL1 (s : R2) : projL1toR2 (liftR2toL1 s) = s := by
  simp [projL1toR2, projL1toR3, projL1toR4, projL1toR5, projL1toR6, projL1toR7,
    projL1toR8, liftR2toL1, liftR3toL1, liftR4toL1, liftR5toL1, liftR6toL1,
    liftR7toL1, liftR8toL1, L1.diag, L1.proj1, proj_lift_id_R7, proj_lift_id_R6,
    proj_lift_id_R5, proj_lift_id_R4, proj_lift_id_R3, proj_lift_id_R2]

theorem proj_liftR3toL1 (t : R3) : projL1toR3 (liftR3toL1 t) = t := by
  simp [projL1toR3, projL1toR4, projL1toR5, projL1toR6, projL1toR7, projL1toR8,
    liftR3toL1, liftR4toL1, liftR5toL1, liftR6toL1, liftR7toL1, liftR8toL1,
    L1.diag, L1.proj1, proj_lift_id_R7, proj_lift_id_R6, proj_lift_id_R5, proj_lift_id_R4,
    proj_lift_id_R3]

theorem proj_liftR4toL1 (m : R4) : projL1toR4 (liftR4toL1 m) = m := by
  simp [projL1toR4, projL1toR5, projL1toR6, projL1toR7, projL1toR8,
    liftR4toL1, liftR5toL1, liftR6toL1, liftR7toL1, liftR8toL1, L1.diag, L1.proj1,
    proj_lift_id_R7, proj_lift_id_R6, proj_lift_id_R5, proj_lift_id_R4]

theorem proj_liftR5toL1 (w : R5) : projL1toR5 (liftR5toL1 w) = w := by
  simp [projL1toR5, projL1toR6, projL1toR7, projL1toR8, liftR5toL1, liftR6toL1,
    liftR7toL1, liftR8toL1, L1.diag, L1.proj1, proj_lift_id_R7, proj_lift_id_R6,
    proj_lift_id_R5]

theorem proj_liftR6toL1 (h : R6) : projL1toR6 (liftR6toL1 h) = h := rfl

theorem proj_liftR7toL1 (c : R7) : projL1toR7 (liftR7toL1 c) = c := by
  exact proj_lift_id_R7 c false

theorem retract_tower_summary :
    (∀ c : R8, projL1toR8 (liftR8toL1 c) = c)
    ∧ (∀ aa : R8 × R8,
        squareProj projL1toR8 (squareRetract liftR8toL1 aa) = aa)
    ∧ (∀ r : R0, projL1toR0 (liftR0toL1 r) = r)
    ∧ (∀ y : R1, projL1toR1 (liftR1toL1 y) = y)
    ∧ (∀ s : R2, projL1toR2 (liftR2toL1 s) = s)
    ∧ (∀ t : R3, projL1toR3 (liftR3toL1 t) = t)
    ∧ (∀ m : R4, projL1toR4 (liftR4toL1 m) = m)
    ∧ (∀ w : R5, projL1toR5 (liftR5toL1 w) = w)
    ∧ (∀ h : R6, projL1toR6 (liftR6toL1 h) = h)
    ∧ (∀ c : R7, projL1toR7 (liftR7toL1 c) = c) :=
  ⟨proj_lift_id_L1,
   squareProj_squareRetract liftR8toL1 projL1toR8 proj_lift_id_L1,
   proj_liftR0toL1,
   proj_liftR1toL1,
   proj_liftR2toL1,
   proj_liftR3toL1,
   proj_liftR4toL1,
   proj_liftR5toL1,
   proj_liftR6toL1,
   proj_liftR7toL1⟩

end RetractTower

end SSBX.Foundation.Squaring
