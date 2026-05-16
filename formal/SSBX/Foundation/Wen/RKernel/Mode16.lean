/-
# Wen.RKernel.Mode16 -- the sixteen V4² action modes

`Mode16` is the action/control layer above state carriers.  It is not a new
cell carrier: it is `V4 x V4`, interpreted later as word-action plus temporal
control.
-/

import SSBX.Foundation.Hierarchy.Operators.V4

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

/-- The sixteen basic action/control structures: one V4 for the word action,
one V4 for the temporal/control action. -/
structure Mode16 where
  word : V4
  temporal : V4
  deriving DecidableEq, BEq, Repr

namespace Mode16

def identity : Mode16 := ⟨.dao, .dao⟩

def pureWord (g : V4) : Mode16 := ⟨g, .dao⟩

def pureTemporal (g : V4) : Mode16 := ⟨.dao, g⟩

def all : List Mode16 :=
  V4.all.flatMap fun word => V4.all.map fun temporal => ⟨word, temporal⟩

theorem all_length : all.length = 16 := by
  native_decide

def compose (a b : Mode16) : Mode16 :=
  ⟨V4.compose a.word b.word, V4.compose a.temporal b.temporal⟩

@[simp] theorem compose_identity_left (m : Mode16) :
    compose identity m = m := by
  cases m
  simp [compose, identity, V4.compose_dao_left]

@[simp] theorem compose_identity_right (m : Mode16) :
    compose m identity = m := by
  cases m
  simp [compose, identity, V4.compose_dao_right]

@[simp] theorem compose_self (m : Mode16) :
    compose m m = identity := by
  cases m
  simp [compose, identity, V4.compose_self]

theorem compose_comm (a b : Mode16) :
    compose a b = compose b a := by
  cases a
  cases b
  simp [compose, V4.compose_comm]

theorem compose_assoc (a b c : Mode16) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a
  cases b
  cases c
  simp [compose, V4.compose_assoc]

def compound : Mode16 := ⟨.cuoZong, .cuoZong⟩

theorem mode16_summary :
    all.length = 16
    ∧ (∀ m : Mode16, compose identity m = m)
    ∧ (∀ m : Mode16, compose m identity = m)
    ∧ (∀ m : Mode16, compose m m = identity)
    ∧ (∀ a b : Mode16, compose a b = compose b a)
    ∧ (∀ a b c : Mode16, compose (compose a b) c = compose a (compose b c)) :=
  ⟨all_length, compose_identity_left, compose_identity_right, compose_self,
    compose_comm, compose_assoc⟩

/-! ## § Bridge to R 4 — Mode16 ≃ R 4

Per `wen-substrate.md` v1.4 §3.7.8 (distinction monism), the R-family is the
**one mathematical core**.  `Mode16` = `V4 × V4` is mathematically
`R 2 × R 2 ≅ R 4 = Fin 4 → Bool`, the algebraic-class realisation at level 4
of the R-tower.  This section proves the equivalence explicitly. -/

open SSBX.Foundation.R in
/-- Project Mode16 to R 4 via V4 ≃ R 2 on each coordinate.
    Coordinates 0,1 are the word axis; coordinates 2,3 are the temporal axis. -/
def toR4 (m : Mode16) : R 4 := fun i =>
  if h : i.val < 2 then V4.toR2 m.word ⟨i.val, h⟩
  else V4.toR2 m.temporal ⟨i.val - 2, by omega⟩

open SSBX.Foundation.R in
/-- Lift R 4 to Mode16 via R 2 ≃ V4 on the (0,1) and (2,3) halves. -/
def ofR4 (v : R 4) : Mode16 :=
  ⟨V4.ofR2 (fun i => v ⟨i.val, by omega⟩),
   V4.ofR2 (fun i => v ⟨i.val + 2, by omega⟩)⟩

theorem ofR4_toR4 (m : Mode16) : ofR4 (toR4 m) = m := by
  obtain ⟨w, t⟩ := m
  simp only [ofR4, toR4]
  congr 1
  · -- word: V4.ofR2 (fun i => toR2 w ⟨i.val, _⟩) = w
    have hword : (fun i : Fin 2 =>
        (if h : (⟨i.val, by omega⟩ : Fin 4).val < 2 then
            V4.toR2 w ⟨(⟨i.val, by omega⟩ : Fin 4).val, h⟩
          else
            V4.toR2 t ⟨(⟨i.val, by omega⟩ : Fin 4).val - 2, by omega⟩))
        = V4.toR2 w := by
      funext i
      have hi : i.val < 2 := i.isLt
      simp [hi]
    rw [hword, V4.ofR2_toR2]
  · -- temporal: V4.ofR2 (fun i => toR2 t ⟨(i.val+2)-2, _⟩) = t
    have htemp : (fun i : Fin 2 =>
        (if h : (⟨i.val + 2, by omega⟩ : Fin 4).val < 2 then
            V4.toR2 w ⟨(⟨i.val + 2, by omega⟩ : Fin 4).val, h⟩
          else
            V4.toR2 t ⟨(⟨i.val + 2, by omega⟩ : Fin 4).val - 2, by omega⟩))
        = V4.toR2 t := by
      funext i
      have hi : ¬ (i.val + 2 < 2) := by omega
      simp [hi]
    rw [htemp, V4.ofR2_toR2]

open SSBX.Foundation.R in
theorem toR4_ofR4 (v : R 4) : toR4 (ofR4 v) = v := by
  funext i
  simp only [toR4, ofR4]
  by_cases h : i.val < 2
  · simp only [h, dif_pos]
    have := V4.toR2_ofR2 (fun j : Fin 2 => v ⟨j.val, by omega⟩)
    have hi : V4.toR2 (V4.ofR2 (fun j : Fin 2 => v ⟨j.val, by omega⟩))
                ⟨i.val, h⟩ = v ⟨i.val, by omega⟩ := by
      rw [this]
    convert hi using 2
  · simp only [h, dif_neg, not_false_eq_true]
    have hi2 : i.val - 2 < 2 := by omega
    have := V4.toR2_ofR2 (fun j : Fin 2 => v ⟨j.val + 2, by omega⟩)
    have hi : V4.toR2 (V4.ofR2 (fun j : Fin 2 => v ⟨j.val + 2, by omega⟩))
                ⟨i.val - 2, hi2⟩ = v ⟨(i.val - 2) + 2, by omega⟩ := by
      rw [this]
    have hsub : (i.val - 2) + 2 = i.val := by omega
    rw [hi]
    congr 1
    apply Fin.ext
    exact hsub

open SSBX.Foundation.R in
/-- `Mode16 ≃ R 4` — the R-family canonical reading at level 4.
    Per `wen-substrate.md` v1.4 §3.7.8 distinction monism. -/
def equivR4 : Mode16 ≃ R 4 where
  toFun := toR4
  invFun := ofR4
  left_inv := ofR4_toR4
  right_inv := toR4_ofR4

end Mode16

end SSBX.Foundation.Wen.RKernel
