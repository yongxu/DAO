/-
# Wen.RKernel.Word64 -- V4-native 64-word carrier

The real Wen Lisp surface uses 64 words.  The core carrier is not `Fin 64`:
it is three independent V4 coordinates, i.e. `V4^3`.
-/

import SSBX.Foundation.Hierarchy.Operators.V4
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

/-- A 64-word coordinate is three V4 axes. -/
structure Word64 where
  first : V4
  second : V4
  third : V4
  deriving DecidableEq, BEq, Repr

namespace Word64

def ofV4 (first second third : V4) : Word64 :=
  ⟨first, second, third⟩

def origin : Word64 :=
  ⟨.dao, .dao, .dao⟩

def withThird (first second : V4) : List Word64 :=
  V4.all.map fun third => ⟨first, second, third⟩

def withSecond (first : V4) : List Word64 :=
  withThird first .dao ++ withThird first .cuo ++
    withThird first .zong ++ withThird first .cuoZong

def all : List Word64 :=
  withSecond .dao ++ withSecond .cuo ++ withSecond .zong ++ withSecond .cuoZong

theorem all_length : all.length = 64 := by native_decide

theorem all_length_eq_v4_card_cubed :
    all.length = Fintype.card V4 ^ 3 := by native_decide

theorem all_length_eq_four_cubed :
    all.length = 4 ^ 3 := by native_decide

/-- `Word64` is exactly three independent V4 coordinates. -/
def v4TripleEquiv : Word64 ≃ V4 × V4 × V4 where
  toFun := fun w => (w.first, w.second, w.third)
  invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by
    intro w
    cases w
    rfl
  right_inv := by
    intro p
    rcases p with ⟨a, b, c⟩
    rfl

instance instFintype : Fintype Word64 where
  elems := all.toFinset
  complete := by
    intro word
    cases word with
    | mk first second third =>
        cases first <;> cases second <;> cases third <;> native_decide

theorem card_eq_v4_card_cubed :
    Fintype.card Word64 = Fintype.card V4 ^ 3 := by native_decide

theorem card_eq_four_cubed :
    Fintype.card Word64 = 4 ^ 3 := by native_decide

theorem card_eq_64 :
    Fintype.card Word64 = 64 := by native_decide

def compose (a b : Word64) : Word64 :=
  ⟨V4.compose a.first b.first,
    V4.compose a.second b.second,
    V4.compose a.third b.third⟩

@[simp] theorem compose_origin_left (w : Word64) :
    compose origin w = w := by
  cases w
  simp [compose, origin, V4.compose_dao_left]

@[simp] theorem compose_origin_right (w : Word64) :
    compose w origin = w := by
  cases w
  simp [compose, origin, V4.compose_dao_right]

@[simp] theorem compose_self (w : Word64) :
    compose w w = origin := by
  cases w
  simp [compose, origin, V4.compose_self]

theorem compose_comm (a b : Word64) :
    compose a b = compose b a := by
  cases a
  cases b
  simp [compose, V4.compose_comm]

theorem compose_assoc (a b c : Word64) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a
  cases b
  cases c
  simp [compose, V4.compose_assoc]

def qian : Word64 := origin

def kun : Word64 := ⟨.cuoZong, .cuoZong, .cuoZong⟩

def complete : Word64 := ⟨.zong, .zong, .zong⟩

def incomplete : Word64 := ⟨.cuo, .cuo, .cuo⟩

theorem word64_summary :
    all.length = 64
    ∧ all.length = Fintype.card V4 ^ 3
    ∧ Fintype.card Word64 = 64
    ∧ (∀ w : Word64, compose origin w = w)
    ∧ (∀ w : Word64, compose w origin = w)
    ∧ (∀ w : Word64, compose w w = origin)
    ∧ (∀ a b : Word64, compose a b = compose b a)
    ∧ (∀ a b c : Word64, compose (compose a b) c = compose a (compose b c)) :=
  ⟨all_length, all_length_eq_v4_card_cubed, card_eq_64,
    compose_origin_left, compose_origin_right, compose_self,
    compose_comm, compose_assoc⟩

/-! ## § Bridge to R 6 — Word64 ≃ R 6

Per `wen-substrate.md` v1.4 §3.7.8 (distinction monism), the R-family is the
**one mathematical core**.  `Word64` = `V4³` is mathematically
`R 2 × R 2 × R 2 ≅ R 6 = Fin 6 → Bool`.  This section proves the equivalence
explicitly.  Coordinates 0,1 are the `first` axis; 2,3 the `second` axis;
4,5 the `third` axis. -/

open SSBX.Foundation.R in
/-- Project Word64 to R 6 via V4 ≃ R 2 on each of the three V4 coordinates. -/
def toR6 (w : Word64) : R 6 := fun i =>
  if h2 : i.val < 2 then V4.toR2 w.first ⟨i.val, h2⟩
  else if h4 : i.val < 4 then V4.toR2 w.second ⟨i.val - 2, by omega⟩
  else V4.toR2 w.third ⟨i.val - 4, by omega⟩

open SSBX.Foundation.R in
/-- Lift R 6 to Word64 via R 2 ≃ V4 on the (0,1), (2,3), (4,5) blocks. -/
def ofR6 (v : R 6) : Word64 :=
  ⟨V4.ofR2 (fun i => v ⟨i.val, by omega⟩),
   V4.ofR2 (fun i => v ⟨i.val + 2, by omega⟩),
   V4.ofR2 (fun i => v ⟨i.val + 4, by omega⟩)⟩

theorem ofR6_toR6 (w : Word64) : ofR6 (toR6 w) = w := by
  obtain ⟨a, b, c⟩ := w
  -- prove each of the three V4.ofR2 ... = corresponding axis
  have hfst : V4.ofR2 (fun i => toR6 ⟨a, b, c⟩ ⟨i.val, by omega⟩) = a := by
    have heq : (fun i : Fin 2 => toR6 ⟨a, b, c⟩ ⟨i.val, by omega⟩) = V4.toR2 a := by
      funext i
      have hi : i.val < 2 := i.isLt
      simp [toR6, hi]
    rw [heq, V4.ofR2_toR2]
  have hsnd : V4.ofR2 (fun i => toR6 ⟨a, b, c⟩ ⟨i.val + 2, by omega⟩) = b := by
    have heq : (fun i : Fin 2 => toR6 ⟨a, b, c⟩ ⟨i.val + 2, by omega⟩)
                  = V4.toR2 b := by
      funext i
      have h2_neg : ¬ (i.val + 2 < 2) := by omega
      have h4_pos : i.val + 2 < 4 := by have := i.isLt; omega
      simp only [toR6, h2_neg, ↓reduceDIte, h4_pos]
      congr
    rw [heq, V4.ofR2_toR2]
  have hthr : V4.ofR2 (fun i => toR6 ⟨a, b, c⟩ ⟨i.val + 4, by omega⟩) = c := by
    have heq : (fun i : Fin 2 => toR6 ⟨a, b, c⟩ ⟨i.val + 4, by omega⟩)
                  = V4.toR2 c := by
      funext i
      have h2_neg : ¬ (i.val + 4 < 2) := by omega
      have h4_neg : ¬ (i.val + 4 < 4) := by omega
      simp only [toR6, h2_neg, ↓reduceDIte, h4_neg]
      congr
    rw [heq, V4.ofR2_toR2]
  show Word64.mk _ _ _ = ⟨a, b, c⟩
  rw [hfst, hsnd, hthr]

open SSBX.Foundation.R in
theorem toR6_ofR6 (v : R 6) : toR6 (ofR6 v) = v := by
  funext i
  simp only [toR6, ofR6]
  split_ifs with h2 h4
  · -- i.val < 2
    have hroundtrip := V4.toR2_ofR2 (fun j : Fin 2 => v ⟨j.val, by omega⟩)
    have hi : V4.toR2 (V4.ofR2 (fun j : Fin 2 => v ⟨j.val, by omega⟩))
                ⟨i.val, h2⟩ = v ⟨i.val, by omega⟩ := by
      rw [hroundtrip]
    convert hi using 2
  · -- 2 ≤ i.val < 4
    have hi2 : i.val - 2 < 2 := by omega
    have hroundtrip := V4.toR2_ofR2 (fun j : Fin 2 => v ⟨j.val + 2, by omega⟩)
    have hi : V4.toR2 (V4.ofR2 (fun j : Fin 2 => v ⟨j.val + 2, by omega⟩))
                ⟨i.val - 2, hi2⟩ = v ⟨(i.val - 2) + 2, by omega⟩ := by
      rw [hroundtrip]
    have hsub : (i.val - 2) + 2 = i.val := by omega
    rw [hi]
    congr 1
    apply Fin.ext
    exact hsub
  · -- i.val ≥ 4
    have hi4 : i.val - 4 < 2 := by have := i.isLt; omega
    have hroundtrip := V4.toR2_ofR2 (fun j : Fin 2 => v ⟨j.val + 4, by omega⟩)
    have hi : V4.toR2 (V4.ofR2 (fun j : Fin 2 => v ⟨j.val + 4, by omega⟩))
                ⟨i.val - 4, hi4⟩ = v ⟨(i.val - 4) + 4, by omega⟩ := by
      rw [hroundtrip]
    have hsub : (i.val - 4) + 4 = i.val := by omega
    rw [hi]
    congr 1
    apply Fin.ext
    exact hsub

open SSBX.Foundation.R in
/-- `Word64 ≃ R 6` — the R-family canonical reading at level 6.
    Per `wen-substrate.md` v1.4 §3.7.8 distinction monism. -/
def equivR6 : Word64 ≃ R 6 where
  toFun := toR6
  invFun := ofR6
  left_inv := ofR6_toR6
  right_inv := toR6_ofR6

end Word64

end SSBX.Foundation.Wen.RKernel
