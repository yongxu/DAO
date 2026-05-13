/-
# Operators · V4.Hexagram -- V4 action on R6/R7/R8 carriers

The canonical V4 kernel acts on Hexagram by content complement and frame
reversal.  R7 and R8 lifts preserve their extra coordinates.
-/

import SSBX.Foundation.Bagua.R7
import SSBX.Foundation.Hierarchy.Operators.V4.Instances
import SSBX.Foundation.Hierarchy.Operators.V4.Temporal
import Mathlib.Algebra.Group.Action.Defs

namespace SSBX.Foundation.Hierarchy.Operators

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R7
open SSBX.Foundation.Bagua.R8

namespace V4

def actHex : V4 → Hexagram → Hexagram
  | .dao, h => h
  | .cuo, h => Hexagram.complement h
  | .zong, h => Hexagram.reverse h
  | .cuoZong, h => Hexagram.complementReverse h

theorem actHex_dao (h : Hexagram) :
    actHex .dao h = h := rfl

theorem actHex_cuo (h : Hexagram) :
    actHex .cuo h = Hexagram.complement h := rfl

theorem actHex_zong (h : Hexagram) :
    actHex .zong h = Hexagram.reverse h := rfl

theorem actHex_cuoZong (h : Hexagram) :
    actHex .cuoZong h = Hexagram.complementReverse h := rfl

theorem actHex_compose (a b : V4) (h : Hexagram) :
    actHex (compose a b) h = actHex a (actHex b h) := by
  cases a <;> cases b <;>
    cases h with
    | mk y1 y2 y3 y4 y5 y6 =>
        cases y1 <;> cases y2 <;> cases y3 <;>
          cases y4 <;> cases y5 <;> cases y6 <;> rfl

theorem actHex_self_inverse (g : V4) (h : Hexagram) :
    actHex g (actHex g h) = h := by
  rw [← actHex_compose, compose_self, actHex_dao]

theorem actHex_cuo_zong (h : Hexagram) :
    actHex .cuoZong h = actHex .cuo (actHex .zong h) := rfl

instance instSMulHexagram : SMul V4 Hexagram where
  smul := actHex

@[simp] theorem smulHex_eq_actHex (g : V4) (h : Hexagram) :
    g • h = actHex g h := rfl

instance instMulActionHexagram : MulAction V4 Hexagram where
  one_smul := by
    intro h
    change actHex (1 : V4) h = h
    rw [one_eq_dao]
    exact actHex_dao h
  mul_smul := by
    intro a b h
    change actHex (a * b) h = actHex a (actHex b h)
    simpa [mul_eq_compose] using actHex_compose a b h

def actR7 (g : V4) (c : R7) : R7 :=
  (actHex g c.1, c.2)

def actR8 (g : V4) (c : R8) : R8 :=
  (actHex g c.1, c.2)

theorem actR7_dao (c : R7) :
    actR7 .dao c = c := by
  rcases c with ⟨h, yin⟩
  rfl

theorem actR8_dao (c : R8) :
    actR8 .dao c = c := by
  rcases c with ⟨h, shi⟩
  rfl

theorem actR7_compose (a b : V4) (c : R7) :
    actR7 (compose a b) c = actR7 a (actR7 b c) := by
  rcases c with ⟨h, yin⟩
  simp [actR7, actHex_compose]

theorem actR8_compose (a b : V4) (c : R8) :
    actR8 (compose a b) c = actR8 a (actR8 b c) := by
  rcases c with ⟨h, shi⟩
  simp [actR8, actHex_compose]

theorem actR7_self_inverse (g : V4) (c : R7) :
    actR7 g (actR7 g c) = c := by
  rcases c with ⟨h, yin⟩
  simp [actR7, actHex_self_inverse]

theorem actR8_self_inverse (g : V4) (c : R8) :
    actR8 g (actR8 g c) = c := by
  rcases c with ⟨h, shi⟩
  simp [actR8, actHex_self_inverse]

instance instSMulR7 : SMul V4 R7 where
  smul := actR7

@[simp] theorem smulR7_eq_actR7 (g : V4) (c : R7) :
    g • c = actR7 g c := rfl

instance instMulActionR7 : MulAction V4 R7 where
  one_smul := by
    intro c
    change actR7 (1 : V4) c = c
    rw [one_eq_dao]
    exact actR7_dao c
  mul_smul := by
    intro a b c
    change actR7 (a * b) c = actR7 a (actR7 b c)
    simpa [mul_eq_compose] using actR7_compose a b c

instance instSMulR8 : SMul V4 R8 where
  smul := actR8

@[simp] theorem smulR8_eq_actR8 (g : V4) (c : R8) :
    g • c = actR8 g c := rfl

instance instMulActionR8 : MulAction V4 R8 where
  one_smul := by
    intro c
    change actR8 (1 : V4) c = c
    rw [one_eq_dao]
    exact actR8_dao c
  mul_smul := by
    intro a b c
    change actR8 (a * b) c = actR8 a (actR8 b c)
    simpa [mul_eq_compose] using actR8_compose a b c

theorem actR7_zong_eq_hexZong (c : R7) :
    actR7 .zong c = hexZong c := by
  rcases c with ⟨h, yin⟩
  rfl

theorem actR8_cuo_eq_hexCuo (c : R8) :
    actR8 .cuo c = R8.hexCuo c := by
  rcases c with ⟨h, shi⟩
  rfl

theorem actR8_zong_eq_hexZong (c : R8) :
    actR8 .zong c = R8.hexZong c := by
  rcases c with ⟨h, shi⟩
  rfl

theorem v4_hexagram_action_summary :
    (∀ h : Hexagram, actHex .dao h = h)
    ∧ (∀ g h, actHex g (actHex g h) = h)
    ∧ (∀ a b h, actHex (compose a b) h = actHex a (actHex b h))
    ∧ (∀ (a b : V4) (h : Hexagram), (a * b) • h = a • (b • h : Hexagram))
    ∧ (∀ c : R7, actR7 .zong c = hexZong c)
    ∧ (∀ c : R8, actR8 .cuo c = R8.hexCuo c)
    ∧ (∀ c : R8, actR8 .zong c = R8.hexZong c) :=
  ⟨actHex_dao, actHex_self_inverse, actHex_compose,
   fun a b h => mul_smul a b h,
   actR7_zong_eq_hexZong, actR8_cuo_eq_hexCuo, actR8_zong_eq_hexZong⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
