/-
# Operators · V4.Hexagram -- V4 action on R6/R7/R8 carriers

The canonical V4 kernel acts on Hexagram by content complement and frame
reversal.  R7 and R8 lifts preserve their extra coordinates.
-/

import SSBX.Foundation.Bagua.R7
import SSBX.Foundation.Hierarchy.Operators.V4.Temporal

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

def actR7 (g : V4) (c : R7) : R7 :=
  (actHex g c.1, c.2)

def actR8 (g : V4) (c : R8) : R8 :=
  (actHex g c.1, c.2)

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
    ∧ (∀ c : R7, actR7 .zong c = hexZong c)
    ∧ (∀ c : R8, actR8 .cuo c = R8.hexCuo c)
    ∧ (∀ c : R8, actR8 .zong c = R8.hexZong c) :=
  ⟨actHex_dao, actHex_self_inverse, actHex_compose,
   actR7_zong_eq_hexZong, actR8_cuo_eq_hexCuo, actR8_zong_eq_hexZong⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
