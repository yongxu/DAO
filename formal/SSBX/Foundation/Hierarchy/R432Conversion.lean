/-
# R432Conversion -- direct R4/R3/R2 conversion API

`LiftProject.lean` already provides the consecutive maps
`R₂ ↔ R₃ ↔ R₄`.  This sidecar packages them as a small user-facing API:
projection, lifted reconstruction, and exact split/join roundtrips.
-/
import SSBX.Foundation.Hierarchy.LiftProject

namespace SSBX.Foundation.Hierarchy.R432Conversion

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Hierarchy.LiftProject

/-! ## Direct projections and lifts -/

/-- Direct projection from R₄ to R₂ through the canonical R₄ → R₃ → R₂ path. -/
def projR4toR2 (m : R4) : R2 :=
  projR3toR2 (projR4toR3 m)

/-- Direct lift from R₂ to R₄, carrying the two extension bits explicitly. -/
def liftR2toR4 (s : R2) (y3 y4 : Yao) : R4 :=
  liftR3toR4 (liftR2toR3 s y3) y4

theorem projR4toR2_liftR2toR4 (s : R2) (y3 y4 : Yao) :
    projR4toR2 (liftR2toR4 s y3 y4) = s := by
  simp [projR4toR2, liftR2toR4, proj_lift_id_R3, proj_lift_id_R2]

/-! ## Exact split/join forms -/

/-- R₃ as R₂ plus one extra Yao. -/
structure R3Frame where
  base : R2
  y3 : Yao
  deriving Repr

/-- R₄ as R₂ plus the two extension Yao bits. -/
structure R4Frame where
  base : R2
  y3 : Yao
  y4 : Yao
  deriving Repr

def splitR3 (t : R3) : R3Frame :=
  { base := projR3toR2 t, y3 := t.y3 }

def joinR3 (f : R3Frame) : R3 :=
  liftR2toR3 f.base f.y3

theorem joinR3_splitR3 (t : R3) :
    joinR3 (splitR3 t) = t := by
  apply Trigram.ext <;>
    simp [splitR3, joinR3, projR3toR2, liftR2toR3,
          Trigram.y1_mk, Trigram.y2_mk, Trigram.y3_mk]

theorem splitR3_joinR3 (f : R3Frame) :
    splitR3 (joinR3 f) = f := by
  cases f with
  | mk base y3 =>
      cases base
      rfl

def splitR4 (m : R4) : R4Frame :=
  let t := projR4toR3 m
  { base := projR3toR2 t
    y3 := t.y3
    y4 := zhengToYao2 m.2 }

def joinR4 (f : R4Frame) : R4 :=
  liftR2toR4 f.base f.y3 f.y4

theorem joinR4_splitR4 (m : R4) :
    joinR4 (splitR4 m) = m := by
  rcases m with ⟨b, z⟩
  cases b <;> cases z <;> rfl

theorem splitR4_joinR4 (f : R4Frame) :
    splitR4 (joinR4 f) = f := by
  cases f with
  | mk base y3 y4 =>
      cases base with
      | mk y1 y2 =>
          cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> rfl

/-- R₄ → R₃ → R₂ and R₂ → R₃ → R₄ are mutually controlled by exactly two
extension bits. -/
theorem r4_r3_r2_conversion_summary :
    (∀ m : R4, joinR4 (splitR4 m) = m)
    ∧ (∀ f : R4Frame, splitR4 (joinR4 f) = f)
    ∧ (∀ t : R3, joinR3 (splitR3 t) = t)
    ∧ (∀ f : R3Frame, splitR3 (joinR3 f) = f)
    ∧ (∀ s y3 y4, projR4toR2 (liftR2toR4 s y3 y4) = s) := by
  exact
    ⟨ joinR4_splitR4
    , splitR4_joinR4
    , joinR3_splitR3
    , splitR3_joinR3
    , projR4toR2_liftR2toR4
    ⟩

end SSBX.Foundation.Hierarchy.R432Conversion
