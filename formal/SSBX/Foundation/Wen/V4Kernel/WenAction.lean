/-
# Wen.V4Kernel.WenAction -- Mode16 actions on Word64 and R8 views

The action layer sits above carriers.  It acts on `Word64 = V4^3` and on the
current R8 implementation through the existing `Word64 ≃ Hexagram` and
`V4 ≃ TemporalCoordinate` bridges.
-/

import SSBX.Foundation.Wen.V4Kernel.Mode16
import SSBX.Foundation.Wen.Layered.Bridges.Word64

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8

namespace Mode16

/-- Uniform word action: one V4 mode acts on each of the three V4 coordinates
of a 64-word state. -/
def actWord (mode : Mode16) (word : Word64) : Word64 :=
  ⟨V4.compose mode.word word.first,
    V4.compose mode.word word.second,
    V4.compose mode.word word.third⟩

def actTemporal (mode : Mode16) (temporal : V4) : V4 :=
  V4.compose mode.temporal temporal

/-- R8 as the kernel wants to read it: a 64-word coordinate plus one V4
temporal coordinate. -/
structure R8View where
  word : Word64
  temporal : V4
  deriving DecidableEq, BEq, Repr

def viewOfR8 (cell : R8) : R8View :=
  ⟨SSBX.Foundation.Wen.Layered.Bridges.Word64.ofHexagram cell.1,
    V4.ofTemporal cell.2⟩

def r8OfView (view : R8View) : R8 :=
  (SSBX.Foundation.Wen.Layered.Bridges.Word64.toHexagram view.word,
    V4.toTemporal view.temporal)

@[simp] theorem r8OfView_viewOfR8 (cell : R8) :
    r8OfView (viewOfR8 cell) = cell := by
  rcases cell with ⟨h, temporal⟩
  simp [r8OfView, viewOfR8, V4.toTemporal_ofTemporal]

@[simp] theorem viewOfR8_r8OfView (view : R8View) :
    viewOfR8 (r8OfView view) = view := by
  cases view with
  | mk word temporal =>
      simp [viewOfR8, r8OfView, V4.ofTemporal_toTemporal]

def actView (mode : Mode16) (view : R8View) : R8View :=
  ⟨actWord mode view.word, actTemporal mode view.temporal⟩

def actR8 (mode : Mode16) (cell : R8) : R8 :=
  r8OfView (actView mode (viewOfR8 cell))

@[simp] theorem actWord_identity (word : Word64) :
    actWord identity word = word := by
  cases word
  simp [actWord, identity, V4.compose_dao_left]

@[simp] theorem actTemporal_identity (temporal : V4) :
    actTemporal identity temporal = temporal := by
  simp [actTemporal, identity, V4.compose_dao_left]

@[simp] theorem actView_identity (view : R8View) :
    actView identity view = view := by
  cases view
  simp [actView]

theorem actWord_compose (a b : Mode16) (word : Word64) :
    actWord (compose a b) word = actWord a (actWord b word) := by
  cases a
  cases b
  cases word
  simp [actWord, compose, V4.compose_assoc]

theorem actTemporal_compose (a b : Mode16) (temporal : V4) :
    actTemporal (compose a b) temporal = actTemporal a (actTemporal b temporal) := by
  cases a
  cases b
  simp [actTemporal, compose, V4.compose_assoc]

theorem actView_compose (a b : Mode16) (view : R8View) :
    actView (compose a b) view = actView a (actView b view) := by
  cases view
  simp [actView, actWord_compose, actTemporal_compose]

@[simp] theorem actWord_self_inverse (mode : Mode16) (word : Word64) :
    actWord mode (actWord mode word) = word := by
  rw [← actWord_compose, compose_self, actWord_identity]

@[simp] theorem actTemporal_self_inverse (mode : Mode16) (temporal : V4) :
    actTemporal mode (actTemporal mode temporal) = temporal := by
  rw [← actTemporal_compose, compose_self, actTemporal_identity]

@[simp] theorem actView_self_inverse (mode : Mode16) (view : R8View) :
    actView mode (actView mode view) = view := by
  rw [← actView_compose, compose_self, actView_identity]

theorem actR8_self_inverse (mode : Mode16) (cell : R8) :
    actR8 mode (actR8 mode cell) = cell := by
  simp [actR8, actView_self_inverse]

def sampleView : R8View :=
  ⟨Word64.qian, .dao⟩

theorem compound_sampleView :
    actView compound sampleView = ⟨Word64.kun, .cuoZong⟩ := by
  rfl

theorem wen_action_summary :
    (∀ word : Word64, actWord identity word = word)
    ∧ (∀ mode word, actWord mode (actWord mode word) = word)
    ∧ (∀ mode view, actView mode (actView mode view) = view)
    ∧ (∀ mode cell, actR8 mode (actR8 mode cell) = cell)
    ∧ actView compound sampleView = ⟨Word64.kun, .cuoZong⟩ :=
  ⟨actWord_identity, actWord_self_inverse, actView_self_inverse,
   actR8_self_inverse, compound_sampleView⟩

end Mode16

end SSBX.Foundation.Wen.V4Kernel
