/-
# Stream Cell256 carrier

`Stream' Cell256` is the concrete coalgebra carrier for trajectories.
-/
import Mathlib.Data.Stream.Init
import SSBX.Foundation.Squaring.V4Tensor

namespace SSBX.Foundation.Squaring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256

namespace StreamCarrier

abbrev TrajCell : Type := Stream' Cell256

def step (s : TrajCell) : Cell256 × TrajCell := (s.head, s.tail)

theorem step_cons (c : Cell256) (s : TrajCell) : step (Stream'.cons c s) = (c, s) := rfl

def unfold {X : Type} (f : X → Cell256 × X) : X → TrajCell :=
  Stream'.corec' f

theorem unfold_head {X : Type} (f : X → Cell256 × X) (x : X) :
    (unfold f x).head = (f x).1 := rfl

theorem unfold_tail {X : Type} (f : X → Cell256 × X) (x : X) :
    (unfold f x).tail = unfold f (f x).2 := by
  rw [unfold, Stream'.corec'_eq]
  rfl

theorem unfold_step {X : Type} (f : X → Cell256 × X) (x : X) :
    step (unfold f x) = ((f x).1, unfold f (f x).2) := by
  simp [step, unfold_head, unfold_tail]

theorem bisim_eq (R : TrajCell → TrajCell → Prop)
    (h : Stream'.IsBisimulation R) {s t : TrajCell} (hr : R s t) : s = t :=
  Stream'.eq_of_bisim R h hr

def alwaysReturn (c : Cell256) : TrajCell := Stream'.const c

theorem alwaysReturn_head (c : Cell256) : (alwaysReturn c).head = c := rfl

theorem alwaysReturn_tail (c : Cell256) : (alwaysReturn c).tail = alwaysReturn c := by
  exact Stream'.tail_const c

/-- A periodic trajectory cycling through the Shi V₄ states at fixed qian. -/
def shiCycle : TrajCell :=
  unfold (fun s : Shi => ((Hexagram.qian, s), Shi.cuo s)) Shi.dao

theorem shiCycle_head : shiCycle.head = (Hexagram.qian, Shi.dao) := rfl

theorem stream_carrier_summary :
    (∀ (c : Cell256) (s : TrajCell), step (Stream'.cons c s) = (c, s))
    ∧ (∀ (X : Type) (f : X → Cell256 × X) (x : X), (unfold f x).head = (f x).1)
    ∧ (∀ (X : Type) (f : X → Cell256 × X) (x : X),
        (unfold f x).tail = unfold f (f x).2)
    ∧ (∀ (R : TrajCell → TrajCell → Prop) (_h : Stream'.IsBisimulation R)
        (s t : TrajCell), R s t → s = t)
    ∧ (∀ c : Cell256, (alwaysReturn c).head = c)
    ∧ (∀ c : Cell256, (alwaysReturn c).tail = alwaysReturn c)
    ∧ shiCycle.head = (Hexagram.qian, Shi.dao) :=
  ⟨step_cons,
   fun _ f x => unfold_head f x,
   fun _ f x => unfold_tail f x,
   fun R h s t hr => bisim_eq R h (s := s) (t := t) hr,
   alwaysReturn_head,
   alwaysReturn_tail,
   shiCycle_head⟩

end StreamCarrier

end SSBX.Foundation.Squaring
