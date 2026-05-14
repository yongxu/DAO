/-
# Foundation.R8.Dynamics — `Stream' (R 8)` coalgebra for trajectories

Adapted from `Foundation/Squaring/StreamCarrier.lean`, restated for the
parametric `R 8` type (and stripped of V₄ / `Shi.complement`-specific
content).  Provides the streaming/coalgebra primitives needed for
`R 8`-trajectory analysis (used by the Behavior judgment, §11 of
`r8.md`).

## What is here

* `Trajectory` = `Stream' (R 8)` — the type of `R 8`-trajectories.
* `step` — extract head + tail.
* `unfold` — corecursive trajectory construction from a state-transition
  function.
* `bisimEq` — bisimulation principle (re-export of `Stream'.eq_of_bisim`).
* `alwaysConst c` — the constant-`c` trajectory.

## Doctrinal anchor

* `r8.md` v0.2 §11.1 (behavior = trajectory),
  §11.4 (behavior metrics, including `behavior_visited`).
-/

import SSBX.Foundation.R.Basic
import Mathlib.Data.Stream.Init

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 The trajectory type -/

/-- An `R 8`-trajectory: an infinite stream of `R 8`-states. -/
abbrev Trajectory : Type := Stream' (R 8)

/-! ## § 2 Step (head + tail) -/

/-- One trajectory step: extract the current state and the remaining
    trajectory. -/
def step (s : Trajectory) : R 8 × Trajectory := (s.head, s.tail)

/-- `step` on a cons recovers `(c, s)`. -/
theorem step_cons (c : R 8) (s : Trajectory) :
    step (Stream'.cons c s) = (c, s) := rfl

/-! ## § 3 Corecursive construction -/

/-- Unfold a state-transition `f : X → R 8 × X` into a trajectory. -/
def unfold {X : Type} (f : X → R 8 × X) : X → Trajectory :=
  Stream'.corec' f

theorem unfold_head {X : Type} (f : X → R 8 × X) (x : X) :
    (unfold f x).head = (f x).1 := rfl

theorem unfold_tail {X : Type} (f : X → R 8 × X) (x : X) :
    (unfold f x).tail = unfold f (f x).2 := by
  rw [unfold, Stream'.corec'_eq]
  rfl

theorem unfold_step {X : Type} (f : X → R 8 × X) (x : X) :
    step (unfold f x) = ((f x).1, unfold f (f x).2) := by
  simp [step, unfold_head, unfold_tail]

/-! ## § 4 Bisimulation principle -/

/-- Two trajectories that are related by a bisimulation are equal. -/
theorem bisimEq (R_rel : Trajectory → Trajectory → Prop)
    (h : Stream'.IsBisimulation R_rel) {s t : Trajectory}
    (hr : R_rel s t) : s = t :=
  Stream'.eq_of_bisim R_rel h hr

/-! ## § 5 Constant trajectories -/

/-- The constant-`c` trajectory: every state is `c`. -/
def alwaysConst (c : R 8) : Trajectory := Stream'.const c

theorem alwaysConst_head (c : R 8) : (alwaysConst c).head = c := rfl

theorem alwaysConst_tail (c : R 8) : (alwaysConst c).tail = alwaysConst c :=
  Stream'.tail_const c

/-! ## § 6 The trajectory from an endomorphism -/

/-- The trajectory of `w₀` under the endomorphism `f : R 8 → R 8`. -/
def fromEndo (f : R 8 → R 8) (w₀ : R 8) : Trajectory :=
  unfold (fun w : R 8 => (w, f w)) w₀

theorem fromEndo_head (f : R 8 → R 8) (w₀ : R 8) :
    (fromEndo f w₀).head = w₀ := rfl

theorem fromEndo_tail (f : R 8 → R 8) (w₀ : R 8) :
    (fromEndo f w₀).tail = fromEndo f (f w₀) := by
  unfold fromEndo
  rw [unfold_tail]

/-! ## § 7 Bundled summary for downstream consumers -/

/-- Summary of the stream-coalgebra primitives for `R 8`-trajectories.
    This is a convenience bundle for downstream usage (kept analogous
    to the `stream_carrier_summary` of the old V4-flavoured
    `StreamCarrier.lean`, but without any V₄-by-name specifics). -/
theorem dynamics_summary :
    (∀ (c : R 8) (s : Trajectory), step (Stream'.cons c s) = (c, s))
    ∧ (∀ (X : Type) (f : X → R 8 × X) (x : X), (unfold f x).head = (f x).1)
    ∧ (∀ (X : Type) (f : X → R 8 × X) (x : X),
        (unfold f x).tail = unfold f (f x).2)
    ∧ (∀ (Rrel : Trajectory → Trajectory → Prop)
        (_h : Stream'.IsBisimulation Rrel) (s t : Trajectory), Rrel s t → s = t)
    ∧ (∀ c : R 8, (alwaysConst c).head = c)
    ∧ (∀ c : R 8, (alwaysConst c).tail = alwaysConst c) :=
  ⟨step_cons,
   fun _ f x => unfold_head f x,
   fun _ f x => unfold_tail f x,
   fun Rrel h s t hr => bisimEq Rrel h (s := s) (t := t) hr,
   alwaysConst_head,
   alwaysConst_tail⟩

end SSBX.Foundation.R8
