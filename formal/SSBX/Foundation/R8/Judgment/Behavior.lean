/-
# Foundation.R8.Judgment.Behavior — R 8 specializations of behavior judgment.

Per `r8.md` v0.2 §11, the parametric behavior-judgment functions
(trajectory classification) from `Foundation/R/Judgment/Behavior.lean`
specialised to `R 8`.

This is a thin wrapper plus a few `R 8`-specific helpers (e.g. the
"behavior richness" 4-level classification of §11.4).

## Doctrinal anchor

* `r8.md` v0.2 §11.1 (behavior = trajectory),
  §11.2 (4 classes: stable / periodic / transient / complex),
  §11.4 (behavior metrics including `behavior_visited` richness levels).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Judgment.Behavior

namespace SSBX.Foundation.R8.Judgment

open SSBX.Foundation.R
open SSBX.Foundation.R.Judgment

namespace Behavior

/-! ## § 1 Re-export the behavior class -/

/-- 4-class behavior taxonomy on R 8.  Per `r8.md` v0.2 §11.2. -/
abbrev BehaviorClass8 : Type := Behavior.BehaviorClass

/-! ## § 2 Trajectory on R 8 -/

/-- The point on the trajectory of `w₀` at iteration `k`. -/
def trajectory8 (f : R 8 → R 8) (w₀ : R 8) (k : ℕ) : R 8 :=
  Behavior.trajectory f w₀ k

@[simp] theorem trajectory8_zero (f : R 8 → R 8) (w₀ : R 8) :
    trajectory8 f w₀ 0 = w₀ := rfl

theorem trajectory8_succ (f : R 8 → R 8) (w₀ : R 8) (k : ℕ) :
    trajectory8 f w₀ (k + 1) = f (trajectory8 f w₀ k) := rfl

/-! ## § 3 Classification on R 8

For `R 8` (256 elements), the bound `256` is a safe upper limit for
finite enumeration of orbits. -/

/-- Classify a behavior on R 8 with default bound 256.  -/
def classify8 (f : R 8 → R 8) (w₀ : R 8) : BehaviorClass8 :=
  Behavior.classify (N := 8) f w₀ 256

/-! ## § 4 Behavior richness levels

Per `r8.md` v0.2 §11.4:

* `|visited| = 1`     → stable
* `|visited| ≤ 8`     → simple periodic
* `9 ≤ |visited| ≤ 64`  → moderate
* `|visited| > 64`    → complex

We encode this as a `BehaviorRichness` taxonomy. -/

/-- Behavior richness tier based on the number of visited states. -/
inductive BehaviorRichness where
  /-- Visits exactly 1 state (stable). -/
  | stableOne
  /-- Visits 2–8 states (simple periodic). -/
  | simplePeriodic
  /-- Visits 9–64 states (moderate). -/
  | moderate
  /-- Visits more than 64 states (complex). -/
  | complex
  deriving DecidableEq, Repr

/-- Classify a visit-count into a richness tier per `r8.md` §11.4. -/
def richnessOfVisitCount (n : ℕ) : BehaviorRichness :=
  if n ≤ 1 then .stableOne
  else if n ≤ 8 then .simplePeriodic
  else if n ≤ 64 then .moderate
  else .complex

@[simp] theorem richness_one : richnessOfVisitCount 1 = .stableOne := by decide

@[simp] theorem richness_eight : richnessOfVisitCount 8 = .simplePeriodic := by decide

@[simp] theorem richness_64 : richnessOfVisitCount 64 = .moderate := by decide

@[simp] theorem richness_65 : richnessOfVisitCount 65 = .complex := by decide

end Behavior

end SSBX.Foundation.R8.Judgment
