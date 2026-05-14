/-
# Foundation.R.Judgment.Behavior — trajectory classification on R N

Per `wen-algebra` v0.6 §7.3: behavior judgment for endomorphisms
`f : R N → R N`.

A trajectory `w0, f(w0), f²(w0), …` falls into one of four classes:

* `stable`    — the trajectory reaches a fixed point.
* `periodic` — the trajectory enters a non-trivial cycle.
* `transient`— the trajectory traverses a long prefix before settling
                (still finite-period, but with long pre-period).
* `complex`  — anything else (used as a catch-all for non-classified).

For finite N (specifically N ≤ 8), classification is computable via
brute-force orbit enumeration.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Judgment.Attractor
import Mathlib.Data.List.Defs
import Mathlib.Data.Finset.Basic

namespace SSBX.Foundation.R.Judgment

open SSBX.Foundation.R

namespace Behavior

variable {N : ℕ}

/-! ## § 1 The four behavior classes -/

/-- Behavior class of a trajectory under `f : R N → R N`. -/
inductive BehaviorClass where
  /-- The trajectory reaches a fixed point of f. -/
  | stable
  /-- The trajectory enters a non-trivial cycle. -/
  | periodic
  /-- The trajectory has a long pre-period before periodicity. -/
  | transient
  /-- Catch-all for non-classified behavior. -/
  | complex
  deriving DecidableEq, Repr

namespace BehaviorClass

/-- All four behavior classes in canonical order. -/
def all : List BehaviorClass :=
  [.stable, .periodic, .transient, .complex]

@[simp] theorem all_length : all.length = 4 := rfl

theorem all_nodup : all.Nodup := by decide

theorem mem_all (b : BehaviorClass) : b ∈ all := by cases b <;> decide

end BehaviorClass

/-! ## § 2 Trajectory definition -/

/-- Iterate `f` from `w0` for `n` steps (the `n+1`-th value of the
    trajectory). -/
def trajectory (f : R N → R N) (w0 : R N) : ℕ → R N
  | 0      => w0
  | k + 1  => f (trajectory f w0 k)

@[simp] theorem trajectory_zero (f : R N → R N) (w0 : R N) :
    trajectory f w0 0 = w0 := rfl

theorem trajectory_succ (f : R N → R N) (w0 : R N) (k : ℕ) :
    trajectory f w0 (k + 1) = f (trajectory f w0 k) := rfl

/-! ## § 3 Classification via prefix scan

For `R N` with `N ≤ 8`, brute-force orbit enumeration is feasible
(at most 2^8 = 256 distinct states).  We classify by stepping until
either a fixed point is hit (stable) or a cycle is detected
(periodic). -/

/-- Helper: check if `w` is a fixed point of `f`. -/
def isFixed [DecidableEq (R N)] (f : R N → R N) (w : R N) : Bool :=
  decide (f w = w)

/-- Classify the behavior of `w0` under `f` by stepping for at most
    `bound` iterations.  At each step:

    * `stable`    if a fixed point is reached.
    * `periodic`  if the initial `w0` is revisited (after at least one
                  step) before the bound is exhausted.
    * `complex`   if the bound is exhausted with neither a fixed point
                  nor a return-to-start (then either the orbit is in
                  a non-`w0`-containing cycle = `transient` regime, or
                  the bound was too short). -/
def classify [DecidableEq (R N)] (f : R N → R N) (w0 : R N) (bound : ℕ) :
    BehaviorClass :=
  let rec aux : ℕ → R N → BehaviorClass
    | 0,     _    => .complex
    | n + 1, curr =>
      if isFixed f curr then .stable
      else if curr = w0 then .periodic
      else aux n (f curr)
  aux bound (f w0)

/-! ## § 4 Concrete sanity examples (small R N) -/

example :
    classify (fun w : R 1 => w) (fun _ => false : R 1) 4 = .stable := by
  decide

example :
    classify (fun w : R 1 => fun i => Bool.xor (w i) true) (fun _ => false : R 1) 4
      = .periodic := by
  decide

end Behavior

end SSBX.Foundation.R.Judgment
