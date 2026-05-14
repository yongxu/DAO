/-
# Foundation.R.Judgment.Attractor — fixed points / orbits on R N

Per `wen-algebra` v0.6 §7.2: attractor judgment for endomorphisms
`f : R N → R N`.

* `fixed_points f` — the finset of `w : R N` with `f w = w`.
* `fixed_point_count f` — its cardinality.
* `orbit f w` — the (eventually periodic) trajectory of `w` under `f`,
  bounded by `2^N` since `R N` is finite.

For finite N these are all `decide`-able / `native_decide`-able.
-/

import SSBX.Foundation.R.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace SSBX.Foundation.R.Judgment

open SSBX.Foundation.R

namespace Attractor

variable {N : ℕ}

/-! ## § 1 Fixed points -/

/-- The finset of fixed points of `f : R N → R N`. -/
def fixed_points (f : R N → R N) : Finset (R N) :=
  Finset.univ.filter (fun w => f w = w)

/-- The number of fixed points. -/
def fixed_point_count (f : R N → R N) : ℕ := (fixed_points f).card

/-- The identity has every element as a fixed point. -/
theorem fixed_points_id : fixed_points (fun w : R N => w) = Finset.univ := by
  unfold fixed_points
  ext w
  simp

theorem fixed_point_count_id :
    fixed_point_count (fun w : R N => w) = Fintype.card (R N) := by
  unfold fixed_point_count
  rw [fixed_points_id]
  rfl

/-- The constant-zero map has exactly one fixed point: 0. -/
theorem fixed_points_zero : fixed_points (fun _ : R N => (0 : R N)) = {0} := by
  unfold fixed_points
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem fixed_point_count_zero :
    fixed_point_count (fun _ : R N => (0 : R N)) = 1 := by
  unfold fixed_point_count
  rw [fixed_points_zero]
  rfl

/-! ## § 2 Orbit truncations

For a finite-state map `f : R N → R N`, every orbit is eventually
periodic; the orbit truncated to `2^N + 1` steps necessarily contains
a repetition (pigeon-hole), so periodicity can be detected. -/

/-- Iterate `f` on `w0` for `steps` steps, producing the trajectory
    as a list of length `steps + 1`. -/
def trajectory (f : R N → R N) (w0 : R N) : ℕ → List (R N)
  | 0      => [w0]
  | k + 1  => w0 :: trajectory f (f w0) k

@[simp] theorem trajectory_zero (f : R N → R N) (w0 : R N) :
    trajectory f w0 0 = [w0] := rfl

theorem trajectory_succ (f : R N → R N) (w0 : R N) (k : ℕ) :
    trajectory f w0 (k + 1) = w0 :: trajectory f (f w0) k := rfl

theorem trajectory_length (f : R N → R N) (w0 : R N) (k : ℕ) :
    (trajectory f w0 k).length = k + 1 := by
  induction k generalizing w0 with
  | zero => rfl
  | succ k ih =>
    rw [trajectory_succ]
    simp [List.length_cons, ih]

end Attractor

end SSBX.Foundation.R.Judgment
