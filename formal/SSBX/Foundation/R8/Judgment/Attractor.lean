/-
# Foundation.R8.Judgment.Attractor — R 8 specializations of attractor judgment.

Per `r8.md` v0.2 §10, the parametric attractor-judgment functions
(fixed points / orbits) from `Foundation/R/Judgment/Attractor.lean`
specialised to `R 8`.

This is a thin wrapper: re-exports `R N`-level functions with
`R 8`-typed signatures.

## Doctrinal anchor

* `r8.md` v0.2 §10.1 (fixed points / orbits / basin),
  §10.2 (linear endomorphism fixed-point dimension),
  §10.4 (judgment functions),
  §10.5 (byte-scale enumerable scale).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Judgment.Attractor

namespace SSBX.Foundation.R8.Judgment

open SSBX.Foundation.R
open SSBX.Foundation.R.Judgment

namespace Attractor

/-! ## § 1 Fixed points on R 8 -/

/-- The fixed-point set of an endomorphism `f : R 8 → R 8`. -/
def fixed_points8 (f : R 8 → R 8) : Finset (R 8) :=
  Attractor.fixed_points (N := 8) f

/-- The number of fixed points. -/
def fixed_point_count8 (f : R 8 → R 8) : ℕ :=
  Attractor.fixed_point_count (N := 8) f

/-! ## § 2 Worked endpoints -/

theorem fixed_point_count8_id :
    fixed_point_count8 (fun w : R 8 => w) = Fintype.card (R 8) :=
  Attractor.fixed_point_count_id

/-- The identity has all 256 elements as fixed points. -/
theorem fixed_point_count8_id_256 :
    fixed_point_count8 (fun w : R 8 => w) = 256 := by
  rw [fixed_point_count8_id, R.R8_card]

theorem fixed_point_count8_zero :
    fixed_point_count8 (fun _ : R 8 => (0 : R 8)) = 1 :=
  Attractor.fixed_point_count_zero

/-! ## § 3 Trajectories on R 8 -/

/-- Iterate `f` on `w₀` for `k` steps. -/
def trajectory8 (f : R 8 → R 8) (w₀ : R 8) (k : ℕ) : List (R 8) :=
  Attractor.trajectory f w₀ k

theorem trajectory8_length (f : R 8 → R 8) (w₀ : R 8) (k : ℕ) :
    (trajectory8 f w₀ k).length = k + 1 :=
  Attractor.trajectory_length f w₀ k

/-! ## § 4 Byte-scale enumeration scale claim

Per `r8.md` v0.2 §10.5: orbit structure on `R 8` is fully enumerable in
O(|R 8|²) = O(65_536) operations.  We expose the bound as a constant. -/

/-- The byte-scale enumeration bound `|R 8|² = 65_536`. -/
def enumeration_bound : ℕ := 65536

theorem enumeration_bound_eq : enumeration_bound = Fintype.card (R 8) * Fintype.card (R 8) := by
  unfold enumeration_bound
  rw [R.R8_card]

end Attractor

end SSBX.Foundation.R8.Judgment
