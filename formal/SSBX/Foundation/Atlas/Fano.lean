/-
# Foundation.Atlas.Fano — R 3 ↔ Fano plane PG(2, 2)

Per `wen-algebra` v0.6 §9.2 and `v4-foundation` v0.5 §15.3:

    R 3 \ {0}  ≃  7 points of the Fano plane PG(2, 2)

The Fano plane is the projective plane of order 2 — the unique
Steiner triple system STS(7).  Its 7 points are the 7 non-zero
vectors of `F_2^3`; its 7 lines are the 7 three-element subsets
`{u, v, u + v}` for non-zero `u ≠ v`.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9.3 (multiple bindings on R 3).
* `v4-foundation.md` v0.5 §15.3 (R 3 — Fano plane, Steiner STS(7)).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Atlas.Fano

open SSBX.Foundation.R

/-! ## § 1 Fano points = non-zero R 3 elements -/

/-- A Fano point is a non-zero element of `R 3`. -/
def Point : Type := { v : R 3 // v ≠ 0 }

instance : DecidableEq Point := by
  unfold Point
  infer_instance

instance : Fintype Point := by
  unfold Point
  infer_instance

/-- |Point| = 7. -/
theorem card_point : Fintype.card Point = 7 := by
  unfold Point
  -- |{v : R 3 // v ≠ 0}| = |R 3| - 1 = 8 - 1 = 7
  decide

/-! ## § 2 Fano lines = triples `{u, v, u + v}` -/

/-- A Fano line is a triple of distinct non-zero R 3 elements that
    sum to zero (equivalently: `{u, v, u + v}` for distinct non-zero
    `u, v` with `u ≠ v`). -/
structure Line where
  p1 : R 3
  p2 : R 3
  p3 : R 3
  p1_ne_zero : p1 ≠ 0
  p2_ne_zero : p2 ≠ 0
  p3_ne_zero : p3 ≠ 0
  p1_ne_p2   : p1 ≠ p2
  p1_ne_p3   : p1 ≠ p3
  p2_ne_p3   : p2 ≠ p3
  sum_zero   : p1 + p2 + p3 = 0

namespace Line

/-- Helper: build `R 3` from 3 bits. -/
private def mk3 (b0 b1 b2 : Bool) : R 3 := fun i =>
  match i.val with
  | 0 => b0
  | 1 => b1
  | _ => b2

/-- The 7 non-zero `R 3` vectors. -/
def e1 : R 3 := mk3 true  false false  -- 100
def e2 : R 3 := mk3 false true  false  -- 010
def e3 : R 3 := mk3 false false true   -- 001
def e12 : R 3 := mk3 true  true  false  -- 110
def e13 : R 3 := mk3 true  false true   -- 101
def e23 : R 3 := mk3 false true  true   -- 011
def e123 : R 3 := mk3 true  true  true  -- 111

/-- Line through `e1, e2, e12` (= `e1 + e2`). -/
def line_12 : Line where
  p1 := e1; p2 := e2; p3 := e12
  p1_ne_zero := by decide
  p2_ne_zero := by decide
  p3_ne_zero := by decide
  p1_ne_p2   := by decide
  p1_ne_p3   := by decide
  p2_ne_p3   := by decide
  sum_zero   := by decide

/-- Line through `e1, e3, e13`. -/
def line_13 : Line where
  p1 := e1; p2 := e3; p3 := e13
  p1_ne_zero := by decide
  p2_ne_zero := by decide
  p3_ne_zero := by decide
  p1_ne_p2   := by decide
  p1_ne_p3   := by decide
  p2_ne_p3   := by decide
  sum_zero   := by decide

/-- Line through `e2, e3, e23`. -/
def line_23 : Line where
  p1 := e2; p2 := e3; p3 := e23
  p1_ne_zero := by decide
  p2_ne_zero := by decide
  p3_ne_zero := by decide
  p1_ne_p2   := by decide
  p1_ne_p3   := by decide
  p2_ne_p3   := by decide
  sum_zero   := by decide

/-- Line through `e1, e23, e123`. -/
def line_1_23 : Line where
  p1 := e1; p2 := e23; p3 := e123
  p1_ne_zero := by decide
  p2_ne_zero := by decide
  p3_ne_zero := by decide
  p1_ne_p2   := by decide
  p1_ne_p3   := by decide
  p2_ne_p3   := by decide
  sum_zero   := by decide

/-- Line through `e2, e13, e123`. -/
def line_2_13 : Line where
  p1 := e2; p2 := e13; p3 := e123
  p1_ne_zero := by decide
  p2_ne_zero := by decide
  p3_ne_zero := by decide
  p1_ne_p2   := by decide
  p1_ne_p3   := by decide
  p2_ne_p3   := by decide
  sum_zero   := by decide

/-- Line through `e3, e12, e123`. -/
def line_3_12 : Line where
  p1 := e3; p2 := e12; p3 := e123
  p1_ne_zero := by decide
  p2_ne_zero := by decide
  p3_ne_zero := by decide
  p1_ne_p2   := by decide
  p1_ne_p3   := by decide
  p2_ne_p3   := by decide
  sum_zero   := by decide

/-- Line through `e12, e13, e23` (the "diagonal" line). -/
def line_diag : Line where
  p1 := e12; p2 := e13; p3 := e23
  p1_ne_zero := by decide
  p2_ne_zero := by decide
  p3_ne_zero := by decide
  p1_ne_p2   := by decide
  p1_ne_p3   := by decide
  p2_ne_p3   := by decide
  sum_zero   := by decide

end Line

/-! ## § 3 The 7 lines collected -/

/-- The seven lines of the Fano plane, in canonical order. -/
def lines : List Line :=
  [ Line.line_12, Line.line_13, Line.line_23,
    Line.line_1_23, Line.line_2_13, Line.line_3_12,
    Line.line_diag ]

theorem seven_lines : lines.length = 7 := by decide

/-! ## § 4 Incidence -/

/-- A point lies on a line iff it is one of the line's three points. -/
def incident (p : Point) (L : Line) : Prop :=
  p.val = L.p1 ∨ p.val = L.p2 ∨ p.val = L.p3

instance instDecidableIncident (p : Point) (L : Line) :
    Decidable (incident p L) := by
  unfold incident
  infer_instance

/-- Each line has exactly three points (by construction). -/
theorem line_card (L : Line) :
    (({L.p1, L.p2, L.p3} : Finset (R 3)).card = 3) := by
  rcases L with ⟨a, b, c, _, _, _, hab, hac, hbc, _⟩
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
  · simp [hbc]
  · simp [hab, hac]

end SSBX.Foundation.Atlas.Fano
