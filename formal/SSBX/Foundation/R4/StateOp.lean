/-
# Foundation.R4.StateOp — State / Op dual identity via phantom mode

Per `r4.md` v0.2 §9 ("State / Op dual identity"):

Every `R 4` element carries **two distinct semantic readings** with
the same underlying bit pattern:

* **State** — a pair `(u, v) ∈ R 2 × R 2` (data).
* **Op**    — a linear endomorphism `R 2 → R 2` (function).

The phantom-mode discipline of `Foundation/R/Phantom.lean` (modes
`State`, `Op`, …) provides the type-level distinction.  This file:

1. Specializes `RPhantom 4 Mode.State` and `RPhantom 4 Mode.Op` to
   `StateR4` and `OpR4` (concrete aliases).
2. Wires `apply` (Op × R 2 → R 2) and `compose` (Op × Op → Op) using
   the matrix view from `EndR2.lean`.
3. Re-exports the explicit `state_to_op` / `op_to_state` coercions
   from `R/Phantom.lean` at `N = 4`.
4. Verifies round-trip identities on `R 4`.

## Doctrinal anchor

* `r4.md` v0.2 §9.1 (dual identity), §9.3 (phantom type discipline),
  §9.4 (type-rule table), §9.5 (explicit coercion).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Phantom
import SSBX.Foundation.R4.EndR2

namespace SSBX.Foundation.R4

open SSBX.Foundation.R

/-! ## § 1 Concrete aliases for the two R 4 modes

We expose `R 4` State / Op as separate types so downstream code can
write `StateR4` / `OpR4` instead of `RPhantom 4 Mode.State` /
`RPhantom 4 Mode.Op`. -/

/-- An `R 4` element tagged as **state** (a pair of `R 2` values). -/
abbrev StateR4 : Type := R.RPhantom 4 R.Mode.State

/-- An `R 4` element tagged as **op** (an endomorphism of `R 2`). -/
abbrev OpR4 : Type := R.RPhantom 4 R.Mode.Op

/-! ## § 2 Apply: `OpR4 × R 2 → R 2`

Per `r4.md §9.4`: `apply : R 4[Op] × R 2 → R 2`.  We use the matrix
view from `EndR2.lean`. -/

/-- Apply an `OpR4` to an `R 2` vector. -/
def applyOp (f : OpR4) (u : R 2) : R 2 :=
  applyR2 f.data u

@[simp] theorem applyOp_data (f : OpR4) (u : R 2) :
    applyOp f u = applyR2 f.data u := rfl

/-! ## § 3 Compose: `OpR4 × OpR4 → OpR4`

Per `r4.md §9.4`: `compose : R 4[Op] × R 4[Op] → R 4[Op]`. -/

/-- Compose two `OpR4` endomorphisms. -/
def composeOp (g f : OpR4) : OpR4 :=
  ⟨composeR2 g.data f.data⟩

@[simp] theorem composeOp_data (g f : OpR4) :
    (composeOp g f).data = composeR2 g.data f.data := rfl

/-! ## § 4 The identity Op (= `xoox`)

Per `r4.md §8.4`: identity matrix `[[1,0],[0,1]]` = `xoox`. -/

/-- The identity `OpR4`. -/
def idOp : OpR4 := ⟨xoox⟩

@[simp] theorem idOp_data : idOp.data = xoox := rfl

/-- Applying `idOp` is the identity on `R 2`. -/
theorem applyOp_id (u : R 2) : applyOp idOp u = u :=
  applyR2_id u

/-- `idOp` is a left identity for `composeOp`. -/
theorem composeOp_id_left (f : OpR4) : composeOp idOp f = f :=
  R.RPhantom.ext (composeR2_id_left f.data)

/-- `idOp` is a right identity for `composeOp`. -/
theorem composeOp_id_right (f : OpR4) : composeOp f idOp = f :=
  R.RPhantom.ext (composeR2_id_right f.data)

/-! ## § 5 Pair construction: `R 2 × R 2 → StateR4`

Per `r4.md §9.4`: `pair : R 2 × R 2 → R 4[State]`.

We build it concretely from `R 2`'s two coordinates. -/

/-- Pack two `R 2` values into a `StateR4`. -/
def pairState (u v : R 2) : StateR4 :=
  ⟨fun i =>
    match i.val with
    | 0 => u ⟨0, by decide⟩
    | 1 => u ⟨1, by decide⟩
    | 2 => v ⟨0, by decide⟩
    | _ => v ⟨1, by decide⟩⟩

/-! ## § 6 Explicit coercions (re-exported)

The State ↔ Op coercions are **explicit `def`s** at the generic
`R/Phantom.lean` layer.  Here we just re-export them at `N = 4` and
verify the round-trip identities for the R 4 case. -/

/-- Coerce a `StateR4` into an `OpR4`.  The underlying bits are
    unchanged; only the semantic tag flips. -/
def stateToOp (s : StateR4) : OpR4 :=
  R.RPhantom.coerce_state_to_op s

/-- Coerce an `OpR4` into a `StateR4`.  Underlying bits unchanged. -/
def opToState (o : OpR4) : StateR4 :=
  R.RPhantom.coerce_op_to_state o

/-! ## § 7 Round-trip identities at R 4 -/

@[simp] theorem stateToOp_opToState (o : OpR4) :
    stateToOp (opToState o) = o := by
  cases o; rfl

@[simp] theorem opToState_stateToOp (s : StateR4) :
    opToState (stateToOp s) = s := by
  cases s; rfl

/-- The coercions preserve underlying data. -/
theorem stateToOp_data (s : StateR4) :
    (stateToOp s).data = s.data := rfl

theorem opToState_data (o : OpR4) :
    (opToState o).data = o.data := rfl

/-! ## § 8 Worked example: State (xo, ox) coerces to Op = identity

Per `r4.md §9.5` discussion: the `R 4` element `xoox` viewed as State
is the pair `(xo, ox)` (i.e. the two basis vectors of `R 2`); viewed
as Op it is the identity matrix.  Same bits, different semantics. -/

/-- The State `(xo, ox)` is the same `R 4` element as `xoox`. -/
theorem pairState_xo_ox_eq_xoox :
    (pairState R.xo R.ox).data = xoox := by
  funext i
  fin_cases i <;> rfl

/-- Coercing State `(xo, ox)` to Op gives the identity Op. -/
theorem stateToOp_pair_xo_ox :
    stateToOp (pairState R.xo R.ox) = idOp :=
  R.RPhantom.ext pairState_xo_ox_eq_xoox

end SSBX.Foundation.R4
