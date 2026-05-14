/-
# Foundation.R.Phantom — phantom mode discipline for R N elements

Per `wen-algebra` v0.6 §6.4 and `v4-foundation` v0.5 §16:

R-Family elements carry a phantom **mode** tag distinguishing different
semantic roles for the same underlying data.  The seven modes are:

* `State`    — a data value (the default reading)
* `Op`       — a linear endomorphism (acting on State)
* `Cause`    — half of a causal pair
* `Effect`   — the other half of a causal pair
* `TimeIn`   — a time-tagged input
* `TimeOut`  — a time-tagged output
* `Frame`    — frame-of-reference

The underlying data type is identical across modes; only the tag
changes.  Coercions between modes (e.g., `State → Op`) **must be
explicit** — silent semantic drift is the failure mode this layer
exists to prevent.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 The seven phantom modes -/

/-- Phantom mode tag for `R N` elements.  Per `wen-algebra` v0.6 §6.4. -/
inductive Mode where
  /-- A data value (the default state-of-the-world reading). -/
  | State
  /-- A linear endomorphism acting on State. -/
  | Op
  /-- The cause-half of a causal pair. -/
  | Cause
  /-- The effect-half of a causal pair. -/
  | Effect
  /-- A time-tagged input. -/
  | TimeIn
  /-- A time-tagged output. -/
  | TimeOut
  /-- A frame-of-reference tag. -/
  | Frame
  deriving DecidableEq, Repr

namespace Mode

/-- All seven modes in canonical order. -/
def all : List Mode :=
  [.State, .Op, .Cause, .Effect, .TimeIn, .TimeOut, .Frame]

@[simp] theorem all_length : all.length = 7 := rfl

theorem all_nodup : all.Nodup := by decide

theorem mem_all (m : Mode) : m ∈ all := by cases m <;> decide

end Mode

/-! ## § 2 Phantom-typed R N elements -/

/-- An `R N` element carrying a phantom mode tag.  Per `wen-algebra`
    v0.6 §6.4. -/
structure RPhantom (N : ℕ) (m : Mode) where
  /-- The underlying `R N` data. -/
  data : R N

namespace RPhantom

variable {N M : ℕ}

@[ext] theorem ext {N : ℕ} {m : Mode} {x y : RPhantom N m}
    (h : x.data = y.data) : x = y := by
  cases x; cases y; congr

/-- The zero RPhantom element at any mode. -/
def zero (N : ℕ) (m : Mode) : RPhantom N m := ⟨0⟩

@[simp] theorem zero_data (N : ℕ) (m : Mode) : (zero N m).data = (0 : R N) := rfl

/-- Pair two State-mode phantoms via direct sum.  Per `wen-algebra`
    v0.6 §6.5 row "pair". -/
def pair {N M : ℕ}
    (u : RPhantom N Mode.State) (v : RPhantom M Mode.State) :
    RPhantom (N + M) Mode.State :=
  ⟨R.append u.data v.data⟩

/-- Causal-pair construction: cause + effect → state.  Per
    `wen-algebra` v0.6 §6.5 row "causal_pair". -/
def causal_pair {N M : ℕ}
    (c : RPhantom N Mode.Cause) (e : RPhantom M Mode.Effect) :
    RPhantom (N + M) Mode.State :=
  ⟨R.append c.data e.data⟩

/-- Time-pair: TimeIn + TimeOut → State (same N, doubled).  Per
    `wen-algebra` v0.6 §6.5 row "time_pair". -/
def time_pair {N : ℕ}
    (tin : RPhantom N Mode.TimeIn) (tout : RPhantom N Mode.TimeOut) :
    RPhantom (N + N) Mode.State :=
  ⟨R.append tin.data tout.data⟩

/-! ## § 3 Explicit coercions

Per the v0.6 doctrine: mode changes must be explicit `def`s, never
silent `instance Coe`s.  This is exactly to prevent semantic drift
("a State got treated as an Op because someone forgot to think"). -/

/-- Explicit coercion: State → Op.  The data is unchanged; only the
    mode tag flips.  Use only when you genuinely mean "treat this
    state as if it were an operator" (e.g., reading a stored map). -/
def coerce_state_to_op {N : ℕ} (s : RPhantom N Mode.State) :
    RPhantom N Mode.Op :=
  ⟨s.data⟩

/-- Explicit coercion: Op → State.  Data unchanged. -/
def coerce_op_to_state {N : ℕ} (o : RPhantom N Mode.Op) :
    RPhantom N Mode.State :=
  ⟨o.data⟩

/-- Explicit coercion: State → Cause.  Data unchanged. -/
def coerce_state_to_cause {N : ℕ} (s : RPhantom N Mode.State) :
    RPhantom N Mode.Cause :=
  ⟨s.data⟩

/-- Explicit coercion: State → Effect.  Data unchanged. -/
def coerce_state_to_effect {N : ℕ} (s : RPhantom N Mode.State) :
    RPhantom N Mode.Effect :=
  ⟨s.data⟩

/-! ## § 4 Round-trip identities -/

@[simp] theorem coerce_op_state_round (s : RPhantom N Mode.State) :
    coerce_op_to_state (coerce_state_to_op s) = s := by
  cases s; rfl

@[simp] theorem coerce_state_op_round (o : RPhantom N Mode.Op) :
    coerce_state_to_op (coerce_op_to_state o) = o := by
  cases o; rfl

end RPhantom

end R

end SSBX.Foundation.R
