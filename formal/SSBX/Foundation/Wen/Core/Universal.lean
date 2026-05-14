/-
# Foundation.Wen.Core.Universal — universal interpreter specification

The **specification** of a universal interpreter on the language-
independent `R 8` bit-machine, and the auxiliary `encodeProgInput`
function that injects a `(program, input)` pair into the linear
`history` boundary of an initial state.

We do **not** construct a universal interpreter here — that
construction is the subject of `Foundation/Wen/MetaInterp/`, where
it is currently axiomatised as `kleene_recursion_axiom`.  This file
provides only the target specification (the `IsUniversal` predicate)
so that future work can prove `IsUniversal U` for an explicit `U`.

## What is here

* **§ 1 Program encoding** — `encodeProgInput`, the canonical injection
  of a `List Instr × R 8` pair into the initial-state `history`.
* **§ 2 Observational equivalence** — `equivObs`, the equivalence
  relation on `State`s used as the universal-interpretation target.
* **§ 3 `IsUniversal`** — the universal-interpreter spec.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §10.7 (Interpreter Foundation, equiv test).
* `r8.md` v0.2 §15.10 (Interpreter primitives, `step` / `trace`).
* The target of `kleene_recursion_axiom` in `Foundation/Wen/MetaInterp/`
  (cf. `KleeneCarrier.lean`).

## Carrier choice for encoding

We use the `history : List (R 8)` channel for `(program, input)`
encoding, rather than splitting the byte (`cur : R 8`) into separate
program/input halves.  Rationale: the `history` channel is
**unbounded** by design (it's the linear tape that gives the machine
universal computation), so a finite encoding always fits.  The
instruction encoding (one `R 8` per `Instr`) is parametric and
left abstract here — concrete encodings (e.g. opcode + operand
packed into one byte) belong to `MetaInterp/`.
-/

import SSBX.Foundation.Wen.Core.Instruction
import SSBX.Foundation.Wen.Core.State
import SSBX.Foundation.Wen.Core.Machine

namespace SSBX.Foundation.Wen.Core

open SSBX.Foundation.R

/-! ## § 1 Program encoding

We assume an abstract encoder of instructions to `R 8` cells.  Any
concrete `encodeInstr : Instr → R 8` and `decodeInstr : R 8 → Option Instr`
forms an encoding scheme; we abstract over the choice via a structure.
-/

/-- An encoding scheme for instructions into `R 8` cells.

    A complete scheme has a decoder that round-trips: every encoded
    instruction can be uniquely recovered from its `R 8` image.
    We do not require the decoder to be surjective; the encoder need
    not hit every `R 8` value. -/
structure InstrEncoding where
  /-- Encode an instruction into one `R 8` cell. -/
  enc : Instr → R 8
  /-- Decode a candidate `R 8` cell into an optional instruction. -/
  dec : R 8 → Option Instr
  /-- Decoder is the left-inverse of encoder. -/
  dec_enc : ∀ i : Instr, dec (enc i) = some i

/-- Encode a program as a list of `R 8` cells. -/
def encodeProg (E : InstrEncoding) (prog : List Instr) : List (R 8) :=
  prog.map E.enc

/-- The standard injection of `(program, input)` into an initial state:
    `cur := input`, `history := encodeProg E prog`. -/
def encodeProgInput (E : InstrEncoding) (prog : List Instr) (input : R 8)
    : State :=
  { cur := input
  , history := encodeProg E prog
  , pc := 0
  , halted := false }

@[simp] theorem encodeProgInput_cur (E : InstrEncoding) (prog : List Instr)
    (input : R 8) :
    (encodeProgInput E prog input).cur = input := rfl

@[simp] theorem encodeProgInput_history (E : InstrEncoding)
    (prog : List Instr) (input : R 8) :
    (encodeProgInput E prog input).history = encodeProg E prog := rfl

@[simp] theorem encodeProgInput_pc (E : InstrEncoding) (prog : List Instr)
    (input : R 8) :
    (encodeProgInput E prog input).pc = 0 := rfl

@[simp] theorem encodeProgInput_halted (E : InstrEncoding) (prog : List Instr)
    (input : R 8) :
    (encodeProgInput E prog input).halted = false := rfl

/-! ## § 2 Observational equivalence

Two states are observationally equivalent if they agree on the
"observable" data: the `cur` cell value and the halt flag.  The
program counter and history are internal scratch — a universal
interpreter is allowed to differ on those, so long as the externally
visible output (`cur`, `halted`) matches that of the original program.

This matches the standard simulation-up-to-stuttering equivalence
used in interpreter-correctness arguments.
-/

/-- Observational equivalence on `State`: agree on `cur` and `halted`. -/
def equivObs (s t : State) : Prop :=
  s.cur = t.cur ∧ s.halted = t.halted

namespace equivObs

theorem refl (s : State) : equivObs s s := ⟨rfl, rfl⟩

theorem symm {s t : State} (h : equivObs s t) : equivObs t s :=
  ⟨h.1.symm, h.2.symm⟩

theorem trans {s t u : State} (h₁ : equivObs s t) (h₂ : equivObs t u) :
    equivObs s u :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

end equivObs

/-- `equivObs` is an equivalence relation. -/
instance : Equivalence equivObs where
  refl := equivObs.refl
  symm := equivObs.symm
  trans := equivObs.trans

/-! ## § 3 Universal interpreter specification

A program `U : List Instr` is **universal** with respect to an
encoding `E : InstrEncoding` iff: for every program `p`, every input
`inp`, and every fuel budget `N`, running `U` on the encoded
`(p, inp)` pair for some bounded amount of fuel produces a state
observationally equivalent to running `p` directly on `inp` for `N`
fuel units.

The "some bounded amount of fuel" is captured by a *fuel translation*
function `f : Nat → Nat`: simulating `N` steps of `p` may take up to
`f N` steps of `U` (typically `f N = c · N` for some constant `c`).
-/

/-- A *universal interpreter* with respect to encoding `E`: `U`
    simulates every program `p` on every input `inp`, with the
    simulation fuel-translated by some computable function `f`. -/
def IsUniversal (E : InstrEncoding) (U : List Instr) : Prop :=
  ∃ f : Nat → Nat,
    ∀ (p : List Instr) (inp : R 8) (N : Nat),
      equivObs
        (runFuel U (f N) (encodeProgInput E p inp))
        (run p inp N)

/-! ## § 4 Sanity lemmas about the spec -/

/-- The identity-program `[]` is universal only over the empty
    program-class.  Concretely: `IsUniversal E []` would require
    `equivObs (encodeProgInput E p inp) (run p inp N)` for all
    `p, inp, N`, which can hold only if every program halts
    immediately at its initial state, which is not the case.

    We do **not** state this as a theorem (it is not always provable
    without a concrete encoding), but document the intent: only
    *non-trivial* `U` can be universal. -/
theorem IsUniversal_target_form (E : InstrEncoding) (U : List Instr)
    (hU : IsUniversal E U) :
    ∃ f : Nat → Nat,
      ∀ (p : List Instr) (inp : R 8) (N : Nat),
        (runFuel U (f N) (encodeProgInput E p inp)).cur = (run p inp N).cur ∧
        (runFuel U (f N) (encodeProgInput E p inp)).halted = (run p inp N).halted := by
  rcases hU with ⟨f, hf⟩
  refine ⟨f, fun p inp N => ?_⟩
  exact hf p inp N

/-- Trivial universality witness: a program is universal-for-itself
    with identity fuel translation. -/
theorem self_simulates (E : InstrEncoding) (p : List Instr)
    (h : ∀ (inp : R 8) (N : Nat),
      equivObs (runFuel p N (encodeProgInput E p inp)) (run p inp N)) :
    ∃ f : Nat → Nat,
      ∀ (inp : R 8) (N : Nat),
        equivObs (runFuel p (f N) (encodeProgInput E p inp))
                 (run p inp N) :=
  ⟨id, h⟩

/-! ## § 5 Fuel-translated simulation

A weaker notion: a program `U` *simulates* program `p` with fuel
translation `f` and encoding `E`.  `IsUniversal` is exactly
"`Simulates` for all `p`".
-/

/-- `Simulates E U p f` says: program `U` simulates program `p` with
    fuel translation `f` and encoding `E`. -/
def Simulates (E : InstrEncoding) (U : List Instr) (p : List Instr)
    (f : Nat → Nat) : Prop :=
  ∀ (inp : R 8) (N : Nat),
    equivObs
      (runFuel U (f N) (encodeProgInput E p inp))
      (run p inp N)

/-- A universal interpreter simulates every program with a single
    fuel translation. -/
theorem IsUniversal_iff_uniform_Simulates (E : InstrEncoding) (U : List Instr) :
    IsUniversal E U ↔
      ∃ f : Nat → Nat, ∀ p : List Instr, Simulates E U p f := by
  unfold IsUniversal Simulates
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, fun p inp N => hf p inp N⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, fun p inp N => hf p inp N⟩

/-! ## § 6 The target of `kleene_recursion_axiom`

`IsUniversal` is the formal target of the universal-interpreter
existence statement.  In `Foundation/Wen/MetaInterp/KleeneCarrier.lean`,
the construction is currently axiomatised:

```
axiom kleene_recursion_axiom : ∃ U : ..., IsUniversal ... U
```

(with a different but equivalent state-machine shape).  This file
provides the canonical, language-independent target.  Future work in
`MetaInterp/` will exhibit an explicit witness `U` and prove
`IsUniversal E U` for a chosen encoding `E`.
-/

/-- The existence statement of a universal interpreter.  This is the
    target of `Foundation/Wen/MetaInterp/`'s construction. -/
def UniversalInterpreterExists (E : InstrEncoding) : Prop :=
  ∃ U : List Instr, IsUniversal E U

end SSBX.Foundation.Wen.Core
