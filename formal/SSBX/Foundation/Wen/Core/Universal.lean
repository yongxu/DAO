/-
# Foundation.Wen.Core.Universal — universal interpreter specification (PartialCell-native)

The **specification** of a universal interpreter on the PartialCell-native
bit-machine, and the auxiliary `encodeProgInput` function that injects a
`(program, input)` pair into the linear `history` boundary of an initial
state.

This is the Phase E.4 port of `Foundation/Wen/Core/Universal.lean` to the
new `CorePartial` substrate.  As in the legacy spec, we do **not**
construct a universal interpreter here — this file provides only the
target predicate (`IsUniversal`), so that future work can prove
`IsUniversal U` for an explicit `U`.

## What is here

* **§ 1 Program encoding** — `InstrEncoding`, `encodeProg`,
  `encodeProgInput`, the canonical injection of a
  `(List Instr × PartialCell 8)` pair into the initial-state `history`.
* **§ 2 Observational equivalence** — `equivObs` on `State`, agreeing
  on `cur` (the partial-cell observable) and the halt flag.
* **§ 3 `IsUniversal`** — the universal-interpreter spec.
* **§ 4–6** — sanity lemmas, `Simulates`, and `UniversalInterpreterExists`.

## Key differences from the legacy port

* The `cur` channel is `PartialCell 8`, not `R 8`.  Observational
  equivalence compares partial cells directly (no extraction to
  `R 8` — `cur` IS the observable, and a universal interpreter
  must reproduce it *including its commitment shape*).
* The instruction-encoding carrier is still `R 8` (one fully-specified
  byte per `Instr`), since the `history` channel itself remains a list
  of partial cells but the encoding alphabet is taken total to keep
  `dec_enc` decidable and useful.  Encoded program cells are injected
  via `PartialCell.ofFull`.
* `encodeProgInput` accepts `PartialCell 8` as input, not `R 8` — the
  caller may supply a partial input, which is the natural shape on
  this substrate.  `init` (the legacy bridge that lifts `R 8`) is
  used only via `PartialCell.ofFull`.
* `run` is defined locally (mirroring the legacy `Wen.Core.Machine.run`)
  as `runFuel prog fuel (State.init inp)` for the totalized input case.

## Doctrinal anchor

* `wen-substrate.md` v1.2 §3.7 (Operation Monism).
* `wen-algebra.md` v0.6 §10.7 (Interpreter Foundation).
* Legacy: `Foundation/Wen/Core/Universal.lean`.
-/

import SSBX.Foundation.Wen.Core.Instruction
import SSBX.Foundation.Wen.Core.State
import SSBX.Foundation.Wen.Core.Machine

namespace SSBX.Foundation.Wen.Core

open SSBX.Foundation.R

/-! ## § 1 Program encoding

We assume an abstract encoder of instructions to `R 8` cells.  The
encoding alphabet is kept *total* (`R 8` rather than `PartialCell 8`)
so that `dec_enc` round-tripping is unambiguous; the program-tape
itself lives in `history : List (PartialCell 8)` (the partial-cell
substrate), and encoded program cells are injected via
`PartialCell.ofFull`.
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

/-- Encode a program as a list of `PartialCell 8` cells (each
    instruction's `R 8` image lifted to a fully-specified partial
    cell via `ofFull`). -/
def encodeProg (E : InstrEncoding) (prog : List Instr)
    : List (PartialCell 8) :=
  prog.map (fun i => PartialCell.ofFull (E.enc i))

/-- The standard injection of `(program, input)` into an initial state:
    `cur := input`, `history := encodeProg E prog`.

    Note: `input` is a `PartialCell 8` here (not `R 8` as in the legacy
    spec), reflecting the substrate.  See `encodeProgInputFull` for the
    totalized-input convenience. -/
def encodeProgInput (E : InstrEncoding) (prog : List Instr)
    (input : PartialCell 8) : State :=
  { cur := input
  , history := encodeProg E prog
  , pc := 0
  , halted := false }

/-- Convenience: encode with a fully-specified `R 8` input (legacy
    parity bridge).  Definitionally equal to
    `encodeProgInput E prog (PartialCell.ofFull inp)`. -/
def encodeProgInputFull (E : InstrEncoding) (prog : List Instr)
    (inp : R 8) : State :=
  encodeProgInput E prog (PartialCell.ofFull inp)

@[simp] theorem encodeProgInput_cur (E : InstrEncoding) (prog : List Instr)
    (input : PartialCell 8) :
    (encodeProgInput E prog input).cur = input := rfl

@[simp] theorem encodeProgInput_history (E : InstrEncoding)
    (prog : List Instr) (input : PartialCell 8) :
    (encodeProgInput E prog input).history = encodeProg E prog := rfl

@[simp] theorem encodeProgInput_pc (E : InstrEncoding) (prog : List Instr)
    (input : PartialCell 8) :
    (encodeProgInput E prog input).pc = 0 := rfl

@[simp] theorem encodeProgInput_halted (E : InstrEncoding) (prog : List Instr)
    (input : PartialCell 8) :
    (encodeProgInput E prog input).halted = false := rfl

@[simp] theorem encodeProgInputFull_cur (E : InstrEncoding) (prog : List Instr)
    (inp : R 8) :
    (encodeProgInputFull E prog inp).cur = PartialCell.ofFull inp := rfl

@[simp] theorem encodeProgInputFull_history (E : InstrEncoding)
    (prog : List Instr) (inp : R 8) :
    (encodeProgInputFull E prog inp).history = encodeProg E prog := rfl

/-! ## § 2 Observational equivalence

Two states are observationally equivalent if they agree on the
"observable" data: the `cur` partial cell and the halt flag.  The
program counter and history are internal scratch — a universal
interpreter is allowed to differ on those, so long as the externally
visible output (`cur`, `halted`) matches that of the original program.

PartialCell-native note: equality on `cur : PartialCell 8` requires
**bit-for-bit identical commitment shape**.  This is strictly stronger
than a "same total bytes" criterion: two states that both have
`cur = ofFull v` agree, but a universal interpreter cannot replace a
partial `cur` with its `none`-completion or vice versa.
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

A program `U : List Instr` is **universal** with respect to an encoding
`E : InstrEncoding` iff: for every program `p`, every (partial) input
`inp`, and every fuel budget `N`, running `U` on the encoded
`(p, inp)` pair for some bounded amount of fuel produces a state
observationally equivalent to running `p` directly on `inp` for `N`
fuel units.

The "some bounded amount of fuel" is captured by a *fuel translation*
function `f : Nat → Nat`: simulating `N` steps of `p` may take up to
`f N` steps of `U` (typically `f N = c · N` for some constant `c`).
-/

/-- A *universal interpreter* with respect to encoding `E`: `U`
    simulates every program `p` on every partial input `inp`, with
    the simulation fuel-translated by some computable function `f`. -/
def IsUniversal (E : InstrEncoding) (U : List Instr) : Prop :=
  ∃ f : Nat → Nat,
    ∀ (p : List Instr) (inp : PartialCell 8) (N : Nat),
      equivObs
        (runFuel U (f N) (encodeProgInput E p inp))
        (runFuel p N { pc := 0, cur := inp, history := [], halted := false })

/-! ## § 4 Sanity lemmas about the spec -/

/-- Pointwise unpacking of `IsUniversal`: the `equivObs` decomposes
    into per-field equalities.  Useful for downstream consumers that
    need direct `.cur` or `.halted` access. -/
theorem IsUniversal_target_form (E : InstrEncoding) (U : List Instr)
    (hU : IsUniversal E U) :
    ∃ f : Nat → Nat,
      ∀ (p : List Instr) (inp : PartialCell 8) (N : Nat),
        (runFuel U (f N) (encodeProgInput E p inp)).cur =
          (runFuel p N { pc := 0, cur := inp, history := [],
                         halted := false }).cur ∧
        (runFuel U (f N) (encodeProgInput E p inp)).halted =
          (runFuel p N { pc := 0, cur := inp, history := [],
                         halted := false }).halted := by
  rcases hU with ⟨f, hf⟩
  refine ⟨f, fun p inp N => ?_⟩
  exact hf p inp N

/-- Trivial universality witness: a program is universal-for-itself
    with identity fuel translation (assuming it self-simulates under
    the encoding). -/
theorem self_simulates (E : InstrEncoding) (p : List Instr)
    (h : ∀ (inp : PartialCell 8) (N : Nat),
      equivObs (runFuel p N (encodeProgInput E p inp))
               (runFuel p N { pc := 0, cur := inp, history := [],
                              halted := false })) :
    ∃ f : Nat → Nat,
      ∀ (inp : PartialCell 8) (N : Nat),
        equivObs (runFuel p (f N) (encodeProgInput E p inp))
                 (runFuel p N { pc := 0, cur := inp, history := [],
                                halted := false }) :=
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
  ∀ (inp : PartialCell 8) (N : Nat),
    equivObs
      (runFuel U (f N) (encodeProgInput E p inp))
      (runFuel p N { pc := 0, cur := inp, history := [], halted := false })

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

/-! ## § 6 Existence statement

The target of any future explicit-universal-interpreter construction.
On the PartialCell substrate this is the §3.7-aligned shape of the
universality claim. -/

/-- The existence statement of a universal interpreter on
    `CorePartial`.  This is the target of any future universal-
    interpreter construction (the analogue of
    `Foundation/Wen/Core/Universal.lean`'s `UniversalInterpreterExists`
    for the partial substrate). -/
def UniversalInterpreterExists (E : InstrEncoding) : Prop :=
  ∃ U : List Instr, IsUniversal E U

end SSBX.Foundation.Wen.Core
