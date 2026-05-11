import SSBX.Foundation.Wen.WenyanQuineHistory
import SSBX.Foundation.Wen.WenyanQuineWitness
import SSBX.Foundation.Wen.WenyanQuineEncoding

/-!
# WenyanQuineConcreteSearch

Concrete search notes for a non-`push`-only Tier 3 witness.

The attempted route is the literal emitter from `WenyanQuineHistory`: generate a
program that emits a target cell stream, and instantiate the target as program
encoding data.  This file records the computable success boundary and the
length obstruction that prevents closing the literal-emitter fixed point.
-/

namespace SSBX.Foundation.Wen.WenyanQuineConcreteSearch

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanQuineEmitter
open SSBX.Foundation.Wen.WenyanQuineHistory
open SSBX.Foundation.Wen.WenyanQuineWitness

def searchStart : R8 := (Hexagram.heaven, Shi.jin)

/-! ## Direct non-push-only candidate -/

def directNonPushSource : List YiInstr :=
  [YiInstr.setShi Shi.ji, YiInstr.push]

def directNonPushInit : YiState :=
  { cur := searchStart
  , history := []
  , pc := 0
  , prog := directNonPushSource
  , halted := false }

def directNonPushFuel : Nat := directNonPushSource.length + 2

/--
The smallest direct non-`push`-only candidate emits the changed current cell.
Its first output is therefore `cellFromIdx 1` (= (heaven, ji) in V₄ R8 indexing),
while its program encoding starts with the `setShi` tag `cellFromIdx 1` followed
by `encShi Shi.ji = cellFromIdx 1` and `push = cellFromIdx 9`.

Note: post-Phase F.2 (Cell192 → R8), Shi indexing is V₄: dao=0, ji=1, jin=2,
wei=3. searchStart = (heaven, jin) → cellToIdx = 0·4+2 = 2. After setShi Shi.ji,
cur = (heaven, ji) → cellToIdx = 0·4+1 = 1. (Pre-migration Z/3 used 0·3+0 = 0.)
-/
theorem direct_non_push_failed_shape :
    (directNonPushInit.runFuel directNonPushFuel).history =
      [cellFromIdx ⟨1, by omega⟩] ∧
    ProgEnc.encProg directNonPushSource =
      [cellFromIdx ⟨1, by omega⟩, cellFromIdx ⟨1, by omega⟩,
       cellFromIdx ⟨9, by omega⟩] ∧
    (directNonPushInit.runFuel directNonPushFuel).history ≠
      ProgEnc.encProg directNonPushSource := by
  native_decide

/-! ## Literal emitter route -/

/--
A non-`push`-only seed whose raw encoding can be emitted by the generator below.
This is not claimed as a quine source; it is the target used to probe the
literal emitter route.
-/
def seedSource : List YiInstr := directNonPushSource

def generatedTarget : List R8 := ProgEnc.encProg seedSource

def generatedSource : List YiInstr :=
  emitCellsFrom searchStart generatedTarget

def generatedInit : YiState :=
  { cur := searchStart
  , history := []
  , pc := 0
  , prog := generatedSource
  , halted := false }

def generatedFuel : Nat := generatedSource.length + 2

/--
The literal emitter works as a generator: it emits the seed program encoding.
This is the useful computable boundary of the concrete search.
-/
theorem generated_emits_seed_encoding :
    (generatedInit.runFuel generatedFuel).history = generatedTarget := by
  native_decide

/--
But that generated program is not a fixed point: its own encoding is longer
than the target it emits.
-/
theorem generated_not_self_encoding :
    (generatedInit.runFuel generatedFuel).history ≠
      ProgEnc.encProg generatedSource ∧
    generatedTarget.length < (ProgEnc.encProg generatedSource).length := by
  native_decide

/-! ## General gate for the literal emitter fixed point -/

theorem emitCellFrom_length_ge_two (cur target : R8) :
    2 ≤ (emitCellFrom cur target).length := by
  simp only [emitCellFrom, List.length_append, List.length_cons, List.length_nil]
  omega

theorem emitCellsInOrderFrom_length_ge_two_mul
    (start : R8) (targets : List R8) :
    2 * targets.length ≤ (emitCellsInOrderFrom start targets).length := by
  induction targets generalizing start with
  | nil =>
      simp [emitCellsInOrderFrom]
  | cons target rest ih =>
      unfold emitCellsInOrderFrom
      have hhead := emitCellFrom_length_ge_two start target
      have htail := ih target
      simp only [List.length_cons, List.length_append]
      omega

theorem emitCellsFrom_length_ge_two_mul
    (start : R8) (targets : List R8) :
    2 * targets.length ≤ (emitCellsFrom start targets).length := by
  unfold emitCellsFrom
  have h := emitCellsInOrderFrom_length_ge_two_mul start targets.reverse
  simpa [List.length_reverse] using h

theorem encInstr_length_ge_one (i : YiInstr) :
    1 ≤ (YiInstrEnc.encInstr i).length := by
  cases i <;> simp [YiInstrEnc.encInstr, YiInstrEnc.encNat]

theorem encProg_length_ge (p : List YiInstr) :
    p.length ≤ (ProgEnc.encProg p).length := by
  induction p with
  | nil =>
      simp [ProgEnc.encProg]
  | cons head tail ih =>
      have hhead := encInstr_length_ge_one head
      have hsplit :
          ProgEnc.encProg (head :: tail) =
            YiInstrEnc.encInstr head ++ ProgEnc.encProg tail := by
        simp [ProgEnc.encProg]
      rw [hsplit]
      simp only [List.length_cons, List.length_append]
      omega

/--
Literal emitter fixed point gate.

If `targets` is nonempty, the program `emitCellsFrom start targets` cannot have
raw encoding exactly equal to `targets`.  Closing the naive equation

`targets = ProgEnc.encProg (emitCellsFrom start targets)`

would require the source to have at least two instructions per emitted cell,
while raw instruction encoding has at least one cell per instruction.
-/
theorem literal_emitter_fixed_point_obstruction
    (start : R8) (targets : List R8) (h_nonempty : targets ≠ []) :
    ProgEnc.encProg (emitCellsFrom start targets) ≠ targets := by
  intro hfix
  have h_emit := emitCellsFrom_length_ge_two_mul start targets
  have h_enc := encProg_length_ge (emitCellsFrom start targets)
  have h_source_le_target :
      (emitCellsFrom start targets).length ≤ targets.length := by
    simpa [hfix] using h_enc
  have h_two_le_one : 2 * targets.length ≤ targets.length :=
    Nat.le_trans h_emit h_source_le_target
  cases targets with
  | nil =>
      exact (h_nonempty rfl).elim
  | cons _ rest =>
      simp at h_two_le_one
      omega

/--
Concrete instantiation of the gate for the seed target above.  The generated
route is a valid emitter for another program's encoding, but it does not close
into a nontrivial self-witness.
-/
theorem generated_literal_fixed_point_obstructed :
    ProgEnc.encProg generatedSource ≠ generatedTarget := by
  apply literal_emitter_fixed_point_obstruction
  native_decide

end SSBX.Foundation.Wen.WenyanQuineConcreteSearch
