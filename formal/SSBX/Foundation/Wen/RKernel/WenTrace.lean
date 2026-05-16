/-
# Wen.RKernel.WenTrace -- mode-labelled paths

Computation at the structural kernel is a path labelled by Mode16 actions.
This is lower than Lisp and higher than R8 cells.
-/

import SSBX.Foundation.Wen.RKernel.WenAction

namespace SSBX.Foundation.Wen.RKernel

namespace WenTrace

structure Step (α : Type) where
  before : α
  mode : Mode16
  after : α
  deriving Repr

def traceWordAux : Word64 → List Mode16 → List (Step Word64) × Word64
  | current, [] => ([], current)
  | current, mode :: rest =>
      let next := Mode16.actWord mode current
      let (steps, final) := traceWordAux next rest
      ({ before := current, mode := mode, after := next } :: steps, final)

def traceWord (start : Word64) (modes : List Mode16) : List (Step Word64) :=
  (traceWordAux start modes).1

def finalWord (start : Word64) (modes : List Mode16) : Word64 :=
  (traceWordAux start modes).2

def wordStates (start : Word64) (modes : List Mode16) : List Word64 :=
  start :: (traceWord start modes).map (fun step => step.after)

def traceViewAux :
    Mode16.R8View → List Mode16 → List (Step Mode16.R8View) × Mode16.R8View
  | current, [] => ([], current)
  | current, mode :: rest =>
      let next := Mode16.actView mode current
      let (steps, final) := traceViewAux next rest
      ({ before := current, mode := mode, after := next } :: steps, final)

def viewStates (start : Mode16.R8View) (modes : List Mode16) :
    List Mode16.R8View :=
  start :: (traceViewAux start modes).1.map (fun step => step.after)

def sampleModes : List Mode16 :=
  [Mode16.pureWord .cuoZong, Mode16.pureWord .zong, Mode16.pureWord .cuo]

theorem sample_wordStates :
    wordStates Word64.qian sampleModes =
      [Word64.qian, Word64.kun, Word64.incomplete, Word64.qian] :=
  rfl

def sampleViewModes : List Mode16 :=
  [Mode16.compound, Mode16.compound]

theorem sample_viewStates :
    viewStates Mode16.sampleView sampleViewModes =
      [Mode16.sampleView, ⟨Word64.kun, .cuoZong⟩, Mode16.sampleView] :=
  rfl

#eval wordStates Word64.qian sampleModes
#eval viewStates Mode16.sampleView sampleViewModes

theorem wen_trace_summary :
    wordStates Word64.qian sampleModes =
      [Word64.qian, Word64.kun, Word64.incomplete, Word64.qian]
    ∧ viewStates Mode16.sampleView sampleViewModes =
      [Mode16.sampleView, ⟨Word64.kun, .cuoZong⟩, Mode16.sampleView] :=
  ⟨sample_wordStates, sample_viewStates⟩

end WenTrace

end SSBX.Foundation.Wen.RKernel
