/-
# Wen.V4Kernel.WenRecursion -- finite recursion as Mode16 cycles

A fixed Mode16 action is self-inverse, so repeated action has period at most
two.  This is the primitive recursion/cycle law below the Lisp surface.
-/

import SSBX.Foundation.Wen.V4Kernel.WenTrace

namespace SSBX.Foundation.Wen.V4Kernel

namespace WenRecursion

def iterateWord (mode : Mode16) : Nat → Word64 → Word64
  | 0, word => word
  | n + 1, word => iterateWord mode n (Mode16.actWord mode word)

def iterateView (mode : Mode16) : Nat → Mode16.R8View → Mode16.R8View
  | 0, view => view
  | n + 1, view => iterateView mode n (Mode16.actView mode view)

@[simp] theorem iterateWord_zero (mode : Mode16) (word : Word64) :
    iterateWord mode 0 word = word := rfl

@[simp] theorem iterateView_zero (mode : Mode16) (view : Mode16.R8View) :
    iterateView mode 0 view = view := rfl

@[simp] theorem iterateWord_two (mode : Mode16) (word : Word64) :
    iterateWord mode 2 word = word := by
  simp [iterateWord]

@[simp] theorem iterateView_two (mode : Mode16) (view : Mode16.R8View) :
    iterateView mode 2 view = view := by
  simp [iterateView]

theorem iterateWord_add_two (mode : Mode16) (n : Nat) (word : Word64) :
    iterateWord mode (n + 2) word = iterateWord mode n word := by
  induction n generalizing word with
  | zero =>
      simp
  | succ n ih =>
      change iterateWord mode (n + 2) (Mode16.actWord mode word) =
        iterateWord mode n (Mode16.actWord mode word)
      exact ih (Mode16.actWord mode word)

theorem iterateView_add_two (mode : Mode16) (n : Nat) (view : Mode16.R8View) :
    iterateView mode (n + 2) view = iterateView mode n view := by
  induction n generalizing view with
  | zero =>
      simp
  | succ n ih =>
      change iterateView mode (n + 2) (Mode16.actView mode view) =
        iterateView mode n (Mode16.actView mode view)
      exact ih (Mode16.actView mode view)

def cycle2Word (mode : Mode16) (start : Word64) : List Word64 :=
  [start, Mode16.actWord mode start, start]

def cycle2View (mode : Mode16) (start : Mode16.R8View) : List Mode16.R8View :=
  [start, Mode16.actView mode start, start]

theorem compound_word_cycle :
    cycle2Word Mode16.compound Word64.qian = [Word64.qian, Word64.kun, Word64.qian] :=
  rfl

theorem compound_view_cycle :
    cycle2View Mode16.compound Mode16.sampleView =
      [Mode16.sampleView, ⟨Word64.kun, .cuoZong⟩, Mode16.sampleView] :=
  rfl

theorem wen_recursion_summary :
    (∀ mode word, iterateWord mode 2 word = word)
    ∧ (∀ mode view, iterateView mode 2 view = view)
    ∧ (∀ mode n word, iterateWord mode (n + 2) word = iterateWord mode n word)
    ∧ (∀ mode n view, iterateView mode (n + 2) view = iterateView mode n view)
    ∧ cycle2Word Mode16.compound Word64.qian = [Word64.qian, Word64.kun, Word64.qian] :=
  ⟨iterateWord_two, iterateView_two, iterateWord_add_two, iterateView_add_two,
   compound_word_cycle⟩

end WenRecursion

end SSBX.Foundation.Wen.V4Kernel
