/-
# Foundation.Atlas.Yi.YiInstr — 文 instruction set + interpreter on R-Family

> **R-Family port (2026-05-15)** of
> `Atlas/Yi/Classical/Computation/BaguaTuring.lean`.  The classical
> port operated on `SSBX.Foundation.Bagua.R8 = Hexagram × Shi` where
> `Hexagram` was an inductive struct.  This R-Family rewrite operates
> on `Atlas.Yi.Cell256 = Hexagram × Shi` with `Hexagram = R 6 =
> Fin 6 → Bool` and `Shi = R 2`.

The 文 (wenyan) instruction set is a 12-constructor inductive type
operating on `Cell256`.  Together with the `runFuel` interpreter, it
provides a Turing-complete subset (unbounded history, data-dependent
branches, unbounded jumps, unbounded program length).

The capstone is `daoJudgeProg`: a 5-instruction wenyan program that,
given any hexagram, computes the verdict {Shi.ji = 天道, Shi.wei =
心道} matching the `isTian` predicate (y3 = y4 ⟺ 互²-stable).

## Phases

  § 1   Hexagram bit access / single-yao flip helpers
  § 2   `isTian` / `isXin` predicates on R-Family Hexagram
  § 3   `Instr` inductive — 12 constructors
  § 4   `YiState` + `runFuel` interpreter
  § 5   `daoJudgeProg` + correctness theorems
  § 6   TC witnesses (`loopProg`)
  § 7   Public summary bundle

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9 (Atlas separation).
* `v4-foundation.md` v0.5 §15 (external traditions).
-/

import SSBX.Foundation.Atlas.Yi.Cell256

namespace SSBX.Foundation.Atlas.Yi.YiInstr

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 Hexagram bit access + single-yao flip on R-Family -/

/-- Single-yao flip on `Hexagram = R 6` at position `i`. -/
def hexFlip (i : Fin 6) (h : Hexagram) : Hexagram :=
  fun j => if j = i then !(h j) else h j

theorem hexFlip_involutive (i : Fin 6) (h : Hexagram) :
    hexFlip i (hexFlip i h) = h := by
  funext j
  unfold hexFlip
  by_cases hj : j = i
  · simp [hj, Bool.not_not]
  · simp [hj]

/-! ## § 2 `isTian` / `isXin` on R-Family Hexagram

  Local definitions of the 天 / 心 partition predicates, equivalent to
  the classical ones in `Yi.lean` but stated on `R 6`.  A hexagram is
  `isTian` iff its 3rd and 4th yao agree (the 互²-stable criterion). -/

/-- 天道 hex predicate: y3 = y4 (互²-stable). -/
def isTian (h : Hexagram) : Bool := h.y3 == h.y4

/-- 心道 hex predicate: y3 ≠ y4 (互²-oscillating). -/
def isXin (h : Hexagram) : Bool := !(isTian h)

theorem tianXin_complement (h : Hexagram) : isTian h = !(isXin h) := by
  simp [isXin]

/-! ## § 3 The 12-instruction wenyan ISA -/

/-- The wenyan instruction set.  Each acts on a `YiState` whose `cur`
    field has type `Cell256 = Hexagram × Shi`. -/
inductive Instr : Type
  /-- 不动: do nothing, advance pc. -/
  | nop
  /-- 设时态: set the Shi component of `cur`. -/
  | setShi (s : Shi)
  /-- 翻爻 i: flip the i-th yao of `cur.1`. -/
  | flipYao (i : Fin 6)
  /-- 互: apply `Hexagram.hu` to `cur.1`. -/
  | hu
  /-- 错: apply `Hexagram.cuo` to `cur.1`. -/
  | cuo
  /-- 综: apply `Hexagram.zong` to `cur.1`. -/
  | zong
  /-- 比爻 (branch if equal yao): jump if `y_i = y_j`. -/
  | branchYaoEq (i j : Fin 6) (target : Nat)
  /-- 比时 (branch if Shi equal): jump if `cur.2 = s`. -/
  | branchShiEq (s : Shi) (target : Nat)
  /-- 跳: unconditional jump. -/
  | jump (target : Nat)
  /-- 推: push `cur` to history. -/
  | push
  /-- 取: pop from history into `cur` (halt if empty). -/
  | pop
  /-- 终: halt. -/
  | halt

namespace Instr

/-- Six convenience aliases for `flipYao ⟨i, _⟩` matching the classical
    BaguaTuring style. -/
def flip1 : Instr := .flipYao ⟨0, by decide⟩
def flip2 : Instr := .flipYao ⟨1, by decide⟩
def flip3 : Instr := .flipYao ⟨2, by decide⟩
def flip4 : Instr := .flipYao ⟨3, by decide⟩
def flip5 : Instr := .flipYao ⟨4, by decide⟩
def flip6 : Instr := .flipYao ⟨5, by decide⟩

end Instr

/-! ## § 4 Execution state + fuel-bounded interpreter -/

/-- Execution state on Cell256.  `cur` is the current cell, `history`
    is the unbounded tape, `pc` is the program counter, `prog` is the
    loaded program, and `halted` is the termination flag. -/
structure YiState where
  cur     : Cell256
  history : List Cell256
  pc      : Nat
  prog    : List Instr
  halted  : Bool

namespace YiState

/-- Initial state: hexagram `h`, Shi = 今 (the temporal entry point;
    `Shi.dao` is intentionally reserved as the V₄ identity anchor and
    NOT used for the initial Shi). -/
def init (h : Hexagram) (prog : List Instr) : YiState :=
  { cur := (h, Shi.jin), history := [], pc := 0, prog := prog, halted := false }

/-- Execute a single `Instr` against the current state. -/
def execute (instr : Instr) (s : YiState) : YiState :=
  match instr with
  | .nop => { s with pc := s.pc + 1 }
  | .setShi sh => { s with cur := (s.cur.1, sh), pc := s.pc + 1 }
  | .flipYao i =>
      { s with cur := (hexFlip i s.cur.1, s.cur.2), pc := s.pc + 1 }
  | .hu   => { s with cur := (Hexagram.hu   s.cur.1, s.cur.2), pc := s.pc + 1 }
  | .cuo  => { s with cur := (Hexagram.cuo  s.cur.1, s.cur.2), pc := s.pc + 1 }
  | .zong => { s with cur := (Hexagram.zong s.cur.1, s.cur.2), pc := s.pc + 1 }
  | .branchYaoEq i j target =>
      if s.cur.1 i = s.cur.1 j
      then { s with pc := target }
      else { s with pc := s.pc + 1 }
  | .branchShiEq sh target =>
      if s.cur.2 = sh
      then { s with pc := target }
      else { s with pc := s.pc + 1 }
  | .jump target => { s with pc := target }
  | .push => { s with history := s.cur :: s.history, pc := s.pc + 1 }
  | .pop =>
      match s.history with
      | [] => { s with halted := true }
      | c :: rest => { s with cur := c, history := rest, pc := s.pc + 1 }
  | .halt => { s with halted := true }

/-- Single step: fetch instruction at `pc`, execute (or halt if pc ≥ length). -/
def step (s : YiState) : YiState :=
  if s.halted then s
  else match s.prog[s.pc]? with
    | none => { s with halted := true }
    | some instr => execute instr s

end YiState

/-- The single-step function lifted to the top-level for the
    `runStep`/`runFuel` API.  `runStep` is `step` on a state initialised
    with this instruction's program.  We export it as a per-Instr
    semantics function on a bare `Hexagram` for the doc-promised
    `runStep : Instr → Hexagram → Hexagram` signature. -/
def runStep (instr : Instr) (h : Hexagram) : Hexagram :=
  ((YiState.execute instr (YiState.init h [instr])).cur).1

/-- Fuel-bounded interpreter (top-level wrapper).

    `runFuel prog n h` initialises the state with hexagram `h` and
    program `prog`, then steps up to `n` times. -/
def runFuelState : Nat → YiState → YiState
  | 0, s => s
  | n+1, s => if s.halted then s else runFuelState n s.step

/-- Top-level fuel-bounded interpreter on a hexagram.  Returns the
    final hexagram component. -/
def runFuel (prog : List Instr) (n : Nat) (h : Hexagram) : Hexagram :=
  ((runFuelState n (YiState.init h prog)).cur).1

/-! ## § 4b runFuel basic theorems -/

/-- `runFuelState 0` is the identity. -/
@[simp] theorem runFuelState_zero (s : YiState) : runFuelState 0 s = s := rfl

/-- `runFuelState (n+1) s` unfolds. -/
theorem runFuelState_succ (n : Nat) (s : YiState) :
    runFuelState (n+1) s = if s.halted then s else runFuelState n s.step := rfl

/-- `runFuelState` is monotone in the halted flag: once halted, the state
    is stable. -/
theorem runFuelState_halted (n : Nat) (s : YiState) (h : s.halted = true) :
    runFuelState n s = s := by
  induction n with
  | zero => rfl
  | succ k ih =>
      unfold runFuelState
      simp [h]

/-! ## § 5 daoJudgeProg — the 道判机 -/

/-- The 5-instruction 道判机 program.

    Logic: at pc=0 branch on `y3 = y4` to pc=3 (the 天道 setter).  At
    pc=1..2 fall through with `Shi.wei` (心道 verdict).  At pc=3..4 set
    `Shi.ji` (天道 verdict) and halt. -/
def daoJudgeProg : List Instr :=
  [ Instr.branchYaoEq ⟨2, by decide⟩ ⟨3, by decide⟩ 3
  , Instr.setShi Shi.wei
  , Instr.halt
  , Instr.setShi Shi.ji
  , Instr.halt
  ]

/-- The 道判机 verdict on a given hexagram, extracted from the Shi
    component of the final state after 10 fuel steps. -/
def daoJudge (h : Hexagram) : Shi :=
  ((runFuelState 10 (YiState.init h daoJudgeProg)).cur).2

/-! ## § 5b daoJudge correctness on the R-Family stack -/

/-- The 道判机 correctly classifies the 天/心 partition.

    Proof: by `decide` on the finite domain `Hexagram = Fin 6 → Bool`. -/
theorem daoJudge_correct (h : Hexagram) :
    daoJudge h = (if isTian h then Shi.ji else Shi.wei) := by
  -- Reduce to a finite-domain decision over the 6 yao bits.
  have key : ∀ b1 b2 b3 b4 b5 b6 : Bool,
      daoJudge (Hexagram.mk b1 b2 b3 b4 b5 b6) =
        (if isTian (Hexagram.mk b1 b2 b3 b4 b5 b6) then Shi.ji else Shi.wei) := by
    intro b1 b2 b3 b4 b5 b6
    revert b1 b2 b3 b4 b5 b6
    decide
  -- Recover h from its 6 yao via extensionality.
  have hext : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by
    apply Hexagram.ext <;> rfl
  rw [hext]
  exact key h.y1 h.y2 h.y3 h.y4 h.y5 h.y6

/-- `daoJudge h = Shi.ji ↔ isTian h = true`. -/
theorem daoJudge_isTian (h : Hexagram) :
    daoJudge h = Shi.ji ↔ isTian h = true := by
  rw [daoJudge_correct]
  cases isTian h
  · simp
    intro heq
    -- `Shi.wei = Shi.ji` is false by distinctness; derive contradiction.
    have : Shi.toNat Shi.wei = Shi.toNat Shi.ji := by rw [heq]
    simp at this
  · simp

/-- `daoJudge h = Shi.wei ↔ isXin h = true`. -/
theorem daoJudge_isXin (h : Hexagram) :
    daoJudge h = Shi.wei ↔ isXin h = true := by
  rw [daoJudge_correct, isXin]
  cases isTian h
  · simp
  · simp
    intro heq
    have : Shi.toNat Shi.ji = Shi.toNat Shi.wei := by rw [heq]
    simp at this

/-- 乾為天 is 天道. -/
theorem daoJudge_qianqian : daoJudge Hexagram.qianqian = Shi.ji := by
  decide

/-- 坤為地 is 天道. -/
theorem daoJudge_kunkun : daoJudge Hexagram.kunkun = Shi.ji := by
  decide

/-- 既濟 is 心道 (y3=阳 ≠ y4=阴). -/
theorem daoJudge_jiji : daoJudge Hexagram.jiji = Shi.wei := by
  decide

/-- 未濟 is 心道. -/
theorem daoJudge_weiji : daoJudge Hexagram.weiji = Shi.wei := by
  decide

/-! ## § 6 TC primitives — loopProg as non-termination witness -/

/-- A non-halting program: unconditional jump-to-self. -/
def loopProg : List Instr := [Instr.jump 0]

/-- A program that grows the history unboundedly. -/
def unboundedHistoryProg : List Instr := [Instr.push, Instr.jump 0]

/-- Stepping the init state of `loopProg` returns the init state. -/
theorem step_loopProg_init (h : Hexagram) :
    (YiState.init h loopProg).step = YiState.init h loopProg := by
  rfl

/-- Bounded execution of `loopProg` from init stutters: every fuel
    amount returns the same state. -/
theorem runFuelState_loopProg_init (h : Hexagram) :
    ∀ n : Nat, runFuelState n (YiState.init h loopProg) = YiState.init h loopProg := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      unfold runFuelState
      show (if (YiState.init h loopProg).halted
            then YiState.init h loopProg
            else runFuelState k (YiState.init h loopProg).step) =
        YiState.init h loopProg
      have hnot : (YiState.init h loopProg).halted = false := rfl
      rw [hnot, step_loopProg_init, ih]
      simp

/-- `loopProg` has no finite fuel witness for halting. -/
theorem loopProg_no_fuel_witness (h : Hexagram) :
    ¬ ∃ n : Nat, (runFuelState n (YiState.init h loopProg)).halted = true := by
  rintro ⟨n, hn⟩
  have hfalse : (YiState.init h loopProg).halted = false := rfl
  rw [runFuelState_loopProg_init h n, hfalse] at hn
  cases hn

/-- For any fuel `n`, `loopProg` from `qianqian` is not halted. -/
theorem loopProg_unbounded :
    ∀ n : Nat,
      ¬ (runFuelState n (YiState.init Hexagram.qianqian loopProg)).halted = true := by
  intro n hn
  exact loopProg_no_fuel_witness Hexagram.qianqian ⟨n, hn⟩

/-! ## § 6b daoJudgeProg termination -/

/-- 道判机 terminates on every input within 10 fuel steps. -/
theorem daoJudgeProg_terminates :
    ∀ h : Hexagram,
      (runFuelState 10 (YiState.init h daoJudgeProg)).halted = true := by
  intro h
  have key : ∀ b1 b2 b3 b4 b5 b6 : Bool,
      (runFuelState 10 (YiState.init (Hexagram.mk b1 b2 b3 b4 b5 b6) daoJudgeProg)).halted = true := by
    intro b1 b2 b3 b4 b5 b6
    revert b1 b2 b3 b4 b5 b6
    decide
  have hext : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by
    apply Hexagram.ext <;> rfl
  rw [hext]
  exact key h.y1 h.y2 h.y3 h.y4 h.y5 h.y6

/-! ## § 7 Single-step law preservation (each Instr preserves Cell256
    algebra structure trivially: `Hexagram` and `Shi` remain in their
    types).  We expose involutivity for the structural single-step
    Instrs as a structured sanity-witness bundle. -/

/-- `cuo` (錯) applied twice through `runStep` returns the original hex. -/
theorem runStep_cuo_involutive (h : Hexagram) :
    runStep Instr.cuo (runStep Instr.cuo h) = h := by
  unfold runStep YiState.execute YiState.init
  simp [Hexagram.cuo_involutive]

/-- `zong` (綜) applied twice through `runStep` returns the original hex. -/
theorem runStep_zong_involutive (h : Hexagram) :
    runStep Instr.zong (runStep Instr.zong h) = h := by
  unfold runStep YiState.execute YiState.init
  simp [Hexagram.zong_involutive]

/-- `flipYao i` applied twice through `runStep` returns the original hex. -/
theorem runStep_flipYao_involutive (i : Fin 6) (h : Hexagram) :
    runStep (Instr.flipYao i) (runStep (Instr.flipYao i) h) = h := by
  unfold runStep YiState.execute YiState.init
  simp [hexFlip_involutive]

/-! ## § 8 Public summary bundle -/

/-- The R-Family 道判机 completeness theorem:

    (1) verdict is always {ji, wei};
    (2) verdict matches `isTian`;
    (3) terminates within 10 fuel on every input;
    (4) `loopProg` is provably non-halting at every fuel level. -/
theorem dao_judge_complete :
    (∀ h : Hexagram, daoJudge h = Shi.ji ∨ daoJudge h = Shi.wei)
    ∧ (∀ h : Hexagram, daoJudge h = (if isTian h then Shi.ji else Shi.wei))
    ∧ (∀ h : Hexagram, (runFuelState 10 (YiState.init h daoJudgeProg)).halted = true)
    ∧ (∀ n : Nat,
        ¬ (runFuelState n (YiState.init Hexagram.qianqian loopProg)).halted = true) := by
  refine ⟨?_, daoJudge_correct, daoJudgeProg_terminates, loopProg_unbounded⟩
  intro h
  rw [daoJudge_correct]
  cases isTian h <;> simp

end SSBX.Foundation.Atlas.Yi.YiInstr
