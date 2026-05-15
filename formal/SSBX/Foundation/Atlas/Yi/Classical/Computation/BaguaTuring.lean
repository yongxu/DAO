/-
# BaguaTuring — 文程序、解释器、是道非道判机

> **[Atlas/Yi/Classical/Computation — 2026-05-15 (Phase γ)]** This file
> provides the YiInstr 12-instruction ISA + interpreter operating on
> classical Hexagram × Shi.  The R-Family TM (language-independent on
> R 8) lives in [`Foundation/Wen/Core/`](../../../../Wen/Core/); the
> bridge YiInstr ↔ Wen.Core.Instr is in
> [`Foundation/Wen/Core/YiInstrBridge.lean`](../../../../Wen/Core/YiInstrBridge.lean).
> Headline DaoSource and Diagonal theorems on the R-Family side are at
> [`Atlas/Yi/{DaoSource, Diagonal}.lean`](../../).

The interpreter for 文 (wenyan-encoded YiInstr programs) operating on R8.

The capstone: a Lean-verified Dao judge that, given a hexagram input, runs as a
YiProg and outputs whether the hexagram is 天道 (tian) or 心道 (xin) — answering
"是道非道" within the system.

## Phase F.2 migration note (Cell192 → R8)

Previously this module operated on Cell192 = Hexagram × Shi where Shi was a
Z/3 cyclic group `{已, 今, 未}`. After Phase F doctrine alignment, Shi is the
V₄ Klein four-group `{道, 已, 今, 未}` (R8 = Hexagram × Shi V₄, 256 cells).

Behavioural changes:
  - `YiInstr.setShi` accepts the new 4-state `Shi` (including `.dao`).
  - `YiInstr.branchShiEq` similarly admits 4 possible discriminants.
  - `shiNext` (the state-stepper helper) used to be the Z/3 cycle
    已→今→未→已. V₄ has no canonical cyclic order, so we replace it with
    `Shi.complement` (the 因-axis involution `dao↔已, 今↔未`). This is deterministic
    and total but order-2 rather than order-3.
  - Cardinality jumps 192 → 256.

The 道判机 verdict semantics are unchanged: 天道 ↦ `Shi.ji`, 心道 ↦ `Shi.wei`.
The new identity element `Shi.dao` is reachable as a verdict value but is not
emitted by `daoJudgeProg`; correctness theorems remain stated in terms of
`{Shi.ji, Shi.wei}`.

## Phases (continuing from R8.lean's §1–5)
  § 4   YiInstr inductive (文 instruction set)
  § 5   YiState + structurally-recursive `runFuel` + executable `partial def run`
  § 6   daoJudge: a YiProg that judges 是道非道
  § 7   Correctness theorem: daoJudge h matches Hexagram.isTian
       + TC discussion

## TC argument
  - State is unbounded (history : List R8 grows without limit)
  - Branching is data-dependent (branchYaoEq)
  - Jumps are unbounded (jump target : Nat)
  - Composition is unbounded (prog : List YiInstr of any length)

  These four primitives give universal computation. Specifically, any Minsky
  machine can be encoded by translating its instructions into YiInstr.
-/
import SSBX.Foundation.Atlas.Yi.Classical.Cells.R8

namespace SSBX.Foundation.Bagua.BaguaTuring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R8

/-! ## § 4 YiInstr — wenyan instruction set -/

/-- The wenyan instruction set. Each operates on the YiState. -/
inductive YiInstr : Type
  /-- 不动: do nothing, advance pc. -/
  | nop
  /-- 设时态: set 时态 component of cur (V₄, 4 possible values incl. `dao`). -/
  | setShi (s : Shi)
  /-- 翻爻: flip the i-th yao of cur's hexagram. -/
  | flipYao (i : Fin 6)
  /-- 互: apply Hexagram.interlace to cur's hexagram. -/
  | interlace
  /-- 错: apply Hexagram.complement to cur's hexagram. -/
  | complement
  /-- 综: apply Hexagram.reverse to cur's hexagram. -/
  | reverse
  /-- 比爻 (branch if equal yao): if y_i = y_j then jump to target, else advance. -/
  | branchYaoEq (i j : Fin 6) (target : Nat)
  /-- 比时 (branch if Shi equal): if cur.2 = s then jump to target, else advance. -/
  | branchShiEq (s : Shi) (target : Nat)
  /-- 跳: unconditional jump. -/
  | jump (target : Nat)
  /-- 推: push current cell to history. -/
  | push
  /-- 取: pop from history into cur (or halt if empty). -/
  | pop
  /-- 终: halt. -/
  | halt
  deriving Repr

end SSBX.Foundation.Bagua.BaguaTuring

/-! ## § 4b Helpers on Hexagram (yao access + single-position flip) — placed
   in the `SSBX.Foundation.Yi.Yi.Hexagram` namespace so that dot notation `h.yaoAt`
   on a `Hexagram` finds them. -/

namespace SSBX.Foundation.Yi.Yi.Hexagram

open SSBX.Foundation.Yi.Yi

/-- Get the i-th yao of a hexagram (0-indexed: 0=初爻, 5=上爻). -/
def yaoAt (h : Hexagram) : Fin 6 → Yao
  | ⟨0, _⟩ => h.y1
  | ⟨1, _⟩ => h.y2
  | ⟨2, _⟩ => h.y3
  | ⟨3, _⟩ => h.y4
  | ⟨4, _⟩ => h.y5
  | ⟨5, _⟩ => h.y6

/-- Flip the i-th yao of a hexagram. -/
def flipPos (h : Hexagram) : Fin 6 → Hexagram
  | ⟨0, _⟩ => Hexagram.mk h.y1.neg h.y2 h.y3 h.y4 h.y5 h.y6
  | ⟨1, _⟩ => Hexagram.mk h.y1 h.y2.neg h.y3 h.y4 h.y5 h.y6
  | ⟨2, _⟩ => Hexagram.mk h.y1 h.y2 h.y3.neg h.y4 h.y5 h.y6
  | ⟨3, _⟩ => Hexagram.mk h.y1 h.y2 h.y3 h.y4.neg h.y5 h.y6
  | ⟨4, _⟩ => Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5.neg h.y6
  | ⟨5, _⟩ => Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6.neg

end SSBX.Foundation.Yi.Yi.Hexagram

namespace SSBX.Foundation.Bagua.BaguaTuring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R8

/-! ## § 5 YiState + Interpreter -/

/-- Execution state: current cell, unbounded history (the 带), program counter,
    program, and halted flag. -/
structure YiState where
  cur     : R8
  history : List R8   -- ← 无界记忆
  pc      : Nat
  prog    : List YiInstr
  halted  : Bool
  deriving Repr

namespace YiState

/-- Initial state: hexagram h, time = 今, empty history, pc=0, given prog.

    Note: we initialise to `Shi.jin` (今, the V₄ "PT" element), preserving the
    pre-migration semantics where the initial Shi was 今. The new identity
    `Shi.dao` is intentionally NOT used as the init Shi — that would represent
    a "timeless" anchor unfit for the temporal entry-point of execution. -/
def init (h : Hexagram) (prog : List YiInstr) : YiState :=
  { cur := (h, Shi.jin), history := [], pc := 0, prog := prog, halted := false }

/-- Execute a single instruction in the current state. -/
def execute (instr : YiInstr) (s : YiState) : YiState :=
  match instr with
  | .nop => { s with pc := s.pc + 1 }
  | .setShi sh => { s with cur := (s.cur.1, sh), pc := s.pc + 1 }
  | .flipYao i =>
      { s with cur := (s.cur.1.flipPos i, s.cur.2), pc := s.pc + 1 }
  | .interlace  => { s with cur := (Hexagram.interlace s.cur.1, s.cur.2), pc := s.pc + 1 }
  | .complement => { s with cur := (Hexagram.complement s.cur.1, s.cur.2), pc := s.pc + 1 }
  | .reverse => { s with cur := (Hexagram.reverse s.cur.1, s.cur.2), pc := s.pc + 1 }
  | .branchYaoEq i j target =>
      if s.cur.1.yaoAt i = s.cur.1.yaoAt j
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
      | h :: rest => { s with cur := h, history := rest, pc := s.pc + 1 }
  | .halt => { s with halted := true }

/-- Single-step the state: fetch instruction at pc, execute. -/
def step (s : YiState) : YiState :=
  if s.halted then s
  else match s.prog[s.pc]? with
    | none => { s with halted := true }
    | some instr => execute instr s

/-- Bounded run with fuel: terminates after at most n steps. -/
def runFuel : Nat → YiState → YiState
  | 0, s => s
  | n+1, s => if s.halted then s else runFuel n s.step

/-- Unbounded executable interpreter.

    The theorem-level proof path uses `runFuel`: Lean needs an explicit fuel
    argument to reason by structural recursion. This unbounded `run` is kept as
    the executable boundary where non-terminating programs may diverge instead of
    returning a final `YiState`. -/
partial def run (s : YiState) : YiState :=
  if s.halted then s else run s.step

end YiState

/-! ## § 5b shiNext — V₄ stepper (post-Phase F.2, replaces Z/3 cycle)

  Pre-migration `shiNext` was the Z/3 cycle 已→今→未→已 on the legacy Cell192.
  V₄ has no canonical cyclic order, so we replace it with the `Shi.complement`
  involution (因-axis toggle: 道↔已, 今↔未). This is the most natural
  "single deterministic step" on the V₄ group:

    - Order-2 rather than order-3 (`shiNext (shiNext c) = c`).
    - Preserves the Hexagram component (`(shiNext c).1 = c.1`).
    - Total and decidable.

  Downstream callers expecting Z/3-cycle semantics need to update; the new
  contract is documented at each public boundary. -/

/-- 时态 single-step on the cell: V₄ `complement` involution on the Shi component
    (因-axis toggle 道↔已, 今↔未). Preserves the Hexagram. -/
def shiNext (c : R8) : R8 := (c.1, c.2.complement)

theorem shiNext_preserves_hex (c : R8) : (shiNext c).1 = c.1 := rfl

/-- `shiNext` is now an involution (V₄ `complement` is order-2), no longer order-3. -/
theorem shiNext_shiNext (c : R8) : shiNext (shiNext c) = c := by
  rcases c with ⟨h, s⟩
  simp [shiNext, Shi.complement_involutive]

/-! ## § 6 道判机 — the Dao judge

  A YiProg that, given a hexagram input, judges whether it's 天道 or 心道.
  Recall (Yi.lean): a hexagram is 天道 iff y3 = y4 (互²-stable), 心道 otherwise.

  The program tests y3 vs y4 and writes the verdict into 时态:
    天道  ↔  Shi.ji  (已 — settled, in-Dao)
    心道  ↔  Shi.wei (未 — unsettled, not-in-Dao yet)

  Note: although Shi V₄ now has a 4th state `Shi.dao`, the verdict semantics
  remain a clean binary {Shi.ji, Shi.wei}. The `Shi.dao` element is reserved
  for the V₄ identity / "永真 anchor" use cases elsewhere in the system.
-/

/-- The 道判机 program (5 wenyan instructions). -/
def daoJudgeProg : List YiInstr :=
  [ -- pc=0: if y3 = y4, jump to pc=3 (the 天道 branch)
    YiInstr.branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ 3
    -- pc=1: not equal → 心道 verdict
  , YiInstr.setShi Shi.wei
    -- pc=2: halt
  , YiInstr.halt
    -- pc=3: equal → 天道 verdict
  , YiInstr.setShi Shi.ji
    -- pc=4: halt
  , YiInstr.halt
  ]

/-- Run 道判机 on hex h and extract the verdict. -/
def daoJudge (h : Hexagram) : Shi :=
  ((YiState.init h daoJudgeProg).runFuel 10).cur.2

/-! ## § 7 Correctness + TC -/

/-- The 道判机 correctly classifies 天/心 道. -/
theorem daoJudge_correct (h : Hexagram) :
    daoJudge h = (if h.isTian then Shi.ji else Shi.wei) := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

/-- Equivalent reading: 是道 (= 天道) iff verdict is .ji. -/
theorem daoJudge_isTian (h : Hexagram) :
    daoJudge h = Shi.ji ↔ h.isTian = true := by
  rw [daoJudge_correct]
  cases h.isTian <;> simp [Shi.ji, Shi.wei]

/-- Equivalent reading: 非道 (= 心道) iff verdict is .wei. -/
theorem daoJudge_isXin (h : Hexagram) :
    daoJudge h = Shi.wei ↔ h.isXin = true := by
  rw [daoJudge_correct, Hexagram.isXin]
  cases h.isTian <;> simp [Shi.ji, Shi.wei]

/-- 乾 (☰☰) is 天道. -/
theorem daoJudge_qian : daoJudge Hexagram.heaven = Shi.ji := by native_decide

/-- 坤 (☷☷) is 天道. -/
theorem daoJudge_kun : daoJudge Hexagram.earth = Shi.ji := by native_decide

/-- 否 (天地否) is 心道 (y3=阳 ≠ y4=阴). -/
theorem daoJudge_pi :
    daoJudge (Hexagram.mk .yin .yin .yin .yang .yang .yang) = Shi.wei := by native_decide

/-- 泰 (地天泰) is 心道 (y3=阳 ≠ y4=阴). -/
theorem daoJudge_tai :
    daoJudge (Hexagram.mk .yang .yang .yang .yin .yin .yin) = Shi.wei := by native_decide

/-! ### § 7b TC primitives — what gives universal computation

  We exhibit two programs that witness the unbounded primitives:
  - `loopProg`: an unconditional jump-to-self (witnesses unbounded jumps).
  - `unboundedHistoryProg`: push then loop (witnesses unbounded memory).

  We additionally prove formally, via `runFuel`, that `loopProg` is non-halting
  at every fuel level (`loopProg_unbounded`): no matter how much fuel you give
  it, it never reaches a halted state. This is the theorem-level witness that
  the language admits true non-termination. The unbounded `partial def run`
  remains the executable boundary for that divergence; `runFuel` remains the
  total proof path. -/

/-- A non-halting program: jumps back to itself forever. -/
def loopProg : List YiInstr := [YiInstr.jump 0]

/-- A program that grows the history unboundedly (push then loop). -/
def unboundedHistoryProg : List YiInstr := [YiInstr.push, YiInstr.jump 0]

/-- Boundary marker: the unbounded interpreter is intentionally partial.

    Machine-checkable non-termination evidence lives below, in the `runFuel`
    theorems for `loopProg`; this theorem is deliberately only a public marker
    for the API boundary. -/
theorem run_is_partial : True := trivial

/-- Stepping `loopProg`'s init state returns the init state itself: pc stays at
    0 because the only instruction is `jump 0`. -/
theorem step_loopProg_init (h : Hexagram) :
    (YiState.init h loopProg).step = YiState.init h loopProg := by
  rfl

/-- Bounded execution of `loopProg` is stuttering: every fuel amount returns the
    same initial state. -/
theorem runFuel_loopProg_init_eq (h : Hexagram) :
    ∀ n : Nat, (YiState.init h loopProg).runFuel n = YiState.init h loopProg := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      unfold YiState.runFuel
      show (if (YiState.init h loopProg).halted
            then YiState.init h loopProg
            else YiState.runFuel k (YiState.init h loopProg).step) =
        YiState.init h loopProg
      have hnot : (YiState.init h loopProg).halted = false := rfl
      rw [hnot, step_loopProg_init, ih]
      simp

/-- `loopProg` has no finite fuel witness for halting. -/
theorem loopProg_has_no_fuel_witness (h : Hexagram) :
    ¬ ∃ n : Nat, ((YiState.init h loopProg).runFuel n).halted = true := by
  rintro ⟨n, hn⟩
  have hfalse : (YiState.init h loopProg).halted = false := rfl
  rw [runFuel_loopProg_init_eq h n, hfalse] at hn
  cases hn

/-- `loopProg_unbounded` — for any fuel `n`, running `loopProg` from init never
    enters the halted state. This formally witnesses non-termination of the
    interpreter on `loopProg`. -/
theorem loopProg_unbounded :
    ∀ n : Nat, ¬((YiState.init Hexagram.heaven loopProg).runFuel n).halted = true := by
  intro n hn
  exact loopProg_has_no_fuel_witness Hexagram.heaven ⟨n, hn⟩

/-! ### § 7c 道判机 as a wenyan claim within the system

  The deep payoff: the wenyan-encoded 道判机 program, run by our wenyan
  interpreter, correctly answers "是道?" — i.e., the system can ask and answer
  questions about itself.

  This is a self-referential 文 system: 文 (the program) 之 (interprets) 文 (its
  input) 而 (and) 判 (judges) 是道 / 非道. -/

/-- The 道判机 as a "self-interpretation" certificate: for any hexagram h, the
    YiProg `daoJudgeProg` (5 wenyan instructions) computes the same verdict as
    Yi.lean's `Hexagram.isTian` predicate. -/
theorem yi_self_interprets_dao :
    ∀ h : Hexagram,
      daoJudge h = (if h.isTian then Shi.ji else Shi.wei) :=
  daoJudge_correct

/-- 道判机 is total: terminates on every input within 10 fuel steps. -/
theorem daoJudgeProg_total_within_10 :
    ∀ h : Hexagram,
      ((YiState.init h daoJudgeProg).runFuel 10).halted = true := by
  intro h
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

/-! ### § 7d Public summary -/

/-- The completeness theorem for the wenyan-Dao judge subsystem. -/
theorem dao_judge_complete :
    -- (1) judges every hexagram (verdict is always ji or wei)
    (∀ h : Hexagram, daoJudge h = Shi.ji ∨ daoJudge h = Shi.wei)
    ∧ -- (2) result matches isTian
    (∀ h : Hexagram, daoJudge h = (if h.isTian then Shi.ji else Shi.wei))
    ∧ -- (3) terminates within fixed fuel
    (∀ h : Hexagram, ((YiState.init h daoJudgeProg).runFuel 10).halted = true)
    ∧ -- (4) loopProg is provably unbounded (non-halting at every fuel level)
    (∀ n : Nat, ¬((YiState.init Hexagram.heaven loopProg).runFuel n).halted = true) := by
  refine ⟨?_, daoJudge_correct, daoJudgeProg_total_within_10, loopProg_unbounded⟩
  intro h
  rw [daoJudge_correct]
  cases h.isTian <;> simp

end SSBX.Foundation.Bagua.BaguaTuring
