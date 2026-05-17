import SSBX.Foundation.Atlas.Yi.Classical.Computation.BaguaTuring

/-!
# OperatorInstructionSemantics — L0 instruction semantic clause ledger

This file records a compact, parameter-erased ledger for the 12 `YiInstr`
constructors from `BaguaTuring`.  Pure/current-cell instructions expose a
`R8 → R8` effect and are checked against `YiState.execute` on `cur`.
State/control instructions are recorded at state/control level and intentionally
do not expose a cell endomap.
-/

namespace SSBX.Text.OperatorInstructionSemantics

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring

/-! ## § 1 Clause kinds -/

/-- Parameter-erased semantic clause kind for each `YiInstr` constructor. -/
inductive L0InstructionClauseKind where
  | nop
  | setShi
  | flipYao
  | interlace
  | complement
  | reverse
  | branchYaoEq
  | branchShiEq
  | jump
  | push
  | pop
  | halt
  -- v2 (2026-05-17)
  | branchYaoYang
  deriving Repr, DecidableEq, BEq

namespace L0InstructionClauseKind

/-- Concrete constructor erasure into the 13 clause kinds (v2). -/
def ofInstr : YiInstr → L0InstructionClauseKind
  | .nop => .nop
  | .setShi _ => .setShi
  | .flipYao _ => .flipYao
  | .interlace => .interlace
  | .complement => .complement
  | .reverse => .reverse
  | .branchYaoEq _ _ _ => .branchYaoEq
  | .branchShiEq _ _ => .branchShiEq
  | .jump _ => .jump
  | .push => .push
  | .pop => .pop
  | .halt => .halt
  | .branchYaoYang _ _ => .branchYaoYang  -- v2

/-- A representative concrete instruction for each parameter-erased kind. -/
def sample : L0InstructionClauseKind → YiInstr
  | .nop => .nop
  | .setShi => .setShi Shi.jin
  | .flipYao => .flipYao ⟨0, by decide⟩
  | .interlace => .interlace
  | .complement => .complement
  | .reverse => .reverse
  | .branchYaoEq => .branchYaoEq ⟨0, by decide⟩ ⟨1, by decide⟩ 0
  | .branchShiEq => .branchShiEq Shi.jin 0
  | .jump => .jump 0
  | .push => .push
  | .pop => .pop
  | .halt => .halt
  | .branchYaoYang => .branchYaoYang ⟨0, by decide⟩ 0  -- v2

theorem ofInstr_sample (k : L0InstructionClauseKind) :
    ofInstr k.sample = k := by
  cases k <;> rfl

end L0InstructionClauseKind

/-- The complete L0 instruction clause-kind ledger (v2 has 13). -/
def l0InstructionClauseKinds : List L0InstructionClauseKind :=
  [.nop, .setShi, .flipYao, .interlace, .complement, .reverse,
   .branchYaoEq, .branchShiEq, .jump, .push, .pop, .halt,
   .branchYaoYang]  -- v2

theorem l0InstructionClauseKinds_length :
    l0InstructionClauseKinds.length = 13 := by
  native_decide

theorem l0InstructionClauseKinds_nodup :
    l0InstructionClauseKinds.Nodup := by
  native_decide

/-! ## § 2 Semantic level and ledger rows -/

/-- Coarse semantic level: either a current-cell endomap or state/control logic. -/
inductive InstructionSemanticLevel where
  | currentCell
  | stateControl
  deriving Repr, DecidableEq, BEq

def clauseLevel : L0InstructionClauseKind → InstructionSemanticLevel
  | .nop => .currentCell
  | .setShi => .currentCell
  | .flipYao => .currentCell
  | .interlace => .currentCell
  | .complement => .currentCell
  | .reverse => .currentCell
  | .branchYaoEq => .stateControl
  | .branchShiEq => .stateControl
  | .jump => .stateControl
  | .push => .stateControl
  | .pop => .stateControl
  | .halt => .stateControl
  | .branchYaoYang => .stateControl  -- v2 (control flow)

def isCurrentCellClause (k : L0InstructionClauseKind) : Bool :=
  clauseLevel k == InstructionSemanticLevel.currentCell

def isStateControlClause (k : L0InstructionClauseKind) : Bool :=
  clauseLevel k == InstructionSemanticLevel.stateControl

/-- Ledger row for one parameter-erased instruction clause. -/
structure L0InstructionSemanticClause where
  kind : L0InstructionClauseKind
  level : InstructionSemanticLevel
  exposesCellEndomap : Bool
  deriving Repr

def semanticClauseFor (k : L0InstructionClauseKind) : L0InstructionSemanticClause :=
  { kind := k
  , level := clauseLevel k
  , exposesCellEndomap := isCurrentCellClause k }

/-- Complete L0 instruction semantic clause ledger. -/
def l0InstructionSemanticClauses : List L0InstructionSemanticClause :=
  l0InstructionClauseKinds.map semanticClauseFor

theorem l0InstructionSemanticClauses_length :
    l0InstructionSemanticClauses.length = 13 := by
  rw [l0InstructionSemanticClauses, List.length_map, l0InstructionClauseKinds_length]

theorem currentCellClauseKinds_length :
    (l0InstructionClauseKinds.filter isCurrentCellClause).length = 6 := by
  native_decide

theorem stateControlClauseKinds_length :
    (l0InstructionClauseKinds.filter isStateControlClause).length = 7 := by  -- v2: +branchYaoYang
  native_decide

/-! ## § 3 Concrete current-cell endomaps -/

/--
Concrete current-cell effect for instructions that operate purely on `cur`.
State/control instructions deliberately return `none`.
-/
def instructionCellEndomap? : YiInstr → Option (R8 → R8)
  | .nop => some id
  | .setShi sh => some (fun c => (c.1, sh))
  | .flipYao i => some (fun c => (c.1.flipPos i, c.2))
  | .interlace => some R8.hexHu
  | .complement => some R8.hexCuo
  | .reverse => some R8.hexZong
  | .branchYaoEq _ _ _ => none
  | .branchShiEq _ _ => none
  | .jump _ => none
  | .push => none
  | .pop => none
  | .halt => none
  | .branchYaoYang _ _ => none  -- v2 (control flow, no cell endomap)

theorem nop_cell_effect_matches_execute (s : YiState) :
    (YiState.execute .nop s).cur = id s.cur := by
  rfl

theorem setShi_cell_effect_matches_execute (sh : Shi) (s : YiState) :
    (YiState.execute (.setShi sh) s).cur = (s.cur.1, sh) := by
  rfl

theorem flipYao_cell_effect_matches_execute (i : Fin 6) (s : YiState) :
    (YiState.execute (.flipYao i) s).cur = (s.cur.1.flipPos i, s.cur.2) := by
  rfl

theorem hu_cell_effect_matches_execute (s : YiState) :
    (YiState.execute .interlace s).cur = R8.hexHu s.cur := by
  rfl

theorem cuo_cell_effect_matches_execute (s : YiState) :
    (YiState.execute .complement s).cur = R8.hexCuo s.cur := by
  rfl

theorem zong_cell_effect_matches_execute (s : YiState) :
    (YiState.execute .reverse s).cur = R8.hexZong s.cur := by
  rfl

theorem instructionCellEndomap?_matches_execute
    (instr : YiInstr) (f : R8 → R8) (s : YiState) :
    instructionCellEndomap? instr = some f →
      (YiState.execute instr s).cur = f s.cur := by
  cases instr <;> intro h <;> simp [instructionCellEndomap?] at h ⊢
  · rw [← h]
    rfl
  · rw [← h]
    rfl
  · rw [← h]
    rfl
  · rw [← h]
    rfl
  · rw [← h]
    rfl
  · rw [← h]
    rfl

/-! ## § 4 State/control non-endomap clauses -/

theorem branchYaoEq_no_cell_endomap (i j : Fin 6) (target : Nat) :
    instructionCellEndomap? (.branchYaoEq i j target) = none := by
  rfl

theorem branchShiEq_no_cell_endomap (sh : Shi) (target : Nat) :
    instructionCellEndomap? (.branchShiEq sh target) = none := by
  rfl

theorem jump_no_cell_endomap (target : Nat) :
    instructionCellEndomap? (.jump target) = none := by
  rfl

theorem push_no_cell_endomap :
    instructionCellEndomap? .push = none := by
  rfl

theorem pop_no_cell_endomap :
    instructionCellEndomap? .pop = none := by
  rfl

theorem halt_no_cell_endomap :
    instructionCellEndomap? .halt = none := by
  rfl

/-- v2: branchYaoYang 不暴露 cell endomap (control flow only). -/
theorem branchYaoYang_no_cell_endomap (i : Fin 6) (target : Nat) :
    instructionCellEndomap? (.branchYaoYang i target) = none := by
  rfl

theorem stateControlClause_no_cell_endomap
    (instr : YiInstr)
    (h : clauseLevel (L0InstructionClauseKind.ofInstr instr) =
      InstructionSemanticLevel.stateControl) :
    instructionCellEndomap? instr = none := by
  cases instr <;> simp [L0InstructionClauseKind.ofInstr, clauseLevel] at h
  all_goals rfl

/--
Summary: there are exactly 13 L0 clause kinds (v2 加入 branchYaoYang).
Six expose current-cell endomaps matching `YiState.execute` on `cur`;
seven are state/control clauses and do not expose a `R8` endomap.
-/
theorem l0_instruction_semantic_clause_summary :
    l0InstructionClauseKinds.length = 13
    ∧ l0InstructionClauseKinds.Nodup
    ∧ l0InstructionSemanticClauses.length = 13
    ∧ (l0InstructionClauseKinds.filter isCurrentCellClause).length = 6
    ∧ (l0InstructionClauseKinds.filter isStateControlClause).length = 7
    ∧ (∀ instr : YiInstr, ∀ f : R8 → R8, ∀ s : YiState,
        instructionCellEndomap? instr = some f →
          (YiState.execute instr s).cur = f s.cur)
    ∧ (∀ instr : YiInstr,
        clauseLevel (L0InstructionClauseKind.ofInstr instr) =
          InstructionSemanticLevel.stateControl →
            instructionCellEndomap? instr = none) := by
  exact
    ⟨ l0InstructionClauseKinds_length
    , l0InstructionClauseKinds_nodup
    , l0InstructionSemanticClauses_length
    , currentCellClauseKinds_length
    , stateControlClauseKinds_length
    , instructionCellEndomap?_matches_execute
    , stateControlClause_no_cell_endomap
    ⟩

end SSBX.Text.OperatorInstructionSemantics
