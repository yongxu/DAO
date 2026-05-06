/-
# CuoInvariance — YiInstr 之 cuo-不变性 + `kleene_recursion_axiom` 之不一致性

## Claim

Every `YiInstr` instruction is **cuo-equivariant** on cur (i.e., commutes with
yao-wise negation `cuo`).  As a consequence:

  ∀ (P : List YiInstr) (h : Hexagram), Halts P h ↔ Halts P (Hexagram.cuo h)

This is a STRUCTURAL property of `BaguaTuring`'s instruction set: branch
decisions (`branchYaoEq`) compare yaos *within* the current cell, which is
invariant under global yao-flip.  The other cur-modifying instructions (`hu`,
`cuo`, `zong`, `flipYao`) all commute with `cuo`.  `setShi` / `branchShiEq`
operate on Shi (untouched by yao-cuo).  History operations (`push` / `pop`)
preserve cuo-relations between cells.

## Implication

This invalidates the `kleene_recursion_axiom` in `GodelLi.lean`:
the axiom claims that for *every* Lean Bool function `decide`, a counter-example
program `D` exists.  But for non-cuo-invariant `decide` (e.g.,
`λ _ h => h.y1 = .yang`), such a `D` cannot exist — its halt profile would
have to disagree at `h` vs `cuo h`, but `Halts D` is forced cuo-invariant.

So `kleene_recursion_axiom` is **provably inconsistent in Lean**.

## What this file delivers

- `cuoCell`: lift `Hexagram.cuo` to `Cell192`
- `cuoState`: lift to `YiState` (cur + history are cuo'd)
- `cuoState_step`: stepwise cuo-equivariance (the core invariant)
- `cuoState_runFuel`: cuo-equivariance under arbitrary fuel
- `halts_cuo_invariant`: the main symmetry of Halts
- `kleene_recursion_axiom_inconsistent`: derives `False` from the axiom

This RESOLVES P17 by showing that `kleene_recursion_axiom` cannot be a theorem
without changes to the axiom statement or the YiInstr language itself.

## Proposed fix

Either:
1.  Replace `KleeneInverter` with a `CuoInvariant`-restricted version, OR
2.  Extend `YiInstr` with a cuo-symmetry-breaking instruction (e.g.,
    `setYao : Fin 6 → Yao → YiInstr`) — this changes the language semantics.

For now, this file documents the inconsistency and provides the proof.
-/
import SSBX.Foundation.GodelLi

namespace SSBX.Foundation.CuoInvariance

open SSBX.Foundation.Yi
open SSBX.Foundation.Cell192
open SSBX.Foundation.BaguaTuring
open SSBX.Foundation.GodelLi

/-! ## § 1 cuo applied to Cell192 and YiState -/

/-- Apply `cuo` to a Cell192's hexagram component (Shi unchanged). -/
def cuoCell (c : Cell192) : Cell192 := (c.1.cuo, c.2)

/-- Cuo is involutive on cells. -/
theorem cuoCell_cuoCell (c : Cell192) : cuoCell (cuoCell c) = c := by
  unfold cuoCell
  simp [Hexagram.cuo_cuo]

/-- Apply cuo to all hexagrams in a YiState (cur + history). -/
def cuoState (s : YiState) : YiState :=
  { cur := cuoCell s.cur
    history := s.history.map cuoCell
    pc := s.pc
    prog := s.prog
    halted := s.halted }

/-- cuoState preserves the halted flag. -/
theorem cuoState_halted (s : YiState) : (cuoState s).halted = s.halted := rfl

/-- cuoState preserves pc. -/
theorem cuoState_pc (s : YiState) : (cuoState s).pc = s.pc := rfl

/-- cuoState preserves prog. -/
theorem cuoState_prog (s : YiState) : (cuoState s).prog = s.prog := rfl

/-! ## § 2 Hexagram-level cuo-equivariance lemmas -/

/-- yaoAt of cuo'd hex = neg of yaoAt. -/
theorem yaoAt_cuo (h : Hexagram) (i : Fin 6) :
    (h.cuo).yaoAt i = (h.yaoAt i).neg := by
  rcases i with ⟨n, hn⟩
  match n, hn with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl

/-- yaoEq is preserved under cuo: comparing two yaos in `h.cuo` matches in `h`. -/
theorem yaoEq_cuo (h : Hexagram) (i j : Fin 6) :
    ((h.cuo).yaoAt i = (h.cuo).yaoAt j) ↔ (h.yaoAt i = h.yaoAt j) := by
  rw [yaoAt_cuo, yaoAt_cuo]
  cases (h.yaoAt i) <;> cases (h.yaoAt j) <;> decide

/-- flipPos commutes with cuo. -/
theorem flipPos_cuo (h : Hexagram) (i : Fin 6) :
    (h.cuo).flipPos i = (h.flipPos i).cuo := by
  rcases i with ⟨n, hn⟩
  match n, hn with
  | 0, _ => simp [Hexagram.flipPos, Hexagram.cuo, Yao.neg_neg]
  | 1, _ => simp [Hexagram.flipPos, Hexagram.cuo, Yao.neg_neg]
  | 2, _ => simp [Hexagram.flipPos, Hexagram.cuo, Yao.neg_neg]
  | 3, _ => simp [Hexagram.flipPos, Hexagram.cuo, Yao.neg_neg]
  | 4, _ => simp [Hexagram.flipPos, Hexagram.cuo, Yao.neg_neg]
  | 5, _ => simp [Hexagram.flipPos, Hexagram.cuo, Yao.neg_neg]

/-- hu commutes with cuo. -/
theorem hu_cuo (h : Hexagram) : (h.cuo).hu = (h.hu).cuo := by
  cases h; rfl

/-- zong commutes with cuo. -/
theorem zong_cuo (h : Hexagram) : (h.cuo).zong = (h.zong).cuo := by
  cases h; rfl

/-! ## § 3 Step-level cuo-equivariance

  Key invariant: `cuoState (s.step) = (cuoState s).step`.

  Proof strategy: we work directly with `step`'s definition (an if-then-else
  plus a match), and reduce both sides via case analysis on the active
  instruction. -/

/-- Helper: when not halted, both cuo'd-then-stepped and stepped-then-cuo'd
    fall through to the prog[pc]? branch with the SAME index. -/
private theorem step_not_halted_helper (s : YiState) (h_nh : s.halted = false) :
    s.step = (match s.prog[s.pc]? with
              | none => { s with halted := true }
              | some instr => YiState.execute instr s) := by
  unfold YiState.step
  rw [h_nh]
  rfl

/-- Helper for cuoState's step. -/
private theorem cuoState_step_not_halted (s : YiState) (h_nh : s.halted = false) :
    (cuoState s).step =
      (match s.prog[s.pc]? with
       | none => { (cuoState s) with halted := true }
       | some instr => YiState.execute instr (cuoState s)) := by
  unfold YiState.step
  show (if (cuoState s).halted = true then cuoState s
        else match (cuoState s).prog[(cuoState s).pc]? with
             | none => { (cuoState s) with halted := true }
             | some instr => YiState.execute instr (cuoState s))
       = match s.prog[s.pc]? with
         | none => { (cuoState s) with halted := true }
         | some instr => YiState.execute instr (cuoState s)
  rw [show (cuoState s).halted = false from h_nh]
  rfl

/-- The CORE INVARIANT: `step` commutes with `cuoState`.  By case analysis on
    the current YiInstr.  This is the lemma that captures cuo as a symmetry of
    YiInstr's transition relation. -/
theorem cuoState_step (s : YiState) :
    cuoState (s.step) = (cuoState s).step := by
  by_cases h_halt : s.halted = true
  · -- halted: step is identity
    have h_halt' : (cuoState s).halted = true := h_halt
    have lhs : s.step = s := by unfold YiState.step; simp [h_halt]
    have rhs : (cuoState s).step = cuoState s := by
      unfold YiState.step; simp [h_halt']
    rw [lhs, rhs]
  · -- not halted
    have h_nh : s.halted = false := by
      cases hh : s.halted
      · rfl
      · exact (h_halt hh).elim
    rw [step_not_halted_helper s h_nh]
    rw [cuoState_step_not_halted s h_nh]
    -- Now goal: cuoState (match s.prog[s.pc]? with ...) = match s.prog[s.pc]? with ...
    rcases h_inst : s.prog[s.pc]? with _ | i
    · -- prog[pc] = none: both halt
      simp [cuoState]
    · -- prog[pc] = some i
      simp
      cases i with
      | nop      => rfl
      | setShi sh => rfl
      | flipYao i =>
        unfold YiState.execute cuoState cuoCell
        simp [flipPos_cuo]
      | hu  =>
        unfold YiState.execute cuoState cuoCell
        simp [hu_cuo]
      | cuo =>
        unfold YiState.execute cuoState cuoCell
        simp [Hexagram.cuo_cuo]
      | zong =>
        unfold YiState.execute cuoState cuoCell
        simp [zong_cuo]
      | branchYaoEq i j t =>
        unfold YiState.execute cuoState cuoCell
        simp only
        by_cases h_eq : s.cur.1.yaoAt i = s.cur.1.yaoAt j
        · rw [if_pos h_eq, if_pos ((yaoEq_cuo s.cur.1 i j).mpr h_eq)]
        · rw [if_neg h_eq, if_neg (fun h => h_eq ((yaoEq_cuo s.cur.1 i j).mp h))]
      | branchShiEq sh t =>
        unfold YiState.execute cuoState cuoCell
        simp only
        by_cases h_eq : s.cur.2 = sh
        · rw [if_pos h_eq, if_pos h_eq]
        · rw [if_neg h_eq, if_neg h_eq]
      | jump t => rfl
      | push =>
        unfold YiState.execute cuoState cuoCell
        simp
      | pop =>
        unfold YiState.execute cuoState
        cases h_hist : s.history with
        | nil => simp
        | cons head rest => simp [cuoCell]
      | halt => rfl

/-! ## § 4 runFuel cuo-equivariance + halts cuo-invariance -/

/-- runFuel commutes with cuoState (for any fuel). -/
theorem cuoState_runFuel (s : YiState) (n : Nat) :
    cuoState (s.runFuel n) = (cuoState s).runFuel n := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    show cuoState (s.runFuel (k+1)) = (cuoState s).runFuel (k+1)
    unfold YiState.runFuel
    by_cases h_halt : s.halted = true
    · have h_halt' : (cuoState s).halted = true := h_halt
      simp [h_halt, h_halt']
    · have h_halt' : s.halted = false := by
        cases hh : s.halted
        · rfl
        · exact (h_halt hh).elim
      have h_halt_cuo : (cuoState s).halted = false := h_halt'
      simp only [h_halt', h_halt_cuo]
      rw [← cuoState_step]
      exact ih s.step

/-- The init state is cuo-equivariant: cuoState (init h P) = init (cuo h) P. -/
theorem cuoState_init (h : Hexagram) (P : List YiInstr) :
    cuoState (YiState.init h P) = YiState.init h.cuo P := rfl

/-- Forward direction: if Halts P h, then Halts P h.cuo. -/
private theorem halts_cuo_forward (P : List YiInstr) (h : Hexagram) :
    Halts P h → Halts P h.cuo := by
  intro ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [← cuoState_init, ← cuoState_runFuel, cuoState_halted]
  exact hn

/-- **MAIN THEOREM**: Halts is cuo-invariant — running P from h halts iff
    running P from cuo h halts. -/
theorem halts_cuo_invariant (P : List YiInstr) (h : Hexagram) :
    Halts P h ↔ Halts P h.cuo := by
  refine ⟨halts_cuo_forward P h, fun hyp => ?_⟩
  have := halts_cuo_forward P h.cuo hyp
  rwa [Hexagram.cuo_cuo] at this

/-! ## § 5 Inconsistency of `kleene_recursion_axiom` -/

/-- A specific non-cuo-invariant Bool decider: outputs Bool from h.y1's value.
    `decide _ h = true` iff h.y1 is yang.  Cuo flips y1, so this distinguishes
    h from cuo h. -/
def nonCuoInvariantDecide : List YiInstr → Hexagram → Bool :=
  fun _ h => match h.y1 with | .yang => true | .yin => false

/-- On `qian` (y1 = yang), decide outputs `true`. -/
theorem nonCuoInvariantDecide_qian (P : List YiInstr) :
    nonCuoInvariantDecide P Hexagram.qian = true := rfl

/-- On `kun = cuo qian` (y1 = yin), decide outputs `false`. -/
theorem nonCuoInvariantDecide_kun (P : List YiInstr) :
    nonCuoInvariantDecide P Hexagram.kun = false := rfl

/-- `kun = cuo qian` (proved by definitional equality). -/
theorem kun_eq_cuo_qian : Hexagram.kun = Hexagram.qian.cuo := rfl

/-- **MAIN INCONSISTENCY THEOREM**: `kleene_recursion_axiom` is incompatible
    with `halts_cuo_invariant`.  Specifically, applying the axiom to the
    non-cuo-invariant decider yields `False`.

    Sketch: take `decide _ h = (h.y1 = yang)`.  KleeneInverter gives D with
    `Halts D h ↔ decide D h = false`.  At `h = qian`: decide = true, so
    ¬Halts D qian.  At `h = kun = cuo qian`: decide = false, so Halts D kun.
    But cuo-invariance gives `Halts D qian ↔ Halts D kun`.  Contradiction. -/
theorem kleene_recursion_axiom_inconsistent : False := by
  obtain ⟨D, hD⟩ := kleene_recursion_axiom nonCuoInvariantDecide
  have h_qian : Halts D Hexagram.qian ↔ nonCuoInvariantDecide D Hexagram.qian = false :=
    hD Hexagram.qian
  have h_kun : Halts D Hexagram.kun ↔ nonCuoInvariantDecide D Hexagram.kun = false :=
    hD Hexagram.kun
  rw [nonCuoInvariantDecide_qian] at h_qian
  rw [nonCuoInvariantDecide_kun] at h_kun
  -- h_qian : Halts D qian ↔ true = false
  have h_not_qian : ¬ Halts D Hexagram.qian := by
    intro hq
    exact Bool.noConfusion (h_qian.mp hq)
  -- h_kun : Halts D kun ↔ false = false → Halts D kun
  have h_kun_holds : Halts D Hexagram.kun := h_kun.mpr rfl
  -- cuo-invariance: Halts D qian ↔ Halts D kun
  have h_cuo_inv : Halts D Hexagram.qian ↔ Halts D Hexagram.kun := by
    rw [kun_eq_cuo_qian]
    exact halts_cuo_invariant D Hexagram.qian
  exact h_not_qian (h_cuo_inv.mpr h_kun_holds)

/-! ## § 6 Public summary -/

/-- The cuo-invariance bundle. -/
theorem cuo_invariance_summary :
    -- (1) Halts is cuo-invariant
    (∀ P h, Halts P h ↔ Halts P h.cuo)
    ∧ -- (2) `kleene_recursion_axiom` is inconsistent with Lean
    False :=
  ⟨halts_cuo_invariant, kleene_recursion_axiom_inconsistent⟩

end SSBX.Foundation.CuoInvariance
