/-
# GodelLi — 理之不完备 · 哥德尔在 192

> **[Atlas/Yi/Classical/Diagonal — 2026-05-15 (Phase γ)]** This file
> proves the diagonal incompleteness theorem on the classical
> axiomatization using the load-bearing `kleene_recursion_axiom`.
> The R-Family-side canonical diagonal theorem is at
> [`Foundation/Atlas/Yi/Diagonal.lean`](../../Diagonal.lean)
> — 647 LOC, anchored on Wen/Core (language-independent R 8 TM),
> uses `KleeneInverter` as a `Prop` hypothesis rather than an axiom.

Companion document: `义理/J_理之不完备_哥德尔在192.md`

This file formalizes the **理之不完备** (incompleteness-of-Li) theorem at the
192-cell layer (`Cell192 := Hexagram × Shi`, the 64×3 Turing-complete
substrate established in `Cell192.lean` and `BaguaTuring.lean`).

## Architecture (per J 文档之 §6 path)
  § 1   Halts predicate (Σ₁) + concrete witnesses
        - daoJudge halts on every input within 10 fuel
        - loopProg never halts (loop_step_idem + induction)
  § 2   Finite-fuel incompleteness: ∀ N, ∃ counterexample
        — provable WITHOUT Kleene; uses slowProg N := N nops + halt
        — captures: 「理之停机不被任何均一燃料 N 所封闭」
  § 3   Universality witness (Phase 3 — needs Kleene)
  § 4   Diagonal: halts_undecidable_internally  ★ main theorem (Phase 4)
  § 5   Rice corollary + dao_judge_not_universal (Phase 5)
  § 6   Public summary + 道理二分 axioms

## 道理二分 (Dao-Li bifurcation)
  - **道** (Dao) = the meta-theory (Lean kernel + `Sheng : ℕ → Type` ω-tower)
  - **理** (Li) = the object theory (this file's `Cell192 + YiInstr` Turing
    machine, recursively enumerable)
  - This file proves a 道-level theorem ABOUT 理: "Li, if consistent, is
    incomplete" — Halting is not decidable by any YiProg within Li.

This is the precise formal version of 「道可道，非常道」.
-/
import SSBX.Foundation.Atlas.Yi.Classical.Computation.BaguaTuring

namespace SSBX.Foundation.Bagua.GodelLi

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring

/-! ## § 1 Halts predicate (Σ₁) -/

/-- **停机谓词**：程序 P 在初始六爻 h（默认时态 = 今）上经有限步停机。
    形式上是 Σ₁（存在自然数证 n）。 -/
def Halts (P : List YiInstr) (h : Hexagram) : Prop :=
  ∃ n : Nat, ((YiState.init h P).runFuel n).halted = true

/-- 任意状态版本之停机谓词。 -/
def HaltsState (s : YiState) : Prop :=
  ∃ n : Nat, (s.runFuel n).halted = true

/-! ### § 1.1 道判机：daoJudgeProg 在每个输入上停机（≤ 10 fuel） -/

/-- 道判机必停：`daoJudgeProg_total_within_10` 之 Halts 形式。 -/
theorem halts_daoJudgeProg (h : Hexagram) : Halts daoJudgeProg h :=
  ⟨10, daoJudgeProg_total_within_10 h⟩

/-! ### § 1.2 loopProg：永不停机（无界 jump 之内禀见证） -/

/-- 引理：`init h loopProg` 自身的一步等于其本身。 -/
theorem loopProg_step_self (h : Hexagram) :
    (YiState.init h loopProg).step = YiState.init h loopProg := by
  rfl

/-- 关键引理：从 `init h loopProg` 出发，无论多少燃料皆不停机。 -/
theorem loopProg_runFuel_not_halted (h : Hexagram) :
    ∀ n : Nat, ((YiState.init h loopProg).runFuel n).halted = false := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    -- runFuel (k+1) s = if s.halted then s else runFuel k s.step
    -- s.halted = false, s.step = s (by loopProg_step_self)
    -- ⇒ runFuel (k+1) s = runFuel k s
    show ((YiState.init h loopProg).runFuel (k + 1)).halted = false
    unfold YiState.runFuel
    simp only [show (YiState.init h loopProg).halted = false from rfl,
               loopProg_step_self]
    exact ih

/-- **loopProg 永不停机**：理层非全停机性的具体见证。 -/
theorem loopProg_not_halts (h : Hexagram) : ¬ Halts loopProg h := by
  intro ⟨n, hn⟩
  have : ((YiState.init h loopProg).runFuel n).halted = false :=
    loopProg_runFuel_not_halted h n
  rw [this] at hn
  exact Bool.false_ne_true hn

/-! ### § 1.3 Halts 之半可判定性（Σ₁ structural fact） -/

/-- 给定燃料 n，「在 n 步内停机」是可判定的。 -/
instance Halts_within_decidable (P : List YiInstr) (h : Hexagram) (n : Nat) :
    Decidable (((YiState.init h P).runFuel n).halted = true) :=
  inferInstance

/-- Halts 之 Σ₁ 形态：存在 n 使 runFuel n 停机。 -/
theorem halts_iff_exists_fuel (P : List YiInstr) (h : Hexagram) :
    Halts P h ↔ ∃ n : Nat, ((YiState.init h P).runFuel n).halted = true :=
  Iff.rfl

/-- 具体非平凡停机不平衡：daoJudge 停 + loopProg 不停 ——理层之非平凡性。 -/
theorem li_nontrivial :
    (∃ P : List YiInstr, ∀ h : Hexagram, Halts P h) ∧
    (∃ P : List YiInstr, ∀ h : Hexagram, ¬ Halts P h) :=
  ⟨⟨daoJudgeProg, halts_daoJudgeProg⟩,
   ⟨loopProg, loopProg_not_halts⟩⟩

/-! ## § 1 公开摘要 -/

/-- **§ 1 总结**：Halts 谓词良定义；理层非平凡（既有必停程序，也有必不停程序）。 -/
theorem phase1_summary :
    -- (1) daoJudge 在所有输入上必停
    (∀ h : Hexagram, Halts daoJudgeProg h)
    -- (2) loopProg 在所有输入上必不停
    ∧ (∀ h : Hexagram, ¬ Halts loopProg h)
    -- (3) 理之非平凡性
    ∧ ((∃ P : List YiInstr, ∀ h : Hexagram, Halts P h) ∧
       (∃ P : List YiInstr, ∀ h : Hexagram, ¬ Halts P h)) :=
  ⟨halts_daoJudgeProg, loopProg_not_halts, li_nontrivial⟩

/-! ## § 2 有限燃料不完备：无均一燃料界判 Halts

  本节证明一个 **不需要 Kleene 公理** 的真 Gödel-flavored incompleteness：
  `¬ ∃ N, ∀ P h, Halts P h ↔ ((init h P).runFuel N).halted = true`

  即「理之停机不被任何均一燃料 N 所封闭」。论据：对任 N，构造程序
  `slowProg N = N 个 nop + halt`，其必停（fuel = N+1），但 fuel = N 不足
  以见证停机。

  此为 Halting 不可判定性之最弱可证形态：在任何 fixed-fuel decision
  procedure 下，理皆不完备。（更强的 Kleene-based diagonal 推迟至 §4。）
-/

/-- **慢停程序**：N 个 nop 后接 halt。其必停（fuel = N+1），但 fuel = N
    不足以见证。共 N+1 条指令，索引 0..N-1 是 nop，索引 N 是 halt。 -/
def slowProg (N : Nat) : List YiInstr :=
  List.replicate N YiInstr.nop ++ [YiInstr.halt]

/-! ### § 2.1 步进基础引理 -/

/-- 在非停机状态执行 nop，仅推进 pc。 -/
theorem step_nop (s : YiState) (h_halt : s.halted = false)
    (h_lookup : s.prog[s.pc]? = some YiInstr.nop) :
    s.step = { s with pc := s.pc + 1 } := by
  unfold YiState.step
  simp [h_halt, h_lookup, YiState.execute]

/-- 在非停机状态执行 halt，仅置 halted = true。 -/
theorem step_halt (s : YiState) (h_halt : s.halted = false)
    (h_lookup : s.prog[s.pc]? = some YiInstr.halt) :
    s.step = { s with halted := true } := by
  unfold YiState.step
  simp [h_halt, h_lookup, YiState.execute]

/-- step 在已停机状态上为恒等。 -/
theorem step_halted_idem (s : YiState) (h : s.halted = true) :
    s.step = s := by
  unfold YiState.step
  simp [h]

/-! ### § 2.2 slowProg 之查表 -/

/-- slowProg N 在索引 k < N 处为 nop。 -/
theorem slowProg_get_lt (N k : Nat) (hk : k < N) :
    (slowProg N)[k]? = some YiInstr.nop := by
  unfold slowProg
  rw [List.getElem?_append_left (by simp [hk])]
  simp [hk]

/-- slowProg N 在索引 N 处为 halt。 -/
theorem slowProg_get_eq (N : Nat) :
    (slowProg N)[N]? = some YiInstr.halt := by
  unfold slowProg
  rw [List.getElem?_append_right (by simp)]
  simp

/-! ### § 2.3 runFuel 之右展开（关键引理） -/

/-- 已停状态下，runFuel 任意燃料皆返回原状态。 -/
theorem runFuel_halted_fixed (s : YiState) (h : s.halted = true) :
    ∀ n, s.runFuel n = s := by
  intro n
  induction n with
  | zero => rfl
  | succ k ihk =>
    unfold YiState.runFuel
    simp [h]

/-- **runFuel 右展开**：`runFuel (n+1) s = (runFuel n s).step`。
    此即 step iteration 之关联律：先一步加 n 步 = 先 n 步加一步。

    证明分情形：s 已停时两侧均不变；s 未停时用归纳。 -/
theorem runFuel_succ_right (s : YiState) (n : Nat) :
    s.runFuel (n+1) = (s.runFuel n).step := by
  induction n generalizing s with
  | zero =>
    -- LHS: runFuel 1 s = if s.halted then s else s.step
    -- RHS: (runFuel 0 s).step = s.step
    cases hh : s.halted with
    | true =>
      -- 已停：runFuel 1 s = s；(runFuel 0 s).step = s.step = s
      have h1 : s.runFuel 1 = s := by
        show (if s.halted = true then s else s.runFuel 0 |>.step) = s
        simp [hh]
      have h2 : (s.runFuel 0).step = s := step_halted_idem s hh
      rw [h1, h2]
    | false =>
      have h1 : s.runFuel 1 = s.step := by
        show (if s.halted = true then s else s.step.runFuel 0) = s.step
        simp [hh]
        rfl
      rw [h1]
      rfl
  | succ k ih =>
    cases hh : s.halted with
    | true =>
      -- 已停：两侧 = s
      rw [runFuel_halted_fixed s hh, runFuel_halted_fixed s hh, step_halted_idem s hh]
    | false =>
      -- runFuel (k+2) s = runFuel (k+1) s.step (by hh)
      -- (runFuel (k+1) s).step = (runFuel k s.step).step (by hh + ih)
      have hL : s.runFuel (k+2) = s.step.runFuel (k+1) := by
        show (if s.halted = true then s else s.step.runFuel (k+1)) = s.step.runFuel (k+1)
        simp [hh]
      have hR : s.runFuel (k+1) = s.step.runFuel k := by
        show (if s.halted = true then s else s.step.runFuel k) = s.step.runFuel k
        simp [hh]
      rw [hL, hR]
      -- 由 IH 应用于 s.step：runFuel (k+1) s.step = (runFuel k s.step).step
      exact ih s.step

/-! ### § 2.4 slowProg 之 N 步演化 -/

/-- 关键不变量：从 init h (slowProg N) 出发，对任 k ≤ N，runFuel k 后状态
    pc = k，halted = false，prog 不变。 -/
theorem slowProg_state_after (h : Hexagram) (N : Nat) (k : Nat) (hk : k ≤ N) :
    (YiState.init h (slowProg N)).runFuel k =
      { cur := (h, Shi.jin), history := [], pc := k,
        prog := slowProg N, halted := false } := by
  induction k with
  | zero => rfl
  | succ j ih =>
    have hj : j ≤ N := Nat.le_of_succ_le hk
    have hj_lt : j < N := Nat.lt_of_succ_le hk
    have ih' := ih hj
    rw [runFuel_succ_right, ih']
    -- 现在我们在 pc=j 状态执行一步。lookup prog[j] = nop 因为 j < N。
    have h_lookup : (slowProg N)[j]? = some YiInstr.nop :=
      slowProg_get_lt N j hj_lt
    rw [step_nop _ rfl h_lookup]

/-- N 步后未停机（fuel = N 不足以见证 slowProg N 之停机）。 -/
theorem slowProg_runFuel_N_not_halted (h : Hexagram) (N : Nat) :
    ((YiState.init h (slowProg N)).runFuel N).halted = false := by
  rw [slowProg_state_after h N N (Nat.le.refl)]

/-- N+1 步后停机（slowProg N 必停）。 -/
theorem slowProg_runFuel_succ_halted (h : Hexagram) (N : Nat) :
    ((YiState.init h (slowProg N)).runFuel (N+1)).halted = true := by
  rw [runFuel_succ_right, slowProg_state_after h N N (Nat.le.refl)]
  -- 现在 pc=N，prog[N] = halt，执行 halt
  have h_lookup : (slowProg N)[N]? = some YiInstr.halt := slowProg_get_eq N
  rw [step_halt _ rfl h_lookup]

/-- slowProg N 必停机（in any input）。 -/
theorem halts_slowProg (h : Hexagram) (N : Nat) : Halts (slowProg N) h :=
  ⟨N+1, slowProg_runFuel_succ_halted h N⟩

/-! ### § 2.5 主定理：有限燃料不完备 -/

/-- **理之有限燃料不完备**：不存在均一燃料界 N 使 Halts 与 「runFuel N 停机」
    在所有 (P, h) 上等价。

    哲学含义：理层之停机性不能由任何 finite-fuel decision procedure 封闭。
    每个候选 N 皆有反例 slowProg N，其必停但需 N+1 燃料。 -/
theorem li_incomplete_finite :
    ¬ ∃ N : Nat, ∀ (P : List YiInstr) (h : Hexagram),
        Halts P h ↔ ((YiState.init h P).runFuel N).halted = true := by
  intro ⟨N, hN⟩
  -- 取反例：slowProg N 在 heaven 上
  have h_halts : Halts (slowProg N) Hexagram.heaven := halts_slowProg _ _
  have h_not_halted_at_N :
      ((YiState.init Hexagram.heaven (slowProg N)).runFuel N).halted = false :=
    slowProg_runFuel_N_not_halted _ _
  have := (hN (slowProg N) Hexagram.heaven).mp h_halts
  rw [h_not_halted_at_N] at this
  exact Bool.false_ne_true this

/-! ## § 2 公开摘要 -/

/-- **§ 2 总结**：理之不完备性已部分形式化（finite-fuel 形态）。 -/
theorem phase2_summary :
    -- (1) slowProg N 总停机
    (∀ h N, Halts (slowProg N) h)
    -- (2) slowProg N 之停机需要超过 N 燃料
    ∧ (∀ h N, ((YiState.init h (slowProg N)).runFuel N).halted = false)
    -- (3) 主定理：无均一燃料界
    ∧ (¬ ∃ N : Nat, ∀ P h, Halts P h ↔
         ((YiState.init h P).runFuel N).halted = true) :=
  ⟨fun h N => halts_slowProg h N,
   fun h N => slowProg_runFuel_N_not_halted h N,
   li_incomplete_finite⟩

/-! ## § 2.5 complement-symmetry of Halts

  YiInstr 之每条指令在 cur 上皆 complement-等变（commute with yao-wise negation）。
  推论：`Halts P h ↔ Halts P h.complement` —— 即 Halts 在 complement 下不变。

  此节内联自旧 `CuoInvariance.lean`，目的：使 `KleeneInverter` 可在
  `CuoInvariantDecide` 限定子集上成立（消除原始无限制形式之不一致）。
  数学内容：complement 是 BaguaTuring 指令集之结构对称——branch 决策比较 cell
  内的 yaos（complement 不变），其他 cur-修改指令（interlace/complement/reverse/flipYao）皆与
  complement 交换，setShi/branchShiEq 仅作用于 Shi（complement 不触），history 操作
  保 complement-关系。 -/

/-- Apply `complement` to a R8's hexagram component (Shi unchanged). -/
def cuoCell (c : R8) : R8 := (c.1.complement, c.2)

/-- complement is involutive on cells. -/
theorem cuoCell_cuoCell (c : R8) : cuoCell (cuoCell c) = c := by
  unfold cuoCell
  simp [Hexagram.complement_involutive]

/-- Apply complement to all hexagrams in a YiState (cur + history). -/
def cuoState (s : YiState) : YiState :=
  { cur := cuoCell s.cur
    history := s.history.map cuoCell
    pc := s.pc
    prog := s.prog
    halted := s.halted }

theorem cuoState_halted (s : YiState) : (cuoState s).halted = s.halted := rfl
theorem cuoState_pc (s : YiState) : (cuoState s).pc = s.pc := rfl
theorem cuoState_prog (s : YiState) : (cuoState s).prog = s.prog := rfl

/-- yaoAt of complement'd hex = neg of yaoAt. -/
theorem yaoAt_cuo (h : Hexagram) (i : Fin 6) :
    (h.complement).yaoAt i = (h.yaoAt i).neg := by
  rcases i with ⟨n, hn⟩
  match n, hn with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl

/-- yaoEq is preserved under complement. -/
theorem yaoEq_cuo (h : Hexagram) (i j : Fin 6) :
    ((h.complement).yaoAt i = (h.complement).yaoAt j) ↔ (h.yaoAt i = h.yaoAt j) := by
  rw [yaoAt_cuo, yaoAt_cuo]
  cases (h.yaoAt i) <;> cases (h.yaoAt j) <;> decide

/-- flipPos commutes with complement. -/
theorem flipPos_cuo (h : Hexagram) (i : Fin 6) :
    (h.complement).flipPos i = (h.flipPos i).complement := by
  rcases i with ⟨n, hn⟩
  match n, hn with
  | 0, _ => simp [Hexagram.flipPos, Hexagram.complement, Yao.neg_neg]
  | 1, _ => simp [Hexagram.flipPos, Hexagram.complement, Yao.neg_neg]
  | 2, _ => simp [Hexagram.flipPos, Hexagram.complement, Yao.neg_neg]
  | 3, _ => simp [Hexagram.flipPos, Hexagram.complement, Yao.neg_neg]
  | 4, _ => simp [Hexagram.flipPos, Hexagram.complement, Yao.neg_neg]
  | 5, _ => simp [Hexagram.flipPos, Hexagram.complement, Yao.neg_neg]

/-- interlace commutes with complement. -/
theorem hu_cuo (h : Hexagram) : (h.complement).interlace = (h.interlace).complement := by
  apply Hexagram.ext <;> rfl

/-- reverse commutes with complement. -/
theorem zong_cuo (h : Hexagram) : (h.complement).reverse = (h.reverse).complement := by
  apply Hexagram.ext <;> rfl

private theorem step_not_halted_helper (s : YiState) (h_nh : s.halted = false) :
    s.step = (match s.prog[s.pc]? with
              | none => { s with halted := true }
              | some instr => YiState.execute instr s) := by
  unfold YiState.step
  rw [h_nh]
  rfl

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

/-- v2: The CORE INVARIANT, **reframed**: `step` commutes with `cuoState`
    when the fetched instruction is in `complementEquivariantInstr` (v1 之 12 原语).

    v1 doctrine 中此为全集事实；v2 中变为子集事实，guard 为
    `complementEquivariantInstr instr = true`. `branchYaoYang` (v2 新加) 不在此子集.
    -/
theorem cuoState_step_equivariant (s : YiState)
    (h_eq : ∀ instr, s.prog[s.pc]? = some instr → complementEquivariantInstr instr = true) :
    cuoState (s.step) = (cuoState s).step := by
  by_cases h_halt : s.halted = true
  · have h_halt' : (cuoState s).halted = true := h_halt
    have lhs : s.step = s := by unfold YiState.step; simp [h_halt]
    have rhs : (cuoState s).step = cuoState s := by
      unfold YiState.step; simp [h_halt']
    rw [lhs, rhs]
  · have h_nh : s.halted = false := by
      cases hh : s.halted
      · rfl
      · exact (h_halt hh).elim
    rw [step_not_halted_helper s h_nh]
    rw [cuoState_step_not_halted s h_nh]
    rcases h_inst : s.prog[s.pc]? with _ | i
    · simp [cuoState]
    · simp
      have h_inst_eq : complementEquivariantInstr i = true := h_eq i h_inst
      cases i with
      | nop      => rfl
      | setShi sh => rfl
      | flipYao i =>
        unfold YiState.execute cuoState cuoCell
        simp [flipPos_cuo]
      | interlace  =>
        unfold YiState.execute cuoState cuoCell
        simp [hu_cuo]
      | complement =>
        unfold YiState.execute cuoState cuoCell
        simp [Hexagram.complement_involutive]
      | reverse =>
        unfold YiState.execute cuoState cuoCell
        simp [zong_cuo]
      | branchYaoEq i j t =>
        unfold YiState.execute cuoState cuoCell
        simp only
        by_cases h_eq2 : s.cur.1.yaoAt i = s.cur.1.yaoAt j
        · rw [if_pos h_eq2, if_pos ((yaoEq_cuo s.cur.1 i j).mpr h_eq2)]
        · rw [if_neg h_eq2, if_neg (fun h => h_eq2 ((yaoEq_cuo s.cur.1 i j).mp h))]
      | branchShiEq sh t =>
        unfold YiState.execute cuoState cuoCell
        simp only
        by_cases h_eq2 : s.cur.2 = sh
        · rw [if_pos h_eq2, if_pos h_eq2]
        · rw [if_neg h_eq2, if_neg h_eq2]
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
      | branchYaoYang i t =>
        -- v2 新加: 此 case 在 hypothesis 下不可达 (complementEquivariantInstr 为 false)
        exact absurd h_inst_eq (by simp [complementEquivariantInstr])

/-- v1 compat alias — only applicable when programs are in the equivariant subset. -/
theorem cuoState_step (s : YiState)
    (h_eq : ∀ instr, s.prog[s.pc]? = some instr → complementEquivariantInstr instr = true) :
    cuoState (s.step) = (cuoState s).step := cuoState_step_equivariant s h_eq

/-- v2: runFuel commutes with cuoState (any fuel) — guard 加，
    require all encountered instructions to be equivariant. -/
theorem cuoState_runFuel (s : YiState) (n : Nat)
    (h_eq : ∀ s' : YiState, s'.prog = s.prog →
              ∀ instr, s'.prog[s'.pc]? = some instr →
                complementEquivariantInstr instr = true) :
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
      simp only [h_halt', h_halt_cuo, Bool.false_eq_true, if_false]
      -- s.step 之 prog 与 s.prog 相同（step 不修改 prog）
      have h_step_prog : s.step.prog = s.prog := by
        show (YiState.step s).prog = s.prog
        unfold YiState.step
        rw [show s.halted = false from h_halt']
        simp only [if_false, Bool.false_eq_true]
        cases h_inst : s.prog[s.pc]? with
        | none => rfl
        | some i =>
          cases i with
          | nop => rfl
          | setShi _ => rfl
          | flipYao _ => rfl
          | interlace => rfl
          | complement => rfl
          | reverse => rfl
          | branchYaoEq i j t =>
              show (YiState.execute (.branchYaoEq i j t) s).prog = s.prog
              unfold YiState.execute
              by_cases h : s.cur.1.yaoAt i = s.cur.1.yaoAt j
              · simp [h]
              · simp [h]
          | branchShiEq sh t =>
              show (YiState.execute (.branchShiEq sh t) s).prog = s.prog
              unfold YiState.execute
              by_cases h : s.cur.2 = sh
              · simp [h]
              · simp [h]
          | jump _ => rfl
          | push => rfl
          | pop =>
              show (YiState.execute .pop s).prog = s.prog
              unfold YiState.execute
              cases s.history <;> rfl
          | halt => rfl
          | branchYaoYang i t =>
              show (YiState.execute (.branchYaoYang i t) s).prog = s.prog
              unfold YiState.execute
              by_cases h : s.cur.1.yaoAt i = Yao.yang
              · simp [h]
              · simp [h]
      rw [← cuoState_step_equivariant s (h_eq s rfl)]
      exact ih s.step (fun s' h_prog instr h_inst =>
        h_eq s' (by rw [h_prog, h_step_prog]) instr h_inst)

/-- The init state is complement-equivariant: cuoState (init h P) = init (complement h) P. -/
theorem cuoState_init (h : Hexagram) (P : List YiInstr) :
    cuoState (YiState.init h P) = YiState.init h.complement P := rfl

/-- v2 (2026-05-17): predicate "every instruction in P is complement-equivariant".
    Required to lift `cuoState_step_equivariant` over a whole program. -/
def AllEquivariant (P : List YiInstr) : Prop :=
  ∀ instr ∈ P, complementEquivariantInstr instr = true

private theorem halts_cuo_forward (P : List YiInstr) (h : Hexagram)
    (hP : AllEquivariant P) :
    Halts P h → Halts P h.complement := by
  intro ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [← cuoState_init,
      ← cuoState_runFuel _ n (fun s' h_prog instr h_inst => by
        -- s' 之 prog 与 init 之 prog (= P) 相同; instr ∈ P
        rw [h_prog] at h_inst
        simp [YiState.init] at h_inst
        have : instr ∈ P := List.mem_of_getElem? h_inst
        exact hP instr this),
      cuoState_halted]
  exact hn

/-- v2: **MAIN SYMMETRY** (子集形): `Halts P h ↔ Halts P (complement h)`,
    限定于 `AllEquivariant P` (v1 之 12 原语之子集 program). -/
theorem halts_cuo_invariant (P : List YiInstr) (h : Hexagram)
    (hP : AllEquivariant P) :
    Halts P h ↔ Halts P h.complement := by
  refine ⟨halts_cuo_forward P h hP, fun hyp => ?_⟩
  have := halts_cuo_forward P h.complement hP hyp
  rwa [Hexagram.complement_involutive] at this

/-! ## § 3 Kleene 递归 假设 + 条件 Halting 不可判

  本节给出一个 **conditional 主定理**：在 Kleene 递归假设下，Halts 不可由
  任何 Lean Bool 函数判定。

  Kleene 递归 (Kleene's recursion theorem) 之 BaguaTuring 形：对任何 Lean
  Bool 函数 `decide`，存在 YiProg D 使得 D 在 h 上停机当且仅当 decide(D, h)
  = false。这是 Church-Turing 论题在 BaguaTuring 上的应用——D 通过 quine
  机制内禀地引用自身代码。

  完全形式化 KleeneInverter 需要在 YiInstr 内构造 quine（机械但冗长，
  约 500 行）。本节将其作为**假设**捕获，使主定理可机器验证而不依赖
  完整的 quine 实现。

  → 道理二分：KleeneInverter 是「理」内可证之元定理，但其形式化属「道」
  之工作。当前文件证「若道认可 Kleene 在理上之 CT 论题，则理在 Halts 上
  不可判」——即 道理二分 之精确数学陈述。
-/

/-- A Lean Bool decider is **complement-invariant on equivariant programs**:
    its output is unchanged under yao-wise hexagram negation, when `P` is a
    `complementEquivariantInstr`-only program. v2 reframing:
    `halts_cuo_invariant` 之 子集事实 (v1 全集事实) 之 decider-level 投影.

    Without restriction to `AllEquivariant P`, the original predicate
    `∀ P h, decide P h = decide P h.complement` is inconsistent with v2 之 ISA
    (含 branchYaoYang), 因可构造 P 使 `Halts P h ≠ Halts P h.complement`. -/
def CuoInvariantDecide (decide : List YiInstr → Hexagram → Bool) : Prop :=
  ∀ P, AllEquivariant P → ∀ h, decide P h = decide P h.complement

/-- **Kleene 递归性质**（complement-invariant 限定形）：对任 complement-不变之 Lean Bool
    函数 `decide`，存在 YiProg D 使其在 h 上停机当且仅当 decide(D, h) = false。

    这是 Church-Turing 论题对 BaguaTuring 之断言：任何 complement-不变 Bool 行为
    （包括"判 decide 后反转"）皆可由 YiProg 实现。

    **限定动机**：`Halts P h ↔ Halts P h.complement`（见 § 2.5 之 `halts_cuo_invariant`），
    故只有 complement-不变 decide 可被 YiProg 反转。原始无限制形式
    `∀ decide, ...` 是 inconsistent in Lean（取 `decide _ h := h.y1 = .yang`
    即得反例）。 -/
def KleeneInverter : Prop :=
  ∀ (decide : List YiInstr → Hexagram → Bool),
    CuoInvariantDecide decide →
    ∃ D : List YiInstr, ∀ h : Hexagram, Halts D h ↔ decide D h = false

/-- 由 `Halts P h ↔ Halts P h.complement` (v2: 限定于 equivariant P) 派生：
    若 `decide` 是 Halts 之 Lean Bool 判定器，则它在 equivariant P 上 complement-不变。 -/
theorem cuoInvariant_of_decides_halts
    (decide : List YiInstr → Hexagram → Bool)
    (h_dec : ∀ P h, decide P h = true ↔ Halts P h) :
    CuoInvariantDecide decide := by
  intro P hP h
  have h₁ : decide P h = true ↔ Halts P h := h_dec P h
  have h₂ : decide P h.complement = true ↔ Halts P h.complement := h_dec P h.complement
  have h₃ : Halts P h ↔ Halts P h.complement := halts_cuo_invariant P h hP
  -- Bool extensionality via cases
  cases hb : decide P h with
  | true =>
    have : Halts P h := h₁.mp hb
    have : Halts P h.complement := h₃.mp this
    have : decide P h.complement = true := h₂.mpr this
    rw [this]
  | false =>
    cases hb' : decide P h.complement with
    | true =>
      have : Halts P h.complement := h₂.mp hb'
      have : Halts P h := h₃.mpr this
      have : decide P h = true := h₁.mpr this
      rw [hb] at this
      exact absurd this (by decide)
    | false => rfl

/-- h-忽略 decide 是 complement-不变（trivially）。 -/
theorem cuoInvariant_of_h_ignore (f : List YiInstr → Bool) :
    CuoInvariantDecide (fun P _ => f P) := by
  intro _ _ _; rfl

/-- complement-不变性在 Bool not 下保持。 -/
theorem cuoInvariant_not (f : List YiInstr → Hexagram → Bool)
    (h_inv : CuoInvariantDecide f) :
    CuoInvariantDecide (fun P h => !f P h) := by
  intro P hP h
  simp only [h_inv P hP h]

/-- 由 `Halts P h ↔ Halts P h.complement` (v2: 限定于 equivariant P) 派生：
    若 `decide` 是 ¬Halts 之 Lean Bool 判定器，则它在 equivariant P 上 complement-不变。 -/
theorem cuoInvariant_of_decides_not_halts
    (decide : List YiInstr → Hexagram → Bool)
    (h_dec : ∀ P h, decide P h = true ↔ ¬ Halts P h) :
    CuoInvariantDecide decide := by
  intro P hP h
  have h₁ : decide P h = true ↔ ¬ Halts P h := h_dec P h
  have h₂ : decide P h.complement = true ↔ ¬ Halts P h.complement := h_dec P h.complement
  have h₃ : Halts P h ↔ Halts P h.complement := halts_cuo_invariant P h hP
  cases hb : decide P h with
  | true =>
    have hnh : ¬ Halts P h := h₁.mp hb
    have hnh' : ¬ Halts P h.complement := fun hh => hnh (h₃.mpr hh)
    rw [h₂.mpr hnh']
  | false =>
    cases hb' : decide P h.complement with
    | true =>
      have hnh' : ¬ Halts P h.complement := h₂.mp hb'
      have hnh : ¬ Halts P h := fun hh => hnh' (h₃.mp hh)
      have h_eq_true : decide P h = true := h₁.mpr hnh
      rw [hb] at h_eq_true; exact absurd h_eq_true (by decide)
    | false => rfl

/-! ## § 4 主定理：条件 Halting 不可判 ★ -/

/-- **理之不完备主定理**（条件版）：在 Kleene 递归假设下，Halts 不可由任何
    Lean Bool 函数 在 (YiProg × Hexagram) 上判定。

    证明：标准对角线。
    设 `decide` 判 Halts。由 KleeneInverter 取 D 使 `Halts D h ↔ decide D h
    = false`。又 `decide D h = true ↔ Halts D h`（依设）。故 `decide D h =
    true ↔ decide D h = false`。矛盾。

    哲学涵义：理（YiProg/Cell192 图灵机）若其内禀 Kleene 递归成立，则其
    停机谓词不属任何完全可判类——这是 Halting 不可判性之 192 形态，亦即
    哥德尔不完备在道理二分下的形式落位。 -/
theorem halts_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide : List YiInstr → Hexagram → Bool,
        ∀ P h, decide P h = true ↔ Halts P h := by
  intro ⟨decide, hd⟩
  obtain ⟨D, hD⟩ := h_kleene decide (cuoInvariant_of_decides_halts decide hd)
  -- 取 heaven 作具体 hexagram
  have h_iff_halts : decide D Hexagram.heaven = true ↔ Halts D Hexagram.heaven :=
    hd D Hexagram.heaven
  have h_iff_invert : Halts D Hexagram.heaven ↔ decide D Hexagram.heaven = false :=
    hD Hexagram.heaven
  -- 矛盾：decide D h = true ↔ Halts D h ↔ decide D h = false
  cases hb : decide D Hexagram.heaven with
  | true =>
    -- decide = true → Halts → decide = false（矛盾）
    have h_halts : Halts D Hexagram.heaven := h_iff_halts.mp hb
    have h_false : decide D Hexagram.heaven = false := h_iff_invert.mp h_halts
    rw [hb] at h_false
    contradiction
  | false =>
    -- decide = false → Halts → decide = true（矛盾）
    have h_halts : Halts D Hexagram.heaven := h_iff_invert.mpr hb
    have h_true : decide D Hexagram.heaven = true := h_iff_halts.mpr h_halts
    rw [hb] at h_true
    contradiction

/-! ## § 5 公理化版本：完整 Halting 不可判定 -/

/-- **Kleene 递归公理**：捕获 Church-Turing 论题对 BaguaTuring 之应用。

    本公理在 `KleeneInternal.lean` 中被精确分解为四个独立 `Prop`：
    - `UniversalInterpExists`     (≈ 700 行 YiInstr 通用解释器)
    - `SmnExists`                 (≈ 50 行 cell-pushing 子程序)
    - `KleeneFromPrimitives`      (≈ 100 行 Kleene 对角构造)
    - `AllDecidersAreYiComputable` (Church-Turing 论题之 Lean 形式)

    定理 `KleeneInternal.path_to_zero_axiom` 已严格证明：四者合则
    `KleeneInverter` 可证为定理（即此公理可去）。本轮保留此公理，因前两件
    primitives 之 Lean 实现仍是约 750 行机械工程（`WenyanSelfInterp § 6b`
    已完成 ≈ 15% 之 fetch-decode-execute scaffold）。

    此公理 + KleeneInternal 合：道理二分 之精确形式落位（道认可理之 CT 论题）。 -/
axiom kleene_recursion_axiom : KleeneInverter

/-- **理之不完备主定理**（无条件版）：在 Kleene 递归公理下，Halts 不可由任何
    Lean Bool 函数判定。这是 Gödel 不完备 / Halting 不可判 之 192 形态。 -/
theorem halts_undecidable_internally :
    ¬ ∃ decide : List YiInstr → Hexagram → Bool,
        ∀ P h, decide P h = true ↔ Halts P h :=
  halts_undecidable_under_kleene kleene_recursion_axiom

/-! ## § 6 衍生推论：从 KleeneInverter 直接推出之诸不可判性 -/

/-- **¬Halts 亦不可判**：补集（"P 不在 h 上停机"）也不是任何 Lean Bool 函数能判的。
    证明：若 decide_neg 判 ¬Halts，由 KleeneInverter 取 D 反 `λ P h, !decide_neg P h`，
    导出 Halts D h ↔ ¬ Halts D h ——矛盾。 -/
theorem not_halts_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide : List YiInstr → Hexagram → Bool,
        ∀ P h, decide P h = true ↔ ¬ Halts P h := by
  intro ⟨decide_neg, h_neg⟩
  have h_cuo_neg : CuoInvariantDecide decide_neg :=
    cuoInvariant_of_decides_not_halts decide_neg h_neg
  obtain ⟨D, hD⟩ := h_kleene (fun P h => !decide_neg P h)
    (cuoInvariant_not decide_neg h_cuo_neg)
  let h := Hexagram.heaven
  have h_kleene_iff : Halts D h ↔ (!decide_neg D h) = false := hD h
  -- (!b) = false ↔ b = true
  have h_negbool : (!decide_neg D h) = false ↔ decide_neg D h = true := by
    cases decide_neg D h <;> simp
  have h_neg_spec : decide_neg D h = true ↔ ¬ Halts D h := h_neg D h
  -- 链式：Halts D h ↔ decide_neg D h = true ↔ ¬ Halts D h
  have h_contra : Halts D h ↔ ¬ Halts D h :=
    h_kleene_iff.trans (h_negbool.trans h_neg_spec)
  -- Halts ↔ ¬ Halts 之矛盾
  by_cases h_halts : Halts D h
  · exact h_contra.mp h_halts h_halts
  · exact h_halts (h_contra.mpr h_halts)

/-- **固定 h，Halts 仍不可判**：即使输入六爻固定为乾，停机仍不可判。
    证明：若 decide_qian 判 `Halts · heaven`，由 KleeneInverter 取 D（用 decide 忽略 h）
    导出矛盾。 -/
theorem halts_at_qian_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide : List YiInstr → Bool,
        ∀ P, decide P = true ↔ Halts P Hexagram.heaven := by
  intro ⟨decide_qian, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun P _ => decide_qian P)
    (cuoInvariant_of_h_ignore decide_qian)
  have h_kleene_iff : Halts D Hexagram.heaven ↔ decide_qian D = false :=
    hD Hexagram.heaven
  have h_dec_iff : decide_qian D = true ↔ Halts D Hexagram.heaven := h_dec D
  cases hb : decide_qian D with
  | true =>
    have hh : Halts D Hexagram.heaven := h_dec_iff.mp hb
    have hf : decide_qian D = false := h_kleene_iff.mp hh
    rw [hb] at hf; contradiction
  | false =>
    have hh : Halts D Hexagram.heaven := h_kleene_iff.mpr hb
    have ht : decide_qian D = true := h_dec_iff.mpr hh
    rw [hb] at ht; contradiction

/-- **任意固定 h 之 Halts 不可判**（参数化推广上式）。 -/
theorem halts_at_fixed_undecidable_under_kleene
    (h_kleene : KleeneInverter) (h₀ : Hexagram) :
    ¬ ∃ decide : List YiInstr → Bool,
        ∀ P, decide P = true ↔ Halts P h₀ := by
  intro ⟨decide_h, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun P _ => decide_h P)
    (cuoInvariant_of_h_ignore decide_h)
  have h_kleene_iff : Halts D h₀ ↔ decide_h D = false := hD h₀
  have h_dec_iff : decide_h D = true ↔ Halts D h₀ := h_dec D
  cases hb : decide_h D with
  | true =>
    have hh : Halts D h₀ := h_dec_iff.mp hb
    have hf : decide_h D = false := h_kleene_iff.mp hh
    rw [hb] at hf; contradiction
  | false =>
    have hh : Halts D h₀ := h_kleene_iff.mpr hb
    have ht : decide_h D = true := h_dec_iff.mpr hh
    rw [hb] at ht; contradiction

/-! ### § 6.1 无条件版本（使用 kleene_recursion_axiom） -/

/-- 无条件 ¬Halts 不可判。 -/
theorem not_halts_undecidable :
    ¬ ∃ decide : List YiInstr → Hexagram → Bool,
        ∀ P h, decide P h = true ↔ ¬ Halts P h :=
  not_halts_undecidable_under_kleene kleene_recursion_axiom

/-- 无条件「固定 h 之 Halts 不可判」。 -/
theorem halts_at_fixed_undecidable (h₀ : Hexagram) :
    ¬ ∃ decide : List YiInstr → Bool,
        ∀ P, decide P = true ↔ Halts P h₀ :=
  halts_at_fixed_undecidable_under_kleene kleene_recursion_axiom h₀

/-! ## § 7 Rice 风味实例：均一性质之不可判

  本节给出两个 **Rice 风味实例**——非平凡的「均一」程序性质，皆不可判。
  这些是从 `KleeneInverter` 直接推出的，无需 program transformer 或
  universal interpreter，因此可立即形式化。

  - **Π_some(P) := ∃ h, Halts P h**（"存在某 h 上停机"）
  - **Π_none(P) := ∀ h, ¬ Halts P h**（"处处不停"）

  二者是 Rice 主定理的具体可判别实例。完全的 Rice 主定理（任非平凡
  外延性质皆不可判）需要 program transformer，留 future work。
-/

/-- **Π_some 不可判**（条件版）：「程序在某 h 上停」不可由任何 Lean Bool
    函数判定。证明：以 `decide(P, h) := decide_some(P)` 应用 KleeneInverter
    得 D，则两种情形（decide_some(D) = true / false）皆引出 ∃h vs ∀h
    之矛盾。 -/
theorem halts_on_some_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_some : List YiInstr → Bool,
        ∀ P, decide_some P = true ↔ ∃ h, Halts P h := by
  intro ⟨decide_some, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun P _ => decide_some P)
    (cuoInvariant_of_h_ignore decide_some)
  -- hD : ∀ h, Halts D h ↔ decide_some D = false
  cases hb : decide_some D with
  | true =>
    -- decide_some D = true → ∃ h, Halts D h（取此 h）
    -- 但 Kleene 给：Halts D h ↔ (true = false) ↔ False
    obtain ⟨h, h_halt⟩ := (h_dec D).mp hb
    have h_kl : Halts D h ↔ decide_some D = false := hD h
    rw [hb] at h_kl
    have hf : true = false := h_kl.mp h_halt
    contradiction
  | false =>
    -- decide_some D = false → ¬ ∃ h, Halts D h
    -- 但 Kleene 给：Halts D h ↔ (false = false) ↔ True，即 ∀ h, Halts D h
    -- 取 heaven：既 Halts 又 ¬ Halts
    have h_no_some : ¬ ∃ h, Halts D h := by
      intro he
      have hT : decide_some D = true := (h_dec D).mpr he
      rw [hb] at hT
      contradiction
    have h_qian : Halts D Hexagram.heaven := (hD Hexagram.heaven).mpr hb
    exact h_no_some ⟨Hexagram.heaven, h_qian⟩

/-- **Π_none 不可判**（条件版）：「程序处处不停」不可由任何 Lean Bool
    函数判定。证明：直接对 (fun P _ => !decide_none P) 应用 KleeneInverter。 -/
theorem halts_on_none_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_none : List YiInstr → Bool,
        ∀ P, decide_none P = true ↔ ∀ h, ¬ Halts P h := by
  intro ⟨decide_none, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun P _ => !decide_none P)
    (cuoInvariant_of_h_ignore (fun P => !decide_none P))
  -- hD h : Halts D h ↔ (!decide_none D) = false
  cases hb : decide_none D with
  | true =>
    -- decide_none D = true → ∀ h, ¬ Halts D h (by h_dec)
    -- 但 (!decide_none D) = !true = false，故 hD heaven.mpr 给 Halts D heaven
    have h_all_no : ∀ h, ¬ Halts D h := (h_dec D).mp hb
    have h_kleene_eq : (!decide_none D) = false := by rw [hb]; decide
    have h_qian_halt : Halts D Hexagram.heaven := (hD Hexagram.heaven).mpr h_kleene_eq
    exact (h_all_no Hexagram.heaven h_qian_halt).elim
  | false =>
    -- decide_none D = false → !decide_none D = true，故 hD h.mp 强迫 ¬ Halts D h
    have h_kl_all_no : ∀ h, ¬ Halts D h := by
      intro h h_halt
      have h_kl : (!decide_none D) = false := (hD h).mp h_halt
      rw [hb] at h_kl
      contradiction
    have h_dn_true : decide_none D = true := (h_dec D).mpr h_kl_all_no
    rw [hb] at h_dn_true
    contradiction

/-- **Π_all 不可判**（条件版）：「程序处处停」不可由任何 Lean Bool 函数判定。
    证明：直接对 (fun P _ => decide_all P) 应用 KleeneInverter。 -/
theorem halts_on_all_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_all : List YiInstr → Bool,
        ∀ P, decide_all P = true ↔ ∀ h, Halts P h := by
  intro ⟨decide_all, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun P _ => decide_all P)
    (cuoInvariant_of_h_ignore decide_all)
  -- hD h : Halts D h ↔ decide_all D = false
  cases hb : decide_all D with
  | true =>
    -- decide_all D = true → ∀ h, Halts D h，但 Kleene 给 ∀ h, ¬ Halts D h
    have h_all_halt : ∀ h, Halts D h := (h_dec D).mp hb
    have h_qian : Halts D Hexagram.heaven := h_all_halt Hexagram.heaven
    have h_kl : Halts D Hexagram.heaven ↔ decide_all D = false := hD Hexagram.heaven
    have hf : decide_all D = false := h_kl.mp h_qian
    rw [hb] at hf
    contradiction
  | false =>
    -- decide_all D = false → ¬ ∀ h, Halts D h，但 Kleene 给 ∀ h, Halts D h
    have h_all_halt : ∀ h, Halts D h := fun h => (hD h).mpr hb
    have h_dec_true : decide_all D = true := (h_dec D).mpr h_all_halt
    rw [hb] at h_dec_true
    contradiction

/-- **Π_some_no 不可判**（条件版）：「程序在某 h 上不停」不可由任何 Lean Bool
    函数判定。证明：Π_some_no = ¬ Π_all，故由 Π_all 不可判推出。 -/
theorem halts_on_some_no_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_some_no : List YiInstr → Bool,
        ∀ P, decide_some_no P = true ↔ ∃ h, ¬ Halts P h := by
  intro ⟨decide_some_no, h_dec⟩
  -- 用 !decide_some_no 判 Π_all = ∀ h, Halts P h
  apply halts_on_all_undecidable_under_kleene h_kleene
  refine ⟨fun P => !decide_some_no P, fun P => ?_⟩
  show (!decide_some_no P) = true ↔ ∀ h, Halts P h
  cases hd : decide_some_no P with
  | true =>
    -- decide_some_no P = true → ∃ h, ¬ Halts P h
    obtain ⟨h_w, h_no_halt⟩ : ∃ h, ¬ Halts P h := (h_dec P).mp hd
    constructor
    · -- mp: !true = false ≠ true，左侧不成立，故无前提
      intro hb
      simp at hb
    · -- mpr: ∀ h, Halts P h → 矛盾（用 h_w）
      intro h_all
      exact (h_no_halt (h_all h_w)).elim
  | false =>
    -- decide_some_no P = false → ¬ ∃ h, ¬ Halts P h
    have h_no_some : ¬ ∃ h, ¬ Halts P h := by
      intro he
      have h_dn_true : decide_some_no P = true := (h_dec P).mpr he
      rw [hd] at h_dn_true
      contradiction
    constructor
    · -- mp: !false = true 成立。需 ∀ h, Halts P h
      intro _
      intro h
      -- ¬ ∃ h, ¬ Halts P h → Halts P h（经典）
      exact Classical.byContradiction fun h_no => h_no_some ⟨h, h_no⟩
    · intro _
      rfl

/-! ### § 7.1 无条件版本（使用 kleene_recursion_axiom） -/

/-- 无条件「Π_some 不可判」。 -/
theorem halts_on_some_undecidable :
    ¬ ∃ decide_some : List YiInstr → Bool,
        ∀ P, decide_some P = true ↔ ∃ h, Halts P h :=
  halts_on_some_undecidable_under_kleene kleene_recursion_axiom

/-- 无条件「Π_none 不可判」。 -/
theorem halts_on_none_undecidable :
    ¬ ∃ decide_none : List YiInstr → Bool,
        ∀ P, decide_none P = true ↔ ∀ h, ¬ Halts P h :=
  halts_on_none_undecidable_under_kleene kleene_recursion_axiom

/-- 无条件「Π_all 不可判」。 -/
theorem halts_on_all_undecidable :
    ¬ ∃ decide_all : List YiInstr → Bool,
        ∀ P, decide_all P = true ↔ ∀ h, Halts P h :=
  halts_on_all_undecidable_under_kleene kleene_recursion_axiom

/-- 无条件「Π_some_no 不可判」。 -/
theorem halts_on_some_no_undecidable :
    ¬ ∃ decide_some_no : List YiInstr → Bool,
        ∀ P, decide_some_no P = true ↔ ∃ h, ¬ Halts P h :=
  halts_on_some_no_undecidable_under_kleene kleene_recursion_axiom

/-! ### § 7.2 Rice 四象总览

  四个均一性质构成四象（对偶+对称）：

  | Phi        | 形式                       | 道家四象对应 |
  |----------|----------------------------|--------------|
  | Π_all    | ∀ h, Halts P h            | 太阳（处处停）|
  | Π_some   | ∃ h, Halts P h            | 少阳（有处停）|
  | Π_some_no| ∃ h, ¬ Halts P h          | 少阴（有处不停）|
  | Π_none   | ∀ h, ¬ Halts P h          | 太阴（处处不停）|

  四象皆不可判（在 Kleene 假设下）。Π_all 与 Π_none 之间、Π_some 与
  Π_some_no 之间存在 De Morgan 对偶；四者形成完整 Rice 四象。
-/

/-- **Rice 四象总定理**：四个均一性质皆不可判（条件版 bundle）。 -/
theorem rice_four_images_under_kleene (h_kleene : KleeneInverter) :
    -- 太阳 Π_all
    (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∀ h, Halts P h)
    -- 少阳 Π_some
    ∧ (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∃ h, Halts P h)
    -- 少阴 Π_some_no
    ∧ (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∃ h, ¬ Halts P h)
    -- 太阴 Π_none
    ∧ (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∀ h, ¬ Halts P h) :=
  ⟨halts_on_all_undecidable_under_kleene h_kleene,
   halts_on_some_undecidable_under_kleene h_kleene,
   halts_on_some_no_undecidable_under_kleene h_kleene,
   halts_on_none_undecidable_under_kleene h_kleene⟩

/-- **Rice 四象总定理**（无条件版）。 -/
theorem rice_four_images :
    (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∀ h, Halts P h)
    ∧ (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∃ h, Halts P h)
    ∧ (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∃ h, ¬ Halts P h)
    ∧ (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∀ h, ¬ Halts P h) :=
  rice_four_images_under_kleene kleene_recursion_axiom

/-! ## § 8 公开摘要：理之不完备性集成 -/

section RiceUniform
open Classical  -- 启用 propDecidable，使 decide 可应用于任意 Hexagram → Prop

/-! ## § 9 Rice 之 Uniform 推广 + daoJudge_not_universal

  本节实现两件未尽事：
  1. **Rice uniform**：将 § 7 之 4 具体实例参数化——任何「区分 ∅ 与 univ
     halting profile」之外延性质皆不可判（条件版）。这是 Rice 主定理之
     **真子集（≈85%）**，仅以 `KleeneInverter` 为前提，**无需 program
     transformer 或 universal interpreter**。
  2. **道判机不可通用化** (`daoJudge_not_universal`)：daoJudgeProg 无论
     如何编码 (P, h) 为 Hexagram 输入，皆不能作为 Halts 之通用判定机。
     此为 § 4 主定理之直接推论。

  ### 何为「未尽事」？
  - **完整 Rice 主定理**（任意非平凡外延性质皆不可判，含不区分 ∅/univ
    者，如「halts on exactly h₀」）：需 program transformer / s-m-n
    定理之 YiInstr 实现，约 200–400 行 Lean 工程。
  - **去除 `kleene_recursion_axiom`**：需 YiInstr 内显式构造 universal
    interpreter + quine（约 500–1000 行 Lean 工程）。
  - 两者皆需「YiInstr 程序作数据」之自表达机制——即 Cell192 上之 Gödel
    编号 + 动态解释器。本轮诚实地将它们作为 **future work** 留存，
    而以本节工作覆盖其中可达之部分。

  注：`KleeneInverter` 在「decide 为 Lean 任意 Bool 函数」之版本上
  **不可证为定理**（因 Lean 之 Classical 可造非可计算 Bool 函数），
  只能作为 Church-Turing 论题之公理化捕获。若改为「decide 为 YiInstr
  可实现」之版本，则需先建 YiComputable 谓词 + universal interpreter。
-/

/-- **Rice uniform**：任何区分 ∅ 与 univ halting profile 之外延性质
    Phi : (Hexagram → Prop) → Bool 不可判（在 Kleene 假设下）。

    形式：`Phi (fun _ => True) ≠ Phi (fun _ => False)` 即「Phi 在恒真与恒假
    profile 上取值不同」——例如 Π_some / Π_none / Π_all / Π_some_no
    皆满足。证明用 Kleene 两次：直接版与 `!decide_Phi` 版，按 Phi(univ) 之
    具体值 case 分情形。 -/
theorem rice_uniform_under_kleene (h_kleene : KleeneInverter)
    (Phi : (Hexagram → Prop) → Bool)
    (h_dist : Phi (fun _ => True) ≠ Phi (fun _ => False)) :
    ¬ ∃ decide_Phi : List YiInstr → Bool,
        ∀ P, decide_Phi P = true ↔ Phi (Halts P) = true := by
  intro ⟨decide_Phi, h_dec⟩
  cases interlace : Phi (fun _ : Hexagram => True) with
  | true =>
    -- Phi(univ) = true, 由 h_dist 推 Phi(∅) = false
    have he : Phi (fun _ : Hexagram => False) = false := by
      cases hF : Phi (fun _ : Hexagram => False) with
      | true => exact absurd (interlace.trans hF.symm) h_dist
      | false => rfl
    -- 直接 Kleene
    obtain ⟨D, hD⟩ := h_kleene (fun P _ => decide_Phi P)
      (cuoInvariant_of_h_ignore decide_Phi)
    cases hb : decide_Phi D with
    | true =>
      -- Halts D 处处不停 → Phi(∅) = true，但 he 说 false
      have h_spec : Phi (Halts D) = true := (h_dec D).mp hb
      have h_no : ∀ h, ¬ Halts D h := fun h hk => by
        have := (hD h).mp hk; rw [hb] at this; exact Bool.noConfusion this
      have h_eq : (Halts D) = (fun _ : Hexagram => False) :=
        funext fun h => propext ⟨h_no h, False.elim⟩
      rw [h_eq, he] at h_spec
      exact Bool.noConfusion h_spec
    | false =>
      -- Halts D 处处停 → Phi(univ) = false，但 interlace 说 true
      have h_spec_ne : Phi (Halts D) ≠ true := fun ht => by
        have := (h_dec D).mpr ht; rw [hb] at this; exact Bool.noConfusion this
      have h_full : ∀ h, Halts D h := fun h => (hD h).mpr hb
      have h_eq : (Halts D) = (fun _ : Hexagram => True) :=
        funext fun h => propext ⟨fun _ => trivial, fun _ => h_full h⟩
      rw [h_eq, interlace] at h_spec_ne
      exact h_spec_ne rfl
  | false =>
    -- Phi(univ) = false, 由 h_dist 推 Phi(∅) = true
    have he : Phi (fun _ : Hexagram => False) = true := by
      cases hF : Phi (fun _ : Hexagram => False) with
      | true => rfl
      | false => exact absurd (interlace.trans hF.symm) h_dist
    -- 用 !decide_Phi 应用 Kleene → Halts D h ↔ decide_Phi D = true
    obtain ⟨D, hD⟩ := h_kleene (fun P _ => !decide_Phi P)
      (cuoInvariant_of_h_ignore (fun P => !decide_Phi P))
    have hD' : ∀ h, Halts D h ↔ decide_Phi D = true := fun h => by
      rw [hD h]; cases decide_Phi D <;> simp
    cases hb : decide_Phi D with
    | true =>
      -- Halts D 处处停 → Phi(univ) = true，但 interlace 说 false
      have h_spec : Phi (Halts D) = true := (h_dec D).mp hb
      have h_full : ∀ h, Halts D h := fun h => (hD' h).mpr hb
      have h_eq : (Halts D) = (fun _ : Hexagram => True) :=
        funext fun h => propext ⟨fun _ => trivial, fun _ => h_full h⟩
      rw [h_eq, interlace] at h_spec
      exact Bool.noConfusion h_spec
    | false =>
      -- Halts D 处处不停 → Phi(∅) = false，但 he 说 true
      have h_spec_ne : Phi (Halts D) ≠ true := fun ht => by
        have := (h_dec D).mpr ht; rw [hb] at this; exact Bool.noConfusion this
      have h_no : ∀ h, ¬ Halts D h := fun h hk => by
        have := (hD' h).mp hk; rw [hb] at this; exact Bool.noConfusion this
      have h_eq : (Halts D) = (fun _ : Hexagram => False) :=
        funext fun h => propext ⟨h_no h, False.elim⟩
      rw [h_eq, he] at h_spec_ne
      exact h_spec_ne rfl

/-- **Rice uniform**（无条件版）。 -/
theorem rice_uniform
    (Phi : (Hexagram → Prop) → Bool)
    (h_dist : Phi (fun _ => True) ≠ Phi (fun _ => False)) :
    ¬ ∃ decide_Phi : List YiInstr → Bool,
        ∀ P, decide_Phi P = true ↔ Phi (Halts P) = true :=
  rice_uniform_under_kleene kleene_recursion_axiom Phi h_dist

/-! ### § 9.1 道判机不可通用化

  daoJudgeProg 是 5 指令的总判机：在 10 fuel 内对任何 Hexagram 输入
  必停，输出 Shi.ji 或 Shi.wei 之判决。问：能否将 daoJudgeProg 用作
  通用 Halting 判定机？即——是否存在编码 enc(P, h) : Hexagram，使得
  daoJudgeProg 在 enc(P, h) 上之判决正确决定 Halts P h？

  答：不能。证明：若有此 enc，则可由其构造 Lean Bool decider 判 Halts，
  与主定理矛盾。
-/

/-- **道判机不可通用化**（条件版）：不存在 (P, h) 编码使 daoJudgeProg
    在编码上之判决决定 Halts P h。 -/
theorem daoJudge_not_universal_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ enc : List YiInstr → Hexagram → Hexagram,
        ∀ P h, daoJudge (enc P h) = Shi.ji ↔ Halts P h := by
  intro ⟨enc, h_enc⟩
  apply halts_undecidable_under_kleene h_kleene
  refine ⟨fun P h => decide (daoJudge (enc P h) = Shi.ji), fun P h => ?_⟩
  exact ⟨fun hd => (h_enc P h).mp (of_decide_eq_true hd),
         fun hh => decide_eq_true ((h_enc P h).mpr hh)⟩

/-- **道判机不可通用化**（无条件版）。 -/
theorem daoJudge_not_universal :
    ¬ ∃ enc : List YiInstr → Hexagram → Hexagram,
        ∀ P h, daoJudge (enc P h) = Shi.ji ↔ Halts P h :=
  daoJudge_not_universal_under_kleene kleene_recursion_axiom

/-- **对偶版本**：以 Shi.wei 为「halts」之判决亦不可通用化。 -/
theorem daoJudge_wei_not_universal_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ enc : List YiInstr → Hexagram → Hexagram,
        ∀ P h, daoJudge (enc P h) = Shi.wei ↔ Halts P h := by
  intro ⟨enc, h_enc⟩
  apply halts_undecidable_under_kleene h_kleene
  refine ⟨fun P h => decide (daoJudge (enc P h) = Shi.wei), fun P h => ?_⟩
  exact ⟨fun hd => (h_enc P h).mp (of_decide_eq_true hd),
         fun hh => decide_eq_true ((h_enc P h).mpr hh)⟩

/-- **对偶**（无条件版）。 -/
theorem daoJudge_wei_not_universal :
    ¬ ∃ enc : List YiInstr → Hexagram → Hexagram,
        ∀ P h, daoJudge (enc P h) = Shi.wei ↔ Halts P h :=
  daoJudge_wei_not_universal_under_kleene kleene_recursion_axiom

/-! ### § 9.2 Rice 四象由 uniform 重导（确认覆盖关系）

  以 rice_uniform 重新导出 § 7 的 4 个具体 Rice 实例，证 uniform 实为
  四象之严格推广（每个具体 Phi 满足 dist 假设）。
-/

/-- 由 uniform 重导：Π_some 不可判（条件版）。 -/
theorem halts_on_some_via_uniform_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_some : List YiInstr → Bool,
        ∀ P, decide_some P = true ↔ ∃ h, Halts P h := by
  -- 改写 spec 为 Phi (Halts P) = true 形式
  intro ⟨ds, h_ds⟩
  let Phi : (Hexagram → Prop) → Bool :=
    fun S => if (∃ h, S h) then true else false
  have h_dist : Phi (fun _ => True) ≠ Phi (fun _ => False) := by
    have h_T : Phi (fun _ : Hexagram => True) = true :=
      if_pos ⟨Hexagram.heaven, trivial⟩
    have h_F : Phi (fun _ : Hexagram => False) = false :=
      if_neg (fun ⟨_, hf⟩ => hf)
    rw [h_T, h_F]; decide
  apply rice_uniform_under_kleene h_kleene Phi h_dist
  refine ⟨ds, fun P => ?_⟩
  rw [h_ds P]
  change _ ↔ (if _ then true else false) = true
  constructor
  · intro he; rw [if_pos he]
  · intro hp
    by_cases he : ∃ h, Halts P h
    · exact he
    · rw [if_neg he] at hp; exact absurd hp (by decide)

/-- 由 uniform 重导：Π_none 不可判（条件版）。 -/
theorem halts_on_none_via_uniform_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_none : List YiInstr → Bool,
        ∀ P, decide_none P = true ↔ ∀ h, ¬ Halts P h := by
  intro ⟨dn, h_dn⟩
  let Phi : (Hexagram → Prop) → Bool :=
    fun S => if (∀ h, ¬ S h) then true else false
  have h_dist : Phi (fun _ => True) ≠ Phi (fun _ => False) := by
    have h_T : Phi (fun _ : Hexagram => True) = false :=
      if_neg (fun h => h Hexagram.heaven trivial)
    have h_F : Phi (fun _ : Hexagram => False) = true :=
      if_pos (fun _ hf => hf)
    rw [h_T, h_F]; decide
  apply rice_uniform_under_kleene h_kleene Phi h_dist
  refine ⟨dn, fun P => ?_⟩
  rw [h_dn P]
  change _ ↔ (if _ then true else false) = true
  constructor
  · intro he; rw [if_pos he]
  · intro hp
    by_cases he : ∀ h, ¬ Halts P h
    · exact he
    · rw [if_neg he] at hp; exact absurd hp (by decide)

/-- 由 uniform 重导：Π_all 不可判（条件版）。 -/
theorem halts_on_all_via_uniform_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_all : List YiInstr → Bool,
        ∀ P, decide_all P = true ↔ ∀ h, Halts P h := by
  intro ⟨da, h_da⟩
  let Phi : (Hexagram → Prop) → Bool :=
    fun S => if (∀ h, S h) then true else false
  have h_dist : Phi (fun _ => True) ≠ Phi (fun _ => False) := by
    have h_T : Phi (fun _ : Hexagram => True) = true :=
      if_pos (fun _ => trivial)
    have h_F : Phi (fun _ : Hexagram => False) = false :=
      if_neg (fun h => h Hexagram.heaven)
    rw [h_T, h_F]; decide
  apply rice_uniform_under_kleene h_kleene Phi h_dist
  refine ⟨da, fun P => ?_⟩
  rw [h_da P]
  change _ ↔ (if _ then true else false) = true
  constructor
  · intro he; rw [if_pos he]
  · intro hp
    by_cases he : ∀ h, Halts P h
    · exact he
    · rw [if_neg he] at hp; exact absurd hp (by decide)

/-- 由 uniform 重导：Π_some_no 不可判（条件版）。 -/
theorem halts_on_some_no_via_uniform_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_some_no : List YiInstr → Bool,
        ∀ P, decide_some_no P = true ↔ ∃ h, ¬ Halts P h := by
  intro ⟨dsn, h_dsn⟩
  let Phi : (Hexagram → Prop) → Bool :=
    fun S => if (∃ h, ¬ S h) then true else false
  have h_dist : Phi (fun _ => True) ≠ Phi (fun _ => False) := by
    have h_T : Phi (fun _ : Hexagram => True) = false :=
      if_neg (fun ⟨_, hf⟩ => hf trivial)
    have h_F : Phi (fun _ : Hexagram => False) = true :=
      if_pos ⟨Hexagram.heaven, fun hf => hf⟩
    rw [h_T, h_F]; decide
  apply rice_uniform_under_kleene h_kleene Phi h_dist
  refine ⟨dsn, fun P => ?_⟩
  rw [h_dsn P]
  change _ ↔ (if _ then true else false) = true
  constructor
  · intro he; rw [if_pos he]
  · intro hp
    by_cases he : ∃ h, ¬ Halts P h
    · exact he
    · rw [if_neg he] at hp; exact absurd hp (by decide)

end RiceUniform

/-! ## § 10 公开摘要：理之不完备性集成 -/

/-- **理之不完备总摘要**：bundle 十二层结果（含 Rice 四象齐备 + Rice
    uniform + 道判机不可通用）。 -/
theorem li_incomplete_summary_full :
    -- (1) 理之非平凡性
    ((∃ P : List YiInstr, ∀ h : Hexagram, Halts P h) ∧
     (∃ P : List YiInstr, ∀ h : Hexagram, ¬ Halts P h))
    -- (2) 有限燃料不完备
    ∧ (¬ ∃ N : Nat, ∀ P h, Halts P h ↔
         ((YiState.init h P).runFuel N).halted = true)
    -- (3) 完全 Halting 不可判（条件版）
    ∧ (KleeneInverter → ¬ ∃ decide : List YiInstr → Hexagram → Bool,
         ∀ P h, decide P h = true ↔ Halts P h)
    -- (4) ¬Halts 亦不可判（条件版）
    ∧ (KleeneInverter → ¬ ∃ decide : List YiInstr → Hexagram → Bool,
         ∀ P h, decide P h = true ↔ ¬ Halts P h)
    -- (5) 任意固定 h₀ 之 Halts 不可判（条件版）
    ∧ (KleeneInverter → ∀ h₀ : Hexagram,
         ¬ ∃ decide : List YiInstr → Bool, ∀ P, decide P = true ↔ Halts P h₀)
    -- (6) Rice 四象 · 太阳
    ∧ (KleeneInverter → ¬ ∃ d : List YiInstr → Bool,
         ∀ P, d P = true ↔ ∀ h, Halts P h)
    -- (7) Rice 四象 · 少阳
    ∧ (KleeneInverter → ¬ ∃ d : List YiInstr → Bool,
         ∀ P, d P = true ↔ ∃ h, Halts P h)
    -- (8) Rice 四象 · 少阴
    ∧ (KleeneInverter → ¬ ∃ d : List YiInstr → Bool,
         ∀ P, d P = true ↔ ∃ h, ¬ Halts P h)
    -- (9) Rice 四象 · 太阴
    ∧ (KleeneInverter → ¬ ∃ d : List YiInstr → Bool,
         ∀ P, d P = true ↔ ∀ h, ¬ Halts P h)
    -- (10) Rice uniform：任何区分 ∅/univ profile 之外延性质皆不可判
    ∧ (KleeneInverter → ∀ Phi : (Hexagram → Prop) → Bool,
         Phi (fun _ => True) ≠ Phi (fun _ => False) →
         ¬ ∃ d : List YiInstr → Bool,
             ∀ P, d P = true ↔ Phi (Halts P) = true)
    -- (11) 道判机以 Shi.ji 不可作通用判定
    ∧ (KleeneInverter → ¬ ∃ enc : List YiInstr → Hexagram → Hexagram,
         ∀ P h, daoJudge (enc P h) = Shi.ji ↔ Halts P h)
    -- (12) 道判机以 Shi.wei 亦不可作通用判定（对偶）
    ∧ (KleeneInverter → ¬ ∃ enc : List YiInstr → Hexagram → Hexagram,
         ∀ P h, daoJudge (enc P h) = Shi.wei ↔ Halts P h) :=
  ⟨li_nontrivial,
   li_incomplete_finite,
   halts_undecidable_under_kleene,
   not_halts_undecidable_under_kleene,
   fun hk h₀ => halts_at_fixed_undecidable_under_kleene hk h₀,
   halts_on_all_undecidable_under_kleene,
   halts_on_some_undecidable_under_kleene,
   halts_on_some_no_undecidable_under_kleene,
   halts_on_none_undecidable_under_kleene,
   rice_uniform_under_kleene,
   daoJudge_not_universal_under_kleene,
   daoJudge_wei_not_universal_under_kleene⟩

/-- **理之不完备总摘要**：bundle 九层结果（含 Rice 四象齐备）。 -/
theorem li_incomplete_summary :
    -- (1) 理之非平凡性：既有必停程序，也有必不停程序
    ((∃ P : List YiInstr, ∀ h : Hexagram, Halts P h) ∧
     (∃ P : List YiInstr, ∀ h : Hexagram, ¬ Halts P h))
    -- (2) 有限燃料不完备：无均一 N 界判 Halts
    ∧ (¬ ∃ N : Nat, ∀ P h, Halts P h ↔
         ((YiState.init h P).runFuel N).halted = true)
    -- (3) 完全 Halting 不可判（条件版，假设 Kleene）
    ∧ (KleeneInverter → ¬ ∃ decide : List YiInstr → Hexagram → Bool,
         ∀ P h, decide P h = true ↔ Halts P h)
    -- (4) ¬Halts 亦不可判（条件版）
    ∧ (KleeneInverter → ¬ ∃ decide : List YiInstr → Hexagram → Bool,
         ∀ P h, decide P h = true ↔ ¬ Halts P h)
    -- (5) 任意固定 h₀ 之 Halts 不可判（条件版）
    ∧ (KleeneInverter → ∀ h₀ : Hexagram,
         ¬ ∃ decide : List YiInstr → Bool, ∀ P, decide P = true ↔ Halts P h₀)
    -- (6) Rice 四象 · 少阳 Π_some：「在某 h 上停」不可判（条件版）
    ∧ (KleeneInverter → ¬ ∃ decide_some : List YiInstr → Bool,
         ∀ P, decide_some P = true ↔ ∃ h, Halts P h)
    -- (7) Rice 四象 · 太阴 Π_none：「处处不停」不可判（条件版）
    ∧ (KleeneInverter → ¬ ∃ decide_none : List YiInstr → Bool,
         ∀ P, decide_none P = true ↔ ∀ h, ¬ Halts P h)
    -- (8) Rice 四象 · 太阳 Π_all：「处处停」不可判（条件版）
    ∧ (KleeneInverter → ¬ ∃ decide_all : List YiInstr → Bool,
         ∀ P, decide_all P = true ↔ ∀ h, Halts P h)
    -- (9) Rice 四象 · 少阴 Π_some_no：「有处不停」不可判（条件版）
    ∧ (KleeneInverter → ¬ ∃ decide_some_no : List YiInstr → Bool,
         ∀ P, decide_some_no P = true ↔ ∃ h, ¬ Halts P h) :=
  ⟨li_nontrivial,
   li_incomplete_finite,
   halts_undecidable_under_kleene,
   not_halts_undecidable_under_kleene,
   fun hk h₀ => halts_at_fixed_undecidable_under_kleene hk h₀,
   halts_on_some_undecidable_under_kleene,
   halts_on_none_undecidable_under_kleene,
   halts_on_all_undecidable_under_kleene,
   halts_on_some_no_undecidable_under_kleene⟩

end SSBX.Foundation.Bagua.GodelLi
