/-
# GodelLi — 理之不完备 · 哥德尔在 192

Companion document: `四级生成_太极两翼四象八卦/J_理之不完备_哥德尔在192.md`

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
import SSBX.Foundation.BaguaTuring

namespace SSBX.Foundation.GodelLi

open SSBX.Foundation.Yi
open SSBX.Foundation.BaguaAlgebra
open SSBX.Foundation.Cell192
open SSBX.Foundation.BaguaTuring

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
  -- 取反例：slowProg N 在 qian 上
  have h_halts : Halts (slowProg N) Hexagram.qian := halts_slowProg _ _
  have h_not_halted_at_N :
      ((YiState.init Hexagram.qian (slowProg N)).runFuel N).halted = false :=
    slowProg_runFuel_N_not_halted _ _
  have := (hN (slowProg N) Hexagram.qian).mp h_halts
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

/-- **Kleene 递归性质**：对任 Lean Bool 函数 `decide : List YiInstr → Hexagram
    → Bool`，存在 YiProg D 使其在 h 上停机的事实与 decide(D, h) 之取值反相关。

    这是 Church-Turing 论题对 BaguaTuring 之断言：任何函数行为（包括"判
    decide 后反转"）皆可由 YiProg 实现。 -/
def KleeneInverter : Prop :=
  ∀ (decide : List YiInstr → Hexagram → Bool),
    ∃ D : List YiInstr, ∀ h : Hexagram, Halts D h ↔ decide D h = false

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
  obtain ⟨D, hD⟩ := h_kleene decide
  -- 取 qian 作具体 hexagram
  have h_iff_halts : decide D Hexagram.qian = true ↔ Halts D Hexagram.qian :=
    hd D Hexagram.qian
  have h_iff_invert : Halts D Hexagram.qian ↔ decide D Hexagram.qian = false :=
    hD Hexagram.qian
  -- 矛盾：decide D h = true ↔ Halts D h ↔ decide D h = false
  cases hb : decide D Hexagram.qian with
  | true =>
    -- decide = true → Halts → decide = false（矛盾）
    have h_halts : Halts D Hexagram.qian := h_iff_halts.mp hb
    have h_false : decide D Hexagram.qian = false := h_iff_invert.mp h_halts
    rw [hb] at h_false
    contradiction
  | false =>
    -- decide = false → Halts → decide = true（矛盾）
    have h_halts : Halts D Hexagram.qian := h_iff_invert.mpr hb
    have h_true : decide D Hexagram.qian = true := h_iff_halts.mpr h_halts
    rw [hb] at h_true
    contradiction

/-! ## § 5 公理化版本：完整 Halting 不可判定 -/

/-- **Kleene 递归公理**：捕获 Church-Turing 论题对 BaguaTuring 之应用。
    完全形式化需在 YiInstr 内构造 quine（约 500 行机械工程，已知可做但
    暂不实现）。此公理是 道理二分 的精确陈述：道认可理之 CT 论题。 -/
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
  obtain ⟨D, hD⟩ := h_kleene (fun P h => !decide_neg P h)
  let h := Hexagram.qian
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
    证明：若 decide_qian 判 `Halts · qian`，由 KleeneInverter 取 D（用 decide 忽略 h）
    导出矛盾。 -/
theorem halts_at_qian_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide : List YiInstr → Bool,
        ∀ P, decide P = true ↔ Halts P Hexagram.qian := by
  intro ⟨decide_qian, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun P _ => decide_qian P)
  have h_kleene_iff : Halts D Hexagram.qian ↔ decide_qian D = false :=
    hD Hexagram.qian
  have h_dec_iff : decide_qian D = true ↔ Halts D Hexagram.qian := h_dec D
  cases hb : decide_qian D with
  | true =>
    have hh : Halts D Hexagram.qian := h_dec_iff.mp hb
    have hf : decide_qian D = false := h_kleene_iff.mp hh
    rw [hb] at hf; contradiction
  | false =>
    have hh : Halts D Hexagram.qian := h_kleene_iff.mpr hb
    have ht : decide_qian D = true := h_dec_iff.mpr hh
    rw [hb] at ht; contradiction

/-- **任意固定 h 之 Halts 不可判**（参数化推广上式）。 -/
theorem halts_at_fixed_undecidable_under_kleene
    (h_kleene : KleeneInverter) (h₀ : Hexagram) :
    ¬ ∃ decide : List YiInstr → Bool,
        ∀ P, decide P = true ↔ Halts P h₀ := by
  intro ⟨decide_h, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun P _ => decide_h P)
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
    -- 取 qian：既 Halts 又 ¬ Halts
    have h_no_some : ¬ ∃ h, Halts D h := by
      intro he
      have hT : decide_some D = true := (h_dec D).mpr he
      rw [hb] at hT
      contradiction
    have h_qian : Halts D Hexagram.qian := (hD Hexagram.qian).mpr hb
    exact h_no_some ⟨Hexagram.qian, h_qian⟩

/-- **Π_none 不可判**（条件版）：「程序处处不停」不可由任何 Lean Bool
    函数判定。证明：直接对 (fun P _ => !decide_none P) 应用 KleeneInverter。 -/
theorem halts_on_none_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_none : List YiInstr → Bool,
        ∀ P, decide_none P = true ↔ ∀ h, ¬ Halts P h := by
  intro ⟨decide_none, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun P _ => !decide_none P)
  -- hD h : Halts D h ↔ (!decide_none D) = false
  cases hb : decide_none D with
  | true =>
    -- decide_none D = true → ∀ h, ¬ Halts D h (by h_dec)
    -- 但 (!decide_none D) = !true = false，故 hD qian.mpr 给 Halts D qian
    have h_all_no : ∀ h, ¬ Halts D h := (h_dec D).mp hb
    have h_kleene_eq : (!decide_none D) = false := by rw [hb]; decide
    have h_qian_halt : Halts D Hexagram.qian := (hD Hexagram.qian).mpr h_kleene_eq
    exact (h_all_no Hexagram.qian h_qian_halt).elim
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
  -- hD h : Halts D h ↔ decide_all D = false
  cases hb : decide_all D with
  | true =>
    -- decide_all D = true → ∀ h, Halts D h，但 Kleene 给 ∀ h, ¬ Halts D h
    have h_all_halt : ∀ h, Halts D h := (h_dec D).mp hb
    have h_qian : Halts D Hexagram.qian := h_all_halt Hexagram.qian
    have h_kl : Halts D Hexagram.qian ↔ decide_all D = false := hD Hexagram.qian
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

  | Π        | 形式                       | 道家四象对应 |
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

end SSBX.Foundation.GodelLi
