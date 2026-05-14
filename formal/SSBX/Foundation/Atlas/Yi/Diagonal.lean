/-
# Foundation.Atlas.Yi.Diagonal — 理之不完备 · 哥德尔在 R 8 (Atlas-Yi 形)

Companion document: `wen-algebra` v0.6, §10.7 (Interpreter Foundation),
§9 (Atlas separation).

This file ports the headline **incompleteness-of-Li** theorem to the
language-independent `R 8`-machine of `Foundation/Wen/Core/`.  The proof
kernel is the standard diagonal argument (Kleene's recursion-based
Halting undecidability), expressed here over the canonical `R 8` ISA
rather than the Yi-named `YiInstr`.

## Doctrine: where this lives

Per `wen-algebra` v0.6 §9, this file is an **Atlas overlay**: a
Yi-flavoured naming hook (the "Yi 道理二分" mediating frame) on a
**language-independent** kernel (the diagonal argument on `R 8`).  The
overlay status is reflected purely in the namespace (`Atlas.Yi.Diagonal`);
no Yi-specific machinery (Hexagram / Shi / YiInstr) is imported.

The legacy Bagua-flavoured version (`Foundation/Bagua/GodelLi.lean`)
remains as a 1275-LOC YiInstr-shaped proof.  This file is its
**Atlas-Yi**, language-independent reformulation in ~500 LOC.

## Architecture (per `GodelLi` § 1-7 path)

  § 1   Halts predicate (Σ₁) + concrete witnesses
        - `haltProg` halts in 1 fuel
        - `loopProg` (= `[.jump 0]`) never halts
  § 2   Finite-fuel incompleteness: ∀ N, ∃ counterexample
        — provable without Kleene; uses `slowProg N := N nops + halt`
  § 3   Universality hypothesis: `KleeneInverter` (Prop, no axiom)
        — no new axiom; conditional formulation
  § 4   Diagonal: `halts_undecidable_under_kleene`  ★ main theorem
        — proved via "decider exists ⇒ contradiction" diagonal
  § 5   Rice-style corollaries: 「处处停」 / 「处处不停」 unfeitable
        - all proved under the same hypothesis

## 道理二分 (Dao-Li bifurcation), Atlas-Yi form

  - **道** (Dao) = the meta-theory (Lean kernel)
  - **理** (Li) = the object theory (this file's `Instr` machine on
    `R 8`, recursively enumerable)
  - This file proves a 道-level theorem ABOUT 理: "Li, if universal,
    cannot internally decide its own halting predicate".

This is the precise formal statement of 「道可道，非常道」 at the Atlas-Yi
layer, in 语言无关 (language-independent) form on `R 8`.

## Constraints obeyed

  * No `sorry`.
  * No new `axiom`s.
  * Imports stay in `Foundation/R/*` and `Foundation/Wen/Core/*`.
  * **No** dependency on `Foundation/Bagua/`, `Foundation/Yi/`,
    or `Foundation/Bagua/BaguaTuring`.

## Doctrinal anchor

  * `wen-algebra.md` v0.6 §10.7 (Interpreter Foundation, IsUniversal target).
  * `r8.md` v0.2 §15.10 (Interpreter primitives).
  * Atlas separation: `wen-algebra.md` v0.6 §9.
-/

import SSBX.Foundation.Wen.Core

namespace SSBX.Foundation.Atlas.Yi.Diagonal

open SSBX.Foundation.R
open SSBX.Foundation.Wen.Core

/-! ## § 1 Halts predicate (Σ₁) on the Wen.Core machine

The halting predicate on a `(program, input)` pair is the existential
fuel quantifier over `runFuel`'s halt flag.  This is the standard Σ₁
form: semi-decidable by direct simulation (each fixed-fuel test is
decidable by `Bool.decEq`).
-/

/-- **停机谓词** (`Halts`): program `p` on input `inp` halts iff there
    is a fuel bound at which `Wen.Core.runFuel` reaches `halted = true`.
    Σ₁-shaped: existential over `Nat`. -/
def Halts (p : List Instr) (inp : R 8) : Prop :=
  ∃ fuel : Nat, (runFuel p fuel (State.init inp)).halted = true

/-- Half of `Halts`: `Halts p inp` ↔ Σ₁-witness via `runFuel`. -/
theorem halts_iff_exists_fuel (p : List Instr) (inp : R 8) :
    Halts p inp ↔ ∃ fuel : Nat, (runFuel p fuel (State.init inp)).halted = true :=
  Iff.rfl

/-- Each fixed-fuel "halts within N" test is decidable.  Underlies
    the Σ₁ shape: `Halts = ∃ N, decidable-test`. -/
instance halts_within_decidable (p : List Instr) (inp : R 8) (n : Nat) :
    Decidable ((runFuel p n (State.init inp)).halted = true) :=
  inferInstance

/-! ### § 1.1 Concrete witness: `haltProg` halts -/

/-- `haltProg`: the singleton `[.halt]` program.  Halts in 1 fuel. -/
def haltProg : List Instr := [.halt]

/-- `haltProg` halts on every input within 1 fuel. -/
theorem haltProg_halts_at (inp : R 8) :
    (runFuel haltProg 1 (State.init inp)).halted = true := by
  -- runFuel haltProg 1 s = step haltProg s (since s.halted = false)
  -- step on init state fetches haltProg[0] = .halt, which sets halted = true
  rw [Examples.runFuel_succ_of_not_halted _ _ _
      (by rfl : (State.init inp).halted = false)]
  rfl

/-- `haltProg` is a `Halts` witness for every input. -/
theorem halts_haltProg (inp : R 8) : Halts haltProg inp :=
  ⟨1, haltProg_halts_at inp⟩

/-! ### § 1.2 Concrete witness: `loopProg` never halts -/

/-- `loopProg`: jump-to-self.  Never halts. -/
def loopProg : List Instr := [.jump 0]

/-- One step of `loopProg` from the init state returns the init state. -/
theorem step_loopProg_init (inp : R 8) :
    step loopProg (State.init inp) = State.init inp := by
  show (if (State.init inp).halted = true then State.init inp
        else match loopProg[(State.init inp).pc]? with
          | none => { State.init inp with halted := true }
          | some instr => executeInstr instr (State.init inp))
      = State.init inp
  rfl

/-- `loopProg` never reaches a halted state — every fuel returns
    the init state. -/
theorem loopProg_runFuel_init (inp : R 8) (n : Nat) :
    runFuel loopProg n (State.init inp) = State.init inp := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Examples.runFuel_succ_of_not_halted _ _ _
          (by rfl : (State.init inp).halted = false)]
      rw [step_loopProg_init]
      exact ih

/-- `loopProg` never reaches a halted state. -/
theorem loopProg_never_halts_at (inp : R 8) (n : Nat) :
    (runFuel loopProg n (State.init inp)).halted = false := by
  rw [loopProg_runFuel_init]
  rfl

/-- **loopProg 永不停机**: concrete witness of non-termination. -/
theorem loopProg_not_halts (inp : R 8) : ¬ Halts loopProg inp := by
  intro ⟨n, hn⟩
  have : (runFuel loopProg n (State.init inp)).halted = false :=
    loopProg_never_halts_at inp n
  rw [this] at hn
  exact Bool.false_ne_true hn

/-! ### § 1.3 Phase 1 summary -/

/-- **§ 1 总结** : Halts is well-defined; the object theory is non-trivial
    (it has both halting and non-halting programs).  Atlas-Yi form. -/
theorem phase1_summary :
    (∀ inp : R 8, Halts haltProg inp)
    ∧ (∀ inp : R 8, ¬ Halts loopProg inp)
    ∧ ((∃ p : List Instr, ∀ inp : R 8, Halts p inp) ∧
       (∃ p : List Instr, ∀ inp : R 8, ¬ Halts p inp)) :=
  ⟨halts_haltProg, loopProg_not_halts,
   ⟨⟨haltProg, halts_haltProg⟩, ⟨loopProg, loopProg_not_halts⟩⟩⟩

/-! ## § 2 Finite-fuel incompleteness: no uniform `N`-fuel bound

For every candidate fuel bound `N`, we exhibit a program `slowProg N`
that halts but requires more than `N` fuel.  This says: **no single
fuel bound suffices** for the halting predicate.  Provable without
Kleene; the weakest provable form of Gödel-flavoured incompleteness.
-/

/-- **慢停程序** `slowProg N`: `N` nops then halt.  Halts in `N+1` fuel,
    but not in `N`. -/
def slowProg (N : Nat) : List Instr := List.replicate N .nop ++ [.halt]

/-! ### § 2.1 Program-lookup lemmas -/

/-- `slowProg N` at index `k < N` is `nop`. -/
theorem slowProg_get_lt (N k : Nat) (hk : k < N) :
    (slowProg N)[k]? = some .nop := by
  unfold slowProg
  rw [List.getElem?_append_left (by simp [hk])]
  simp [hk]

/-- `slowProg N` at index `N` is `halt`. -/
theorem slowProg_get_eq (N : Nat) :
    (slowProg N)[N]? = some .halt := by
  unfold slowProg
  rw [List.getElem?_append_right (by simp)]
  simp

/-! ### § 2.2 `runFuel_succ_right` — right-step association

`runFuel (n+1) s = step (runFuel n s)` once both sides agree on the
halt case.  This is the standard "step iteration is associative":
running `n` steps then one more = running `n+1` steps.
-/

/-- `runFuel (n+1) s = step (runFuel n s)`.  Together with
    `runFuel_succ` this gives the "right-step" rewrite needed for
    invariant-style proofs about `slowProg`. -/
theorem runFuel_succ_right (prog : List Instr) (n : Nat) (s : State) :
    runFuel prog (n+1) s = step prog (runFuel prog n s) := by
  induction n generalizing s with
  | zero =>
      -- runFuel 1 s = if s.halted then s else step prog s
      -- step prog (runFuel 0 s) = step prog s
      -- Both reduce identically to step prog s when s is not halted,
      -- and to s when s is halted (since step prog s = s).
      by_cases h : s.halted = true
      · -- both sides equal s
        have hL : runFuel prog 1 s = s := by
          show (if s.halted = true then s else runFuel prog 0 (step prog s)) = s
          simp [h]
        have hR : step prog (runFuel prog 0 s) = s := by
          show step prog s = s
          exact step_halted prog s h
        rw [hL, hR]
      · have h' : s.halted = false := by
          match hh : s.halted with
          | true => exact absurd hh h
          | false => rfl
        have hL : runFuel prog 1 s = step prog s := by
          show (if s.halted = true then s else runFuel prog 0 (step prog s)) = step prog s
          simp [h']
        rw [hL]
        rfl
  | succ k ih =>
      by_cases h : s.halted = true
      · have hL : runFuel prog (k+2) s = s := by
          have h2 : runFuel prog (k+2) s = runFuel prog (k+1) s := by
            rw [show (k+2) = (k+1)+1 from rfl]
            show (if s.halted = true then s else runFuel prog (k+1) (step prog s))
                = runFuel prog (k+1) s
            simp [h]
            exact (runFuel_halt_idempotent prog (k+1) s h).symm
          rw [h2]
          exact runFuel_halt_idempotent prog (k+1) s h
        have hR : step prog (runFuel prog (k+1) s) = s := by
          rw [runFuel_halt_idempotent prog (k+1) s h, step_halted prog s h]
        rw [hL, hR]
      · have h' : s.halted = false := by
          match hh : s.halted with
          | true => exact absurd hh h
          | false => rfl
        -- runFuel (k+2) s = runFuel (k+1) (step prog s) (by h')
        have hL : runFuel prog (k+2) s = runFuel prog (k+1) (step prog s) := by
          show (if s.halted = true then s else runFuel prog (k+1) (step prog s))
              = runFuel prog (k+1) (step prog s)
          simp [h']
        -- runFuel (k+1) s = runFuel k (step prog s) (by h')
        have hR : runFuel prog (k+1) s = runFuel prog k (step prog s) := by
          show (if s.halted = true then s else runFuel prog k (step prog s))
              = runFuel prog k (step prog s)
          simp [h']
        rw [hL, hR]
        exact ih (step prog s)

/-! ### § 2.3 Step shapes on `nop` and `halt` -/

/-- One `step` on a non-halted state with `nop` at the program counter
    advances `pc` by 1, preserving everything else. -/
theorem step_nop_at (prog : List Instr) (s : State) (h_halt : s.halted = false)
    (h_lookup : prog[s.pc]? = some .nop) :
    step prog s = { s with pc := s.pc + 1 } := by
  unfold step
  simp [h_halt, h_lookup, executeInstr]

/-- One `step` on a non-halted state with `halt` at the program counter
    flips `halted` to `true`. -/
theorem step_halt_at (prog : List Instr) (s : State) (h_halt : s.halted = false)
    (h_lookup : prog[s.pc]? = some .halt) :
    step prog s = { s with halted := true } := by
  unfold step
  simp [h_halt, h_lookup, executeInstr]

/-! ### § 2.4 Invariant + main fuel-bound lemmas -/

/-- Invariant: after `k` ≤ `N` steps, `slowProg N` has advanced pc to
    `k`, with `cur = inp`, no history, no halt. -/
theorem slowProg_state_after (N : Nat) (inp : R 8) (k : Nat) (hk : k ≤ N) :
    runFuel (slowProg N) k (State.init inp)
      = { cur := inp, history := [], pc := k, halted := false } := by
  induction k with
  | zero => rfl
  | succ j ih =>
      have hj : j ≤ N := Nat.le_of_succ_le hk
      have hj_lt : j < N := Nat.lt_of_succ_le hk
      rw [runFuel_succ_right, ih hj]
      -- now apply step at pc = j; program[j] = nop because j < N
      have h_lookup0 : (slowProg N)[j]? = some .nop := slowProg_get_lt N j hj_lt
      -- target state has pc = j, halted = false
      have h_halt :
          ({ cur := inp, history := [], pc := j, halted := false } : State).halted = false := rfl
      have h_pc_eq :
          ({ cur := inp, history := [], pc := j, halted := false } : State).pc = j := rfl
      -- rewrite the lookup with the state's pc form
      have h_lookup :
          (slowProg N)[({ cur := inp, history := [], pc := j, halted := false } : State).pc]?
            = some .nop := by
        rw [h_pc_eq]; exact h_lookup0
      rw [step_nop_at (slowProg N)
          ({ cur := inp, history := [], pc := j, halted := false } : State)
          h_halt h_lookup]

/-- After `N` fuel, `slowProg N` is NOT halted. -/
theorem slowProg_runFuel_N_not_halted (N : Nat) (inp : R 8) :
    (runFuel (slowProg N) N (State.init inp)).halted = false := by
  rw [slowProg_state_after N inp N (Nat.le.refl)]

/-- After `N+1` fuel, `slowProg N` IS halted. -/
theorem slowProg_runFuel_succ_halted (N : Nat) (inp : R 8) :
    (runFuel (slowProg N) (N+1) (State.init inp)).halted = true := by
  rw [runFuel_succ_right, slowProg_state_after N inp N (Nat.le.refl)]
  have h_lookup0 : (slowProg N)[N]? = some .halt := slowProg_get_eq N
  have h_halt :
      ({ cur := inp, history := [], pc := N, halted := false } : State).halted = false := rfl
  have h_pc_eq :
      ({ cur := inp, history := [], pc := N, halted := false } : State).pc = N := rfl
  have h_lookup :
      (slowProg N)[({ cur := inp, history := [], pc := N, halted := false } : State).pc]?
        = some .halt := by
    rw [h_pc_eq]; exact h_lookup0
  rw [step_halt_at (slowProg N)
      ({ cur := inp, history := [], pc := N, halted := false } : State)
      h_halt h_lookup]

/-- `slowProg N` halts on every input. -/
theorem halts_slowProg (N : Nat) (inp : R 8) : Halts (slowProg N) inp :=
  ⟨N+1, slowProg_runFuel_succ_halted N inp⟩

/-! ### § 2.5 Main finite-fuel incompleteness -/

/-- **理之有限燃料不完备** (Atlas-Yi form): no uniform fuel bound `N`
    decides Halts.  Each candidate `N` is defeated by `slowProg N`.

    Provable without Kleene; captures: 「理之停机不被任何均一燃料 N 所封闭」. -/
theorem li_incomplete_finite :
    ¬ ∃ N : Nat, ∀ (p : List Instr) (inp : R 8),
        Halts p inp ↔ (runFuel p N (State.init inp)).halted = true := by
  intro ⟨N, hN⟩
  -- counterexample: slowProg N on the zero input
  have h_halts : Halts (slowProg N) (0 : R 8) := halts_slowProg N _
  have h_not_halted_at_N :
      (runFuel (slowProg N) N (State.init (0 : R 8))).halted = false :=
    slowProg_runFuel_N_not_halted N _
  have := (hN (slowProg N) (0 : R 8)).mp h_halts
  rw [h_not_halted_at_N] at this
  exact Bool.false_ne_true this

/-! ### § 2.6 Phase 2 summary -/

/-- **§ 2 总结**: finite-fuel incompleteness fully formalised. -/
theorem phase2_summary :
    (∀ N inp, Halts (slowProg N) inp)
    ∧ (∀ N inp, (runFuel (slowProg N) N (State.init inp)).halted = false)
    ∧ (¬ ∃ N : Nat, ∀ p inp, Halts p inp ↔
         (runFuel p N (State.init inp)).halted = true) :=
  ⟨fun N inp => halts_slowProg N inp,
   fun N inp => slowProg_runFuel_N_not_halted N inp,
   li_incomplete_finite⟩

/-! ## § 3 The Kleene-inverter hypothesis (no new axiom)

We do not introduce a Kleene axiom.  Instead, we follow the Atlas-Yi
doctrine: the diagonal theorem is stated **conditionally** on the
existence of a self-referential inverter (the Kleene-recursion
property).  The conditional theorem becomes unconditional once
`Foundation/Wen/MetaInterp/` constructs an explicit witness.

Why conditional: per the wen-algebra plan, the diagonal kernel is
generic over any universal-interpreter / s-m-n / Kleene-recursion
backbone.  We expose the dependency explicitly rather than
re-axiomatising it.
-/

/-- A *Kleene-style inverter* for a Lean Bool decider on `(p, inp)`:
    given `decide : List Instr → R 8 → Bool`, the inverter exhibits
    a program `D` such that `D` halts on every input `inp` iff
    `decide D inp = false`.

    This is **not** an axiom; it is the conditional hypothesis under
    which the diagonal lemma yields contradiction.  Future work in
    `Foundation/Wen/MetaInterp/` will derive `KleeneInverter` from
    `IsUniversal U` + an s-m-n theorem; here we state it abstractly
    and prove the diagonal under this hypothesis. -/
def KleeneInverter : Prop :=
  ∀ decide : List Instr → R 8 → Bool,
    ∃ D : List Instr, ∀ inp : R 8, Halts D inp ↔ decide D inp = false

/-! ## § 4 Diagonal: conditional halts-undecidability ★

The core lemma: under `KleeneInverter`, no Lean `Bool` function can
decide `Halts`.  Standard diagonal: given decider, invert to a
self-referential program; contradiction.
-/

/-- **理之不完备主定理** (Atlas-Yi form, conditional):
    under a Kleene-style inverter, the halting predicate `Halts` on
    `(List Instr, R 8)` is not decidable by any Lean Bool function.

    Diagonal argument: suppose decider `decide` exists.  Apply
    `KleeneInverter` to get `D` with `Halts D inp ↔ decide D inp = false`.
    But by assumption `decide D inp = true ↔ Halts D inp`.  Chain to
    get `decide D inp = true ↔ decide D inp = false`.  Contradiction. -/
theorem halts_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide : List Instr → R 8 → Bool,
        ∀ p inp, decide p inp = true ↔ Halts p inp := by
  intro ⟨decide, hd⟩
  obtain ⟨D, hD⟩ := h_kleene decide
  -- pick a specific input (the zero vector)
  let inp : R 8 := 0
  have h_iff_halts : decide D inp = true ↔ Halts D inp := hd D inp
  have h_iff_invert : Halts D inp ↔ decide D inp = false := hD inp
  -- contradiction: decide D inp = true ↔ Halts D inp ↔ decide D inp = false
  cases hb : decide D inp with
  | true =>
      have h_halts : Halts D inp := h_iff_halts.mp hb
      have h_false : decide D inp = false := h_iff_invert.mp h_halts
      rw [hb] at h_false
      contradiction
  | false =>
      have h_halts : Halts D inp := h_iff_invert.mpr hb
      have h_true : decide D inp = true := h_iff_halts.mpr h_halts
      rw [hb] at h_true
      contradiction

/-- **¬Halts 不可判** (Atlas-Yi form, conditional): the complement of
    `Halts` is likewise undecidable.

    Diagonal via `!decide`: substitute the negated decider into
    `KleeneInverter` to get `Halts D inp ↔ ¬ Halts D inp`. -/
theorem not_halts_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide : List Instr → R 8 → Bool,
        ∀ p inp, decide p inp = true ↔ ¬ Halts p inp := by
  intro ⟨decide_neg, h_neg⟩
  obtain ⟨D, hD⟩ := h_kleene (fun p inp => !decide_neg p inp)
  let inp : R 8 := 0
  have h_kleene_iff : Halts D inp ↔ (!decide_neg D inp) = false := hD inp
  have h_negbool : (!decide_neg D inp) = false ↔ decide_neg D inp = true := by
    cases decide_neg D inp <;> simp
  have h_neg_spec : decide_neg D inp = true ↔ ¬ Halts D inp := h_neg D inp
  -- chain: Halts D inp ↔ decide_neg D inp = true ↔ ¬ Halts D inp
  have h_contra : Halts D inp ↔ ¬ Halts D inp :=
    h_kleene_iff.trans (h_negbool.trans h_neg_spec)
  by_cases h_h : Halts D inp
  · exact h_contra.mp h_h h_h
  · exact h_h (h_contra.mpr h_h)

/-- **固定 input 之 Halts 不可判** (Atlas-Yi form, conditional):
    even with `inp` fixed to `0`, deciding `Halts p 0` over the
    program alone is undecidable. -/
theorem halts_at_zero_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_zero : List Instr → Bool,
        ∀ p, decide_zero p = true ↔ Halts p (0 : R 8) := by
  intro ⟨decide_zero, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun p _ => decide_zero p)
  have h_kleene_iff : Halts D (0 : R 8) ↔ decide_zero D = false := hD (0 : R 8)
  have h_dec_iff : decide_zero D = true ↔ Halts D (0 : R 8) := h_dec D
  cases hb : decide_zero D with
  | true =>
      have hh : Halts D (0 : R 8) := h_dec_iff.mp hb
      have hf : decide_zero D = false := h_kleene_iff.mp hh
      rw [hb] at hf
      contradiction
  | false =>
      have hh : Halts D (0 : R 8) := h_kleene_iff.mpr hb
      have ht : decide_zero D = true := h_dec_iff.mpr hh
      rw [hb] at ht
      contradiction

/-- **任意固定 input 之 Halts 不可判** (parametrised). -/
theorem halts_at_fixed_undecidable_under_kleene (h_kleene : KleeneInverter)
    (inp₀ : R 8) :
    ¬ ∃ decide_h : List Instr → Bool,
        ∀ p, decide_h p = true ↔ Halts p inp₀ := by
  intro ⟨decide_h, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun p _ => decide_h p)
  have h_kleene_iff : Halts D inp₀ ↔ decide_h D = false := hD inp₀
  have h_dec_iff : decide_h D = true ↔ Halts D inp₀ := h_dec D
  cases hb : decide_h D with
  | true =>
      have hh : Halts D inp₀ := h_dec_iff.mp hb
      have hf : decide_h D = false := h_kleene_iff.mp hh
      rw [hb] at hf
      contradiction
  | false =>
      have hh : Halts D inp₀ := h_kleene_iff.mpr hb
      have ht : decide_h D = true := h_dec_iff.mpr hh
      rw [hb] at ht
      contradiction

/-! ## § 5 Rice-style corollaries

Standard "uniform program properties are undecidable" — four images:
* Π_all     ≡ `∀ inp, Halts p inp`
* Π_some    ≡ `∃ inp, Halts p inp`
* Π_some_no ≡ `∃ inp, ¬ Halts p inp`
* Π_none    ≡ `∀ inp, ¬ Halts p inp`

All four are undecidable under `KleeneInverter`.
-/

/-- **Π_some 不可判**: "halts on some input" is undecidable. -/
theorem halts_on_some_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_some : List Instr → Bool,
        ∀ p, decide_some p = true ↔ ∃ inp, Halts p inp := by
  intro ⟨decide_some, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun p _ => decide_some p)
  cases hb : decide_some D with
  | true =>
      obtain ⟨inp, h_halt⟩ := (h_dec D).mp hb
      have h_kl : Halts D inp ↔ decide_some D = false := hD inp
      rw [hb] at h_kl
      have hf : true = false := h_kl.mp h_halt
      contradiction
  | false =>
      have h_no_some : ¬ ∃ inp, Halts D inp := by
        intro he
        have hT : decide_some D = true := (h_dec D).mpr he
        rw [hb] at hT
        contradiction
      have h_zero : Halts D (0 : R 8) := (hD (0 : R 8)).mpr hb
      exact h_no_some ⟨(0 : R 8), h_zero⟩

/-- **Π_none 不可判**: "halts on no input" is undecidable. -/
theorem halts_on_none_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_none : List Instr → Bool,
        ∀ p, decide_none p = true ↔ ∀ inp, ¬ Halts p inp := by
  intro ⟨decide_none, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun p _ => !decide_none p)
  cases hb : decide_none D with
  | true =>
      have h_all_no : ∀ inp, ¬ Halts D inp := (h_dec D).mp hb
      have h_negkl : (!decide_none D) = false := by rw [hb]; decide
      have h_zero_halt : Halts D (0 : R 8) := (hD (0 : R 8)).mpr h_negkl
      exact (h_all_no (0 : R 8) h_zero_halt).elim
  | false =>
      have h_kl_all_no : ∀ inp, ¬ Halts D inp := by
        intro inp h_h
        have h_kl : (!decide_none D) = false := (hD inp).mp h_h
        rw [hb] at h_kl
        contradiction
      have h_dn_true : decide_none D = true := (h_dec D).mpr h_kl_all_no
      rw [hb] at h_dn_true
      contradiction

/-- **Π_all 不可判**: "halts on every input" is undecidable. -/
theorem halts_on_all_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_all : List Instr → Bool,
        ∀ p, decide_all p = true ↔ ∀ inp, Halts p inp := by
  intro ⟨decide_all, h_dec⟩
  obtain ⟨D, hD⟩ := h_kleene (fun p _ => decide_all p)
  cases hb : decide_all D with
  | true =>
      have h_all_halt : ∀ inp, Halts D inp := (h_dec D).mp hb
      have h_zero : Halts D (0 : R 8) := h_all_halt (0 : R 8)
      have h_kl : Halts D (0 : R 8) ↔ decide_all D = false := hD (0 : R 8)
      have hf : decide_all D = false := h_kl.mp h_zero
      rw [hb] at hf
      contradiction
  | false =>
      have h_all_halt : ∀ inp, Halts D inp := fun inp => (hD inp).mpr hb
      have h_dec_true : decide_all D = true := (h_dec D).mpr h_all_halt
      rw [hb] at h_dec_true
      contradiction

/-- **Π_some_no 不可判**: "fails to halt on some input" is undecidable. -/
theorem halts_on_some_no_undecidable_under_kleene (h_kleene : KleeneInverter) :
    ¬ ∃ decide_some_no : List Instr → Bool,
        ∀ p, decide_some_no p = true ↔ ∃ inp, ¬ Halts p inp := by
  intro ⟨decide_some_no, h_dec⟩
  -- reduce: !decide_some_no decides Π_all (∀ inp, Halts p inp)
  apply halts_on_all_undecidable_under_kleene h_kleene
  refine ⟨fun p => !decide_some_no p, fun p => ?_⟩
  show (!decide_some_no p) = true ↔ ∀ inp, Halts p inp
  cases hd : decide_some_no p with
  | true =>
      obtain ⟨inp_w, h_no_halt⟩ : ∃ inp, ¬ Halts p inp := (h_dec p).mp hd
      constructor
      · intro hb; simp at hb
      · intro h_all
        exact (h_no_halt (h_all inp_w)).elim
  | false =>
      have h_no_some : ¬ ∃ inp, ¬ Halts p inp := by
        intro he
        have h_dn_true : decide_some_no p = true := (h_dec p).mpr he
        rw [hd] at h_dn_true
        contradiction
      constructor
      · intro _ inp
        exact Classical.byContradiction fun h_no => h_no_some ⟨inp, h_no⟩
      · intro _
        rfl

/-! ### § 5.1 Rice 四象 (four-image bundle) -/

/-- **Rice 四象总定理** (Atlas-Yi form, conditional): all four uniform
    halting-style properties are undecidable. -/
theorem rice_four_images_under_kleene (h_kleene : KleeneInverter) :
    (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∀ inp, Halts p inp)
    ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∃ inp, Halts p inp)
    ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∃ inp, ¬ Halts p inp)
    ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∀ inp, ¬ Halts p inp) :=
  ⟨halts_on_all_undecidable_under_kleene h_kleene,
   halts_on_some_undecidable_under_kleene h_kleene,
   halts_on_some_no_undecidable_under_kleene h_kleene,
   halts_on_none_undecidable_under_kleene h_kleene⟩

/-! ## § 6 Public summary

A bundle that exposes:
* §§ 1-2 unconditional results (no Kleene needed)
* §§ 4-5 conditional results (under `KleeneInverter`)
-/

/-- **Public summary** (Atlas-Yi form): bundle of all proved results.

    Sections 1-2 are unconditional; sections 4-5 are conditional on
    `KleeneInverter`.  No new axiom introduced; no `sorry`. -/
theorem diagonal_summary :
    -- § 1: non-trivial halting
    ((∀ inp : R 8, Halts haltProg inp) ∧
     (∀ inp : R 8, ¬ Halts loopProg inp))
    -- § 2: finite-fuel incompleteness (unconditional)
    ∧ (¬ ∃ N : Nat, ∀ p inp,
         Halts p inp ↔ (runFuel p N (State.init inp)).halted = true)
    -- § 4: main diagonal (conditional on KleeneInverter)
    ∧ (KleeneInverter →
         ¬ ∃ decide : List Instr → R 8 → Bool,
             ∀ p inp, decide p inp = true ↔ Halts p inp)
    -- § 5: Rice four-images (conditional on KleeneInverter)
    ∧ (KleeneInverter →
         (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∀ inp, Halts p inp)
         ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∃ inp, Halts p inp)
         ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∃ inp, ¬ Halts p inp)
         ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∀ inp, ¬ Halts p inp)) :=
  ⟨⟨halts_haltProg, loopProg_not_halts⟩,
   li_incomplete_finite,
   halts_undecidable_under_kleene,
   rice_four_images_under_kleene⟩

end SSBX.Foundation.Atlas.Yi.Diagonal
