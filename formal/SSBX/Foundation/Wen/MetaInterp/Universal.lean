/-
# Universal — universal-compose theorem for `metaInterpProg`

This file states the **universal-compose interface** (B.T4.G.U0): the
assembled `metaInterpProg : List YiInstr` of length 88 (see `Assembly.lean`)
has an unconditional zero-step/prologue theorem, and the exact-fuel arbitrary
program theorem is derived from explicit semantic obligations.

The full proof is multi-day work; this file's scope is a clean, readable
**theorem statement** plus a structured **semantic-obligation interface**
(U.1–U.4), so downstream slots can provide concrete witnesses without
changing the public composition theorem.

## Strategy-B caveat

`metaInterpProg` uses fixed default arguments for the 5 parameterized opcodes
(setShi → dao, flipYao → 0, branchYaoEq → 0 0 0, branchShiEq → dao 0,
jump → 0).  Hence the theorem as stated below is true only when the simulated
program `P` consists of opcodes whose parameters happen to match those
defaults; **full universality** requires sub-dispatch trees per parameterized
arm (see `SubDispatch_BranchShiEq` / `SubDispatch_BranchYaoEq`).  This is
sub-obligation U.5 (documentation-only at this layer; promotion is the next
ticket).

## Roadmap for discharging the semantic obligations

| Tag                | Status | Cites                                                                |
|--------------------|--------|----------------------------------------------------------------------|
| `B.T4.G.U0`        | proved conditionally | exact-fuel composition from explicit semantic obligations |
| `B.T4.G.U0a`       | proved | zero-step/prologue composition |
| `B.T4.G.U1`        | obligation field | `PrologueProg.postPrologueContract`,                         |
|                    |        | `Assembly.metaInterpProg_routes_outerLoop_to_fetch`,                 |
|                    |        | `Assembly.metaInterpProg_fetch_routes_*_exact`,                      |
|                    |        | `Assembly.metaInterpProg_dispatch_routes_<op>_at_fuel` × 12,         |
|                    |        | `ExecuteBlocks.Aggregate.executeBlock_<op>_local_effect`             |
| `B.T4.G.U2`        | obligation field | induction on iteration count `k`, applying U.1               |
| `B.T4.G.U3`        | obligation field | halt-flag closure: once sim.halted, META loops in halt block |
| `B.T4.G.U4`        | proved | fuel arithmetic — pure `omega`/`Nat.le_*` reasoning                  |
| `B.T4.G.U5`        | proved boundary | strategy-B fixed-parameter coverage is not full program space |
-/
import SSBX.Foundation.Wen.MetaInterp.Assembly

namespace SSBX.Foundation.Wen.MetaInterp.Universal

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Assembly

/-! ## § 1  Universal-compose theorem (U.0) -/

/-- A generous fuel bound: each simulated instruction takes at most
    `metaInterpProg.length` (= 88) fuel ticks of META execution; the
    additive `+ 5` accounts for a budget cushion.  This is an upper
    budget, not the exact fuel for the `n`-step semantic theorem. -/
def metaFuelBound (n : Nat) : Nat := metaInterpProg.length * (n + 5)

/-- The META starting state encoding the input pair `(P, h)`: cur = (h, jin),
    history = encProg P, pc = 0, prog = metaInterpProg, halted = false.

    This is exactly `RunWith h metaInterpProg (ProgEnc.encProg P)`. -/
def metaStart (h : Hexagram) (P : List YiInstr) : YiState :=
  RunWith h metaInterpProg (ProgEnc.encProg P)

/-! ### Forward-declared placeholder for the post-prologue META state -/

/-- The META state immediately after the 5-fuel prologue: at pc =
    `outerLoopOffset` with history = `encMetaHistory h (YiState.init h P)`. -/
def metaPostPrologue (h : Hexagram) (P : List YiInstr) : YiState :=
  metaStateOf h (YiState.init h P) metaInterpProg outerLoopOffset

/-- Steady-state META loop state: after the first outer-loop entry jump, each
    execute block returns directly to `fetchOffset`, not to `outerLoopOffset`. -/
def metaFetchState (h : Hexagram) (sim : YiState) : YiState :=
  metaStateOf h sim metaInterpProg fetchOffset

/-- **U.0a — Embedded prologue.**  The first five instructions of the full
    `metaInterpProg` are the prologue, so the canonical META start state reaches
    the canonical post-prologue META state in exactly five fuel ticks. -/
theorem metaStart_runFuel_five_eq_postPrologue
    (h : Hexagram) (P : List YiInstr) :
    (metaStart h P).runFuel 5 = metaPostPrologue h P := by
  rfl

/-! ## § 2  Sub-obligations U.1 – U.4

  These are stated with their **real conclusions** (no `True := trivial`
  placeholders), but as an explicit evidence interface rather than hidden
  proof holes.  Concrete semantic witnesses belong to the fetch/dispatch/
  execute-block wave; `metaInterpProg_simulates` (U.0) below is derived from
  these obligations by composition. -/

/-- Per-iteration fuel cost: bounded by `metaInterpProg.length` (= 88).
    A single outer-loop iteration walks
    `outerLoop → fetch → dispatch → executeBlock → jump-back`, which
    touches every instruction at most once. -/
def loopFuelPerIter : Nat := metaInterpProg.length

/-- Exact fuel for the `n`-step semantic-compose theorem:
    5 prologue ticks plus `n` full loop iterations. -/
def exactMetaFuel (n : Nat) : Nat := 5 + loopFuelPerIter * n

theorem exactMetaFuel_zero : exactMetaFuel 0 = 5 := by
  simp [exactMetaFuel]

theorem metaInterpProg_simulates_zero_steps
    (h : Hexagram) (P : List YiInstr) :
    let simResult := (YiState.init h P).runFuel 0
    let metaResult := (metaStart h P).runFuel (exactMetaFuel 0)
    metaResult.history = encMetaHistory h simResult ∧
      metaResult.halted = simResult.halted := by
  rw [exactMetaFuel_zero, metaStart_runFuel_five_eq_postPrologue h P]
  simp [metaPostPrologue, metaStateOf, YiState.runFuel, YiState.init]

/-- Explicit U.1/U.2/U.3 loop obligations.

    This is the honest F.7c interface: the composition layer no longer stores
    local proof holes.  Instead, the missing semantic work is a value of this
    proposition, to be supplied by the concrete fetch/dispatch/execute-block
    proofs when those bodies are refined. -/
structure SemanticLoopObligations : Prop where
  firstIteration :
    ∀ h sim,
      (sim.prog ≠ [] → True) →
      sim.halted = false →
        let μ  := metaStateOf h sim metaInterpProg outerLoopOffset
        let μ' := μ.runFuel loopFuelPerIter
        μ'.history = encMetaHistory h sim.step ∧
        μ'.halted = sim.step.halted ∧
        μ'.pc = fetchOffset
  steadyIteration :
    ∀ h sim,
      (sim.prog ≠ [] → True) →
      sim.halted = false →
        let μ  := metaFetchState h sim
        let μ' := μ.runFuel loopFuelPerIter
        μ'.history = encMetaHistory h sim.step ∧
        μ'.halted = sim.step.halted ∧
        μ'.pc = fetchOffset
  kIterations :
    ∀ h P k,
      let μ₀ := metaPostPrologue h P
      let μ_k := μ₀.runFuel (loopFuelPerIter * k)
      let sim_k := (YiState.init h P).runFuel k
      μ_k.history = encMetaHistory h sim_k ∧
      μ_k.halted = sim_k.halted
  haltedPadding :
    ∀ h sim extraFuel,
      sim.halted = true →
        let μ := metaStateOf h sim metaInterpProg outerLoopOffset
        let μ' := μ.runFuel (loopFuelPerIter + extraFuel)
        μ'.history = encMetaHistory h sim ∧
        μ'.halted = true

/-- `runFuel` is additive in the fuel argument.  This public local lemma is
    the structural plumbing needed by U.0. -/
theorem runFuel_add (s : YiState) (m n : Nat) :
    s.runFuel (m + n) = (s.runFuel m).runFuel n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : s.runFuel (m + (k + 1)) = (s.runFuel (m + k)).step := by
      have : m + (k + 1) = (m + k) + 1 := by omega
      rw [this, SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right]
    have h2 : (s.runFuel m).runFuel (k + 1) = ((s.runFuel m).runFuel k).step :=
      SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right _ _
    rw [h1, h2, ih]

/-- Generic META padding lemma: once a META state itself is halted, any
    additional fuel is a no-op.  This is the sound, unconditional part of
    halt padding; routing an encoded halted sim-state into such a META state
    remains part of the U.3 semantic obligation. -/
theorem metaInterpProg_meta_halted_padding
    (μ : YiState) (hμ : μ.halted = true) (extraFuel : Nat) :
    μ.runFuel extraFuel = μ :=
  SSBX.Foundation.Bagua.GodelLi.runFuel_halted_fixed μ hμ extraFuel

/-- Field form of `metaInterpProg_meta_halted_padding`, useful for callers
    that only need history and halted-flag stability. -/
theorem metaInterpProg_meta_halted_padding_fields
    (μ : YiState) (hμ : μ.halted = true) (extraFuel : Nat) :
    (μ.runFuel extraFuel).history = μ.history
      ∧ (μ.runFuel extraFuel).halted = true := by
  rw [metaInterpProg_meta_halted_padding μ hμ extraFuel]
  exact ⟨rfl, hμ⟩

/-- **U.1 — Single iteration of the meta loop simulates one sim instruction.**

    Hypothesis: META state at `pc = outerLoopOffset`, history = encoding of
    a non-halted simulated state `sim`.  After `loopFuelPerIter` fuel
    ticks (entry jump + fetch + dispatch + execute + writeback + jump-back
    to fetch), META state encodes `sim.step`.

    Discharge plan:
    - `metaInterpProg_routes_outerLoop_to_fetch` (1 fuel) → `pc = fetchOffset`.
    - `Assembly.metaInterpProg_fetch_routes_running_to_dispatch_exact` →
      decode next opcode.
    - `Assembly.metaInterpProg_dispatch_routes_<op>_at_fuel` →
      matching execute block.
    - `ExecuteBlocks.Aggregate.executeBlock_<op>_local_effect` → per-op effect.
    - Trailing `jump fetchOffset` → back to fetch for the next steady-state
      iteration; the outer-loop entry is only the first post-prologue entry. -/
theorem metaInterpProg_first_iteration_simulates
    (O : SemanticLoopObligations)
    (h : Hexagram) (sim : YiState)
    (h_prog : sim.prog ≠ [] → True)  -- placeholder (always satisfied)
    (h_running : sim.halted = false) :
    let μ  := metaStateOf h sim metaInterpProg outerLoopOffset
    let μ' := μ.runFuel loopFuelPerIter
    μ'.history = encMetaHistory h sim.step ∧
    μ'.halted = sim.step.halted ∧
    μ'.pc = fetchOffset := by
  exact O.firstIteration h sim h_prog h_running

/-- **U.1s — Steady-state iteration.**  After the first pass, execute blocks
    return directly to `fetchOffset`; this is the invariant later concrete
    witnesses must target. -/
theorem metaInterpProg_steady_iteration_simulates
    (O : SemanticLoopObligations)
    (h : Hexagram) (sim : YiState)
    (h_prog : sim.prog ≠ [] → True)
    (h_running : sim.halted = false) :
    let μ  := metaFetchState h sim
    let μ' := μ.runFuel loopFuelPerIter
    μ'.history = encMetaHistory h sim.step ∧
    μ'.halted = sim.step.halted ∧
    μ'.pc = fetchOffset := by
  exact O.steadyIteration h sim h_prog h_running

/-- **U.2 — Loop closure / k-iteration induction.**

    By induction on `k` using U.1 (and U.3 to absorb halted iterations):
    after `loopFuelPerIter * k` fuel ticks starting from the post-prologue
    META state, META state encodes `(YiState.init h P).runFuel k`. -/
theorem metaInterpProg_k_iterations
    (O : SemanticLoopObligations)
    (h : Hexagram) (P : List YiInstr) (k : Nat) :
    let μ₀ := metaPostPrologue h P
    let μ_k := μ₀.runFuel (loopFuelPerIter * k)
    let sim_k := (YiState.init h P).runFuel k
    μ_k.history = encMetaHistory h sim_k ∧
    μ_k.halted = sim_k.halted := by
  exact O.kIterations h P k

/-- **U.3 — Halt propagation.**

    Once the simulated state halts (`sim.halted = true`), the META state
    encoding it is also halt-equivalent: any further fuel applied to
    META preserves both `history = encMetaHistory h sim` and `halted`.
    Cites `ExecuteBlocks.Aggregate.executeBlock_halt_local_effect` and
    `YiState.runFuel` idempotence on halted states. -/
theorem metaInterpProg_halts_when_sim_halts
    (O : SemanticLoopObligations)
    (h : Hexagram) (sim : YiState)
    (h_halted : sim.halted = true) (extraFuel : Nat) :
    let μ := metaStateOf h sim metaInterpProg outerLoopOffset
    let μ' := μ.runFuel (loopFuelPerIter + extraFuel)
    μ'.history = encMetaHistory h sim ∧
    μ'.halted = true := by
  exact O.haltedPadding h sim extraFuel h_halted

/-- **U.4 — Fuel arithmetic / sufficient bound.**

    The budget fuel `metaFuelBound n = metaInterpProg.length * (n + 5)`
    dominates the exact fuel `exactMetaFuel n = 5 + loopFuelPerIter * n`.
    The exact theorem below uses `exactMetaFuel`; the budget theorem is for
    callers that need an upper bound after separately proving halted-padding
    stability.

    This is pure `Nat` arithmetic and should be discharged by `omega`
    once `K_iter ≤ metaInterpProg.length` is exposed. -/
theorem metaInterpProg_fuel_bound (n : Nat) :
    exactMetaFuel n ≤ metaFuelBound n := by
  -- Pure arithmetic: metaInterpProg.length = 88 and
  -- metaFuelBound n = 88 * (n + 5) = 88*n + 440 ≥ 88*n + 5.
  unfold exactMetaFuel loopFuelPerIter metaFuelBound
  rw [metaInterpProg_length]
  -- 5 + 88 * n ≤ 88 * (n + 5) = 88*n + 440.
  have h1 : 88 * (n + 5) = 88 * n + 88 * 5 := Nat.mul_add 88 n 5
  omega

/-! ## § 2.5  U.0 — Universal compose (derived from U.1–U.3) -/

/-- Explicit semantic obligations required for the exact universal-compose
    theorem.  This separates proof plumbing from the still-open semantic work:

    * `exactLoop` is the k-iteration semantic simulation.
    * `haltedPadding` is the later bridge from exact fuel to any larger budget
      once the simulated state is known to have halted.

    The first field is enough for exact-fuel U.0 below; the embedded prologue
    part is already proved as `metaStart_runFuel_five_eq_postPrologue`. -/
structure SemanticComposeObligations : Prop where
  exactLoop :
    ∀ h P n,
      let simResult := (YiState.init h P).runFuel n
      let metaResult := (metaPostPrologue h P).runFuel (loopFuelPerIter * n)
      metaResult.history = encMetaHistory h simResult ∧
      metaResult.halted = simResult.halted
  haltedPadding :
    ∀ h sim extraFuel,
      sim.halted = true →
        let μ := metaStateOf h sim metaInterpProg outerLoopOffset
        let μ' := μ.runFuel (loopFuelPerIter + extraFuel)
        μ'.history = encMetaHistory h sim ∧ μ'.halted = true

namespace SemanticComposeObligations

/-- U.1/U.2/U.3 loop obligations are sufficient to supply the U.0
    composition interface. -/
def ofLoop (O : SemanticLoopObligations) : SemanticComposeObligations where
  exactLoop := O.kIterations
  haltedPadding := O.haltedPadding

end SemanticComposeObligations

/-- **U.0 — Universal compose.**

    Running `metaInterpProg` from the canonical META start state for
    `(P, h)`, with exact fuel `exactMetaFuel n`, produces a META state whose
    history encodes the result of running `P` from `h` for `n` fuel
    ticks (under `encMetaHistory` with register-Hex = `h`), and whose
    `halted` flag agrees with the simulation's.

    This theorem is fully proved from the explicit semantic obligations above;
    no additional proof hole is hidden in the composition layer. -/
theorem metaInterpProg_simulates
    (O : SemanticComposeObligations)
    (h : Hexagram) (P : List YiInstr) (n : Nat) :
    let simResult := (YiState.init h P).runFuel n
    let metaResult := (metaStart h P).runFuel (exactMetaFuel n)
    metaResult.history = encMetaHistory h simResult ∧
    metaResult.halted = simResult.halted := by
  unfold exactMetaFuel
  rw [runFuel_add, metaStart_runFuel_five_eq_postPrologue h P]
  exact O.exactLoop h P n

/-- Convenience form of U.0 when the caller has supplied the finer U.1/U.2/U.3
    loop-obligation package. -/
theorem metaInterpProg_simulates_from_loop
    (O : SemanticLoopObligations)
    (h : Hexagram) (P : List YiInstr) (n : Nat) :
    let simResult := (YiState.init h P).runFuel n
    let metaResult := (metaStart h P).runFuel (exactMetaFuel n)
    metaResult.history = encMetaHistory h simResult ∧
    metaResult.halted = simResult.halted :=
  metaInterpProg_simulates (SemanticComposeObligations.ofLoop O) h P n

/-- The current open frontier for full semantic universal-compose: the exact
    theorem is now just an instance of these obligations, while larger budget
    fuels additionally require halted-padding. -/
theorem semantic_compose_frontier_summary :
    (SemanticComposeObligations →
      ∀ h P n,
        let simResult := (YiState.init h P).runFuel n
        let metaResult := (metaStart h P).runFuel (exactMetaFuel n)
        metaResult.history = encMetaHistory h simResult ∧
        metaResult.halted = simResult.halted)
    ∧ (∀ n, exactMetaFuel n ≤ metaFuelBound n)
    ∧ True := by
  exact ⟨(fun O h P n => metaInterpProg_simulates O h P n),
    metaInterpProg_fuel_bound,
    trivial⟩

/-- F.7c incremental frontier: Universal.lean now has a no-sorry bridge from
    U.1/U.2/U.3 loop evidence to the exact-fuel U.0 theorem.  The remaining
    work is to construct `SemanticLoopObligations` from concrete
    fetch/dispatch/execute-block semantics. -/
theorem semantic_loop_obligation_frontier_summary :
    (SemanticLoopObligations → SemanticComposeObligations)
    ∧ (SemanticLoopObligations →
      ∀ h P n,
        let simResult := (YiState.init h P).runFuel n
        let metaResult := (metaStart h P).runFuel (exactMetaFuel n)
        metaResult.history = encMetaHistory h simResult ∧
        metaResult.halted = simResult.halted)
    ∧ True := by
  exact ⟨SemanticComposeObligations.ofLoop,
    (fun O h P n => metaInterpProg_simulates_from_loop O h P n),
    trivial⟩

/-! ## § 3  U.5 — Strategy-B compatibility boundary -/

/-- Source instructions covered by the current Strategy-B assembly shape.
    Parameterized instructions are compatible only when their parameters match
    the fixed defaults embedded in `Assembly.metaInterpProg`.

    v2 (2026-05-17): `branchYaoYang` 不在 Strategy-B 兼容子集 (留作 v2 obligation). -/
def StrategyBCompatibleInstr : YiInstr → Prop
  | .nop => True
  | .setShi sh => sh = Shi.dao
  | .flipYao i => i = 0
  | .interlace => True
  | .complement => True
  | .reverse => True
  | .branchYaoEq i j target => i = 0 ∧ j = 0 ∧ target = 0
  | .branchShiEq sh target => sh = Shi.dao ∧ target = 0
  | .jump target => target = 0
  | .push => True
  | .pop => True
  | .halt => True
  | .branchYaoYang _ _ => False  -- v2: not covered by current Strategy-B

/-- Programs covered by the current Strategy-B fixed-parameter assembly. -/
def StrategyBCompatibleProgram (P : List YiInstr) : Prop :=
  ∀ instr, instr ∈ P → StrategyBCompatibleInstr instr

theorem strategyB_setShi_ji_not_compatible :
    ¬ StrategyBCompatibleInstr (YiInstr.setShi Shi.ji) := by
  simp [StrategyBCompatibleInstr, Shi.ji, Shi.dao]

theorem strategyB_has_noncompatible_program :
    ∃ P : List YiInstr, ¬ StrategyBCompatibleProgram P := by
  refine ⟨[YiInstr.setShi Shi.ji], ?_⟩
  intro hP
  exact strategyB_setShi_ji_not_compatible (hP _ (by simp))

theorem strategyB_not_full_program_space :
    ¬ (∀ P : List YiInstr, StrategyBCompatibleProgram P) := by
  intro hP
  exact strategyB_setShi_ji_not_compatible
    (hP [YiInstr.setShi Shi.ji] _ (by simp))

/-- Current checked boundary for universal compose: zero-step/prologue compose
    is unconditional, while the present Strategy-B assembly does not cover the
    whole source-program space. -/
theorem universal_compose_current_boundary_summary :
    (∀ h P,
      let simResult := (YiState.init h P).runFuel 0
      let metaResult := (metaStart h P).runFuel (exactMetaFuel 0)
      metaResult.history = encMetaHistory h simResult ∧
        metaResult.halted = simResult.halted)
    ∧ (∃ P : List YiInstr, ¬ StrategyBCompatibleProgram P) := by
  exact ⟨(fun h P => metaInterpProg_simulates_zero_steps h P),
    strategyB_has_noncompatible_program⟩

/-- **U.5 — Strategy-B caveat (coarse marker).**

    For *full* universality (∀ P : List YiInstr — including those whose
    parameterized opcodes have non-default arguments) the assembled
    program must be promoted: each of the 5 parameterized arms
    (setShi / flipYao / branchYaoEq / branchShiEq / jump) must read its
    parameter cell from META.history at dispatch-time and route to one
    of N specialized blocks.  See
    `SubDispatch_BranchShiEq` / `SubDispatch_BranchYaoEq` for the
    intended pattern.

    The compatibility predicates above make this gap machine-checkable; this
    trivial theorem remains as the older coarse file-level marker. -/
theorem metaInterpProg_strategyB_limitations : True := trivial

end SSBX.Foundation.Wen.MetaInterp.Universal
