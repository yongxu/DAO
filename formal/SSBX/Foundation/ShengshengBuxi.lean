/-
Machine-checkable core of 生生不息.

This module proves a deliberately small wenyan statement:

  生生不息者，诸期皆开，递递有间，境以其间而复开。

It is a proof of the continuation core, not a proof that every value-semantic
claim in the whole text follows without premises.
-/
import SSBX.Core
import SSBX.Roster
import SSBX.Foundation.MonadRoot

namespace SSBX.Foundation.ShengshengBuxi

open SSBX.Core.GammaProcess
open SSBX.Roster
open SSBX.Foundation.MonadRoot

def provableWenyanLine : String :=
  "生生不息者，诸期皆开，递递有间，境以其间而复开。"

/--
The same line, stripped to the registered single-glyph layer.

`时` / `步` / `承` are intentionally avoided here because they are not part of
the current single-glyph roster.  `期` / `递` / `以` keep the sentence inside
the already-proved atom system.
-/
def provableWenyanAtoms : List AtomName :=
  [.«生», .«生», .«不», .«息», .«者», .«诸», .«期», .«皆», .«开»,
   .«递», .«递», .«有», .«间», .«境», .«以», .«其», .«间», .«而»,
   .«复», .«开»]

theorem provable_wenyan_atoms_registered {a : AtomName}
    (_h : a ∈ provableWenyanAtoms) :
    (A a) ∈ allSymbols :=
  allSymbols_complete (A a)

theorem provable_wenyan_atoms_rooted {a : AtomName}
    (_h : a ∈ provableWenyanAtoms) :
    Reachable «一元» (MonadNode.atom a) :=
  all_atoms_reachable_from_root a

/--
An infinite open run: at every natural-number stage the field is open, and the
next stage is produced by applying 生合 to a valid interval at the current stage.
-/
structure OpenRun (M : Model) (C : OpenCriteria M) where
  state : Nat -> M.Gamma
  interval : (n : Nat) -> IntervalDomain M (state n)
  step_eq : ∀ n, state (n + 1) = step M (state n) (interval n)
  open_at : ∀ n, Open M C (state n)

/--
The provable core of 生生不息: the given field starts an infinite open run.
-/
def ShengshengBuxi (M : Model) (C : OpenCriteria M) (g : M.Gamma) : Prop :=
  ∃ run : OpenRun M C, run.state 0 = g

theorem buxi_open_at_zero {M : Model} {C : OpenCriteria M} {g : M.Gamma}
    (h : ShengshengBuxi M C g) :
    Open M C g := by
  rcases h with ⟨run, hzero⟩
  rw [← hzero]
  exact run.open_at 0

theorem buxi_has_interval_at_zero {M : Model} {C : OpenCriteria M} {g : M.Gamma}
    (h : ShengshengBuxi M C g) :
    HasInterval M g :=
  open_has_interval (buxi_open_at_zero h)

theorem buxi_not_absolute_closed {M : Model} {C : OpenCriteria M} {g : M.Gamma}
    (h : ShengshengBuxi M C g) :
    ¬ AbsoluteClosed M g := by
  intro hclosed
  exact hclosed (buxi_has_interval_at_zero h)

theorem buxi_open_at_every_step {M : Model} {C : OpenCriteria M} {g : M.Gamma}
    (h : ShengshengBuxi M C g) :
    ∃ run : OpenRun M C, run.state 0 = g ∧ ∀ n, Open M C (run.state n) := by
  rcases h with ⟨run, hzero⟩
  exact ⟨run, hzero, run.open_at⟩

theorem buxi_has_interval_at_every_step {M : Model} {C : OpenCriteria M}
    {g : M.Gamma} (h : ShengshengBuxi M C g) :
    ∃ run : OpenRun M C, run.state 0 = g ∧ ∀ n, HasInterval M (run.state n) := by
  rcases h with ⟨run, hzero⟩
  exact ⟨run, hzero, fun n => open_has_interval (run.open_at n)⟩

theorem buxi_step_returns_open {M : Model} {C : OpenCriteria M} {g : M.Gamma}
    (h : ShengshengBuxi M C g) :
    ∃ run : OpenRun M C,
      run.state 0 = g ∧
        ∀ n, Open M C (step M (run.state n) (run.interval n)) := by
  rcases h with ⟨run, hzero⟩
  refine ⟨run, hzero, ?_⟩
  intro n
  simpa [run.step_eq n] using run.open_at (n + 1)

def unitOpenRun : OpenRun unitProcess unitOpenCriteria where
  state := fun _ => ()
  interval := fun _ => ⟨(), trivial⟩
  step_eq := by
    intro _
    rfl
  open_at := by
    intro _
    exact unitProcess_open

theorem unitProcess_shengsheng_buxi :
    ShengshengBuxi unitProcess unitOpenCriteria () := by
  exact ⟨unitOpenRun, rfl⟩

/--
The code-level certificate for the wenyan sentence: the phrase is registered
and rooted, and the minimal Γ-process is a machine-checked witness of the
provable continuation core.
-/
structure ProvableWenyanCertificate where
  line : String
  line_eq : line = provableWenyanLine
  atoms : List AtomName
  atoms_eq : atoms = provableWenyanAtoms
  atoms_registered :
    ∀ a, a ∈ atoms -> (A a) ∈ allSymbols
  atoms_rooted :
    ∀ a, a ∈ atoms -> Reachable «一元» (MonadNode.atom a)
  symbol_registered : (G .«生生不息») ∈ allSymbols
  symbol_rooted : Reachable «一元» «生生不息论»
  model_witness : ShengshengBuxi unitProcess unitOpenCriteria ()

def provableWenyanCertificate : ProvableWenyanCertificate :=
  { line := provableWenyanLine
    line_eq := rfl
    atoms := provableWenyanAtoms
    atoms_eq := rfl
    atoms_registered := by
      intro a h
      exact provable_wenyan_atoms_registered h
    atoms_rooted := by
      intro a h
      exact provable_wenyan_atoms_rooted h
    symbol_registered := by decide
    symbol_rooted := ssbx_reachable_from_root
    model_witness := unitProcess_shengsheng_buxi }

theorem provable_wenyan_has_certificate :
    Nonempty ProvableWenyanCertificate :=
  ⟨provableWenyanCertificate⟩

end SSBX.Foundation.ShengshengBuxi
