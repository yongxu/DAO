import SSBX.Pending.Interfaces

namespace SSBX
namespace Pending
namespace Examples

open Interfaces

/-!
Finite toy instances for the pending empirical interfaces.

The data below are model-internal fixtures only.  They are real Lean data and
proof objects, but they do not assert any external-world fact.
-/

inductive ExampleStatus where
  | instantiated
  | conditional
  deriving DecidableEq, Repr

def statusOf : Interfaces.PendingName -> ExampleStatus
  | .auditData => .instantiated
  | .calibration => .instantiated
  | .threshold => .instantiated
  | .degreePeriod => .conditional
  | .openProjection => .conditional
  | .evilContinuation => .conditional

theorem statusOf_covers_all (n : Interfaces.PendingName) :
    statusOf n = ExampleStatus.instantiated ∨
      statusOf n = ExampleStatus.conditional := by
  cases n <;> simp [statusOf]

theorem pending_names_stay_pending (n : Interfaces.PendingName) :
    n.kind = SSBX.Core.Kind.pending :=
  Interfaces.PendingName.kind_pending n

namespace ToyAudit

inductive Claim where
  | stable
  | defeated
  | thin
  deriving DecidableEq, Repr

inductive Record where
  | supportA
  | supportB
  | defeatC
  deriving DecidableEq, Repr

inductive Source where
  | sourceA
  | sourceB
  | sourceC
  deriving DecidableEq, Repr

def records : List Record :=
  [.supportA, .supportB, .defeatC]

def claimOf : Record -> Claim
  | .supportA => .stable
  | .supportB => .stable
  | .defeatC => .defeated

def sourceOf : Record -> Source
  | .supportA => .sourceA
  | .supportB => .sourceB
  | .defeatC => .sourceC

def supports : Record -> Claim -> Prop
  | .supportA, .stable => True
  | .supportB, .stable => True
  | _, _ => False

def defeats : Record -> Claim -> Prop
  | .defeatC, .defeated => True
  | _, _ => False

def independent (r1 r2 : Record) : Prop :=
  sourceOf r1 ≠ sourceOf r2

def model : AuditData.Model where
  Claim := Claim
  Record := Record
  Source := Source
  records := records
  claimOf := claimOf
  sourceOf := sourceOf
  supports := supports
  defeats := defeats
  independent := independent

def run : Claim -> Tri
  | .stable => Tri.top
  | .defeated => Tri.bot
  | .thin => Tri.unk

def validInput : Claim -> Prop
  | .stable => True
  | .defeated => True
  | .thin => False

theorem wellFormed : AuditData.WellFormed model := by
  simp [AuditData.WellFormed, model, records]

theorem stable_supports : AuditData.AuditSupports model Claim.stable := by
  refine ⟨Record.supportA, Record.supportB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)
  · intro h
    cases h
  · simp [model, independent, sourceOf]
  · simp [model, supports]
  · simp [model, supports]
  · intro h
    rcases h with ⟨d, _hdmem, hddef⟩
    cases d <;> simp [model, defeats] at hddef

theorem defeated_defeats : AuditData.AuditDefeats model Claim.defeated := by
  exact ⟨Record.defeatC,
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
    by simp [model, defeats]⟩

def interface : AuditData.Interface where
  model := model
  run := run
  validInput := validInput
  sound := by
    intro c h
    cases c
    · exact ⟨wellFormed, stable_supports⟩
    · exact ⟨wellFormed, defeated_defeats⟩
    · cases h
  unknown_on_invalid := by
    intro c h
    cases c <;> simp [validInput, run] at *

theorem stable_run_top : interface.run Claim.stable = Tri.top :=
  rfl

theorem stable_top_sound :
    AuditData.WellFormed interface.model ∧
      AuditData.AuditSupports interface.model Claim.stable :=
  AuditData.top_sound interface stable_run_top

theorem defeated_run_bot : interface.run Claim.defeated = Tri.bot :=
  rfl

theorem defeated_bot_sound :
    AuditData.WellFormed interface.model ∧
      AuditData.AuditDefeats interface.model Claim.defeated :=
  AuditData.bot_sound interface defeated_run_bot

theorem thin_unknown_on_invalid :
    interface.run Claim.thin = Tri.unk := by
  exact interface.unknown_on_invalid Claim.thin (by simp [interface, validInput])

end ToyAudit

namespace ToyCalibration

inductive Evidence where
  | train
  | valid
  | stale
  | unaudited
  deriving DecidableEq, Repr

inductive Param where
  | p1
  | fallback
  deriving DecidableEq, Repr

def fit : Evidence -> Param
  | .train => .p1
  | _ => .fallback

def loss : Param -> Evidence -> Nat
  | .p1, .train => 1
  | .p1, .valid => 2
  | .p1, .stale => 5
  | .p1, .unaudited => 7
  | .fallback, _ => 9

def audited : Evidence -> Prop
  | .train => True
  | .valid => True
  | .stale => True
  | .unaudited => False

def model : Calibration.Model where
  Domain := Unit
  Param := Param
  Evidence := Evidence
  fit := fit
  loss := loss
  tolerance := 2
  audited := audited

def run : Calibration.Input model -> Tri
  | ⟨.train, .valid⟩ => Tri.top
  | ⟨.train, .stale⟩ => Tri.bot
  | _ => Tri.unk

def validInput : Calibration.Input model -> Prop
  | ⟨.train, .valid⟩ => True
  | ⟨.train, .stale⟩ => True
  | _ => False

theorem train_valid_calibrated :
    Calibration.Calibrated model (model.fit Evidence.train)
      Evidence.train Evidence.valid := by
  exact ⟨by decide, by decide, trivial, trivial⟩

theorem train_stale_not_calibrated :
    ¬ Calibration.Calibrated model (model.fit Evidence.train)
      Evidence.train Evidence.stale := by
  intro h
  have hle : 5 <= 2 := by
    simpa [Calibration.Calibrated, model, fit, loss] using h.2.1
  exact (by decide : ¬ 5 <= 2) hle

def interface : Calibration.Interface where
  model := model
  run := run
  validInput := validInput
  sound := by
    intro x h
    cases x with
    | mk trainEvidence validEvidence =>
        cases trainEvidence <;> cases validEvidence <;>
          simp [run, validInput, Calibration.Certifies] at *
        · exact train_valid_calibrated
        · exact train_stale_not_calibrated
  unknown_on_invalid := by
    intro x h
    cases x with
    | mk trainEvidence validEvidence =>
        cases trainEvidence <;> cases validEvidence <;> simp [run, validInput] at *

def goodInput : Calibration.Input model :=
  ⟨.train, .valid⟩

def staleInput : Calibration.Input model :=
  ⟨.train, .stale⟩

def unauditedInput : Calibration.Input model :=
  ⟨.train, .unaudited⟩

theorem good_run_top : interface.run goodInput = Tri.top :=
  rfl

theorem good_top_sound :
    Calibration.Calibrated interface.model
      (interface.model.fit goodInput.train) goodInput.train goodInput.valid :=
  Calibration.top_sound interface good_run_top

theorem stale_run_bot : interface.run staleInput = Tri.bot :=
  rfl

theorem stale_bot_sound :
    ¬ Calibration.Calibrated interface.model
      (interface.model.fit staleInput.train) staleInput.train staleInput.valid :=
  Calibration.bot_sound interface stale_run_bot

theorem unaudited_unknown :
    interface.run unauditedInput = Tri.unk := by
  exact interface.unknown_on_invalid unauditedInput
    (by simp [interface, validInput, unauditedInput])

end ToyCalibration

namespace ToyThreshold

inductive Item where
  | rightCase
  | evilCase
  | conflictCase
  | unknownCase
  deriving DecidableEq, Repr

def rightScore : Item -> Nat
  | .rightCase => 8
  | .evilCase => 1
  | .conflictCase => 8
  | .unknownCase => 8

def evilScore : Item -> Nat
  | .rightCase => 1
  | .evilCase => 8
  | .conflictCase => 8
  | .unknownCase => 1

def audited : Item -> Prop
  | .unknownCase => False
  | _ => True

def model : Threshold.Model where
  X := Item
  rightScore := rightScore
  evilScore := evilScore
  rightCut := 7
  evilCut := 7
  margin := 1
  audited := audited

def run : Threshold.Input model -> Tri
  | ⟨.right, .rightCase⟩ => Tri.top
  | ⟨.evil, .evilCase⟩ => Tri.top
  | ⟨.evil, .rightCase⟩ => Tri.bot
  | ⟨.right, .evilCase⟩ => Tri.bot
  | _ => Tri.unk

def validInput (x : Threshold.Input model) : Prop :=
  model.audited x.x

theorem right_case_certified :
    Threshold.RightByThreshold model Item.rightCase := by
  exact ⟨by decide, by decide, trivial⟩

theorem evil_case_certified :
    Threshold.EvilByThreshold model Item.evilCase := by
  exact ⟨by decide, by decide, trivial⟩

theorem evil_case_not_right :
    ¬ Threshold.RightByThreshold model Item.evilCase := by
  intro h
  have hcut : 7 <= 1 := by
    simpa [Threshold.RightByThreshold, model, rightScore] using h.1
  exact (by decide : ¬ 7 <= 1) hcut

theorem right_case_not_evil :
    ¬ Threshold.EvilByThreshold model Item.rightCase := by
  intro h
  have hcut : 7 <= 1 := by
    simpa [Threshold.EvilByThreshold, model, evilScore] using h.1
  exact (by decide : ¬ 7 <= 1) hcut

def interface : Threshold.Interface where
  model := model
  run := run
  validInput := validInput
  sound := by
    intro x h
    cases x with
    | mk side item =>
        cases side <;> cases item <;>
          simp [run, validInput, model, audited, Threshold.Certifies] at *
        · exact right_case_certified
        · exact evil_case_not_right
        · exact right_case_not_evil
        · exact evil_case_certified
  unknown_on_invalid := by
    intro x h
    cases x with
    | mk side item =>
        cases side <;> cases item <;>
          simp [run, validInput, model, audited] at *
  conflict_not_top := by
    intro x h
    cases x <;>
      simp [Threshold.ThresholdConflict, model, rightScore, evilScore, run] at *

theorem right_run_top :
    interface.run ⟨.right, Item.rightCase⟩ = Tri.top :=
  rfl

theorem right_top_sound :
    Threshold.RightByThreshold interface.model Item.rightCase :=
  Threshold.right_top_sound interface right_run_top

theorem evil_run_top :
    interface.run ⟨.evil, Item.evilCase⟩ = Tri.top :=
  rfl

theorem evil_top_sound :
    Threshold.EvilByThreshold interface.model Item.evilCase :=
  Threshold.evil_top_sound interface evil_run_top

theorem conflict_case_conflict :
    Threshold.ThresholdConflict model Item.conflictCase := by
  exact ⟨by decide, by decide⟩

theorem conflict_case_not_top :
    interface.run ⟨.right, Item.conflictCase⟩ ≠ Tri.top ∧
      interface.run ⟨.evil, Item.conflictCase⟩ ≠ Tri.top :=
  Threshold.conflict_not_top interface conflict_case_conflict

theorem unknown_case_invalid :
    ¬ interface.validInput ⟨.right, Item.unknownCase⟩ := by
  simp [interface, validInput, model, audited]

theorem unknown_case_unknown :
    interface.run ⟨.right, Item.unknownCase⟩ = Tri.unk :=
  interface.unknown_on_invalid ⟨.right, Item.unknownCase⟩ unknown_case_invalid

end ToyThreshold

namespace Conditional

open SSBX.Core.GammaProcess

theorem degreePeriod_cycle_top
    {M : Model} {D : DaoCriteria M} (I : DegreePeriod.Interface M D)
    {g : M.Gamma} {p : D.Path} {d : M.Degree} {t : M.Horizon}
    (h : I.run ⟨.cycle, g, p, d, t⟩ = Tri.top) :
    D.relevant g p d t ∧ D.canContinue g p d t ∧ ¬ D.badAt g p d t :=
  DegreePeriod.cycle_top_sound I h

theorem openProjection_top
    {M : Model} {C : OpenCriteria M} (I : OpenProjection.Interface M C)
    {g : M.Gamma} {i : IntervalDomain M g}
    (h : I.run ⟨g, i⟩ = Tri.top) :
    OpenProjection.OpenProjectionSound M C g i :=
  OpenProjection.top_sound I h

theorem evilContinuation_top (I : EvilContinuation.Interface)
    {tau : I.model.Trace} (h : I.run tau = Tri.top) :
    I.model.audited tau ∧ EvilContinuation.EvilPersists I.model tau ∧
      ¬ I.model.hasDefeater tau :=
  EvilContinuation.top_sound I h

end Conditional

end Examples
end Pending
end SSBX
