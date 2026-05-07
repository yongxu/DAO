import SSBX.Core

namespace SSBX
namespace Pending
namespace Interfaces

abbrev Tri := SSBX.Core.Tri

namespace Tri

abbrev top : Tri :=
  SSBX.Core.Tri.top

abbrev bot : Tri :=
  SSBX.Core.Tri.bot

abbrev unk : Tri :=
  SSBX.Core.Tri.unk

end Tri

/--
The six names remain pending here: this module only records checkable
interfaces and certificate directions.
-/
inductive PendingName where
  | evilContinuation
  | openProjection
  | auditData
  | threshold
  | degreePeriod
  | calibration
  deriving DecidableEq, Repr

def PendingName.kind (_ : PendingName) : SSBX.Core.Kind :=
  .pending

theorem PendingName.kind_pending (n : PendingName) :
    n.kind = SSBX.Core.Kind.pending :=
  rfl

/--
Common boundary for empirical interfaces.

`sound` says only that a valid input has a certificate for the value actually
returned by `run`. `unknown_on_invalid` is the conservative fallback for
missing data, failed audits, or uninstantiated empirical models.
-/
structure TriInterface (Input : Type u) where
  run : Input -> Tri
  validInput : Input -> Prop
  certifies : Input -> Tri -> Prop
  sound : ∀ x, validInput x -> certifies x (run x)
  unknown_on_invalid : ∀ x, ¬ validInput x -> run x = Tri.unk

namespace TriInterface

theorem invalid_unknown {Input : Type u} (I : TriInterface Input) {x : Input}
    (h : ¬ I.validInput x) :
    I.run x = Tri.unk :=
  I.unknown_on_invalid x h

theorem invalid_not_top {Input : Type u} (I : TriInterface Input) {x : Input}
    (h : ¬ I.validInput x) :
    I.run x ≠ Tri.top := by
  rw [I.invalid_unknown h]
  exact SSBX.Core.Tri.unk_not_top

theorem invalid_not_bot {Input : Type u} (I : TriInterface Input) {x : Input}
    (h : ¬ I.validInput x) :
    I.run x ≠ Tri.bot := by
  rw [I.invalid_unknown h]
  intro hbot
  cases hbot

end TriInterface

namespace AuditData

structure Model where
  Claim : Type u
  Record : Type v
  Source : Type w
  records : List Record
  claimOf : Record -> Claim
  sourceOf : Record -> Source
  supports : Record -> Claim -> Prop
  defeats : Record -> Claim -> Prop
  independent : Record -> Record -> Prop

def WellFormed (A : Model) : Prop :=
  A.records.Nodup

def AuditSupports (A : Model) (c : A.Claim) : Prop :=
  ∃ r1 r2,
    r1 ∈ A.records ∧ r2 ∈ A.records ∧
    r1 ≠ r2 ∧
    A.independent r1 r2 ∧
    A.supports r1 c ∧ A.supports r2 c ∧
    ¬ (∃ d, d ∈ A.records ∧ A.defeats d c)

def AuditDefeats (A : Model) (c : A.Claim) : Prop :=
  ∃ d, d ∈ A.records ∧ A.defeats d c

def Certifies (A : Model) (c : A.Claim) : Tri -> Prop
  | .top => WellFormed A ∧ AuditSupports A c
  | .bot => WellFormed A ∧ AuditDefeats A c
  | .unk => True

structure Interface where
  model : Model
  run : model.Claim -> Tri
  validInput : model.Claim -> Prop
  sound : ∀ c, validInput c -> Certifies model c (run c)
  unknown_on_invalid : ∀ c, ¬ validInput c -> run c = Tri.unk

def Interface.toTriInterface (I : Interface) : TriInterface I.model.Claim where
  run := I.run
  validInput := I.validInput
  certifies := Certifies I.model
  sound := I.sound
  unknown_on_invalid := I.unknown_on_invalid

theorem top_sound (I : Interface) {c : I.model.Claim}
    (h : I.run c = Tri.top) :
    WellFormed I.model ∧ AuditSupports I.model c := by
  by_cases hv : I.validInput c
  · have hs := I.sound c hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid c hv
    rw [h] at hu
    cases hu

theorem bot_sound (I : Interface) {c : I.model.Claim}
    (h : I.run c = Tri.bot) :
    WellFormed I.model ∧ AuditDefeats I.model c := by
  by_cases hv : I.validInput c
  · have hs := I.sound c hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid c hv
    rw [h] at hu
    cases hu

end AuditData

namespace Calibration

structure Model where
  Domain : Type u
  Param : Type v
  Evidence : Type w
  fit : Evidence -> Param
  loss : Param -> Evidence -> Nat
  tolerance : Nat
  audited : Evidence -> Prop

structure Input (C : Model) where
  train : C.Evidence
  valid : C.Evidence

def Calibrated (C : Model) (p : C.Param)
    (train valid : C.Evidence) : Prop :=
  C.loss p train <= C.tolerance ∧
    C.loss p valid <= C.tolerance ∧
    C.audited train ∧ C.audited valid

def Certifies (C : Model) (x : Input C) : Tri -> Prop
  | .top => Calibrated C (C.fit x.train) x.train x.valid
  | .bot => ¬ Calibrated C (C.fit x.train) x.train x.valid
  | .unk => True

structure Interface where
  model : Model
  run : Input model -> Tri
  validInput : Input model -> Prop
  sound : ∀ x, validInput x -> Certifies model x (run x)
  unknown_on_invalid : ∀ x, ¬ validInput x -> run x = Tri.unk

def Interface.toTriInterface (I : Interface) : TriInterface (Input I.model) where
  run := I.run
  validInput := I.validInput
  certifies := Certifies I.model
  sound := I.sound
  unknown_on_invalid := I.unknown_on_invalid

theorem top_sound (I : Interface) {x : Input I.model}
    (h : I.run x = Tri.top) :
    Calibrated I.model (I.model.fit x.train) x.train x.valid := by
  by_cases hv : I.validInput x
  · have hs := I.sound x hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid x hv
    rw [h] at hu
    cases hu

theorem bot_sound (I : Interface) {x : Input I.model}
    (h : I.run x = Tri.bot) :
    ¬ Calibrated I.model (I.model.fit x.train) x.train x.valid := by
  by_cases hv : I.validInput x
  · have hs := I.sound x hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid x hv
    rw [h] at hu
    cases hu

end Calibration

namespace Threshold

inductive Side where
  | right
  | evil
  deriving DecidableEq, Repr

structure Model where
  X : Type u
  rightScore : X -> Nat
  evilScore : X -> Nat
  rightCut : Nat
  evilCut : Nat
  margin : Nat
  audited : X -> Prop

structure Input (T : Model) where
  side : Side
  x : T.X

def RightByThreshold (T : Model) (x : T.X) : Prop :=
  T.rightCut <= T.rightScore x ∧
    T.evilScore x + T.margin < T.evilCut ∧
    T.audited x

def EvilByThreshold (T : Model) (x : T.X) : Prop :=
  T.evilCut <= T.evilScore x ∧
    T.rightScore x + T.margin < T.rightCut ∧
    T.audited x

def ThresholdConflict (T : Model) (x : T.X) : Prop :=
  T.rightCut <= T.rightScore x ∧ T.evilCut <= T.evilScore x

def Certifies (T : Model) : Input T -> Tri -> Prop
  | ⟨.right, x⟩, .top => RightByThreshold T x
  | ⟨.evil, x⟩, .top => EvilByThreshold T x
  | ⟨.right, x⟩, .bot => ¬ RightByThreshold T x
  | ⟨.evil, x⟩, .bot => ¬ EvilByThreshold T x
  | _, .unk => True

structure Interface where
  model : Model
  run : Input model -> Tri
  validInput : Input model -> Prop
  sound : ∀ x, validInput x -> Certifies model x (run x)
  unknown_on_invalid : ∀ x, ¬ validInput x -> run x = Tri.unk
  conflict_not_top :
    ∀ x, ThresholdConflict model x ->
      run ⟨.right, x⟩ ≠ Tri.top ∧ run ⟨.evil, x⟩ ≠ Tri.top

def Interface.toTriInterface (I : Interface) : TriInterface (Input I.model) where
  run := I.run
  validInput := I.validInput
  certifies := Certifies I.model
  sound := I.sound
  unknown_on_invalid := I.unknown_on_invalid

theorem right_top_sound (I : Interface) {x : I.model.X}
    (h : I.run ⟨.right, x⟩ = Tri.top) :
    RightByThreshold I.model x := by
  by_cases hv : I.validInput ⟨.right, x⟩
  · have hs := I.sound ⟨.right, x⟩ hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid ⟨.right, x⟩ hv
    rw [h] at hu
    cases hu

theorem evil_top_sound (I : Interface) {x : I.model.X}
    (h : I.run ⟨.evil, x⟩ = Tri.top) :
    EvilByThreshold I.model x := by
  by_cases hv : I.validInput ⟨.evil, x⟩
  · have hs := I.sound ⟨.evil, x⟩ hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid ⟨.evil, x⟩ hv
    rw [h] at hu
    cases hu

theorem conflict_not_top (I : Interface) {x : I.model.X}
    (h : ThresholdConflict I.model x) :
    I.run ⟨.right, x⟩ ≠ Tri.top ∧ I.run ⟨.evil, x⟩ ≠ Tri.top :=
  I.conflict_not_top x h

end Threshold

namespace DegreePeriod

open SSBX.Core.GammaProcess

inductive Query where
  | relevance
  | cycle
  deriving DecidableEq, Repr

structure Input (M : Model) (D : DaoCriteria M) where
  query : Query
  g : M.Gamma
  p : D.Path
  d : M.Degree
  t : M.Horizon

def RelevantDegreePeriod (M : Model) (D : DaoCriteria M)
    (g : M.Gamma) (p : D.Path) (d : M.Degree) (t : M.Horizon) : Prop :=
  D.relevant g p d t

def DegreePeriodContinues (M : Model) (D : DaoCriteria M)
    (g : M.Gamma) (p : D.Path) (d : M.Degree) (t : M.Horizon) : Prop :=
  D.relevant g p d t ∧ D.canContinue g p d t ∧ ¬ D.badAt g p d t

def Certifies (M : Model) (D : DaoCriteria M) : Input M D -> Tri -> Prop
  | ⟨.relevance, g, p, d, t⟩, .top =>
      RelevantDegreePeriod M D g p d t
  | ⟨.cycle, g, p, d, t⟩, .top =>
      DegreePeriodContinues M D g p d t
  | ⟨.relevance, g, p, d, t⟩, .bot =>
      ¬ RelevantDegreePeriod M D g p d t
  | ⟨.cycle, g, p, d, t⟩, .bot =>
      ¬ DegreePeriodContinues M D g p d t
  | _, .unk => True

structure Interface (M : Model) (D : DaoCriteria M) where
  run : Input M D -> Tri
  validInput : Input M D -> Prop
  sound : ∀ x, validInput x -> Certifies M D x (run x)
  unknown_on_invalid : ∀ x, ¬ validInput x -> run x = Tri.unk

def Interface.toTriInterface {M : Model} {D : DaoCriteria M}
    (I : Interface M D) : TriInterface (Input M D) where
  run := I.run
  validInput := I.validInput
  certifies := Certifies M D
  sound := I.sound
  unknown_on_invalid := I.unknown_on_invalid

theorem relevance_top_sound {M : Model} {D : DaoCriteria M}
    (I : Interface M D) {g : M.Gamma} {p : D.Path}
    {d : M.Degree} {t : M.Horizon}
    (h : I.run ⟨.relevance, g, p, d, t⟩ = Tri.top) :
    D.relevant g p d t := by
  by_cases hv : I.validInput ⟨.relevance, g, p, d, t⟩
  · have hs := I.sound ⟨.relevance, g, p, d, t⟩ hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid ⟨.relevance, g, p, d, t⟩ hv
    rw [h] at hu
    cases hu

theorem cycle_top_sound {M : Model} {D : DaoCriteria M}
    (I : Interface M D) {g : M.Gamma} {p : D.Path}
    {d : M.Degree} {t : M.Horizon}
    (h : I.run ⟨.cycle, g, p, d, t⟩ = Tri.top) :
    D.relevant g p d t ∧ D.canContinue g p d t ∧ ¬ D.badAt g p d t := by
  by_cases hv : I.validInput ⟨.cycle, g, p, d, t⟩
  · have hs := I.sound ⟨.cycle, g, p, d, t⟩ hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid ⟨.cycle, g, p, d, t⟩ hv
    rw [h] at hu
    cases hu

end DegreePeriod

namespace OpenProjection

open SSBX.Core.GammaProcess

structure Input (M : Model) where
  g : M.Gamma
  interval : IntervalDomain M g

def OpenProjectionSound (M : Model) (C : OpenCriteria M)
    (g : M.Gamma) (i : IntervalDomain M g) : Prop :=
  Open M C (step M g i) ∧ (Tendency M g ∨ Opportunity M C g)

def Certifies (M : Model) (C : OpenCriteria M) (x : Input M) : Tri -> Prop
  | .top => OpenProjectionSound M C x.g x.interval
  | .bot => ¬ OpenProjectionSound M C x.g x.interval
  | .unk => True

structure Interface (M : Model) (C : OpenCriteria M) where
  run : Input M -> Tri
  validInput : Input M -> Prop
  sound : ∀ x, validInput x -> Certifies M C x (run x)
  unknown_on_invalid : ∀ x, ¬ validInput x -> run x = Tri.unk

def Interface.toTriInterface {M : Model} {C : OpenCriteria M}
    (I : Interface M C) : TriInterface (Input M) where
  run := I.run
  validInput := I.validInput
  certifies := Certifies M C
  sound := I.sound
  unknown_on_invalid := I.unknown_on_invalid

theorem top_sound {M : Model} {C : OpenCriteria M}
    (I : Interface M C) {g : M.Gamma} {i : IntervalDomain M g}
    (h : I.run ⟨g, i⟩ = Tri.top) :
    OpenProjectionSound M C g i := by
  by_cases hv : I.validInput ⟨g, i⟩
  · have hs := I.sound ⟨g, i⟩ hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid ⟨g, i⟩ hv
    rw [h] at hu
    cases hu

end OpenProjection

namespace EvilContinuation

structure Model where
  Trace : Type u
  minWindows : Nat
  evilAt : Trace -> Nat -> Tri
  audited : Trace -> Prop
  hasDefeater : Trace -> Prop

def EvilWindow (E : Model) (tau : E.Trace) (n : Nat) : Prop :=
  E.evilAt tau n = Tri.top

def EvilPersists (E : Model) (tau : E.Trace) : Prop :=
  ∃ ns : List Nat,
    ns.length >= E.minWindows ∧
    ns.Nodup ∧
    ∀ n, n ∈ ns -> EvilWindow E tau n

def EvilContinuation (E : Model) (tau : E.Trace) : Prop :=
  E.audited tau ∧ EvilPersists E tau ∧ ¬ E.hasDefeater tau

def Certifies (E : Model) (tau : E.Trace) : Tri -> Prop
  | .top => EvilContinuation E tau
  | .bot => ¬ EvilContinuation E tau
  | .unk => True

structure Interface where
  model : Model
  run : model.Trace -> Tri
  validInput : model.Trace -> Prop
  sound : ∀ tau, validInput tau -> Certifies model tau (run tau)
  unknown_on_invalid : ∀ tau, ¬ validInput tau -> run tau = Tri.unk

def Interface.toTriInterface (I : Interface) : TriInterface I.model.Trace where
  run := I.run
  validInput := I.validInput
  certifies := Certifies I.model
  sound := I.sound
  unknown_on_invalid := I.unknown_on_invalid

theorem persists_window_sound (E : Model) {tau : E.Trace}
    (h : EvilPersists E tau) :
    ∃ ns : List Nat,
      ns.length >= E.minWindows ∧
      ns.Nodup ∧
      ∀ n, n ∈ ns -> E.evilAt tau n = Tri.top :=
  h

theorem top_sound (I : Interface) {tau : I.model.Trace}
    (h : I.run tau = Tri.top) :
    I.model.audited tau ∧
      EvilPersists I.model tau ∧
      ¬ I.model.hasDefeater tau := by
  by_cases hv : I.validInput tau
  · have hs := I.sound tau hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid tau hv
    rw [h] at hu
    cases hu

theorem bot_sound (I : Interface) {tau : I.model.Trace}
    (h : I.run tau = Tri.bot) :
    ¬ EvilContinuation I.model tau := by
  by_cases hv : I.validInput tau
  · have hs := I.sound tau hv
    rw [h] at hs
    exact hs
  · have hu := I.unknown_on_invalid tau hv
    rw [h] at hu
    cases hu

end EvilContinuation

end Interfaces
end Pending
end SSBX
