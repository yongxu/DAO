/-
SSBX core proof skeleton: terms, registries, three-valued logic, and the minimal model.
-/
namespace SSBX.Core

abbrev Name := Nat

inductive Ty where
  | field
  | focus
  | interval
  | community
  | scale
  | window
  | truth
  | term
  deriving DecidableEq, Repr

inductive Kind where
  | atom
  | generated
  | primitive
  | recursive
  | pending
  deriving DecidableEq, Repr

inductive Polarity where
  | positive
  | negative
  | mixed
  | none
  deriving DecidableEq, Repr

inductive RecSemantics where
  | lfp
  | gfp
  | stratified
  | threeValued
  | externalAudit
  deriving DecidableEq, Repr

inductive Tri where
  | top
  | bot
  | unk
  deriving DecidableEq, Repr

namespace Tri

def neg : Tri -> Tri
  | top => bot
  | bot => top
  | unk => unk

def and : Tri -> Tri -> Tri
  | bot, _ => bot
  | _, bot => bot
  | top, top => top
  | _, _ => unk

def or : Tri -> Tri -> Tri
  | top, _ => top
  | _, top => top
  | bot, bot => bot
  | _, _ => unk

def assertable : Tri -> Prop
  | top => True
  | bot => False
  | unk => False

theorem unk_not_top : unk ≠ top := by
  intro h
  cases h

theorem unk_not_assertable : ¬ assertable unk := by
  intro h
  cases h

theorem neg_unk : neg unk = unk := rfl

theorem unk_and_not_assertable (p : Tri) : ¬ assertable (and p unk) := by
  cases p <;> intro h <;> cases h

theorem unk_or_top : or unk top = top := rfl

end Tri

inductive Term where
  | atom : Name -> Term
  | mountain : Name -> List Term -> Term
  | prim : Name -> Term
  | recur : Name -> Term
  | pending : Name -> Term
  deriving Repr

structure Entry where
  kind : Kind
  sort : Ty
  roots : List Name
  deps : List Name
  polarity : Polarity
  recSem : Option RecSemantics
  deriving Repr

abbrev Registry := Term -> Option Entry

def Registered (R : Registry) (t : Term) : Prop :=
  ∃ e, R t = some e

inductive WellFormed (R : Registry) : Term -> Prop where
  | byRegistry {t : Term} {e : Entry} : R t = some e -> WellFormed R t

theorem no_unregistered_formal_term {R : Registry} {t : Term} :
    WellFormed R t -> Registered R t := by
  intro h
  cases h with
  | byRegistry hreg => exact ⟨_, hreg⟩

structure RegistryInvariant (R : Registry) where
  generated_have_roots :
    ∀ (t : Term) (e : Entry), R t = some e -> e.kind = Kind.generated -> e.roots ≠ []
  recursive_has_semantics :
    ∀ (t : Term) (e : Entry), R t = some e -> e.kind = Kind.recursive ->
      ∃ sem, e.recSem = some sem

theorem generated_terms_have_roots {R : Registry} (inv : RegistryInvariant R)
    {t : Term} {e : Entry} (hreg : R t = some e) (hk : e.kind = Kind.generated) :
    e.roots ≠ [] :=
  inv.generated_have_roots t e hreg hk

theorem recursive_terms_have_semantics {R : Registry} (inv : RegistryInvariant R)
    {t : Term} {e : Entry} (hreg : R t = some e) (hk : e.kind = Kind.recursive) :
    ∃ sem, e.recSem = some sem :=
  inv.recursive_has_semantics t e hreg hk

def Typed (R : Registry) (t : Term) (s : Ty) : Prop :=
  ∃ e, R t = some e ∧ e.sort = s

inductive ExpandsTo (R : Registry) : Term -> Term -> Prop where
  | refl {t : Term} : WellFormed R t -> ExpandsTo R t t
  | step {t u : Term} : WellFormed R t -> WellFormed R u -> ExpandsTo R t u

structure ExpansionInvariant (R : Registry) where
  preserves_sort :
    ∀ (t u : Term) (s : Ty), ExpandsTo R t u -> Typed R t s -> Typed R u s

theorem type_preservation {R : Registry} (inv : ExpansionInvariant R)
    {t u : Term} {s : Ty} (hexp : ExpandsTo R t u) (ht : Typed R t s) :
    Typed R u s :=
  inv.preserves_sort t u s hexp ht

structure ExpansionSystem where
  expands : Term -> Term -> Prop
  nonrecursive : Term -> Prop
  nonrecursive_terminates : ∀ t, nonrecursive t -> Acc expands t

theorem nonrecursive_expansion_terminates (S : ExpansionSystem)
    {t : Term} (h : S.nonrecursive t) : Acc S.expands t :=
  S.nonrecursive_terminates t h

structure Model where
  Field : Type
  Focus : Type
  Interval : Type
  Community : Type
  Scale : Type
  Window : Type
  validIntervals : Field -> Scale -> Window -> List Interval
  step : Field -> Interval -> Field
  omega : Nat -> Nat -> Nat -> Nat -> Tri
  omegaB : List Nat -> Nat -> Tri
  audit : Field -> Tri

def unitModel : Model where
  Field := Unit
  Focus := Unit
  Interval := Unit
  Community := Unit
  Scale := Unit
  Window := Unit
  validIntervals := fun _ _ _ => [()]
  step := fun _ _ => ()
  omega := fun _ _ _ _ => Tri.top
  omegaB := fun _ _ => Tri.top
  audit := fun _ => Tri.top

theorem minimal_model_exists : Nonempty Model :=
  ⟨unitModel⟩

def HasInterval (M : Model) : Prop :=
  ∃ (g : M.Field) (s : M.Scale) (w : M.Window) (i : M.Interval),
    i ∈ M.validIntervals g s w

theorem unitModel_has_interval : HasInterval unitModel := by
  exact ⟨(), (), (), (), List.Mem.head []⟩

namespace GammaProcess

/--
Field-level continuation interface.

`Gamma` is the current field of concern; `validInterval g i` is the formal
counterpart of `i ∈ 间(Γ)`; `shenghe` is the dependent form of 生合, so it can
only be applied after a proof that the interval is valid for this Γ.
-/
structure Model where
  Gamma : Type
  Focus : Type
  Relation : Type
  Interval : Type
  Degree : Type
  Horizon : Type
  Limit : Type
  state : Gamma -> Focus -> Type
  relationState : Gamma -> Relation -> Type
  limitedBy : Gamma -> Limit -> Prop
  grid : Gamma -> Interval -> Interval -> Prop
  weight : Gamma -> Interval -> Nat
  coupling : Gamma -> Interval -> Interval -> Int
  historicalLaw : Gamma -> Interval -> Prop
  openLaw : Gamma -> Interval -> Prop
  validInterval : Gamma -> Interval -> Prop
  valid_iff_law :
    ∀ g i, validInterval g i ↔
      (historicalLaw g i ∨ openLaw g i) ∧ ∃ l : Limit, limitedBy g l
  shenghe : (g : Gamma) -> (i : Interval) -> validInterval g i -> Gamma

def HasLimit (M : Model) (g : M.Gamma) : Prop :=
  ∃ l : M.Limit, M.limitedBy g l

def HistoricalLaw (M : Model) (g : M.Gamma) (i : M.Interval) : Prop :=
  M.historicalLaw g i

def OpenLaw (M : Model) (g : M.Gamma) (i : M.Interval) : Prop :=
  M.openLaw g i

def Law (M : Model) (g : M.Gamma) (i : M.Interval) : Prop :=
  HistoricalLaw M g i ∨ OpenLaw M g i

def LawfulInterval (M : Model) (g : M.Gamma) (i : M.Interval) : Prop :=
  Law M g i ∧ HasLimit M g

theorem validInterval_iff_law (M : Model) (g : M.Gamma) (i : M.Interval) :
    M.validInterval g i ↔ LawfulInterval M g i :=
  M.valid_iff_law g i

theorem validInterval_has_limit {M : Model} {g : M.Gamma} {i : M.Interval} :
    M.validInterval g i -> HasLimit M g := by
  intro h
  exact ((validInterval_iff_law M g i).1 h).2

theorem historicalLaw_valid {M : Model} {g : M.Gamma} {i : M.Interval} :
    HistoricalLaw M g i -> HasLimit M g -> M.validInterval g i := by
  intro h
  intro hlimit
  exact (validInterval_iff_law M g i).2 ⟨Or.inl h, hlimit⟩

theorem openLaw_valid {M : Model} {g : M.Gamma} {i : M.Interval} :
    OpenLaw M g i -> HasLimit M g -> M.validInterval g i := by
  intro h
  intro hlimit
  exact (validInterval_iff_law M g i).2 ⟨Or.inr h, hlimit⟩

def IntervalDomain (M : Model) (g : M.Gamma) : Type :=
  { i : M.Interval // M.validInterval g i }

def step (M : Model) (g : M.Gamma) (i : IntervalDomain M g) : M.Gamma :=
  M.shenghe g i.val i.property

def HasInterval (M : Model) (g : M.Gamma) : Prop :=
  Nonempty (IntervalDomain M g)

def StepOpen (M : Model) (CanContinue : M.Gamma -> Prop) (g : M.Gamma) : Prop :=
  ∃ i : IntervalDomain M g, CanContinue (step M g i)

structure OpenCriteria (M : Model) where
  unfinished : M.Gamma -> Prop
  responsive : M.Gamma -> Prop
  repairable : M.Gamma -> Prop
  regenerative : M.Gamma -> Prop

def Turning {M : Model} (C : OpenCriteria M) (g : M.Gamma) : Prop :=
  C.repairable g ∧ C.regenerative g

structure OpenProfile where
  unfinished : Prop
  possible : Prop
  responsive : Prop
  transformable : Prop

def openProfile (M : Model) (C : OpenCriteria M) (g : M.Gamma) : OpenProfile :=
  { unfinished := C.unfinished g
    possible := HasInterval M g
    responsive := C.responsive g
    transformable := Turning C g }

def Open (M : Model) (C : OpenCriteria M) (g : M.Gamma) : Prop :=
  (openProfile M C g).unfinished ∧
    (openProfile M C g).possible ∧
    (openProfile M C g).responsive ∧
    (openProfile M C g).transformable

def Closed (M : Model) (C : OpenCriteria M) (g : M.Gamma) : Prop :=
  ¬ Open M C g

theorem closed_iff_not_open (M : Model) (C : OpenCriteria M)
    (g : M.Gamma) :
    Closed M C g ↔ ¬ Open M C g :=
  Iff.rfl

theorem open_has_interval {M : Model} {C : OpenCriteria M}
    {g : M.Gamma} :
    Open M C g -> HasInterval M g := by
  intro h
  exact h.2.1

def AbsoluteClosed (M : Model) (g : M.Gamma) : Prop :=
  ¬ HasInterval M g

def SituationalClosed (M : Model) (C : OpenCriteria M) (g : M.Gamma) : Prop :=
  HasInterval M g ∧ ¬ Open M C g

def ResultClosed (M : Model) (C : OpenCriteria M)
    (g : M.Gamma) (i : IntervalDomain M g) : Prop :=
  ¬ Open M C (step M g i)

theorem absoluteClosed_not_open {M : Model} {C : OpenCriteria M} {g : M.Gamma} :
    AbsoluteClosed M g -> ¬ Open M C g := by
  intro hno hopen
  exact hno (open_has_interval hopen)

theorem situationalClosed_closed {M : Model} {C : OpenCriteria M} {g : M.Gamma} :
    SituationalClosed M C g -> Closed M C g := by
  intro h
  exact h.2

theorem closed_iff_absolute_or_situational (M : Model) (C : OpenCriteria M)
    (g : M.Gamma) :
    Closed M C g ↔ AbsoluteClosed M g ∨ SituationalClosed M C g := by
  classical
  constructor
  · intro h
    by_cases hi : HasInterval M g
    · exact Or.inr ⟨hi, h⟩
    · exact Or.inl hi
  · intro h
    cases h with
    | inl hno =>
        exact absoluteClosed_not_open hno
    | inr hs =>
        exact situationalClosed_closed hs

def PropDiffers (p q : Prop) : Prop :=
  (p ∧ ¬ q) ∨ (q ∧ ¬ p)

def ProfileDiffers (p q : OpenProfile) : Prop :=
  PropDiffers p.unfinished q.unfinished ∨
    PropDiffers p.possible q.possible ∨
    PropDiffers p.responsive q.responsive ∨
    PropDiffers p.transformable q.transformable

def Opportunity (M : Model) (C : OpenCriteria M) (g : M.Gamma) : Prop :=
  ∃ i j : IntervalDomain M g,
    i.val ≠ j.val ∧
      ProfileDiffers (openProfile M C (step M g i))
        (openProfile M C (step M g j))

def Coupled (M : Model) (g : M.Gamma) (i j : M.Interval) : Prop :=
  M.coupling g i j ≠ 0 ∨ M.coupling g j i ≠ 0

def DirectionalWeightDifference (M : Model) (g : M.Gamma)
    (i j : IntervalDomain M g) : Prop :=
  M.grid g i.val j.val ∧
    Coupled M g i.val j.val ∧
    M.weight g i.val ≠ M.weight g j.val

def Tendency (M : Model) (g : M.Gamma) : Prop :=
  ∃ i j : IntervalDomain M g, DirectionalWeightDifference M g i j

/-- Yuan as the first triadic formation: interval, focus, and transition. -/
structure YuanTriad (M : Model) where
  gamma : M.Gamma
  focus : M.Focus
  interval : M.Interval
  valid : M.validInterval gamma interval
  after : M.Gamma
  after_eq : after = M.shenghe gamma interval valid

theorem yuan_after_is_shenghe {M : Model} (y : YuanTriad M) :
    y.after = M.shenghe y.gamma y.interval y.valid :=
  y.after_eq

/-- Abstract predicates for 几 / 势 / 机 over the field continuation model. -/
structure SystemDynamics (M : Model) where
  trace : (g : M.Gamma) -> IntervalDomain M g -> Prop
  momentum : List M.Gamma -> Prop
  pivot : M.Gamma -> Prop

/--
An action or transition changes the future interval domain when the valid
interval predicate after 生合 is not extensionally the same as before.
-/
def ChangesFutureIntervals (M : Model) (g : M.Gamma) (i : IntervalDomain M g) : Prop :=
  ¬ ∀ j : M.Interval, M.validInterval g j ↔ M.validInterval (step M g i) j

structure ValueCriteria (M : Model) (C : OpenCriteria M) where
  peaceful : M.Gamma -> Prop
  harmonious : M.Gamma -> Prop
  highTension : M.Gamma -> Prop
  noTaking : M.Gamma -> Prop
  noRootClosure : M.Gamma -> Prop
  mayOpenDimension : M.Gamma -> Prop
  auditUnbroken : M.Gamma -> Prop

def RightCrisis (M : Model) (C : OpenCriteria M)
    (V : ValueCriteria M C) (g : M.Gamma) : Prop :=
  V.highTension g ∧
    Tendency M g ∧
    Opportunity M C g ∧
    V.noTaking g ∧
    V.noRootClosure g ∧
    V.mayOpenDimension g ∧
    V.auditUnbroken g

theorem rightCrisis_has_tendency {M : Model} {C : OpenCriteria M}
    {V : ValueCriteria M C} {g : M.Gamma} :
    RightCrisis M C V g -> Tendency M g := by
  intro h
  exact h.2.1

def Good (M : Model) (C : OpenCriteria M)
    (V : ValueCriteria M C) (g : M.Gamma) : Prop :=
  V.peaceful g ∨ V.harmonious g ∨ RightCrisis M C V g

structure FreedomCriteria (M : Model) where
  choice : (a : M.Focus) -> (g : M.Gamma) -> IntervalDomain M g -> Prop
  badAfter : M.Gamma -> Prop
  forcedBad : M.Focus -> M.Gamma -> Prop
  recognizableGood : M.Focus -> M.Gamma -> Prop

def GoodPath (M : Model) (F : FreedomCriteria M)
    (a : M.Focus) (g : M.Gamma) : Prop :=
  ∃ i : IntervalDomain M g, F.choice a g i ∧ ¬ F.badAfter (step M g i)

def Freedom (M : Model) (F : FreedomCriteria M)
    (a : M.Focus) (g : M.Gamma) : Prop :=
  GoodPath M F a g ∧ ¬ F.forcedBad a g ∧ F.recognizableGood a g

theorem freedom_has_good_path {M : Model} {F : FreedomCriteria M}
    {a : M.Focus} {g : M.Gamma} :
    Freedom M F a g -> GoodPath M F a g := by
  intro h
  exact h.1

structure DaoCriteria (M : Model) where
  Path : Type
  relevant : M.Gamma -> Path -> M.Degree -> M.Horizon -> Prop
  canContinue : M.Gamma -> Path -> M.Degree -> M.Horizon -> Prop
  badAt : M.Gamma -> Path -> M.Degree -> M.Horizon -> Prop

def HasRelevantScope (M : Model) (D : DaoCriteria M) (p : D.Path) (g : M.Gamma) :
    Prop :=
  ∃ d t, D.relevant g p d t

def TrueDao (M : Model) (D : DaoCriteria M) (p : D.Path) (g : M.Gamma) : Prop :=
  HasRelevantScope M D p g ∧
    ∀ d t, D.relevant g p d t -> D.canContinue g p d t ∧ ¬ D.badAt g p d t

theorem trueDao_has_relevant_scope {M : Model} {D : DaoCriteria M}
    {p : D.Path} {g : M.Gamma} :
    TrueDao M D p g -> HasRelevantScope M D p g := by
  intro h
  exact h.1

def unitProcess : Model where
  Gamma := Unit
  Focus := Unit
  Relation := Unit
  Interval := Unit
  Degree := Unit
  Horizon := Unit
  Limit := Unit
  state := fun _ _ => Unit
  relationState := fun _ _ => Unit
  limitedBy := fun _ _ => True
  grid := fun _ _ _ => True
  weight := fun _ _ => 0
  coupling := fun _ _ _ => 0
  historicalLaw := fun _ _ => True
  openLaw := fun _ _ => False
  validInterval := fun _ _ => True
  valid_iff_law := by
    intro _ _
    simp
  shenghe := fun _ _ _ => ()

theorem unitProcess_has_interval : HasInterval unitProcess () := by
  exact ⟨⟨(), trivial⟩⟩

def unitOpenCriteria : OpenCriteria unitProcess where
  unfinished := fun _ => True
  responsive := fun _ => True
  repairable := fun _ => True
  regenerative := fun _ => True

theorem unitProcess_open : Open unitProcess unitOpenCriteria () := by
  exact ⟨trivial, unitProcess_has_interval, trivial, trivial, trivial⟩

inductive OnticRoot where
  | thing
  | motion
  | interval
  deriving DecidableEq, Repr

namespace OnticRoot

def dimension : OnticRoot -> String
  | .thing => "0-dimensional discreteness"
  | .motion => "n-dimensional process extension"
  | .interval => "topological relation without intrinsic metric"

end OnticRoot

inductive Manifestation where
  | wei
  | chang
  | trace
  deriving DecidableEq, Repr

namespace Manifestation

def visibleRoots : Manifestation -> List OnticRoot
  | .wei => [.thing, .interval]
  | .chang => [.motion, .thing]
  | .trace => [.interval, .motion]

def bracketedRoot : Manifestation -> OnticRoot
  | .wei => .motion
  | .chang => .interval
  | .trace => .thing

def shape : Manifestation -> String
  | .wei => "pointed position"
  | .chang => "extended medium"
  | .trace => "contact interface"

theorem visible_roots_pair (m : Manifestation) :
    (visibleRoots m).length = 2 := by
  cases m <;> rfl

theorem bracketed_root_not_visible (m : Manifestation) :
    bracketedRoot m ∉ visibleRoots m := by
  cases m <;> decide

end Manifestation

inductive StaticFace where
  | noPersistentSplit
  | pointOnField
  | contactBoundary
  deriving DecidableEq, Repr

inductive DynamicMark where
  | trace
  | momentum
  | pivot
  deriving DecidableEq, Repr

namespace DynamicMark

def ofManifestation : Manifestation -> DynamicMark
  | .wei => .trace
  | .chang => .momentum
  | .trace => .pivot

def staticFaceOf : Manifestation -> StaticFace
  | .wei => .noPersistentSplit
  | .chang => .pointOnField
  | .trace => .contactBoundary

def expansionMode : DynamicMark -> String
  | .trace => "foundational seed at the zero-dimensional limit"
  | .momentum => "trace extended through a continuous medium"
  | .pivot => "trace gathered through topological routing"

theorem wei_mark_is_foundational :
    ofManifestation .wei = .trace :=
  rfl

end DynamicMark

inductive Gate where
  | open
  | closed
  deriving DecidableEq, Repr

inductive EventResult where
  | life
  | extinction
  | formation
  | reversal
  | turning
  | keeping
  deriving DecidableEq, Repr

namespace Gate

def result : DynamicMark -> Gate -> EventResult
  | .trace, .open => .life
  | .trace, .closed => .extinction
  | .momentum, .open => .formation
  | .momentum, .closed => .reversal
  | .pivot, .open => .turning
  | .pivot, .closed => .keeping

theorem gate_binary (g : Gate) : g = .open ∨ g = .closed := by
  cases g <;> simp

end Gate

inductive CompositeForm where
  | network
  | body
  | flow
  deriving DecidableEq, Repr

namespace CompositeForm

def parts : CompositeForm -> Manifestation × Manifestation
  | .network => (.wei, .trace)
  | .body => (.wei, .chang)
  | .flow => (.chang, .trace)

def feedbackTarget : CompositeForm -> Manifestation
  | .network => .wei
  | .body => .chang
  | .flow => .trace

theorem parts_distinct (c : CompositeForm) :
    (parts c).1 ≠ (parts c).2 := by
  cases c <;> decide

end CompositeForm

end GammaProcess

end SSBX.Core
