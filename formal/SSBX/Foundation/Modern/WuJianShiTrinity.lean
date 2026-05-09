/-
# WuJianShiTrinity — 物 / 间 / 事 三位一体

Companion: `义理/物间事三位一体 · 时空事件.md`

This module proves only a typed skeleton:

1. a `WuJianShiExpression` is completely reconstructed from thing, interval,
   and event fields;
2. the three aspects are exhaustive and pairwise distinct;
3. reading `间` as spacetime gives an equivalent carrier + spacetime + event
   interface.

It is not a physics proof, a metaphysical completion proof, or a claim that
every external domain has already been faithfully modeled in this file.
-/

namespace SSBX.Foundation.Modern.WuJianShiTrinity

universe u v w

/-! ## § 1 The three irreducible aspect positions -/

/-- The three structural positions: 物, 间, 事. -/
inductive TriuneAspect : Type
  | wu
  | jian
  | shi
  deriving Repr, DecidableEq

namespace TriuneAspect

/-- Chinese surface form for the aspect. -/
def surface : TriuneAspect → String
  | .wu => "物"
  | .jian => "间"
  | .shi => "事"

/-- The aspect interface has no fourth case. -/
theorem exhaustive (a : TriuneAspect) :
    a = .wu ∨ a = .jian ∨ a = .shi := by
  cases a <;> simp

/-- The three aspect positions do not collapse into one another. -/
theorem pairwise_distinct :
    TriuneAspect.wu ≠ TriuneAspect.jian
      ∧ TriuneAspect.wu ≠ TriuneAspect.shi
      ∧ TriuneAspect.jian ≠ TriuneAspect.shi := by
  simp

end TriuneAspect

/-! ## § 2 物-间-事 expressions -/

/--
An expression in this layer has three projections:

* `thing`: what can be picked out as a carrier or relatively stable identity;
* `interval`: the differentiating / locating medium, including spacetime or
  relational interval readings;
* `event`: occurrence, change, action, or happening.
-/
structure WuJianShiExpression (Thing : Type u) (Interval : Type v) (Event : Type w) where
  thing : Thing
  interval : Interval
  event : Event

variable {Thing : Type u} {Interval : Type v} {Event : Type w}

/-- Being expressible by 物-间-事 means having exactly these three witnesses. -/
def ExpressedByTriad (x : WuJianShiExpression Thing Interval Event) : Prop :=
  ∃ thing : Thing, ∃ interval : Interval, ∃ event : Event,
    x = { thing := thing, interval := interval, event := event }

/-- Every value of the interface decomposes into 物, 间, and 事. -/
theorem every_wjs_expression_decomposes
    (x : WuJianShiExpression Thing Interval Event) :
    ExpressedByTriad x := by
  cases x with
  | mk thing interval event =>
      exact ⟨thing, interval, event, rfl⟩

/-- Rebuild an expression from its three projections. -/
def rebuild (thing : Thing) (interval : Interval) (event : Event) :
    WuJianShiExpression Thing Interval Event :=
  { thing := thing, interval := interval, event := event }

/-- Taking the three fields and rebuilding returns the original expression. -/
theorem wjs_rebuild_identity (x : WuJianShiExpression Thing Interval Event) :
    rebuild x.thing x.interval x.event = x := by
  cases x
  rfl

/-- The three projections jointly determine the expression. -/
theorem wjs_fields_determine_expression
    {x y : WuJianShiExpression Thing Interval Event}
    (hThing : x.thing = y.thing)
    (hInterval : x.interval = y.interval)
    (hEvent : x.event = y.event) :
    x = y := by
  cases x
  cases y
  simp at hThing hInterval hEvent
  simp [hThing, hInterval, hEvent]

/-- Presence of an aspect in a concrete expression. -/
def AspectPresent (x : WuJianShiExpression Thing Interval Event) :
    TriuneAspect → Prop
  | .wu => ∃ thing : Thing, x.thing = thing
  | .jian => ∃ interval : Interval, x.interval = interval
  | .shi => ∃ event : Event, x.event = event

/-- Any existing expression has all three aspects present. -/
theorem every_aspect_present
    (x : WuJianShiExpression Thing Interval Event) (a : TriuneAspect) :
    AspectPresent x a := by
  cases a with
  | wu =>
      exact ⟨x.thing, rfl⟩
  | jian =>
      exact ⟨x.interval, rfl⟩
  | shi =>
      exact ⟨x.event, rfl⟩

/-! ## § 3 Spacetime + event reading -/

/--
The physicalized reading: a carrier is situated in spacetime through an
occurrence.  This is the `时空 + event` surface, with the carrier kept explicit
so that `物` is not silently erased.
-/
structure SpacetimeEventExpression
    (Thing : Type u) (SpaceTime : Type v) (Event : Type w) where
  carrier : Thing
  spacetime : SpaceTime
  occurrence : Event

variable {SpaceTime : Type v}

/-- Read a 物-间-事 expression as carrier + spacetime + event. -/
def toSpacetimeEvent
    (x : WuJianShiExpression Thing SpaceTime Event) :
    SpacetimeEventExpression Thing SpaceTime Event :=
  { carrier := x.thing, spacetime := x.interval, occurrence := x.event }

/-- Read carrier + spacetime + event back as 物-间-事. -/
def fromSpacetimeEvent
    (x : SpacetimeEventExpression Thing SpaceTime Event) :
    WuJianShiExpression Thing SpaceTime Event :=
  { thing := x.carrier, interval := x.spacetime, event := x.occurrence }

/-- The 物-间-事 reading survives translation to spacetime-event form. -/
theorem from_to_spacetime_event_identity
    (x : WuJianShiExpression Thing SpaceTime Event) :
    fromSpacetimeEvent (toSpacetimeEvent x) = x := by
  cases x
  rfl

/-- The spacetime-event reading survives translation to 物-间-事 form. -/
theorem to_from_spacetime_event_identity
    (x : SpacetimeEventExpression Thing SpaceTime Event) :
    toSpacetimeEvent (fromSpacetimeEvent x) = x := by
  cases x
  rfl

/-! ## § 4 Public summaries -/

/-- Public summary for the triune interface. -/
theorem wjs_trinity_summary
    (x : WuJianShiExpression Thing Interval Event) :
    ExpressedByTriad x
      ∧ rebuild x.thing x.interval x.event = x
      ∧ (∀ a : TriuneAspect, a = .wu ∨ a = .jian ∨ a = .shi)
      ∧ AspectPresent x .wu
      ∧ AspectPresent x .jian
      ∧ AspectPresent x .shi
      ∧ TriuneAspect.wu ≠ TriuneAspect.jian
      ∧ TriuneAspect.wu ≠ TriuneAspect.shi
      ∧ TriuneAspect.jian ≠ TriuneAspect.shi := by
  exact
    ⟨ every_wjs_expression_decomposes x
    , wjs_rebuild_identity x
    , TriuneAspect.exhaustive
    , every_aspect_present x .wu
    , every_aspect_present x .jian
    , every_aspect_present x .shi
    , TriuneAspect.pairwise_distinct.1
    , TriuneAspect.pairwise_distinct.2.1
    , TriuneAspect.pairwise_distinct.2.2
    ⟩

/-- Public summary for the equivalence with the spacetime-event reading. -/
theorem spacetime_event_equivalence_summary
    (x : WuJianShiExpression Thing SpaceTime Event)
    (y : SpacetimeEventExpression Thing SpaceTime Event) :
    fromSpacetimeEvent (toSpacetimeEvent x) = x
      ∧ toSpacetimeEvent (fromSpacetimeEvent y) = y :=
  ⟨from_to_spacetime_event_identity x, to_from_spacetime_event_identity y⟩

end SSBX.Foundation.Modern.WuJianShiTrinity
