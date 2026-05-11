/-
# KnowableBoundary — 可知边界 / 语言边界 / 可描述之理

Companion: `义理/边界/可知边界 · 语言与理.md`

本文件形式化一条薄命题：

1. 语言的边界就是可描述之理的边界；
2. 边界之内，可说即以理可描述；
3. 边界之外，不可说；若仍作为 utterance 出现，也不是理；
4. 可感 / 不可感 等其他“可”的边界由相邻边界文件承接；本文件只保留
   defer anchor，说明它们不属于本文的可知边界。
-/
import SSBX.Foundation.Modern.UnityBoundary

namespace SSBX.Foundation.Modern.KnowableBoundary

open SSBX.Foundation.Modern.UnityBoundary

/-! ## § 1 Language boundary = describable-Li boundary -/

/-- 语言表达沿用上一层的 `WenExpression`。 -/
abbrev LanguageExpression := WenExpression

/-- 可描述之理沿用上一层的 `LiExpression`。 -/
abbrev DescribableLiExpression := LiExpression

/-- 语言边界：文字表达的表达极限。 -/
def languageBoundary (w : LanguageExpression) : BoundaryKind :=
  wenLimit w

/-- 可描述之理的边界：理表达的表达极限。 -/
def describableLiBoundary (l : DescribableLiExpression) : BoundaryKind :=
  liLimit l

/-- **语言边界 = 可描述之理的边界**。 -/
theorem language_boundary_eq_describable_li_boundary
    (w : LanguageExpression) (l : DescribableLiExpression) :
    languageBoundary w = describableLiBoundary l :=
  (li_wen_boundaries_coincide l w).symm

/-! ## § 2 The knowable region -/

/-- 本文件只处理“可知”边界：界内为可描述之理，界外为其外部。 -/
inductive KnowableRegion : Type
  | withinDescribableLi
  | beyondDescribableLi
  deriving Repr, DecidableEq

/-- 可说：位于可描述之理界内。 -/
def Sayable (r : KnowableRegion) : Prop :=
  r = .withinDescribableLi

/-- 是理：位于可描述之理界内。 -/
def IsLi (r : KnowableRegion) : Prop :=
  r = .withinDescribableLi

/-- 可知：本文件先限定为“语言可描述之理”。 -/
def Knowable (r : KnowableRegion) : Prop :=
  IsLi r

/-- 在本文件的界内，`可说` 与 `是理` 是同一个边界条件。 -/
theorem sayable_iff_is_li (r : KnowableRegion) :
    Sayable r ↔ IsLi r :=
  Iff.rfl

/-- 可知边界即语言边界：可知 iff 可说。 -/
theorem knowable_iff_sayable (r : KnowableRegion) :
    Knowable r ↔ Sayable r :=
  Iff.rfl

/-- 界外不可说。 -/
theorem beyond_describable_li_is_unsayable :
    ¬ Sayable .beyondDescribableLi := by
  intro h
  cases h

/-- 界外不是理。 -/
theorem beyond_describable_li_is_not_li :
    ¬ IsLi .beyondDescribableLi := by
  intro h
  cases h

/-! ## § 3 If said beyond the boundary, it is not Li -/

/-- 话语事件：只记录它声称落在哪个可知区域。 -/
structure Utterance where
  region : KnowableRegion
  deriving Repr

/-- 理性话语：其区域仍在可描述之理界内。 -/
def IsLiUtterance (u : Utterance) : Prop :=
  IsLi u.region

/-- 越界话语：声称落在可描述之理之外。 -/
def BeyondBoundaryUtterance (u : Utterance) : Prop :=
  u.region = .beyondDescribableLi

/-- “说了也非理”：若一个 utterance 落在边界之外，它就不是理性话语。 -/
theorem beyond_boundary_utterance_is_non_li
    (u : Utterance) (h : BeyondBoundaryUtterance u) :
    ¬ IsLiUtterance u := by
  intro interlace
  unfold BeyondBoundaryUtterance at h
  unfold IsLiUtterance IsLi at interlace
  rw [h] at interlace
  cases interlace

/-! ## § 4 Other ke-boundaries are deferred from this file -/

/-- 其他“可”的边界：可感、不可感、可行、不可行、可证、不可证、
    可测、不可测、可名、不可名等。本文件只枚举其留项位；相邻边界文件承接处理。 -/
inductive DeferredKeBoundary : Type
  | feelable
  | unfeelable
  | actionable
  | unactionable
  | provable
  | unprovable
  | measurable
  | unmeasurable
  | nameable
  | unnameable
  deriving Repr, DecidableEq

/-- 本文件不处理这些非可知轴的边界。 -/
def handledHere (_b : DeferredKeBoundary) : Bool := false

/-- 可感 / 可行 / 可证 / 可测 / 可名等边界在本文件中全部 deferred。 -/
theorem deferred_ke_boundaries_are_not_handled_here (b : DeferredKeBoundary) :
    handledHere b = false := by
  cases b <;> rfl

/-! ## § 5 Public summary -/

/-- 公开摘要：
    (1) 语言边界等于可描述之理的边界；
    (2) 可说 iff 是理 iff 可知；
    (3) 界外不可说且非理；
    (4) 界外若被强作话语，也不是理性话语；
    (5) 可感 / 可行 / 可证 / 可测 / 可名等非可知轴边界 deferred。 -/
theorem knowable_boundary_summary :
    (∀ w : LanguageExpression, ∀ l : DescribableLiExpression,
      languageBoundary w = describableLiBoundary l)
    ∧ (∀ r : KnowableRegion, Sayable r ↔ IsLi r)
    ∧ (∀ r : KnowableRegion, Knowable r ↔ Sayable r)
    ∧ ¬ Sayable .beyondDescribableLi
    ∧ ¬ IsLi .beyondDescribableLi
    ∧ (∀ u : Utterance, BeyondBoundaryUtterance u → ¬ IsLiUtterance u)
    ∧ (∀ b : DeferredKeBoundary, handledHere b = false) :=
  ⟨language_boundary_eq_describable_li_boundary,
   sayable_iff_is_li,
   knowable_iff_sayable,
   beyond_describable_li_is_unsayable,
   beyond_describable_li_is_not_li,
   beyond_boundary_utterance_is_non_li,
   deferred_ke_boundaries_are_not_handled_here⟩

end SSBX.Foundation.Modern.KnowableBoundary
