/-
# UnityBoundary — 统一 / 理限 / 文限

Companion: `义理/统一边界 · 从理到文.md`

本文件只形式化一个薄的边界命题：

1. 统一不是一条普通的信息描述；
2. 统一在本文接口中是 shared boundary condition；
3. 理表达与文表达都先降到 finite expression；
4. 因此二者的极限边界一致。

这不是形而上学完备证明，而是本项目语言边界的 machine-checked skeleton。
-/

namespace SSBX.Foundation.Modern.UnityBoundary

/-! ## § 1 Unity is not ordinary information -/

/-- 普通信息描述：bit 或有限 token 片段。 -/
inductive InformationDescription : Type
  | bit (b : Bool)
  | finiteText (tokens : Nat)
  deriving Repr, DecidableEq

/-- 信息描述的内容种类。 -/
inductive DescriptionContent : Type
  | finiteContent
  | boundaryPointer
  deriving Repr, DecidableEq

/-- 普通信息描述只能给有限内容。 -/
def contentOfInfo : InformationDescription → DescriptionContent
  | .bit _ => .finiteContent
  | .finiteText _ => .finiteContent

/-- 统一若可被谈及，只能作为边界指针，而不是普通 finite content。 -/
def unityContent : DescriptionContent := .boundaryPointer

/-- 信息描述不能把统一作为一个普通内容项给出。 -/
theorem information_description_never_is_unity (d : InformationDescription) :
    contentOfInfo d ≠ unityContent := by
  cases d <;> simp [contentOfInfo, unityContent]

/-! ## § 2 Unity as shared boundary -/

/-- 统一的角色：不是对象层信息，而是共享边界条件。 -/
inductive UnityRole : Type
  | informationObject
  | sharedBoundaryCondition
  deriving Repr, DecidableEq

/-- 本文定义的统一。 -/
def unity : UnityRole := .sharedBoundaryCondition

/-- 统一不是对象层信息。 -/
theorem unity_not_information_object :
    unity ≠ UnityRole.informationObject := by
  intro h
  cases h

/-- 统一是什么：共享边界条件。 -/
theorem unity_is_shared_boundary_condition :
    unity = UnityRole.sharedBoundaryCondition :=
  rfl

/-! ## § 3 Li and Wen share the same finite-expression boundary -/

/-- 任意有限表达的共同底层：只记录其有限 token 数。 -/
structure FiniteExpression where
  tokenCount : Nat
  deriving Repr

/-- 有限表达的极限：总有更深一层在当前 tokenCount 之外。 -/
def HasOutsideDepth (e : FiniteExpression) : Prop :=
  ∃ n : Nat, e.tokenCount < n

/-- 每个有限表达都有外部深度。 -/
theorem finite_expression_has_outside_depth (e : FiniteExpression) :
    HasOutsideDepth e :=
  ⟨e.tokenCount + 1, Nat.lt_succ_self e.tokenCount⟩

/-- 边界种类：当前模型只保留“共享极限边界”。 -/
inductive BoundaryKind : Type
  | sharedLimit
  deriving Repr, DecidableEq

/-- 任何有限表达最终都抵达同一种表达极限。 -/
def finiteExpressionBoundary (_e : FiniteExpression) : BoundaryKind :=
  .sharedLimit

/-- 理表达：形式、证明、模型等理层表达的有限 token 承载。 -/
structure LiExpression where
  tokens : Nat
  deriving Repr

/-- 文表达：字、句、篇章等文层表达的有限 token 承载。 -/
structure WenExpression where
  tokens : Nat
  deriving Repr

/-- 理表达降到有限表达。 -/
def LiExpression.toFinite (e : LiExpression) : FiniteExpression :=
  ⟨e.tokens⟩

/-- 文表达降到有限表达。 -/
def WenExpression.toFinite (e : WenExpression) : FiniteExpression :=
  ⟨e.tokens⟩

/-- 理的表达极限。 -/
def liLimit (e : LiExpression) : BoundaryKind :=
  finiteExpressionBoundary e.toFinite

/-- 文字的表达极限。 -/
def wenLimit (e : WenExpression) : BoundaryKind :=
  finiteExpressionBoundary e.toFinite

/-- 理的极限是共享极限边界。 -/
theorem li_limit_is_shared (e : LiExpression) :
    liLimit e = BoundaryKind.sharedLimit :=
  rfl

/-- 文的极限是共享极限边界。 -/
theorem wen_limit_is_shared (e : WenExpression) :
    wenLimit e = BoundaryKind.sharedLimit :=
  rfl

/-- 理限与文限一致：二者都经由 finite expression 抵达同一个 sharedLimit。 -/
theorem li_wen_boundaries_coincide (l : LiExpression) (w : WenExpression) :
    liLimit l = wenLimit w :=
  rfl

/-- 理表达的“外部深度”谓词。 -/
def liHasOutsideDepth (l : LiExpression) : Prop :=
  HasOutsideDepth l.toFinite

/-- 文表达的“外部深度”谓词。 -/
def wenHasOutsideDepth (w : WenExpression) : Prop :=
  HasOutsideDepth w.toFinite

/-- 每个理表达都有其 tokenCount 之外的深度。 -/
theorem li_expression_has_outside_depth (l : LiExpression) :
    liHasOutsideDepth l :=
  finite_expression_has_outside_depth l.toFinite

/-- 每个文表达都有其 tokenCount 之外的深度。 -/
theorem wen_expression_has_outside_depth (w : WenExpression) :
    wenHasOutsideDepth w :=
  finite_expression_has_outside_depth w.toFinite

/-- 若理表达与文表达的有限长度相同，则它们的外部深度边界谓词等价。 -/
theorem li_wen_outside_depth_equiv_of_same_count
    (l : LiExpression) (w : WenExpression) (h : l.tokens = w.tokens) :
    liHasOutsideDepth l ↔ wenHasOutsideDepth w := by
  change (∃ n : Nat, l.tokens < n) ↔ (∃ n : Nat, w.tokens < n)
  rw [h]

/-! ## § 4 Public summary -/

/-- 公开摘要：
    (1) 普通信息描述不能把统一作为 finite content 给出；
    (2) 统一是 shared boundary condition；
    (3) 理限与文限一致；
    (4) 二者都具有有限表达的外部深度边界。 -/
theorem unity_boundary_summary :
    (∀ d : InformationDescription, contentOfInfo d ≠ unityContent)
    ∧ unity = UnityRole.sharedBoundaryCondition
    ∧ (∀ l : LiExpression, ∀ w : WenExpression, liLimit l = wenLimit w)
    ∧ (∀ l : LiExpression, liHasOutsideDepth l)
    ∧ (∀ w : WenExpression, wenHasOutsideDepth w) :=
  ⟨information_description_never_is_unity,
   unity_is_shared_boundary_condition,
   li_wen_boundaries_coincide,
   li_expression_has_outside_depth,
   wen_expression_has_outside_depth⟩

end SSBX.Foundation.Modern.UnityBoundary
