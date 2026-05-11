/-
# YonedaFull —— 米田引理之完整双射版本（Phase 4 续之续）

Companion: `义理/类与映 · 从元到映.md` § 米田续

`Modern/CatExt.lean` § 6 已 anchor 协变 Hom 函子 `homFunctor C A : Functor C SetCat`，
然其上**米田引理**之核心断言尚阙：对任意 `F : Functor C SetCat`，

  `NatTrans (homFunctor C A) F  ≃  F.obj A`

本文补足之：
  § 1   米田正向映射 `yonedaForward η = η.app A (𝟙 A)`
  § 2   米田反向映射 `yonedaBackward x = ⟨fun B f => F.map f x, naturality⟩`
  § 3   `forward ∘ backward = id`（借函子 `map_id` 律）
  § 4   `backward ∘ forward = id`（借自然变换 `naturality` + `id_left`）
  § 5   双射结构 `YonedaEquiv` 与米田嵌入忠实性推论
  § 6   `BaguaCat1` 上之米田 vacuous 实例（Hom = Unit ⇒ 平凡见证）
  § 7   公开摘要

## 道理二分立场
本文件全程在 LeiYing 之 homemade `Cat` 框架内进行；不引入 Mathlib，
不诉诸 `Equiv`，仅以二元结构记录双射。米田之"道"在于函子值
点 `F.obj A` 与从 `Hom(A, -)` 出之自然变换之间之**信息守恒**——
此即"理"层之同构。全文 0 sorry / 0 axiom。

universe 处理：与 `CatExt` § 6 一致，固定 `C : Cat.{1, 0}` (= `TyCat`)，
`F : Functor C SetCat.{0}`，使两端共享 universe `(1, 0)`。
-/
import SSBX.Foundation.Modern.CatExt

namespace SSBX.Foundation.Modern.YonedaFull

open SSBX.Foundation.Eight.LeiYing
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Modern.CatExt

/-! ## § 1 米田正向映射 yonedaForward

给定自然变换 `η : Hom(A, -) ⇒ F`，于点 `A` 之 component 应用于
恒等态射 `𝟙 A : Hom(A, A)`，得 `F.obj A` 中之元素。 -/

/-- **米田正向映射**：`η ↦ η.app A (𝟙 A)`。 -/
def yonedaForward {C : TyCat} {A : C.Obj} {F : Functor C SetCat.{0}}
    (η : NatTrans (homFunctor C A) F) : F.obj A :=
  η.app A (C.id A)

/-! ## § 2 米田反向映射 yonedaBackward

给定 `x : F.obj A`，构造自然变换：在点 `B` 上，态射 `f : Hom(A, B)` ↦
`F.map f x ∈ F.obj B`。自然性方块由 `F.map_comp` 给出。 -/

/-- **米田反向映射之 component**：`B ↦ (f ↦ F.map f x)`。 -/
def yonedaBackwardApp {C : TyCat} {A : C.Obj} {F : Functor C SetCat.{0}}
    (x : F.obj A) (B : C.Obj) : SetCat.{0}.Hom ((homFunctor C A).obj B) (F.obj B) :=
  fun (f : C.Hom A B) => F.map f x

/-- **米田反向映射**：`x ↦ ⟨fun B f => F.map f x, naturality⟩`。 -/
def yonedaBackward {C : TyCat} {A : C.Obj} {F : Functor C SetCat.{0}}
    (x : F.obj A) : NatTrans (homFunctor C A) F where
  app := yonedaBackwardApp x
  naturality := fun {X Y} f => by
    -- 目标：SetCat.comp ((homFunctor C A).map f) (app Y) = SetCat.comp (app X) (F.map f)
    -- 即 (fun g => F.map (C.comp g f) x) = (fun g => F.map f (F.map g x))
    funext (g : C.Hom A X)
    -- 左边：app Y ((homFunctor C A).map f g) = F.map (C.comp g f) x
    -- 右边：F.map f (app X g) = F.map f (F.map g x)
    show F.map (C.comp g f) x = F.map f (F.map g x)
    -- 由 F.map_comp : F.map (C.comp g f) = SetCat.comp (F.map g) (F.map f)
    --              = fun y => F.map f (F.map g y)
    rw [F.map_comp g f]
    rfl

/-! ## § 3 forward ∘ backward = id

由 `F.map_id A : F.map (𝟙 A) = id_{F.obj A}` 即得。 -/

/-- **米田 round-trip 1**：`yonedaForward (yonedaBackward x) = x`。 -/
theorem yonedaForward_backward {C : TyCat} {A : C.Obj}
    {F : Functor C SetCat.{0}} (x : F.obj A) :
    yonedaForward (yonedaBackward (A := A) (F := F) x) = x := by
  -- 解开定义：yonedaForward η = η.app A (𝟙 A)；
  -- 此处 η = yonedaBackward x，η.app A = yonedaBackwardApp x A = (fun f => F.map f x)
  -- 故 yonedaForward (yonedaBackward x) = F.map (𝟙 A) x
  show F.map (C.id A) x = x
  -- 由 F.map_id A : F.map (𝟙 A) = SetCat.id (F.obj A) = id
  rw [F.map_id A]
  rfl

/-! ## § 4 backward ∘ forward = id

关键步：自然变换 `η` 之 naturality 方块在 `f : Hom(A, B)` 上施加到
`𝟙 A : Hom(A, A)`，得 `η.app B f = F.map f (η.app A (𝟙 A))`。 -/

/-- **NatTrans 之外延律**：`app` 字段逐点相等 ⇒ 整体相等（naturality 是 Prop）。 -/
theorem natTrans_ext {C D : Cat.{u, v}} {F G : Functor C D}
    {η₁ η₂ : NatTrans F G} (h : ∀ X, η₁.app X = η₂.app X) : η₁ = η₂ := by
  rcases η₁ with ⟨app₁, nat₁⟩
  rcases η₂ with ⟨app₂, nat₂⟩
  have happ : app₁ = app₂ := by funext X; exact h X
  subst happ
  rfl

/-- **米田 round-trip 2**：`yonedaBackward (yonedaForward η) = η`。 -/
theorem yonedaBackward_forward {C : TyCat} {A : C.Obj}
    {F : Functor C SetCat.{0}} (η : NatTrans (homFunctor C A) F) :
    yonedaBackward (yonedaForward η) = η := by
  -- 借 natTrans_ext：逐点 app 字段相等即可
  apply natTrans_ext
  intro B
  -- 目标：(yonedaBackward (yonedaForward η)).app B = η.app B
  -- LHS 解 def 后 = (fun f : C.Hom A B => F.map f (η.app A (C.id A)))
  funext (f : C.Hom A B)
  -- 目标：(yonedaBackward (yonedaForward η)).app B f = η.app B f
  -- 解开 def：左 = F.map f (η.app A (C.id A))
  show F.map f (η.app A (C.id A)) = η.app B f
  -- 由 η 之自然性 nat f：在 g = C.id A 处取 component
  have hnat := η.naturality f
  have hpt' := congrFun hnat (C.id A)
  -- hpt' : SetCat.comp ((homFunctor C A).map f) (η.app B) (C.id A)
  --        = SetCat.comp (η.app A) (F.map f) (C.id A)
  -- SetCat.comp 之解开 : SetCat.comp p q = fun a => q (p a)，
  -- (homFunctor C A).map f g = C.comp g f；故 reduce 后：
  have hpt : η.app B (C.comp (C.id A) f) = F.map f (η.app A (C.id A)) := hpt'
  -- 化简 hpt 左边之 id_left
  rw [C.id_left] at hpt
  -- hpt : η.app B f = F.map f (η.app A (C.id A))
  exact hpt.symm

/-! ## § 5 米田双射结构 + 嵌入忠实性 -/

/-- **米田双射** `Y(F, A) : NatTrans (Hom(A, -)) F  ≃  F.obj A`，
    以二元结构记录（不依 Mathlib `Equiv`）。 -/
structure YonedaEquiv {C : TyCat} (A : C.Obj) (F : Functor C SetCat.{0}) where
  toFun     : NatTrans (homFunctor C A) F → F.obj A
  invFun    : F.obj A → NatTrans (homFunctor C A) F
  left_inv  : ∀ η, invFun (toFun η) = η
  right_inv : ∀ x, toFun (invFun x) = x

/-- **米田引理** —— 主结果：双射成立。 -/
def yonedaEquiv (C : TyCat) (A : C.Obj) (F : Functor C SetCat.{0}) :
    YonedaEquiv A F where
  toFun     := yonedaForward
  invFun    := yonedaBackward
  left_inv  := yonedaBackward_forward
  right_inv := yonedaForward_backward

/-- **米田嵌入之忠实性推论** —— 表示函子相等（`obj` 与 `map` 同构）
    意味着自然变换 → 元素之双射成立。此处给一弱形式：
    `homFunctor C A` 与某 `F` 之间任一自然变换由其在 `(A, 𝟙 A)` 上之值
    完全决定。 -/
theorem yoneda_faithful {C : TyCat} {A : C.Obj}
    {F : Functor C SetCat.{0}} (η₁ η₂ : NatTrans (homFunctor C A) F)
    (h : yonedaForward η₁ = yonedaForward η₂) : η₁ = η₂ := by
  -- 由 round-trip 2：η_i = yonedaBackward (yonedaForward η_i)。
  rw [← yonedaBackward_forward η₁, ← yonedaBackward_forward η₂, h]

/-- **米田嵌入之满性推论** —— 任意 `x : F.obj A` 都被某个自然变换"击中"。 -/
theorem yoneda_full {C : TyCat} {A : C.Obj}
    {F : Functor C SetCat.{0}} (x : F.obj A) :
    ∃ η : NatTrans (homFunctor C A) F, yonedaForward η = x :=
  ⟨yonedaBackward x, yonedaForward_backward x⟩

/-! ## § 6 BaguaCat1 上之米田 vacuous 实例

`BaguaCat1` 是 indiscrete (Hom = Unit)，故 `homFunctor BaguaCat1 (heaven-lift)` 之
obj 处处为 `Unit`。任意 `F : Functor BaguaCat1 SetCat.{0}` 之米田双射在此变 trivial。
-/

/-- **BaguaCat1 之 heaven-lift** alias。 -/
abbrev qianLift : BaguaCat1.Obj := ULift.up Trigram.heaven

/-- **常 Unit 函子**：`BaguaCat1 → SetCat.{0}` 之处处 `Unit`、处处恒等之函子。 -/
def constUnitFunctor : Functor BaguaCat1 SetCat.{0} where
  obj := fun _ => Unit
  map := fun _ => fun u => u
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- **BaguaCat1 上 homFunctor 与 constUnitFunctor 之 obj 等同**。 -/
theorem homFunctor_bagua_obj_eq (X : BaguaCat1.Obj) :
    (homFunctor BaguaCat1 qianLift).obj X = constUnitFunctor.obj X := rfl

/-- **米田 vacuous 实例**：`yonedaForward` 在 `constUnitFunctor` 上击中 `()`。 -/
theorem yoneda_bagua_forward
    (η : NatTrans (homFunctor BaguaCat1 qianLift) constUnitFunctor) :
    yonedaForward η = () := by
  -- F.obj qianLift = Unit；唯一元素 = ()
  cases yonedaForward η
  rfl

/-- **米田 vacuous 实例 · 反向**：`yonedaBackward ()` 之 component 处处为 `id : Unit → Unit`。 -/
theorem yoneda_bagua_backward_app (X : BaguaCat1.Obj) (f : BaguaCat1.Hom qianLift X) :
    (yonedaBackward (F := constUnitFunctor) (A := qianLift) ()).app X f = () := by
  -- 解开：yonedaBackward () = ⟨fun B f => F.map f (), _⟩
  -- F = constUnitFunctor；F.map f () = ()
  rfl

/-- **BaguaCat1 上米田双射 anchor**。 -/
def yonedaEquivBagua : YonedaEquiv qianLift constUnitFunctor :=
  yonedaEquiv BaguaCat1 qianLift constUnitFunctor

/-! ## § 7 公开摘要 -/

/-- **YonedaFull 总摘要**：
    (1) `yonedaForward` 与 `yonedaBackward` 互逆（米田引理之核心双射）
    (2) `yoneda_faithful`：自然变换由 `(A, 𝟙 A)` 上之值唯一决定
    (3) `yoneda_full`：每个 `F.obj A` 元素被某自然变换击中
    (4) `yonedaEquiv`：米田双射作 data
    (5) BaguaCat1 上 vacuous 实例：常 Unit 函子之 forward 必返 `()`
    (6) BaguaCat1 上 vacuous 实例：backward `()` 之 component 处处返 `()` -/
theorem yonedaFull_summary :
    -- (1a) round-trip 1
    (∀ {C : TyCat} {A : C.Obj} {F : Functor C SetCat.{0}} (x : F.obj A),
        yonedaForward (yonedaBackward (A := A) (F := F) x) = x)
    -- (1b) round-trip 2
    ∧ (∀ {C : TyCat} {A : C.Obj} {F : Functor C SetCat.{0}}
          (η : NatTrans (homFunctor C A) F),
        yonedaBackward (yonedaForward η) = η)
    -- (2) faithful
    ∧ (∀ {C : TyCat} {A : C.Obj} {F : Functor C SetCat.{0}}
          (η₁ η₂ : NatTrans (homFunctor C A) F),
        yonedaForward η₁ = yonedaForward η₂ → η₁ = η₂)
    -- (3) full / surjective
    ∧ (∀ {C : TyCat} {A : C.Obj} {F : Functor C SetCat.{0}} (x : F.obj A),
        ∃ η : NatTrans (homFunctor C A) F, yonedaForward η = x)
    -- (4) yonedaEquiv data well-typed: invFun ∘ toFun = id 在 BaguaCat1 上
    ∧ ((yonedaEquivBagua.invFun (yonedaEquivBagua.toFun
          (yonedaBackward (F := constUnitFunctor) (A := qianLift) ())))
        = yonedaBackward (F := constUnitFunctor) (A := qianLift) ())
    -- (5) bagua vacuous forward
    ∧ (∀ (η : NatTrans (homFunctor BaguaCat1 qianLift) constUnitFunctor),
        yonedaForward η = ())
    -- (6) bagua vacuous backward component
    ∧ (∀ (X : BaguaCat1.Obj) (f : BaguaCat1.Hom qianLift X),
        (yonedaBackward (F := constUnitFunctor) (A := qianLift) ()).app X f = ()) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C A F x; exact yonedaForward_backward x
  · intro C A F η; exact yonedaBackward_forward η
  · intro C A F η₁ η₂ h; exact yoneda_faithful η₁ η₂ h
  · intro C A F x; exact yoneda_full x
  · exact yonedaEquivBagua.left_inv _
  · intro η; exact yoneda_bagua_forward η
  · intro X f; exact yoneda_bagua_backward_app X f

end SSBX.Foundation.Modern.YonedaFull
