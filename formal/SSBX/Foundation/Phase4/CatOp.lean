/-
# CatOp —— 反范畴 / 函子范畴 / 米田嵌入作函子（Phase 4 续之续之续）

Companion: `四级生成_太极两翼四象八卦/类与映 · 从元到映.md` § 反范畴与函子范畴

`Phase4/YonedaFull.lean` 已给米田引理之核心双射 `NatTrans (Hom(A, -)) F ≃ F.obj A`，
然此为**单点 A 之断言**；米田**嵌入**之"道"在于其作为函子

  `y : C^op → [C, Set]`,    `A ↦ Hom(A, -)`,    `f ↦ (precomp by f)`

**整体**之 functoriality（map_id / map_comp）随 A 变化之自然性。本文补足之：
  § 1   `Cat.op` 反范畴 + `Cat.op_op` 自反 + `Functor.op` 反变变协变
  § 2   `FunctorCat` 函子范畴（NatTrans 之纵向复合 + 单位 + 三律）
  § 3   `yonedaEmbed` 米田嵌入作函子 `Cat.op C → FunctorCat C SetCat`
  § 4   米田嵌入之忠实性
  § 5   公开摘要

## 道理二分立场
`LeiYing` 之 `Cat.{u, v}` 要求 `C, D : Cat.{u, v}` 同 universe 方可 form
`Functor C D`。`FunctorCat C D` 之 `Obj = Functor C D : Type max u v`、
`Hom = NatTrans : Type max u v`，故 `FunctorCat C D : Cat.{max u v, max u v}`。
为使 `Cat.op C` 与之同 universe，需 ULift `Cat.op C` 之 `Hom` 至 `Type max u v`。
此即 `Cat.opLift1`：在 `TyCat = Cat.{1, 0}` 之 specialization 下，将 `Hom : Type 0`
ULift 至 `Type 1`，使 source / target 双方共住 `Cat.{1, 1}`。

universe 处理：与 `CatExt` § 6 / `YonedaFull` 一致，固定 base 在 `TyCat`，
然 yoneda 嵌入之 ambient 范畴在 `Cat.{1, 1}`。全文 0 sorry / 0 axiom。
-/
import SSBX.Foundation.Phase4.YonedaFull

namespace SSBX.Foundation.Phase4.CatOp

open SSBX.Foundation.Eight.LeiYing
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Phase4.CatExt
open SSBX.Foundation.Phase4.YonedaFull

universe u v

/-! ## § 1 反范畴 Cat.op

反范畴 `C^op` 之 obj 同 `C`，但 hom 反向：`(C^op).Hom A B := C.Hom B A`，
复合顺序亦反：`(C^op).comp f g := C.comp g f`。三律由 `C` 之三律对偶得出。 -/

/-- **反范畴** `C^op`：对象不变，态射方向反，复合顺序反。 -/
def Cat.op (C : Cat.{u, v}) : Cat.{u, v} where
  Obj      := C.Obj
  Hom A B  := C.Hom B A
  id X     := C.id X
  comp f g := C.comp g f
  id_left  := fun f => C.id_right f
  id_right := fun f => C.id_left f
  assoc    := fun f g h => (C.assoc h g f).symm

/-- **反范畴自反**：`(C^op)^op = C`（在 LeiYing 之结构层 rfl）。 -/
theorem Cat.op_op (C : Cat.{u, v}) : Cat.op (Cat.op C) = C := rfl

/-- **反范畴之 obj 不变**。 -/
theorem Cat.op_obj (C : Cat.{u, v}) : (Cat.op C).Obj = C.Obj := rfl

/-- **反范畴之 hom 反向**。 -/
theorem Cat.op_hom (C : Cat.{u, v}) (A B : C.Obj) :
    (Cat.op C).Hom A B = C.Hom B A := rfl

/-- **反范畴之 id 同源**。 -/
theorem Cat.op_id (C : Cat.{u, v}) (X : C.Obj) :
    (Cat.op C).id X = C.id X := rfl

/-- **反范畴之复合反序**。 -/
theorem Cat.op_comp (C : Cat.{u, v}) {X Y Z : C.Obj}
    (f : (Cat.op C).Hom X Y) (g : (Cat.op C).Hom Y Z) :
    (Cat.op C).comp f g = C.comp g f := rfl

/-- **函子之反变** `F.op : C^op → D^op`：obj 不变，map 同 `F.map` 但 hom 方向反转
    自动适配（因 `(C^op).Hom A B = C.Hom B A`）。 -/
def Functor.op {C D : Cat.{u, v}} (F : Functor C D) :
    Functor (Cat.op C) (Cat.op D) where
  obj      := F.obj
  map      := fun {X Y} f => F.map (X := Y) (Y := X) f
  map_id   := fun X => F.map_id X
  map_comp := fun {X Y Z} f g => F.map_comp (X := Z) (Y := Y) (Z := X) g f

/-- **恒等函子之 op = 恒等函子**。 -/
theorem Functor.op_idFunctor (C : Cat.{u, v}) :
    Functor.op (idFunctor C) = idFunctor (Cat.op C) := rfl

/-- **BaguaCat 之反范畴**：仍 indiscrete on Trigram（Hom = Unit 自对偶）。 -/
def BaguaCatOp : Cat.{0, 0} := Cat.op BaguaCat

/-- **BaguaCat^op 之 hom = Unit**（indiscrete 性自对偶）。 -/
theorem baguaCatOp_hom_unit (X Y : BaguaCatOp.Obj) :
    BaguaCatOp.Hom X Y = Unit := rfl

/-- **BaguaCat^op 之对象数 = 8**。 -/
theorem baguaCatOp_obj_card : Trigram.all.length = 8 := by decide

/-! ## § 2 函子范畴 FunctorCat

`FunctorCat C D` 之 obj = `Functor C D`，hom = `NatTrans F G`。
需补 NatTrans 之**纵向复合** `vcomp σ τ`（pointwise `D.comp`）：
  `(σ ⋙ τ).app X = D.comp (σ.app X) (τ.app X)`。
其自然性方块由 `D.assoc` 与 `σ`、`τ` 各自之 naturality 拼接而成。 -/

/-- **NatTrans 纵向复合**：`σ : F ⇒ G`, `τ : G ⇒ H` ⇒ `σ ⋙ τ : F ⇒ H`。 -/
def NatTrans.vcomp {C D : Cat.{u, v}} {F G H : Functor C D}
    (σ : NatTrans F G) (τ : NatTrans G H) : NatTrans F H where
  app := fun X => D.comp (σ.app X) (τ.app X)
  naturality := fun {X Y} f => by
    -- 目标：D.comp (F.map f) (D.comp (σ.app Y) (τ.app Y))
    --     = D.comp (D.comp (σ.app X) (τ.app X)) (H.map f)
    -- 借 assoc 重组，再代入 σ、τ 之 naturality。
    have hστ_assoc1 :
        D.comp (F.map f) (D.comp (σ.app Y) (τ.app Y))
          = D.comp (D.comp (F.map f) (σ.app Y)) (τ.app Y) :=
      (D.assoc (F.map f) (σ.app Y) (τ.app Y)).symm
    have hσnat : D.comp (F.map f) (σ.app Y) = D.comp (σ.app X) (G.map f) :=
      σ.naturality f
    have hτnat : D.comp (G.map f) (τ.app Y) = D.comp (τ.app X) (H.map f) :=
      τ.naturality f
    rw [hστ_assoc1, hσnat, D.assoc, hτnat, ← D.assoc]

/-- **NatTrans 纵向复合 · 左单位律**：`idNat F ⋙ σ = σ`。 -/
theorem NatTrans.vcomp_idNat_left {C D : Cat.{u, v}} {F G : Functor C D}
    (σ : NatTrans F G) :
    NatTrans.vcomp (idNat F) σ = σ := by
  apply natTrans_ext
  intro X
  show D.comp (D.id (F.obj X)) (σ.app X) = σ.app X
  exact D.id_left (σ.app X)

/-- **NatTrans 纵向复合 · 右单位律**：`σ ⋙ idNat G = σ`。 -/
theorem NatTrans.vcomp_idNat_right {C D : Cat.{u, v}} {F G : Functor C D}
    (σ : NatTrans F G) :
    NatTrans.vcomp σ (idNat G) = σ := by
  apply natTrans_ext
  intro X
  show D.comp (σ.app X) (D.id (G.obj X)) = σ.app X
  exact D.id_right (σ.app X)

/-- **NatTrans 纵向复合 · 结合律**。 -/
theorem NatTrans.vcomp_assoc {C D : Cat.{u, v}}
    {F G H K : Functor C D}
    (σ : NatTrans F G) (τ : NatTrans G H) (ρ : NatTrans H K) :
    NatTrans.vcomp (NatTrans.vcomp σ τ) ρ
      = NatTrans.vcomp σ (NatTrans.vcomp τ ρ) := by
  apply natTrans_ext
  intro X
  show D.comp (D.comp (σ.app X) (τ.app X)) (ρ.app X)
       = D.comp (σ.app X) (D.comp (τ.app X) (ρ.app X))
  exact D.assoc (σ.app X) (τ.app X) (ρ.app X)

/-- **函子范畴** `[C, D]`：obj = Functor C D，hom = NatTrans，复合 = vcomp。
    universe：`Functor C D : Type max u v`，`NatTrans : Type max u v`，
    故 `FunctorCat C D : Cat.{max u v, max u v}`。 -/
def FunctorCat (C D : Cat.{u, v}) : Cat.{max u v, max u v} where
  Obj      := Functor C D
  Hom F G  := NatTrans F G
  id F     := idNat F
  comp σ τ := NatTrans.vcomp σ τ
  id_left  := NatTrans.vcomp_idNat_left
  id_right := NatTrans.vcomp_idNat_right
  assoc    := NatTrans.vcomp_assoc

/-- **FunctorCat 之 obj 即 Functor**。 -/
theorem FunctorCat_obj (C D : Cat.{u, v}) :
    (FunctorCat C D).Obj = Functor C D := rfl

/-- **FunctorCat 之 hom 即 NatTrans**。 -/
theorem FunctorCat_hom (C D : Cat.{u, v}) (F G : Functor C D) :
    (FunctorCat C D).Hom F G = NatTrans F G := rfl

/-- **FunctorCat 之 id = idNat**。 -/
theorem FunctorCat_id (C D : Cat.{u, v}) (F : Functor C D) :
    (FunctorCat C D).id F = idNat F := rfl

/-! ## § 3 米田嵌入作函子 yonedaEmbed

源 `Cat.op C` 在 `Cat.{u, v}`；目标 `FunctorCat C SetCat` 在 `Cat.{max u v, max u v}`。
LeiYing 之 `Functor` 要求两端共享 universes。为弥合此 gap，在 `TyCat = Cat.{1, 0}`
specialization 之上构造 `Cat.opLift1`：将 `Cat.op C` 之 hom 由 `Type 0` ULift 至 `Type 1`，
得 `Cat.{1, 1}` 范畴。同 universe `(1, 1)` 与 `FunctorCat C SetCat.{0}`。 -/

/-- **TyCat 上之 op 升 hom universe** `Cat.opLift1`：
    `Obj = C.Obj`，`Hom A B = ULift (C.Hom B A)`。 -/
def Cat.opLift1 (C : TyCat) : Cat.{1, 1} where
  Obj      := C.Obj
  Hom A B  := ULift (C.Hom B A)
  id X     := ⟨C.id X⟩
  comp f g := ⟨C.comp g.down f.down⟩
  id_left  := fun {X Y} f => by
    cases f
    show ULift.up (C.comp _ _) = _
    rw [C.id_right]
  id_right := fun {X Y} f => by
    cases f
    show ULift.up (C.comp _ _) = _
    rw [C.id_left]
  assoc    := fun {W X Y Z} f g h => by
    cases f; cases g; cases h
    show ULift.up _ = ULift.up _
    congr 1
    exact (C.assoc _ _ _).symm

/-- **米田嵌入之 obj 部分**：`A ↦ homFunctor C A`。 -/
def yonedaEmbedObj (C : TyCat) (A : (Cat.opLift1 C).Obj) :
    (FunctorCat C SetCat.{0}).Obj :=
  homFunctor C A

/-- **米田嵌入之 map 部分 · component**：给 `f : Hom_{C^op}(A, B) = C.Hom B A`，
    构造 `homFunctor C A ⇒ homFunctor C B` 之 component：
    在 `X` 处，`g : C.Hom A X ↦ C.comp f g : C.Hom B X`（precomposition）。 -/
def yonedaEmbedMapApp {C : TyCat} {A B : (Cat.opLift1 C).Obj}
    (f : (Cat.opLift1 C).Hom A B) (X : C.Obj) :
    SetCat.{0}.Hom ((homFunctor C A).obj X) ((homFunctor C B).obj X) :=
  fun (g : C.Hom A X) => C.comp f.down g

/-- **米田嵌入之 map 部分**：自然变换 `homFunctor C A ⇒ homFunctor C B`。
    自然性方块：`(precomp f) ∘ post g = post g ∘ (precomp f)`，
    即 `C.comp f (C.comp h g) = C.comp (C.comp f h) g`，由 `C.assoc` 得。 -/
def yonedaEmbedMap {C : TyCat} {A B : (Cat.opLift1 C).Obj}
    (f : (Cat.opLift1 C).Hom A B) :
    NatTrans (homFunctor C A) (homFunctor C B) where
  app := yonedaEmbedMapApp f
  naturality := fun {X Y} h => by
    -- 目标：SetCat.comp ((homFunctor C A).map h) (yonedaEmbedMapApp f Y)
    --     = SetCat.comp (yonedaEmbedMapApp f X) ((homFunctor C B).map h)
    -- 即 (fun g => C.comp f (C.comp g h)) = (fun g => C.comp (C.comp f g) h)
    funext (g : C.Hom A X)
    show C.comp f.down (C.comp g h) = C.comp (C.comp f.down g) h
    exact (C.assoc f.down g h).symm

/-- **米田嵌入** `y : (Cat.opLift1 C) → FunctorCat C SetCat`：
    `A ↦ homFunctor C A`，`f ↦ precomp by f`。 -/
def yonedaEmbed (C : TyCat) :
    Functor (Cat.opLift1 C) (FunctorCat C SetCat.{0}) where
  obj := yonedaEmbedObj C
  map := fun {A B} f => yonedaEmbedMap f
  map_id := fun A => by
    -- 目标：yonedaEmbedMap (id A) = idNat (homFunctor C A)
    -- (id A).down = C.id A
    -- yonedaEmbedMap (id A).app X g = C.comp (C.id A) g = g
    -- idNat (homFunctor C A).app X g = SetCat.id _ g = g
    apply natTrans_ext
    intro X
    funext g
    show C.comp (C.id A) g = g
    exact C.id_left g
  map_comp := fun {A B C'} f g => by
    -- 目标：yonedaEmbedMap (comp f g) = vcomp (yonedaEmbedMap f) (yonedaEmbedMap g)
    -- (comp f g).down = C.comp g.down f.down
    -- LHS.app X h = C.comp (C.comp g.down f.down) h
    -- RHS.app X h = SetCat.comp (yonedaEmbedMap f).app (yonedaEmbedMap g).app X h
    --            = (yonedaEmbedMap g).app X ((yonedaEmbedMap f).app X h)
    --            = C.comp g.down (C.comp f.down h)
    apply natTrans_ext
    intro X
    funext h
    show C.comp (C.comp g.down f.down) h = C.comp g.down (C.comp f.down h)
    exact C.assoc g.down f.down h

/-- **米田嵌入之 obj 求值**：`yonedaEmbed C` 在 `A` 上 = `homFunctor C A`。 -/
theorem yonedaEmbed_obj (C : TyCat) (A : C.Obj) :
    (yonedaEmbed C).obj A = homFunctor C A := rfl

/-- **米田嵌入之 map component 求值** —— `precomposition by f.down`。 -/
theorem yonedaEmbed_map_app {C : TyCat} {A B : C.Obj}
    (f : (Cat.opLift1 C).Hom A B) (X : C.Obj) (g : C.Hom A X) :
    ((yonedaEmbed C).map f).app X g = C.comp f.down g := rfl

/-! ## § 4 米田嵌入之忠实性

源态射 `f, g : Hom_{C^op}(A, B) = C.Hom B A` 之 down 不同 ⇒ `yonedaEmbed.map` 不同：
两态射 `f.down ≠ g.down` 时，在 `X = A` 取 `h = C.id A`，`(yonedaEmbed.map f).app A (C.id A)
= C.comp f.down (C.id A) = f.down`，类似 `g`，故二者 component 相异。
此即 `yoneda_faithful` 在嵌入层之化身。 -/

/-- **米田嵌入忠实** —— `yonedaEmbed C` 上之 `map` 单射：`map f = map g → f = g`。
    证：在 `(A, C.id A)` 处取 component 之求值。 -/
theorem yonedaEmbed_faithful (C : TyCat) {A B : (Cat.opLift1 C).Obj}
    (f g : (Cat.opLift1 C).Hom A B)
    (h : (yonedaEmbed C).map f = (yonedaEmbed C).map g) : f = g := by
  -- 由 h 取 app A 之 component，再取 (C.id A) 之 value：
  have happ : ((yonedaEmbed C).map f).app A = ((yonedaEmbed C).map g).app A := by
    rw [h]
  have hpt : ((yonedaEmbed C).map f).app A (C.id A)
              = ((yonedaEmbed C).map g).app A (C.id A) := by
    rw [happ]
  -- LHS = C.comp f.down (C.id A) = f.down
  -- RHS = C.comp g.down (C.id A) = g.down
  have hLHS : ((yonedaEmbed C).map f).app A (C.id A) = f.down := by
    show C.comp f.down (C.id A) = f.down
    exact C.id_right f.down
  have hRHS : ((yonedaEmbed C).map g).app A (C.id A) = g.down := by
    show C.comp g.down (C.id A) = g.down
    exact C.id_right g.down
  -- 故 f.down = g.down，二 ULift 同 down 即等
  have hdown : f.down = g.down := by
    rw [← hLHS, ← hRHS]; exact hpt
  cases f
  cases g
  congr

/-- **米田嵌入忠实 · 反演形式** —— `f ≠ g → map f ≠ map g`。 -/
theorem yonedaEmbed_map_injective (C : TyCat) {A B : (Cat.opLift1 C).Obj}
    (f g : (Cat.opLift1 C).Hom A B) (h : f ≠ g) :
    (yonedaEmbed C).map f ≠ (yonedaEmbed C).map g := by
  intro heq
  exact h (yonedaEmbed_faithful C f g heq)

/-! ## § 4.5 BaguaCat1 上之米田嵌入 vacuous 实例

`BaguaCat1` 之 hom = Unit，故 `Cat.opLift1 BaguaCat1` 之 hom = ULift Unit；
任意 `f : ULift Unit` 之 down = ()，米田嵌入之 map component 处处为 `(C.comp () _)`。 -/

/-- **BaguaCat1 上之米田嵌入实例**。 -/
def yonedaEmbedBagua : Functor (Cat.opLift1 BaguaCat1) (FunctorCat BaguaCat1 SetCat.{0}) :=
  yonedaEmbed BaguaCat1

/-- **BaguaCat1 之米田嵌入 obj 在 qianLift 处** = `homFunctor BaguaCat1 qianLift`。 -/
theorem yonedaEmbedBagua_obj :
    yonedaEmbedBagua.obj qianLift = homFunctor BaguaCat1 qianLift := rfl

/-- **BaguaCat1 上 op-lifted hom 必平凡**：所有 `f : (Cat.opLift1 BaguaCat1).Hom A B` 相等。 -/
theorem opLift1_bagua_hom_unique
    (A B : (Cat.opLift1 BaguaCat1).Obj)
    (f g : (Cat.opLift1 BaguaCat1).Hom A B) : f = g := by
  cases f with
  | up f' => cases g with
    | up g' => cases f'; cases g'; rfl

/-! ## § 5 公开摘要

汇总六大事实：
  (1) `Cat.op` 良定义 + 自反 `op_op`
  (2) `Functor.op` 良定义（反变变协变于 op 端）
  (3) `FunctorCat` 良定义 + obj/hom 求值正确
  (4) `NatTrans.vcomp` 满足三律
  (5) `yonedaEmbed` 是 Functor（functoriality 验证）
  (6) `yonedaEmbed` 忠实
-/

/-- **CatOp 总摘要**：
    (1) `Cat.op_op C = C`
    (2) `Cat.op` 之 hom 反向：`(Cat.op C).Hom A B = C.Hom B A`
    (3) `Functor.op (idFunctor C) = idFunctor (Cat.op C)`
    (4) `FunctorCat C D` 之 obj = Functor C D
    (5) `NatTrans.vcomp` 单位律 + 结合律
    (6) `yonedaEmbed C` 之 obj A = `homFunctor C A`
    (7) `yonedaEmbed C` 之 map component 在 X 上 = precomposition
    (8) `yonedaEmbed` 忠实：`map f = map g → f = g`
    (9) BaguaCat1 之 op-lift hom 必相等（vacuous 见证） -/
theorem catOp_summary :
    -- (1) op 自反
    (∀ (C : Cat.{0, 0}), Cat.op (Cat.op C) = C)
    -- (2) op hom 反向
    ∧ (∀ (C : Cat.{0, 0}) (A B : C.Obj),
        (Cat.op C).Hom A B = C.Hom B A)
    -- (3) Functor.op 恒等
    ∧ (∀ (C : Cat.{0, 0}),
        Functor.op (idFunctor C) = idFunctor (Cat.op C))
    -- (4) FunctorCat obj
    ∧ ((FunctorCat BaguaCat1 SetCat.{0}).Obj = Functor BaguaCat1 SetCat.{0})
    -- (5a) vcomp 左单位
    ∧ (∀ {C D : Cat.{0, 0}} {F G : Functor C D} (σ : NatTrans F G),
        NatTrans.vcomp (idNat F) σ = σ)
    -- (5b) vcomp 右单位
    ∧ (∀ {C D : Cat.{0, 0}} {F G : Functor C D} (σ : NatTrans F G),
        NatTrans.vcomp σ (idNat G) = σ)
    -- (5c) vcomp 结合
    ∧ (∀ {C D : Cat.{0, 0}} {F G H K : Functor C D}
          (σ : NatTrans F G) (τ : NatTrans G H) (ρ : NatTrans H K),
        NatTrans.vcomp (NatTrans.vcomp σ τ) ρ
          = NatTrans.vcomp σ (NatTrans.vcomp τ ρ))
    -- (6) yonedaEmbed obj
    ∧ (∀ (C : TyCat) (A : C.Obj),
        (yonedaEmbed C).obj A = homFunctor C A)
    -- (7) yonedaEmbed map component
    ∧ (∀ (C : TyCat) {A B : C.Obj}
          (f : (Cat.opLift1 C).Hom A B) (X : C.Obj) (g : C.Hom A X),
        ((yonedaEmbed C).map f).app X g = C.comp f.down g)
    -- (8) yonedaEmbed faithful
    ∧ (∀ (C : TyCat) {A B : (Cat.opLift1 C).Obj}
          (f g : (Cat.opLift1 C).Hom A B),
        (yonedaEmbed C).map f = (yonedaEmbed C).map g → f = g)
    -- (9) Bagua op-lift vacuous
    ∧ (∀ (A B : (Cat.opLift1 BaguaCat1).Obj)
          (f g : (Cat.opLift1 BaguaCat1).Hom A B), f = g) := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C; exact Cat.op_op C
  · intro C A B; rfl
  · intro C; rfl
  · intro C D F G σ; exact NatTrans.vcomp_idNat_left σ
  · intro C D F G σ; exact NatTrans.vcomp_idNat_right σ
  · intro C D F G H K σ τ ρ; exact NatTrans.vcomp_assoc σ τ ρ
  · intro C A; rfl
  · intro C A B f X g; rfl
  · intro C A B f g h; exact yonedaEmbed_faithful C f g h
  · intro A B f g; exact opLift1_bagua_hom_unique A B f g

end SSBX.Foundation.Phase4.CatOp
