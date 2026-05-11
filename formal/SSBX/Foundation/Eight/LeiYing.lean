/-
# LeiYing — 类与映 · 范畴 / 函子 / 自然变换 / 伴随之最薄骨架

Companion document: `义理/类与映 · 从元到映.md`

This file gives the **finite, no-Mathlib** core of the **类映** 衍 file:
  § 1   Cat structure（universe-polymorphic，三公理）
  § 2   SetCat instance（universe Type → Type 之集合范畴）
  § 3   TrivialCat（单对象单态射）
  § 4   BaguaCat（indiscrete on Trigram，借 simply transitive 之 Unit 实现）
  § 5   Functor structure
  § 6   恒等函子 / 函子复合
  § 7   NatTrans structure + 恒等 NatTrans
  § 8   Adjunction skeleton（unit / counit）
  § 9   公开摘要

## 道理二分立场
本文件仅依 Lean stdlib + Yi.lean，不引入 Mathlib `CategoryTheory`。
所有结构 0 sorry / 0 axiom；高阶范畴 / Topos / 模型范畴 等 future work。
-/
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.BaguaAlgebra

namespace SSBX.Foundation.Eight.LeiYing

open SSBX.Foundation.Yi.Yi

universe u v

/-! ## § 1 范畴 Cat -/

/-- **范畴**：对象类 + 态射类 + 复合 + 单位 + 三律。Universe-polymorphic。 -/
structure Cat where
  Obj      : Type u
  Hom      : Obj → Obj → Type v
  id       : (X : Obj) → Hom X X
  comp     : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_left  : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  id_right : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  assoc    : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
               comp (comp f g) h = comp f (comp g h)

/-! ## § 2 SetCat —— 类型 + 函数 之范畴 -/

/-- **集合范畴 SetCat.{u}**：对象 = Type u，态射 = 函数。 -/
def SetCat : Cat.{u+1, u} where
  Obj := Type u
  Hom A B := A → B
  id _ := fun a => a
  comp f g := fun a => g (f a)
  id_left _ := rfl
  id_right _ := rfl
  assoc _ _ _ := rfl

/-! ## § 3 TrivialCat —— 单对象单态射之极简范畴 -/

/-- **平凡范畴**：一对象一态射。 -/
def TrivialCat : Cat.{0, 0} where
  Obj := Unit
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  id_left _ := rfl
  id_right _ := rfl
  assoc _ _ _ := rfl

/-! ## § 4 BaguaCat —— 八卦作 indiscrete 范畴

借 (Z/2)³ 之 simply transitive 性：Hom(A,B) 单元（在群作用下唯一 flip 元素 a → b）。
此处用 `Unit` 表示该唯一态射，结构层简洁；与 BaguaAlgebra 之 transform 桥接由 `BaguaAlgebra.transform_correct` 见证。 -/

/-- **八卦范畴**：对象 = 八卦，态射 = Unit（唯一态射，由 (Z/2)³ 单纯传递性）。 -/
def BaguaCat : Cat.{0, 0} where
  Obj := Trigram
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  id_left _ := rfl
  id_right _ := rfl
  assoc _ _ _ := rfl

/-- **八卦范畴穷尽**：对象 = 8 卦。 -/
theorem baguaCat_obj_card : Trigram.all.length = 8 := by decide

/-- **重卦范畴**：对象 = 64 卦。 -/
def HexagramCat : Cat.{0, 0} where
  Obj := Hexagram
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  id_left _ := rfl
  id_right _ := rfl
  assoc _ _ _ := rfl

/-- **重卦范畴穷尽**：对象 = 64 卦。 -/
theorem hexagramCat_obj_card : Hexagram.allHex.length = 64 := by decide

/-! ## § 5 函子 Functor -/

/-- **函子**：跨类之合保 + 元保。 -/
structure Functor (C : Cat.{u, v}) (D : Cat.{u, v}) where
  obj      : C.Obj → D.Obj
  map      : {X Y : C.Obj} → C.Hom X Y → D.Hom (obj X) (obj Y)
  map_id   : ∀ X, map (C.id X) = D.id (obj X)
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
               map (C.comp f g) = D.comp (map f) (map g)

/-! ## § 6 恒等函子 + 函子复合 -/

/-- **恒等函子** Id_C : C → C。 -/
def idFunctor (C : Cat.{u, v}) : Functor C C where
  obj := fun X => X
  map := fun f => f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- **函子复合** F ∘ G。 -/
def Functor.comp {C D E : Cat.{u, v}}
    (F : Functor C D) (G : Functor D E) : Functor C E where
  obj := fun X => G.obj (F.obj X)
  map := fun f => G.map (F.map f)
  map_id := fun X => by rw [F.map_id, G.map_id]
  map_comp := fun f g => by rw [F.map_comp, G.map_comp]

/-! ## § 7 自然变换 NatTrans -/

/-- **自然变换** F ⇒ G：每对象一态射 + 自然性方块。 -/
structure NatTrans {C D : Cat.{u, v}} (F G : Functor C D) where
  app         : (X : C.Obj) → D.Hom (F.obj X) (G.obj X)
  naturality  : ∀ {X Y : C.Obj} (f : C.Hom X Y),
                  D.comp (F.map f) (app Y) = D.comp (app X) (G.map f)

/-- **恒等自然变换** id_F : F ⇒ F。 -/
def idNat {C D : Cat.{u, v}} (F : Functor C D) : NatTrans F F where
  app := fun X => D.id (F.obj X)
  naturality := fun f => by
    rw [D.id_left, D.id_right]

/-! ## § 8 BaguaCat → BaguaCat 之恒等函子 -/

/-- **恒等函子在 BaguaCat 上**之具体实例。 -/
def idBagua : Functor BaguaCat BaguaCat := idFunctor BaguaCat

/-! ## § 9 伴随 Adjunction · skeleton -/

/-- **伴随** F ⊣ G：unit / counit + 两 triangle laws skeleton。
    此处仅记 unit / counit；triangle laws 留 future work。 -/
structure Adjunction {C D : Cat.{u, v}}
    (F : Functor C D) (G : Functor D C) where
  unit    : NatTrans (idFunctor C) (Functor.comp F G)
  counit  : NatTrans (Functor.comp G F) (idFunctor D)

/-- **恒等伴随** Id ⊣ Id（trivial witness）。 -/
def idAdjunction (C : Cat.{u, v}) : Adjunction (idFunctor C) (idFunctor C) where
  unit   := idNat (idFunctor C)
  counit := idNat (idFunctor C)

/-! ## § 10 公开摘要 -/

/-- **类映总摘要**：
    (1) BaguaCat 是 Cat（八卦层 finite category）—— `BaguaCat.id heaven = ()`
    (2) Trigram.all.length = 8（八卦穷尽）
    (3) idFunctor BaguaCat 之 obj on heaven = heaven
    (4) idFunctor BaguaCat ∘ idFunctor BaguaCat 之 obj on heaven = heaven
    (5) Hexagram.allHex.length = 64（重卦穷尽） -/
theorem leiying_summary :
    (BaguaCat.id heaven = ())
    ∧ (Trigram.all.length = 8)
    ∧ ((idFunctor BaguaCat).obj heaven = heaven)
    ∧ ((Functor.comp (idFunctor BaguaCat) (idFunctor BaguaCat)).obj heaven = heaven)
    ∧ (Hexagram.allHex.length = 64) := by
  refine ⟨rfl, ?_, rfl, rfl, ?_⟩
  · decide
  · decide

end SSBX.Foundation.Eight.LeiYing
