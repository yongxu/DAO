/-
# CatExt — 类映续 · monoidal / Yoneda / curry-uncurry / Monad / CCC anchor (Phase 4 续)

Companion: `四级生成_太极两翼四象八卦/类与映 · 从元到映.md` § 续篇

`Eight/LeiYing.lean` 已给 Cat / Functor / NatTrans / Adjunction skeleton +
SetCat / BaguaCat / HexagramCat / TrivialCat 之最薄骨架。本文延伸：
  § 1   Curry / Uncurry adjunction（concrete adjunction · 双射）
  § 2   Cartesian Closed Category (CCC) anchor + SetCat 是 CCC
  § 3   Monad on a Cat（endofunctor + unit + mult + 三律）
  § 4   Identity Monad（任意 C 之恒等单子）
  § 5   State Monad on Type（具体单子 · funext 验证三律）
  § 6   Yoneda anchor —— Hom(A, -) : C → SetCat 是函子
  § 7   BaguaCat / HexagramCat 之 CCC vacuous instance
  § 8   公开摘要

## 道理二分立场
LeiYing 之骨架属"理"层之 finite no-Mathlib 范畴论；本文借 Lean stdlib 之
funext / Equiv 升至 concrete adjunction / monad / CCC 之"道"层 anchor。
全文 0 sorry / 0 axiom，universe-polymorphic in spots，Type 0 anchored elsewhere。
-/
import SSBX.Foundation.Eight.LeiYing

namespace SSBX.Foundation.Phase4.CatExt

open SSBX.Foundation.Eight.LeiYing
open SSBX.Foundation.Yi.Yi

universe u v

/-! ## § 1 Curry / Uncurry adjunction

对任意类型 A B C：
  (A × B → C) ≃ (A → B → C)
此双射即 product ⊣ exponential 伴随之 hom-set form 在 Type 上之具体见证。 -/

/-- **curry**：(A × B → C) → (A → B → C)。 -/
def curry {A B C : Type u} (f : A × B → C) : A → B → C :=
  fun a b => f (a, b)

/-- **uncurry**：(A → B → C) → (A × B → C)。 -/
def uncurry {A B C : Type u} (f : A → B → C) : A × B → C :=
  fun p => f p.1 p.2

/-- **curry ∘ uncurry = id**。 -/
theorem curry_uncurry {A B C : Type u} (f : A → B → C) :
    curry (uncurry f) = f := rfl

/-- **uncurry ∘ curry = id**。 -/
theorem uncurry_curry {A B C : Type u} (f : A × B → C) :
    uncurry (curry f) = f := by
  funext p
  cases p
  rfl

/-- **curry/uncurry 双射 anchor**：以二元结构记录之，避免 Mathlib `Equiv` 之依赖。 -/
structure CurryEquiv (A B C : Type u) where
  toFun    : (A × B → C) → (A → B → C)
  invFun   : (A → B → C) → (A × B → C)
  left_inv  : ∀ f, invFun (toFun f) = f
  right_inv : ∀ f, toFun (invFun f) = f

/-- **curry/uncurry 在 Type 上之双射 instance**。 -/
def curryEquiv (A B C : Type u) : CurryEquiv A B C where
  toFun    := curry
  invFun   := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-! ## § 2 Cartesian Closed Category (CCC) anchor

CCC = Cat with terminal + binary products + exponentials。
此处给最薄骨架（不证 universal property 之全部，只 exhibit data）。 -/

/-- **CCC 数据**：终对象 + 积 + 指数（纯数据层）。 -/
structure CCCData (C : Cat.{u, v}) where
  terminal : C.Obj
  prod     : C.Obj → C.Obj → C.Obj
  exp      : C.Obj → C.Obj → C.Obj

/-- **SetCat 是 CCC**：terminal = PUnit，product = ×，exponential = →。 -/
def setCatCCC : CCCData (SetCat.{u}) where
  terminal := PUnit
  prod     := fun A B => A × B
  exp      := fun A B => A → B

/-- **SetCat 之 terminal map**：唯一 A → PUnit。 -/
def setCatTerminalMap (A : Type u) : A → PUnit := fun _ => PUnit.unit

/-- **SetCat 之 terminal map 唯一性**。 -/
theorem setCatTerminalMap_unique (A : Type u) (f g : A → PUnit) : f = g := by
  funext a
  cases f a
  cases g a
  rfl

/-- **SetCat 之 product 投影 fst**。 -/
def setCatFst (A B : Type u) : A × B → A := fun p => p.1

/-- **SetCat 之 product 投影 snd**。 -/
def setCatSnd (A B : Type u) : A × B → B := fun p => p.2

/-- **SetCat 之 product pairing**：⟨f, g⟩ : X → A × B from X → A and X → B。 -/
def setCatPair {X A B : Type u} (f : X → A) (g : X → B) : X → A × B :=
  fun x => (f x, g x)

/-- **fst ∘ ⟨f, g⟩ = f**。 -/
theorem setCatPair_fst {X A B : Type u} (f : X → A) (g : X → B) :
    (fun x => setCatFst A B (setCatPair f g x)) = f := rfl

/-- **snd ∘ ⟨f, g⟩ = g**。 -/
theorem setCatPair_snd {X A B : Type u} (f : X → A) (g : X → B) :
    (fun x => setCatSnd A B (setCatPair f g x)) = g := rfl

/-- **SetCat 之 evaluation map**：(A → B) × A → B。 -/
def setCatEval (A B : Type u) : (A → B) × A → B := fun p => p.1 p.2

/-! ## § 3 Monad on a category

定义：Monad on C = endofunctor T : C → C + η : Id ⟹ T + μ : T∘T ⟹ T + 三律。
三律以 NatTrans component-wise 形式陈述（用 Prop 字段）。 -/

/-- **范畴上之单子** —— endofunctor + unit + mult + 三律。 -/
structure CatMonad (C : Cat.{u, v}) where
  T          : Functor C C
  η          : NatTrans (idFunctor C) T
  μ          : NatTrans (Functor.comp T T) T
  /-- **左单位律** μ ∘ Tη = id_T (对每个 X)。 -/
  left_unit  : ∀ X : C.Obj,
    C.comp (T.map (η.app X)) (μ.app X) = C.id (T.obj X)
  /-- **右单位律** μ ∘ ηT = id_T (对每个 X)。 -/
  right_unit : ∀ X : C.Obj,
    C.comp (η.app (T.obj X)) (μ.app X) = C.id (T.obj X)
  /-- **结合律** μ ∘ Tμ = μ ∘ μT (对每个 X)。 -/
  assoc      : ∀ X : C.Obj,
    C.comp (T.map (μ.app X)) (μ.app X) = C.comp (μ.app (T.obj X)) (μ.app X)

/-! ## § 4 Identity Monad —— 任意 C 上之恒等单子 -/

/-- **恒等单子**：T = Id, η = id, μ = id。三律 trivially 成立。 -/
def idMonad (C : Cat.{u, v}) : CatMonad C where
  T          := idFunctor C
  η          := idNat (idFunctor C)
  μ          := idNat (Functor.comp (idFunctor C) (idFunctor C))
  left_unit  := fun X => by
    -- T.map (η.app X) = (idFunctor C).map (id X) = id X
    -- μ.app X = id X
    -- comp id id = id
    show C.comp (C.id X) (C.id X) = C.id X
    exact C.id_left (C.id X)
  right_unit := fun X => by
    show C.comp (C.id X) (C.id X) = C.id X
    exact C.id_left (C.id X)
  assoc      := fun X => by
    show C.comp (C.id X) (C.id X) = C.comp (C.id X) (C.id X)
    rfl

/-! ## § 5 State Monad on Type —— 具体单子 + funext 验证三律 -/

/-- **状态单子之载体**：State σ α := σ → α × σ。 -/
def State (σ α : Type u) : Type u := σ → α × σ

/-- **State 之 pure**：a ↦ λ s, (a, s)。 -/
def State.pure {σ α : Type u} (a : α) : State σ α :=
  fun s => (a, s)

/-- **State 之 bind**：m >>= k = λ s, let (a, s') := m s; k a s'。 -/
def State.bind {σ α β : Type u} (m : State σ α) (k : α → State σ β) : State σ β :=
  fun s => let p := m s; k p.1 p.2

/-- **State 单子律 · 左单位**：pure a >>= k = k a。 -/
theorem State.pure_bind {σ α β : Type u} (a : α) (k : α → State σ β) :
    State.bind (State.pure (σ := σ) a) k = k a := by
  funext s
  rfl

/-- **State 单子律 · 右单位**：m >>= pure = m。 -/
theorem State.bind_pure {σ α : Type u} (m : State σ α) :
    State.bind m (State.pure (σ := σ)) = m := by
  funext s
  rfl

/-- **State 单子律 · 结合**：(m >>= k) >>= h = m >>= (fun a => k a >>= h)。 -/
theorem State.bind_assoc {σ α β γ : Type u}
    (m : State σ α) (k : α → State σ β) (h : β → State σ γ) :
    State.bind (State.bind m k) h
      = State.bind m (fun a => State.bind (k a) h) := by
  funext s
  rfl

/-- **State 单子之三律 anchor 摘要**。 -/
theorem state_monad_laws (σ α β γ : Type u)
    (a : α) (k : α → State σ β) (m : State σ α) (h : β → State σ γ) :
    State.bind (State.pure (σ := σ) a) k = k a
    ∧ State.bind m (State.pure (σ := σ)) = m
    ∧ State.bind (State.bind m k) h
        = State.bind m (fun a => State.bind (k a) h) :=
  ⟨State.pure_bind a k, State.bind_pure m, State.bind_assoc m k h⟩

/-! ## § 6 Yoneda anchor —— Hom(A, -) : C → SetCat 是函子

完整 Yoneda 引理涉 universe polymorphism 与 NatTrans on `Hom(A, -)`，
此处 anchor only：固定 A : C.Obj，构造 covariant Hom-functor 之 obj/map，
证 functoriality（map_id / map_comp）。

LeiYing 之 `Functor C D` 要求 C, D 共享 universes `(u, v)`。
SetCat.{v} : Cat.{v+1, v}，故 source C 必为 Cat.{v+1, v}。
此处取 v = 0：source = Cat.{1, 0}, target = SetCat.{0} : Cat.{1, 0}。 -/

/-- **同源范畴 alias**：与 SetCat.{0} 同 universe (1, 0) 之 Cat。 -/
abbrev TyCat := Cat.{1, 0}

/-- **协变 Hom 函子** Hom(A, -) : C → SetCat.{0}。
    obj X = C.Hom A X (作为 Type 0 中之集合)；
    map f g = C.comp g f (post-composition)。 -/
def homFunctor (C : TyCat) (A : C.Obj) : Functor C SetCat.{0} where
  obj  := fun X => C.Hom A X
  map  := fun {X Y} f => fun (g : C.Hom A X) => C.comp g f
  map_id := fun X => by
    funext g
    exact C.id_right g
  map_comp := fun {X Y Z} f g => by
    funext h
    show C.comp h (C.comp f g) = C.comp (C.comp h f) g
    exact (C.assoc h f g).symm

/-- **Hom 函子之 obj 求值**：homFunctor C A 在对象 X 上 = C.Hom A X。 -/
theorem homFunctor_obj (C : TyCat) (A X : C.Obj) :
    (homFunctor C A).obj X = C.Hom A X := rfl

/-- **BaguaCat 在 Cat.{1, 0} 上之 lift**（同样 indiscrete on Trigram，
    但 Obj universe 升至 Type 1，便于与 SetCat.{0} 形成 Functor）。 -/
def BaguaCat1 : TyCat where
  Obj      := ULift Trigram
  Hom _ _  := Unit
  id _     := ()
  comp _ _ := ()
  id_left _ := rfl
  id_right _ := rfl
  assoc _ _ _ := rfl

/-- **Hom 函子在 BaguaCat1 上 anchor**：固定 qian-lift，任意对象映为 Unit。 -/
theorem homFunctor_baguaLift_obj (X : ULift Trigram) :
    (homFunctor BaguaCat1 (ULift.up Trigram.qian)).obj X = Unit := rfl

/-! ## § 7 BaguaCat / HexagramCat 之 CCC vacuous instance

由 BaguaCat 是 indiscrete (Hom = Unit)，任意对象皆 terminal / product / exp。
随便挑 qian 作 terminal、prod、exp 即可。 -/

/-- **BaguaCat 之 CCC 数据**：terminal / prod / exp 皆任取（取 qian / 第一参数）。 -/
def baguaCCC : CCCData BaguaCat where
  terminal := Trigram.qian
  prod     := fun X _ => X
  exp      := fun _ Y => Y

/-- **HexagramCat 之 CCC 数据**：取 Hexagram.qian 作 terminal。 -/
def hexagramCCC : CCCData HexagramCat where
  terminal := SSBX.Foundation.Yi.Yi.Hexagram.qian
  prod     := fun X _ => X
  exp      := fun _ Y => Y

/-- **BaguaCat indiscrete 性**：任意 Hom = Unit。 -/
theorem bagua_hom_unit (X Y : BaguaCat.Obj) : BaguaCat.Hom X Y = Unit := rfl

/-- **BaguaCat 任意对象皆 terminal**：唯一态射 X → qian。 -/
theorem bagua_terminal_unique (X : BaguaCat.Obj) (f g : BaguaCat.Hom X qian) : f = g := by
  cases f
  cases g
  rfl

/-! ## § 8 公开摘要 -/

/-- **CatExt 总摘要**：
    (1) curry/uncurry 是 Type 上之双射（curryEquiv）
    (2) SetCat 是 CCC（setCatCCC）
    (3) 任意 Cat 有恒等单子 idMonad
    (4) State σ 满足单子三律
    (5) homFunctor 是函子（functoriality）
    (6) BaguaCat 是 vacuous CCC（baguaCCC）
    (7) BaguaCat indiscrete: 任意 Hom = Unit
    (8) HexagramCat 亦 vacuous CCC（hexagramCCC）
    (9) curry/uncurry 互逆
    (10) State 单子之 pure/bind/assoc 三律 -/
theorem catExt_summary :
    -- (1)(9) curry/uncurry
    (∀ {A B C : Type} (f : A → B → C), curry (uncurry f) = f)
    ∧ (∀ {A B C : Type} (f : A × B → C), uncurry (curry f) = f)
    -- (2) SetCat CCC terminal
    ∧ (setCatCCC.{0}.terminal = PUnit)
    -- (3) idMonad 之 T = idFunctor
    ∧ ((idMonad TrivialCat).T.obj () = ())
    -- (4)(10) State 单子律
    ∧ (∀ {σ α β : Type} (a : α) (k : α → State σ β),
        State.bind (State.pure (σ := σ) a) k = k a)
    ∧ (∀ {σ α : Type} (m : State σ α),
        State.bind m (State.pure (σ := σ)) = m)
    -- (5) homFunctor obj
    ∧ ((homFunctor BaguaCat1 (ULift.up Trigram.qian)).obj
        (ULift.up Trigram.qian) = Unit)
    -- (6) baguaCCC terminal = qian
    ∧ (baguaCCC.terminal = Trigram.qian)
    -- (7) bagua Hom = Unit
    ∧ (BaguaCat.Hom qian qian = Unit)
    -- (8) hexagramCCC terminal
    ∧ (hexagramCCC.terminal = SSBX.Foundation.Yi.Yi.Hexagram.qian) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro A B C f; rfl
  · intro A B C f; funext p; cases p; rfl
  · intro σ α β a k; rfl
  · intro σ α m; funext s; rfl

end SSBX.Foundation.Phase4.CatExt
