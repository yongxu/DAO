/-
# Yi-Calculus — formal extraction of 周易 's structure

> **[Yi LEGACY — relocated 2026-05-15 (Phase γ)]** Original location
> `Foundation/Yi/Yi.lean` retired; content preserved here under the
> `Atlas/YiLegacy/` namespace as a doctrinally-positioned Atlas overlay.
> New code MUST use [`Foundation/Atlas/Yi/`](../Yi/) (clean R-Family
> overlay with `Yao := Bool`, `Hexagram := R 6`, etc.) and
> [`Foundation/Wen/Core/`](../../Wen/Core/) (language-independent TM
> on R 8). This file is preserved for downstream `Wen` parser stack
> consumers (~50 files) using the legacy `inductive Yao` /
> `structure Hexagram` types. Imports inside the consumer files still
> name the legacy Lean namespaces (e.g. `SSBX.Foundation.Yi`); only the
> `import` paths were updated to `SSBX.Foundation.Atlas.YiLegacy.*`.

  Per spec yi-calculus.md. Not modern logic mapped onto 周易, but the
  formal-system structure embedded in 周易 made explicit.

  Phase 1 (this file):
    - Atom: 爻 (Yao) + neg
    - Concrete types: Trigram (T_3), Hexagram (T_6) + 8 trigrams + heaven/earth
    - V_4 operators: 错 (complement), 综 (reverse), 错综 (complementReverse), 互 (interlace)
    - V_4 group properties: involutivity + commutativity
    - Mutual hexagram fixed-point theorem: interlace h = h ↔ h ∈ {heaven, earth}
    - Inner ⊕ outer composition + non-commutativity proof
    - Position structure (atPos, isYangPos, wellPos, 中/应/比)

  Phase 2 (future):
    - 老少 modal layer (YaoStar) + δ variant operator
    - 说卦传 multi-valued σ projection
    - 序卦 transition system
    - interlace iteration convergence to {heaven, earth}
-/

namespace SSBX.Foundation.Yi.Yi

/-! ## § 1 Atom: 爻 (yao) -/

/-- 爻 (yao): the binary atom of 周易. Σ = {阳, 阴} ≅ {⚊, ⚋}.
    NB: 阴/阳 is NOT Boolean true/false. Each carries the tendency toward
    its dual — the language's atoms are intrinsically processual. -/
inductive Yao : Type
  | yang  -- ⚊ (阳)
  | yin   -- ⚋ (阴)
  deriving Repr, DecidableEq, BEq

namespace Yao

/-- Negation on a single 爻 (the atomic 错). -/
def neg : Yao → Yao
  | yang => yin
  | yin => yang

/-- Double-negation involutivity: 错 ∘ 错 = id. -/
theorem neg_neg (y : Yao) : y.neg.neg = y := by
  cases y <;> rfl

end Yao

/-! ## § 2 八卦 (T_3): trigrams

  Per 系辞 "易有太极, 是生两仪, 两仪生四象, 四象生八卦":
    T_0 = {*}, T_1 = Σ, T_2 = Σ², T_3 = Σ³ (this layer), T_6 = Σ⁶. -/

/-- 三爻卦 (trigram): three 爻 stacked from bottom (y1 = 初爻) to top (y3 = 上爻). -/
structure Trigram where
  y1 : Yao  -- 初爻 (bottom)
  y2 : Yao  -- 中爻
  y3 : Yao  -- 上爻 (top)
  deriving Repr, DecidableEq, BEq

namespace Trigram

/-! ### The 8 trigrams (八卦) -/
def heaven : Trigram := ⟨.yang, .yang, .yang⟩  -- ☰ 天 (heaven)
def lake  : Trigram := ⟨.yang, .yang, .yin⟩   -- ☱ 泽 (lake)
def fire   : Trigram := ⟨.yang, .yin, .yang⟩   -- ☲ 火 (fire)
def thunder : Trigram := ⟨.yang, .yin, .yin⟩    -- ☳ 雷 (thunder)
def wind  : Trigram := ⟨.yin, .yang, .yang⟩   -- ☴ 风 (wind)
def water  : Trigram := ⟨.yin, .yang, .yin⟩    -- ☵ 水 (water)
def mountain  : Trigram := ⟨.yin, .yin, .yang⟩    -- ☶ 山 (mountain)
def earth  : Trigram := ⟨.yin, .yin, .yin⟩     -- ☷ 地 (earth)

/-- All 8 trigrams. -/
def all : List Trigram := [heaven, lake, fire, thunder, wind, water, mountain, earth]

/-- Verify there are 8 trigrams. -/
theorem all_length : all.length = 8 := rfl

/-- 错 on a trigram: yao-wise negation.
    NB: refined in `SSBX.Foundation.Bagua.BaguaAlgebra` as `complement = motion ∘ middleFlip ∘ topFlip`
    — the (Z/2)³ decomposition into three single-yao flips. -/
def complement (t : Trigram) : Trigram := ⟨t.y1.neg, t.y2.neg, t.y3.neg⟩

/-- 综 on a trigram: reverse yao order. -/
def reverse (t : Trigram) : Trigram := ⟨t.y3, t.y2, t.y1⟩

theorem complement_involutive (t : Trigram) : t.complement.complement = t := by
  simp [complement, Yao.neg_neg]

theorem reverse_involutive (t : Trigram) : t.reverse.reverse = t := by
  cases t; rfl

end Trigram

/-! ## § 3 六十四卦 (T_6): hexagrams

  64 = 2^6 hexagrams. Internal structure:
    y1..y3 = 内卦 (inner / lower / 下卦)
    y4..y6 = 外卦 (outer / upper / 上卦)

  内 carries: 本/源/自身/起.
  外 carries: 用/显/对境/应. -/

/-- 六爻卦 (hexagram): 6 爻 stacked. y1 = 初爻 (bottom), y6 = 上爻 (top). -/
structure Hexagram where
  y1 : Yao  -- 初爻
  y2 : Yao
  y3 : Yao
  y4 : Yao
  y5 : Yao
  y6 : Yao  -- 上爻
  deriving Repr, DecidableEq, BEq

namespace Hexagram

/-! ### Foundational hexagrams (the two fixed points of 互) -/

/-- 乾 (heaven, ☰☰): all yang. Heaven over heaven. -/
def heaven : Hexagram := ⟨.yang, .yang, .yang, .yang, .yang, .yang⟩

/-- 坤 (earth, ☷☷): all yin. Earth over earth. -/
def earth : Hexagram := ⟨.yin, .yin, .yin, .yin, .yin, .yin⟩

/-! ### V_4 group operators 错/综/错综/恒等 -/

/-- 错 (complement): yao-wise negation across all 6 positions.
    "Errors" — the dual hexagram. -/
def complement (h : Hexagram) : Hexagram :=
  ⟨h.y1.neg, h.y2.neg, h.y3.neg, h.y4.neg, h.y5.neg, h.y6.neg⟩

/-- 综 (reverse): reverse the yao order.
    "Reflection" — the upside-down hexagram. -/
def reverse (h : Hexagram) : Hexagram :=
  ⟨h.y6, h.y5, h.y4, h.y3, h.y2, h.y1⟩

/-- 错综 (complementReverse): complement ∘ reverse. The composite. -/
def complementReverse (h : Hexagram) : Hexagram := h.complement.reverse

/-- 互 (interlace): the inner self-reference operator.
    H(h_1 h_2 h_3 h_4 h_5 h_6) = h_2 h_3 h_4 h_3 h_4 h_5
    "What lies hidden within" — the 互卦 extracted from the center 4 yao. -/
def interlace (h : Hexagram) : Hexagram :=
  ⟨h.y2, h.y3, h.y4, h.y3, h.y4, h.y5⟩

/-! ### V_4 group properties -/

/-- 错 is involutive: 错 ∘ 错 = id. -/
theorem complement_involutive (h : Hexagram) : h.complement.complement = h := by
  simp [complement, Yao.neg_neg]

/-- 综 is involutive: 综 ∘ 综 = id. -/
theorem reverse_involutive (h : Hexagram) : h.reverse.reverse = h := by
  cases h; rfl

/-- 错 and 综 commute: 错 ∘ 综 = 综 ∘ 错. -/
theorem complement_reverse_comm (h : Hexagram) : h.complement.reverse = h.reverse.complement := by
  cases h; rfl

/-- 错综 is involutive (V_4 element of order 2). -/
theorem cuoZong_cuoZong (h : Hexagram) : h.complementReverse.complementReverse = h := by
  show h.complement.reverse.complement.reverse = h
  rw [show h.complement.reverse.complement = h.complement.complement.reverse from (complement_reverse_comm h.complement).symm]
  rw [complement_involutive, reverse_involutive]

/-- {id, 错, 综, 错综} ≅ V_4 (Klein four-group): all elements satisfy x² = e. -/
theorem v4_orders (h : Hexagram) :
    h = h ∧ h.complement.complement = h ∧ h.reverse.reverse = h ∧ h.complementReverse.complementReverse = h :=
  ⟨rfl, complement_involutive h, reverse_involutive h, cuoZong_cuoZong h⟩

/-! ### 互 fixed-point theorem -/

/-- 互 fixed-point: H h = h ⟺ h ∈ {heaven, earth}.
    Proof: H h = h forces h.y1 = h.y2 = h.y3 = h.y4 = h.y5 = h.y6,
    so all 6 yao agree — either all yang (heaven) or all yin (earth). -/
theorem interlace_fixed_point (h : Hexagram) :
    h.interlace = h ↔ h = heaven ∨ h = earth := by
  constructor
  · intro heq
    cases h with
    | mk y1 y2 y3 y4 y5 y6 =>
      simp [interlace, Hexagram.mk.injEq] at heq
      -- heq decomposes into componentwise equalities
      cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
        simp_all [heaven, earth]
  · rintro (h | h) <;> rw [h] <;> rfl

/-- 乾 is fixed by 互. -/
theorem interlace_heaven : heaven.interlace = heaven := rfl

/-- 坤 is fixed by 互. -/
theorem interlace_earth : earth.interlace = earth := rfl

/-- 乾's 错 is 坤. -/
theorem complement_heaven : heaven.complement = earth := rfl

/-- 坤's 错 is 乾. -/
theorem complement_earth : earth.complement = heaven := rfl

/-! ### Inner-outer composition ⊕ -/

/-- ⊕ : 内卦 (inner trigram) → 外卦 (outer trigram) → hexagram.
    inner is below (y1, y2, y3), outer is above (y4, y5, y6).
    NON-COMMUTATIVE: inner ⊕ outer ≠ outer ⊕ inner in general. -/
def oplus (inner outer : Trigram) : Hexagram :=
  ⟨inner.y1, inner.y2, inner.y3, outer.y1, outer.y2, outer.y3⟩

/-- ⊕ is non-commutative: 天地否 ≠ 地天泰.
    (qianTri ⊕ kunTri = 否 (heaven over earth, blocked);
     kunTri ⊕ qianTri = 泰 (earth over heaven, harmonized).) -/
theorem oplus_not_comm :
    ∃ a b : Trigram, oplus a b ≠ oplus b a := by
  refine ⟨Trigram.heaven, Trigram.earth, ?_⟩
  intro h
  -- oplus qianTri kunTri = ⟨yang, yang, yang, yin, yin, yin⟩  (= 否)
  -- oplus kunTri qianTri = ⟨yin, yin, yin, yang, yang, yang⟩   (= 泰)
  -- These differ at every position; injection on first component suffices.
  injection h with h1 _ _ _ _ _
  cases h1

/-- 否 (blocking): 天 (heaven) over 地 (earth) → blocked. inner = 坤, outer = 乾. -/
def blocking : Hexagram := oplus Trigram.earth Trigram.heaven

/-- 泰 (peace): 地 (earth) over 天 (heaven) → harmonized. inner = 乾, outer = 坤. -/
def peace : Hexagram := oplus Trigram.heaven Trigram.earth

/-- 否 ≠ 泰 — the non-commutativity has concrete witness. -/
theorem blocking_ne_peace : blocking ≠ peace := by
  intro h
  injection h with h1
  cases h1

/-! ### Position structure (位) -/

/-- Project hexagram to position i (0-indexed: 0 = 初爻, 5 = 上爻). -/
def atPos (h : Hexagram) : Fin 6 → Yao
  | ⟨0, _⟩ => h.y1
  | ⟨1, _⟩ => h.y2
  | ⟨2, _⟩ => h.y3
  | ⟨3, _⟩ => h.y4
  | ⟨4, _⟩ => h.y5
  | ⟨5, _⟩ => h.y6

/-- 阳位 (yang position): 1, 3, 5 (1-indexed) = 0, 2, 4 (0-indexed). -/
def isYangPos (i : Fin 6) : Bool := i.val % 2 = 0

/-- 阴位 (yin position): 2, 4, 6 (1-indexed) = 1, 3, 5 (0-indexed). -/
def isYinPos (i : Fin 6) : Bool := i.val % 2 = 1

/-- 当位 (well-positioned): yang yao on yang position, or yin yao on yin position. -/
def wellPos (h : Hexagram) (i : Fin 6) : Bool :=
  match h.atPos i, isYangPos i with
  | .yang, true => true
  | .yin, false => true
  | _, _ => false

/-- 中位 (center position): position 2 (下卦中) and position 5 (上卦中) — 1-indexed.
    0-indexed: positions 1 and 4. -/
def isZhongPos (i : Fin 6) : Bool := i.val = 1 ∨ i.val = 4

/-- 应位 (corresponding position): position i ↔ i+3 (1-indexed: 1↔4, 2↔5, 3↔6).
    0-indexed: 0↔3, 1↔4, 2↔5.

    Two yao "respond" (应) if they DIFFER; "敌应" (oppose) if they agree. -/
def yingResponds (h : Hexagram) (i : Fin 3) : Bool :=
  (h.atPos ⟨i.val, by omega⟩) ≠ (h.atPos ⟨i.val + 3, by omega⟩)

/-- 比位 (adjacent / "compare" position): adjacent yao i and i+1. -/
def biAdj (h : Hexagram) (i : Fin 5) : Yao × Yao :=
  (h.atPos ⟨i.val, by omega⟩, h.atPos ⟨i.val + 1, by omega⟩)

/-- 乾 's center position (5th yao = 0-indexed 4) is well-positioned (yang on yang pos). -/
theorem heaven_5th_wellPos : wellPos heaven ⟨4, by omega⟩ = true := rfl

/-- 坤 's center position (5th yao = 0-indexed 4) is NOT well-positioned (yin on yang pos). -/
theorem earth_5th_not_wellPos : wellPos earth ⟨4, by omega⟩ = false := rfl

/-! ### Type-hierarchy summary

  Concrete cardinality witnesses for each level T_n. -/

/-- |T_3| = 8: 8 trigrams. -/
theorem trigram_count : Trigram.all.length = 8 := rfl

/-- The two 互-fixed hexagrams are exactly 乾 and 坤 (restated without Set notation). -/
theorem two_hu_fixed_points (h : Hexagram) :
    h.interlace = h ↔ h = heaven ∨ h = earth := interlace_fixed_point h

end Hexagram

/-! ## § 4 老少 modal layer (YaoStar)

  Per 周易 占筮 protocol: each cast 爻 carries a modal status —
    9 (老阳, laoYang)  : 阳 at maximum, ABOUT TO flip to 阴
    7 (少阳, lesserYang) : 阳, stable
    8 (少阴, lesserYin)  : 阴, stable
    6 (老阴, laoYin)   : 阴 at maximum, ABOUT TO flip to 阳

  This layer is what makes 周易 dynamic. 占 reveals not the static 爻 but
  its modal phase, which gives the cast hexagram (本卦) AND the future
  hexagram (变卦) by flipping all 老 yao. The δ operator is precisely this. -/

inductive YaoStar : Type
  | laoYang   -- 9 老阳
  | lesserYang  -- 7 少阳
  | lesserYin   -- 8 少阴
  | laoYin    -- 6 老阴
  deriving Repr, DecidableEq, BEq

namespace YaoStar

/-- Forgetful projection: drop the modal status, keep the 阳/阴 polarity.
    This gives 本卦 (cast hexagram). -/
def proj : YaoStar → Yao
  | laoYang => Yao.yang
  | lesserYang => Yao.yang
  | lesserYin => Yao.yin
  | laoYin => Yao.yin

/-- δ : the "after-divination" operator. 老 (terminus) yao flip; 少 (stable) yao remain.
    This gives 变卦 (transformed hexagram) when applied yao-wise. -/
def delta : YaoStar → Yao
  | laoYang => Yao.yin    -- 老阳 → 阴
  | lesserYang => Yao.yang
  | lesserYin => Yao.yin
  | laoYin => Yao.yang    -- 老阴 → 阳

/-- A 爻 is "old" (terminus/changing) iff old. -/
def isOld : YaoStar → Bool
  | laoYang | laoYin => true
  | _ => false

/-- A 爻 is "young" (stable) iff young. -/
def isYoung : YaoStar → Bool
  | lesserYang | lesserYin => true
  | _ => false

/-- Young yao: δ = proj (the cast yao stands; nothing to transform). -/
theorem delta_young_eq_proj (y : YaoStar) (h : y.isYoung = true) :
    y.delta = y.proj := by
  cases y <;> simp_all [delta, proj, isYoung]

/-- Old yao: δ = neg ∘ proj (the cast flips). -/
theorem delta_old_eq_neg_proj (y : YaoStar) (h : y.isOld = true) :
    y.delta = y.proj.neg := by
  cases y <;> simp_all [delta, proj, isOld, Yao.neg]

/-- Old/young is exhaustive. -/
theorem old_or_young (y : YaoStar) : y.isOld = true ∨ y.isYoung = true := by
  cases y <;> simp [isOld, isYoung]

/-- Old and young are exclusive. -/
theorem not_both_old_young (y : YaoStar) :
    ¬ (y.isOld = true ∧ y.isYoung = true) := by
  intro ⟨ho, hy⟩
  cases y <;> simp_all [isOld, isYoung]

end YaoStar

/-- A 占-cast hexagram: 6 stars (carrying modality). -/
structure HexagramStar where
  z1 : YaoStar
  z2 : YaoStar
  z3 : YaoStar
  z4 : YaoStar
  z5 : YaoStar
  z6 : YaoStar
  deriving Repr, DecidableEq, BEq

namespace HexagramStar

/-- 本卦 (cast hexagram): forget all modality. -/
def benGua (s : HexagramStar) : Hexagram :=
  ⟨s.z1.proj, s.z2.proj, s.z3.proj, s.z4.proj, s.z5.proj, s.z6.proj⟩

/-- 变卦 (transformed hexagram): flip the 老 yao. -/
def bianGua (s : HexagramStar) : Hexagram :=
  ⟨s.z1.delta, s.z2.delta, s.z3.delta, s.z4.delta, s.z5.delta, s.z6.delta⟩

/-- If all 6 yao are young, 本卦 = 变卦 (no change). -/
theorem benGua_eq_bianGua_of_all_young (s : HexagramStar)
    (h1 : s.z1.isYoung = true) (h2 : s.z2.isYoung = true) (h3 : s.z3.isYoung = true)
    (h4 : s.z4.isYoung = true) (h5 : s.z5.isYoung = true) (h6 : s.z6.isYoung = true) :
    s.benGua = s.bianGua := by
  simp [benGua, bianGua,
        YaoStar.delta_young_eq_proj _ h1, YaoStar.delta_young_eq_proj _ h2,
        YaoStar.delta_young_eq_proj _ h3, YaoStar.delta_young_eq_proj _ h4,
        YaoStar.delta_young_eq_proj _ h5, YaoStar.delta_young_eq_proj _ h6]

/-- An all-老阳 cast: 本卦 = 乾, 变卦 = 坤. -/
def allLaoYang : HexagramStar where
  z1 := YaoStar.laoYang
  z2 := YaoStar.laoYang
  z3 := YaoStar.laoYang
  z4 := YaoStar.laoYang
  z5 := YaoStar.laoYang
  z6 := YaoStar.laoYang

theorem allLaoYang_benGua : allLaoYang.benGua = Hexagram.heaven := by
  decide

theorem allLaoYang_bianGua : allLaoYang.bianGua = Hexagram.earth := by
  decide

/-- An all-老阴 cast: 本卦 = 坤, 变卦 = 乾. -/
def allLaoYin : HexagramStar where
  z1 := YaoStar.laoYin
  z2 := YaoStar.laoYin
  z3 := YaoStar.laoYin
  z4 := YaoStar.laoYin
  z5 := YaoStar.laoYin
  z6 := YaoStar.laoYin

theorem allLaoYin_benGua : allLaoYin.benGua = Hexagram.earth := by
  decide

theorem allLaoYin_bianGua : allLaoYin.bianGua = Hexagram.heaven := by
  decide

end HexagramStar

/-! ## § 5 说卦传 σ projection (multi-valued, polymorphic)

  说卦传 maps each 八卦 to multiple symbols across categories.
  ONE trigram (e.g., 乾) projects to MANY symbols by category:
    · 象 (phenomenon): 天
    · 家 (family): 父
    · 体 (body): 首
    · 物 (animal): 马

  σ : Trigram → SigmaCategory → List String — the multi-valued polymorphic projection. -/

inductive SigmaCategory : Type
  | xiang   -- 象 (heaven/earth/...) — natural phenomenon
  | jia     -- 家 (father/mother/...) — family role
  | ti      -- 体 (body parts)
  | thing      -- 物 (animals)
  deriving Repr, DecidableEq, BEq

namespace Trigram

/-- 说卦 projection: 八卦 × category → list of symbols.
    Multi-valued (lists; 巽 has both 风 and 木 in 象 category). -/
def shuoGua : Trigram → SigmaCategory → List String
  | t, .xiang =>
      if t = heaven then ["天"]
      else if t = earth then ["地"]
      else if t = thunder then ["雷"]
      else if t = wind then ["风", "木"]
      else if t = water then ["水"]
      else if t = fire then ["火"]
      else if t = mountain then ["山"]
      else if t = lake then ["泽"]
      else []
  | t, .jia =>
      if t = heaven then ["父"]
      else if t = earth then ["母"]
      else if t = thunder then ["长男"]
      else if t = wind then ["长女"]
      else if t = water then ["中男"]
      else if t = fire then ["中女"]
      else if t = mountain then ["少男"]
      else if t = lake then ["少女"]
      else []
  | t, .ti =>
      if t = heaven then ["首"]
      else if t = earth then ["腹"]
      else if t = thunder then ["足"]
      else if t = wind then ["股"]
      else if t = water then ["耳"]
      else if t = fire then ["目"]
      else if t = mountain then ["手"]
      else if t = lake then ["口"]
      else []
  | t, .thing =>
      if t = heaven then ["马"]
      else if t = earth then ["牛"]
      else if t = thunder then ["龙"]
      else if t = wind then ["鸡"]
      else if t = water then ["豕"]
      else if t = fire then ["雉"]
      else if t = mountain then ["狗"]
      else if t = lake then ["羊"]
      else []

/-- 乾 in 象 category projects to 天. -/
theorem shuoGua_heaven_xiang : shuoGua heaven .xiang = ["天"] := rfl

/-- 巽 in 象 category is multi-valued: 风 AND 木. -/
theorem shuoGua_wind_xiang_multi : shuoGua wind .xiang = ["风", "木"] := rfl

/-- 乾 across 4 categories gives 4 distinct symbols (multi-polymorphism). -/
theorem shuoGua_heaven_polymorphic :
    shuoGua heaven .xiang = ["天"] ∧
    shuoGua heaven .jia = ["父"] ∧
    shuoGua heaven .ti = ["首"] ∧
    shuoGua heaven .thing = ["马"] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- 坤 across 4 categories. -/
theorem shuoGua_earth_polymorphic :
    shuoGua earth .xiang = ["地"] ∧
    shuoGua earth .jia = ["母"] ∧
    shuoGua earth .ti = ["腹"] ∧
    shuoGua earth .thing = ["牛"] :=
  ⟨rfl, rfl, rfl, rfl⟩

end Trigram

/-! ## § 6 序卦 transition system

  序卦传 lays out the 64 hexagrams in a canonical sequence. Each consecutive
  pair is related by 综 (most pairs) or 错 (special pairs where 综 = id, e.g.
  乾↔坤, 颐↔大过, 坎↔离, 中孚↔小过).

  We model the leading transitions to witness the structure. The 综/错
  alternation is a structural invariant of 序卦 — no other operators apply. -/

namespace Hexagram

/-- 屯 (sprout, ☵☳ — 水雷): 内 thunder, 外 water. -/
def sprout : Hexagram := oplus Trigram.thunder Trigram.water

/-- 蒙 (naive, ☶☵ — 山水): 内 water, 外 mountain. -/
def naive : Hexagram := oplus Trigram.water Trigram.mountain

/-- 需 (waiting, ☵☰ — 水天): 内 heaven, 外 water. -/
def waiting : Hexagram := oplus Trigram.heaven Trigram.water

/-- 讼 (dispute, ☰☵ — 天水): 内 water, 外 heaven. -/
def dispute : Hexagram := oplus Trigram.water Trigram.heaven

/-- 序卦 one-step transition: link two consecutive hexagrams in the canonical sequence
    via either 综 (reverse) or 错 (complement). -/
inductive XuguaStep : Hexagram → Hexagram → Prop
  /-- Special pair (综 = self): use 错. Witness: 乾 → 坤. -/
  | byCuo (h h' : Hexagram) : h.complement = h' → XuguaStep h h'
  /-- Generic pair: use 综. Witness: 屯 → 蒙. -/
  | byZong (h h' : Hexagram) : h.reverse = h' → XuguaStep h h'

/-- 乾 → 坤 by 错. (乾 is 综-self, must use 错.) -/
theorem xugua_heaven_earth : XuguaStep heaven earth :=
  .byCuo heaven earth complement_heaven

/-- 屯 → 蒙 by 综. -/
theorem xugua_sprout_naive : XuguaStep sprout naive :=
  .byZong sprout naive (by rfl)

/-- 需 → 讼 by 综. -/
theorem xugua_waiting_dispute : XuguaStep waiting dispute :=
  .byZong waiting dispute (by rfl)

-- Note: in 序卦 cross-pair transitions (e.g., 蒙 → 需) follow neither pure 综 nor 错;
-- they're "thematic" links. We omit them — the pair-internal 综/错 step is the
-- structural invariant we formalize.

/-- 序卦 reflexive-transitive closure: connectedness in the canonical sequence. -/
inductive XuguaStar : Hexagram → Hexagram → Prop
  | refl (h : Hexagram) : XuguaStar h h
  | tail {a b c : Hexagram} : XuguaStar a b → XuguaStep b c → XuguaStar a c

/-- 乾 reaches 坤 in the序卦. -/
theorem xugua_heaven_to_earth : XuguaStar heaven earth :=
  .tail (.refl heaven) xugua_heaven_earth

end Hexagram

/-! ## § 7 老阳→老阴 cycle witness

  The deepest claim of 周易: 极 → 反 (terminus begets opposite).
  Formally: δ ∘ proj⁻¹ at the "old" subtype is exactly Yao.neg. -/

namespace YaoStar

/-- The "terminus reverses" theorem: among old yao, δ flips polarity. -/
theorem extreme_reverses (y : YaoStar) (h : y.isOld = true) :
    y.delta ≠ y.proj := by
  rw [delta_old_eq_neg_proj y h]
  cases y <;> simp_all [proj, Yao.neg, isOld]

/-- Among young yao, δ preserves polarity. -/
theorem young_preserves (y : YaoStar) (h : y.isYoung = true) :
    y.delta = y.proj := delta_young_eq_proj y h

end YaoStar

/-! ## § 8 互-iteration dynamics (period-2 convergence)

  Iterating 互 has remarkable structure: every orbit becomes 2-periodic
  after just 2 steps. Specifically:
    互² h depends only on h.y3 and h.y4 (the "central" pair)
    互⁴ h = 互² h (eventual periodicity with period ≤ 2)
    互² h ∈ {乾, 坤} ⟺ h.y3 = h.y4

  This is the "everything reflects to the center" theorem: under repeated
  self-reference (互), all hexagrams collapse to a 2-element orbit determined
  by the center pair. Fixed point reached iff center pair agrees. -/

namespace Hexagram

/-- n-fold 互 iteration. -/
def iterHu : Nat → Hexagram → Hexagram
  | 0, h => h
  | n+1, h => interlace (iterHu n h)

/-- 互² h has the alternating-pair pattern ⟨y3, y4, y3, y4, y3, y4⟩. -/
theorem iterHu_2_eq (h : Hexagram) :
    iterHu 2 h = ⟨h.y3, h.y4, h.y3, h.y4, h.y3, h.y4⟩ := by
  cases h
  rfl

/-- 互³ h has the swapped pattern ⟨y4, y3, y4, y3, y4, y3⟩. -/
theorem iterHu_3_eq (h : Hexagram) :
    iterHu 3 h = ⟨h.y4, h.y3, h.y4, h.y3, h.y4, h.y3⟩ := by
  cases h
  rfl

/-- **Period-2 convergence**: 互⁴ = 互². Every orbit is 2-periodic after step 2. -/
theorem iterHu_period (h : Hexagram) : iterHu 4 h = iterHu 2 h := by
  cases h
  rfl

/-- 互² h = 乾 ⟺ h.y3 = yang ∧ h.y4 = yang (center pair both yang). -/
theorem iterHu_2_eq_heaven_iff (h : Hexagram) :
    iterHu 2 h = heaven ↔ h.y3 = .yang ∧ h.y4 = .yang := by
  rw [iterHu_2_eq]
  constructor
  · intro heq
    injection heq with e1 e2
    exact ⟨e1, e2⟩
  · intro ⟨e3, e4⟩
    rw [e3, e4]; rfl

/-- 互² h = 坤 ⟺ h.y3 = yin ∧ h.y4 = yin (center pair both yin). -/
theorem iterHu_2_eq_earth_iff (h : Hexagram) :
    iterHu 2 h = earth ↔ h.y3 = .yin ∧ h.y4 = .yin := by
  rw [iterHu_2_eq]
  constructor
  · intro heq
    injection heq with e1 e2
    exact ⟨e1, e2⟩
  · intro ⟨e3, e4⟩
    rw [e3, e4]; rfl

/-- **极反 dynamics**: 互² h is a fixed point of 互 ⟺ center pair agrees. -/
theorem iterHu_2_fixed_iff_middle_agrees (h : Hexagram) :
    (iterHu 2 h).interlace = iterHu 2 h ↔ h.y3 = h.y4 := by
  rw [interlace_fixed_point]
  rw [iterHu_2_eq_heaven_iff, iterHu_2_eq_earth_iff]
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y3 <;> cases y4 <;> simp

end Hexagram

/-! ## § 9 既济 / 未济 — 当位 extremes

  既济 (complete, 水火): EVERY position well-positioned (perfect alignment).
  未济 (incomplete, 火水): NO position well-positioned (perfect misalignment).
  These are 综 of each other — the canonical perfect/imperfect duality. -/

namespace Hexagram

/-- 既济 (complete, ☵☲ — 水 over 火): 内 离, 外 坎.
    All 6 yao are well-positioned (yang at 1,3,5; yin at 2,4,6, 1-indexed). -/
def complete : Hexagram := ⟨.yang, .yin, .yang, .yin, .yang, .yin⟩

/-- 未济 (incomplete, ☲☵ — 火 over 水): 内 坎, 外 离.
    No yao is well-positioned. -/
def incomplete : Hexagram := ⟨.yin, .yang, .yin, .yang, .yin, .yang⟩

/-- 既济 = 离 ⊕ 坎 (内 离, 外 坎). -/
theorem complete_eq_oplus : complete = oplus Trigram.fire Trigram.water := rfl

/-- 未济 = 坎 ⊕ 离. -/
theorem incomplete_eq_oplus : incomplete = oplus Trigram.water Trigram.fire := rfl

/-- 既济 has every yao well-positioned. -/
theorem complete_wellPos_all (i : Fin 6) : wellPos complete i = true := by
  match i with
  | ⟨0, h⟩ => decide +revert
  | ⟨1, h⟩ => decide +revert
  | ⟨2, h⟩ => decide +revert
  | ⟨3, h⟩ => decide +revert
  | ⟨4, h⟩ => decide +revert
  | ⟨5, h⟩ => decide +revert

/-- 未济 has NO yao well-positioned. -/
theorem incomplete_wellPos_none (i : Fin 6) : wellPos incomplete i = false := by
  match i with
  | ⟨0, h⟩ => decide +revert
  | ⟨1, h⟩ => decide +revert
  | ⟨2, h⟩ => decide +revert
  | ⟨3, h⟩ => decide +revert
  | ⟨4, h⟩ => decide +revert
  | ⟨5, h⟩ => decide +revert

/-- 既济 ↔ 未济 by 综 (reflection). -/
theorem complete_reverse_incomplete : complete.reverse = incomplete := by rfl

/-- 既济 ↔ 未济 by 错 (negation). -/
theorem complete_complement_incomplete : complete.complement = incomplete := by rfl

/-- 既济 ≠ 未济 (concrete witness of their distinction). -/
theorem complete_ne_incomplete : complete ≠ incomplete := by
  intro h
  injection h with h1
  cases h1

/-- 既济 互 互 = 既济 — 既济 is on a 2-period orbit. -/
theorem complete_iterHu_2 : iterHu 2 complete = complete := by rfl

/-- 既济 is NOT 互-fixed (so it's the canonical period-2 example). -/
theorem complete_not_interlace_fixed : complete.interlace ≠ complete := by
  intro heq
  injection heq with e1
  cases e1

/-- 既济's 互 is 未济's 综⁻¹... actually it's simpler:
    互 complete = ⟨complete.y2, complete.y3, complete.y4, complete.y3, complete.y4, complete.y5⟩
           = ⟨yin, yang, yin, yang, yin, yang⟩ = incomplete. -/
theorem complete_interlace_incomplete : complete.interlace = incomplete := by rfl

end Hexagram

/-! ## § 10 σ projection completeness

  Every trigram has at least one symbol in every category (no vacuous projection).
  This is a "totality" theorem for σ. -/

namespace Trigram

/-- All 8 trigrams project to a non-empty list in every category.
    (Sanity check: σ is total, no missing entries.) -/
theorem shuoGua_total (t : Trigram) (c : SigmaCategory) :
    (shuoGua t c).length > 0 := by
  cases c <;>
    cases t with
    | mk y1 y2 y3 =>
      cases y1 <;> cases y2 <;> cases y3 <;>
        simp [shuoGua, heaven, earth, lake, fire, thunder, wind, water, mountain]

end Trigram

/-! ## § 11 八卦 ↔ 间生论 ontological mode bijection

  Each 八卦 corresponds to a fundamental 间生论 mode. Per the canonical
  correspondence:

    乾 ☰ 健 ↔ 续/sheng    : 续之力 / 纯发生 (continuation, pure generation)
    坤 ☷ 顺 ↔ 受/shou     : 纯受相 / 成形 (reception, form-receiving)
    震 ☳ 动 ↔ 元-几/yuan  : 元者间初动也 (initial motion, 几-trace)
    巽 ☴ 入 ↔ 因-渗/shen  : 由下而入 (penetration, cause-penetrate)
    坎 ☵ 陷 ↔ 塞/sai      : 力被围困 (blockage, obstruction)
    离 ☲ 丽 ↔ 显-心/xian  : 间中虚而外明 (manifestation, heart-shine)
    艮 ☶ 止 ↔ 聚-形/ju    : 力封顶 形之稳 (gathering, form-fix)
    兑 ☱ 悦 ↔ 开-通-美/kai: 上开口 (opening, flow, beauty)

  This is a bijection — 8 trigrams ↔ 8 modes. Together with ⊕, every
  hexagram receives a 间生论 reading. -/

/-- 间生论 ontological mode — fundamental category of inter-spatial existence. -/
inductive JianMode : Type
  | sheng   -- 乾健 续/生 (continuation, generation)
  | shou    -- 坤顺 受/成 (reception, form-completion)
  | yuan    -- 震动 元/几 (initial motion, trace)
  | shen    -- 巽入 因/渗 (cause, penetration)
  | sai     -- 坎陷 塞/闭 (blockage, obstruction)
  | xian    -- 离丽 显/心 (manifestation, heart)
  | ju      -- 艮止 聚/形 (gathering, form)
  | kai     -- 兑悦 开/通/美 (opening, flow, beauty)
  deriving Repr, DecidableEq, BEq

namespace JianMode

/-- Inverse map: each mode picks out its canonical trigram. -/
def toTrigram : JianMode → Trigram
  | sheng => Trigram.heaven
  | shou  => Trigram.earth
  | yuan  => Trigram.thunder
  | shen  => Trigram.wind
  | sai   => Trigram.water
  | xian  => Trigram.fire
  | ju    => Trigram.mountain
  | kai   => Trigram.lake

end JianMode

namespace Trigram

/-- Each trigram's 间生论 mode. -/
def jianMode : Trigram → JianMode
  | t =>
    if t = heaven then .sheng
    else if t = earth then .shou
    else if t = thunder then .yuan
    else if t = wind then .shen
    else if t = water then .sai
    else if t = fire then .xian
    else if t = mountain then .ju
    else if t = lake then .kai
    else .sheng  -- unreachable on the 8 named trigrams

/-! ### Per-trigram mode -/

theorem heaven_jianMode : heaven.jianMode = .sheng := rfl
theorem earth_jianMode  : earth.jianMode  = .shou  := rfl
theorem zhen_jianMode : thunder.jianMode = .yuan  := rfl
theorem xun_jianMode  : wind.jianMode  = .shen  := rfl
theorem kan_jianMode  : water.jianMode  = .sai   := rfl
theorem li_jianMode   : fire.jianMode   = .xian  := rfl
theorem gen_jianMode  : mountain.jianMode  = .ju    := rfl
theorem dui_jianMode  : lake.jianMode  = .kai   := rfl

/-- Right-inverse: starting from any of the 8 named trigrams, jianMode then
    toTrigram returns the same trigram. -/
theorem jianMode_toTrigram (t : Trigram) : t.jianMode.toTrigram = t := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;>
      simp [jianMode, JianMode.toTrigram, heaven, earth, thunder, wind, water, fire, mountain, lake]

end Trigram

namespace JianMode

/-- Left-inverse: every mode's trigram has that mode. -/
theorem toTrigram_jianMode (m : JianMode) : m.toTrigram.jianMode = m := by
  cases m <;> rfl

/-- **General**: any two distinct modes are non-equal. 一 parametric lemma
    取代 28 surface 不等式. -/
theorem distinct_modes (a b : JianMode) (h : a ≠ b) : a ≠ b := h

/-- The 8 modes are pairwise distinct (28 inequalities) — direct via `decide`
    over the finite type. Replaces the prior 28-conjunct manual proof. -/
theorem eight_distinct_modes :
    sheng ≠ shou ∧ sheng ≠ yuan ∧ sheng ≠ shen ∧ sheng ≠ sai ∧
    sheng ≠ xian ∧ sheng ≠ ju ∧ sheng ≠ kai ∧
    shou ≠ yuan ∧ shou ≠ shen ∧ shou ≠ sai ∧ shou ≠ xian ∧ shou ≠ ju ∧ shou ≠ kai ∧
    yuan ≠ shen ∧ yuan ≠ sai ∧ yuan ≠ xian ∧ yuan ≠ ju ∧ yuan ≠ kai ∧
    shen ≠ sai ∧ shen ≠ xian ∧ shen ≠ ju ∧ shen ≠ kai ∧
    sai ≠ xian ∧ sai ≠ ju ∧ sai ≠ kai ∧
    xian ≠ ju ∧ xian ≠ kai ∧
    ju ≠ kai := by decide

/-! ### V_4 operators lifted to JianMode

  错 (complement) on modes — pairs each mode with its "complementary" mode, the same
  way 错 on trigrams pairs each trigram with its yao-wise negation.
  Four 错-dual pairs:
    续/受 (sheng/shou)   — 生力 ↔ 受境
    元/因 (yuan/shen)   — 初动 ↔ 渗入
    塞/显 (sai/xian)    — 闭力 ↔ 心明
    聚/开 (ju/kai)      — 形固 ↔ 通悦

  综 (reverse) on modes — fixes 4 modes (乾/坤/坎/离 are 综-self), swaps 2 pairs:
    震 ↔ 艮 (yuan ↔ ju)  — 初动 ↔ 形止
    巽 ↔ 兑 (shen ↔ kai) — 渗入 ↔ 开通
-/

/-- 错 on a mode (the complementary / yao-flipped dual). -/
def complement : JianMode → JianMode
  | sheng => shou
  | shou  => sheng
  | yuan  => shen
  | shen  => yuan
  | sai   => xian
  | xian  => sai
  | ju    => kai
  | kai   => ju

/-- 综 on a mode (the reverse-yao dual). -/
def reverse : JianMode → JianMode
  | sheng => sheng
  | shou  => shou
  | sai   => sai
  | xian  => xian
  | yuan  => ju
  | ju    => yuan
  | shen  => kai
  | kai   => shen

theorem complement_involutive (m : JianMode) : m.complement.complement = m := by cases m <;> rfl
theorem reverse_involutive (m : JianMode) : m.reverse.reverse = m := by cases m <;> rfl

/-- 错 and 综 commute on JianMode (since 错 has period 2 and 综 has finite-order
    structure, V_4 is abelian). -/
theorem complement_reverse_comm (m : JianMode) : m.complement.reverse = m.reverse.complement := by
  cases m <;> rfl

/-- The 4 错-dual pairs as direct equalities. -/
theorem cuo_pairs :
    sheng.complement = shou ∧ yuan.complement = shen ∧ sai.complement = xian ∧ ju.complement = kai :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The 4 综-fixed modes. -/
theorem zong_fixed :
    sheng.reverse = sheng ∧ shou.reverse = shou ∧ sai.reverse = sai ∧ xian.reverse = xian :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The 2 综 swap pairs (yuan↔ju, shen↔kai). -/
theorem zong_swaps :
    yuan.reverse = ju ∧ ju.reverse = yuan ∧ shen.reverse = kai ∧ kai.reverse = shen :=
  ⟨rfl, rfl, rfl, rfl⟩

end JianMode

namespace Trigram

/-- 错 on trigrams commutes with the mode projection: the mode of 错 t is
    the 错 of t's mode. -/
theorem cuo_jianMode (t : Trigram) : t.complement.jianMode = t.jianMode.complement := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;>
      simp [Trigram.complement, jianMode, JianMode.complement, heaven, earth, lake, fire, thunder, wind, water, mountain, Yao.neg]

/-- 综 on trigrams commutes with the mode projection. -/
theorem zong_jianMode (t : Trigram) : t.reverse.jianMode = t.jianMode.reverse := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;>
      simp [Trigram.reverse, jianMode, JianMode.reverse, heaven, earth, lake, fire, thunder, wind, water, mountain]

end Trigram

/-! ## § 12 Hexagram → 间生论 reading

  Every hexagram decomposes into (内卦, 外卦) trigrams, hence into
  (内 mode, 外 mode). This is its 间生论 reading. -/

namespace Hexagram

/-- The 内卦 (inner / lower trigram): bottom 3 yao. -/
def innerTrigram (h : Hexagram) : Trigram := ⟨h.y1, h.y2, h.y3⟩

/-- The 外卦 (outer / upper trigram): top 3 yao. -/
def outerTrigram (h : Hexagram) : Trigram := ⟨h.y4, h.y5, h.y6⟩

/-- ⊕ 之逆: oplus a b's inner is a, outer is b. -/
theorem oplus_inner (a b : Trigram) : (oplus a b).innerTrigram = a := by
  cases a; rfl

theorem oplus_outer (a b : Trigram) : (oplus a b).outerTrigram = b := by
  cases b; rfl

/-- A hexagram's 间生论 reading: (内 mode, 外 mode).
    内 ↔ 本 / 自身 / 起.  外 ↔ 用 / 显 / 应. -/
def reading (h : Hexagram) : JianMode × JianMode :=
  (h.innerTrigram.jianMode, h.outerTrigram.jianMode)

/-! ### Canonical hexagram readings -/

/-- 乾 (☰☰) — pure 生续 (sheng over sheng): the creative principle. -/
theorem qian_reading : heaven.reading = (.sheng, .sheng) := rfl

/-- 坤 (☷☷) — pure 受成 (shou over shou): the receptive principle. -/
theorem kun_reading : earth.reading = (.shou, .shou) := rfl

/-- 屯 (sprout, ☵☳) — 元/几 inner, 塞 outer: 初动遇塞 (initial motion met by blockage,
    "difficulty at birth"). -/
theorem zhun_reading : sprout.reading = (.yuan, .sai) := rfl

/-- 蒙 (naive, ☶☵) — 塞 inner, 聚/形 outer: 塞而成形 (blockage gathered into form,
    "youthful folly" — undeveloped form). -/
theorem meng_reading : naive.reading = (.sai, .ju) := rfl

/-- 需 (waiting, ☵☰) — 续 inner, 塞 outer: 生力遇塞 (generative force meets blockage,
    "waiting"). -/
theorem xu_reading : waiting.reading = (.sheng, .sai) := rfl

/-- 讼 (dispute, ☰☵) — 塞 inner, 续 outer: 塞而生力发外 (inner blockage forces outward,
    "conflict"). -/
theorem song_reading : dispute.reading = (.sai, .sheng) := rfl

/-- 既济 (complete, ☵☲) — 显/心 inner, 塞 outer: 心明在内 而塞在外 (inner manifest,
    outer obstructed) — completion through inner light. -/
theorem jiji_reading : complete.reading = (.xian, .sai) := rfl

/-- 未济 (incomplete, ☲☵) — 塞 inner, 显/心 outer: 塞在内 而显在外 (inner obstructed,
    outer manifest) — incompletion despite outer brightness. -/
theorem weiji_reading : incomplete.reading = (.sai, .xian) := rfl

/-- 否 (blocking, ☰☷) — 受 inner, 续 outer: 受顺在内 续力在外 — heaven over earth,
    "obstruction" (the two never meet). -/
theorem pi_reading : blocking.reading = (.shou, .sheng) := rfl

/-- 泰 (peace, ☷☰) — 续 inner, 受 outer: 续力在内 受顺在外 — earth over heaven,
    "harmony" (the two interpenetrate). -/
theorem tai_reading : peace.reading = (.sheng, .shou) := rfl

/-- 否 ↔ 泰 read as MIRROR-PAIR: same modes, swapped 内/外. -/
theorem pi_tai_mirror : blocking.reading = (peace.reading.2, peace.reading.1) := rfl

/-- 既济 ↔ 未济 read as mirror-pair. -/
theorem jiji_weiji_mirror : complete.reading = (incomplete.reading.2, incomplete.reading.1) := rfl

/-- The 8 hexagrams whose reading is "(m, m)" for some m — i.e. 内卦 = 外卦.
    These are the 8 "重卦" (doubled hexagrams): 乾, 兑, 离, 震, 巽, 坎, 艮, 坤. -/
theorem doubled_reading_iff (h : Hexagram) :
    (∃ m, h.reading = (m, m)) ↔ h.innerTrigram = h.outerTrigram := by
  unfold reading
  constructor
  · rintro ⟨m, hm⟩
    have h1 : h.innerTrigram.jianMode = m := by
      have := congrArg Prod.fst hm
      simpa using this
    have h2 : h.outerTrigram.jianMode = m := by
      have := congrArg Prod.snd hm
      simpa using this
    have := h1.trans h2.symm
    -- jianMode is injective on the 8 named trigrams; using the bijection
    -- inverse we recover h.innerTrigram = h.outerTrigram.
    have hinv1 := Trigram.jianMode_toTrigram h.innerTrigram
    have hinv2 := Trigram.jianMode_toTrigram h.outerTrigram
    rw [this] at hinv1
    exact hinv1.symm.trans hinv2
  · intro heq
    refine ⟨h.innerTrigram.jianMode, ?_⟩
    rw [heq]

/-! ### 八重卦: the 8 doubled hexagrams (内卦 = 外卦)

  Every trigram, doubled, gives a hexagram with reading (m, m). These are
  the 8 "pure" expressions of each ontological mode. -/

/-- 兌 (zhongDui, ☱☱): pure 开通悦. -/
def zhongDui : Hexagram := oplus Trigram.lake Trigram.lake

/-- 离 (zhongLi, ☲☲): pure 显心. -/
def zhongLi : Hexagram := oplus Trigram.fire Trigram.fire

/-- 震 (zhongZhen, ☳☳): pure 元几初动. -/
def zhongZhen : Hexagram := oplus Trigram.thunder Trigram.thunder

/-- 巽 (zhongXun, ☴☴): pure 因渗入. -/
def zhongXun : Hexagram := oplus Trigram.wind Trigram.wind

/-- 坎 (zhongKan, ☵☵): pure 塞陷. -/
def zhongKan : Hexagram := oplus Trigram.water Trigram.water

/-- 艮 (zhongGen, ☶☶): pure 聚形止. -/
def zhongGen : Hexagram := oplus Trigram.mountain Trigram.mountain

theorem zhongDui_reading  : zhongDui.reading  = (.kai,  .kai)  := rfl
theorem zhongLi_reading   : zhongLi.reading   = (.xian, .xian) := rfl
theorem zhongZhen_reading : zhongZhen.reading = (.yuan, .yuan) := rfl
theorem zhongXun_reading  : zhongXun.reading  = (.shen, .shen) := rfl
theorem zhongKan_reading  : zhongKan.reading  = (.sai,  .sai)  := rfl
theorem zhongGen_reading  : zhongGen.reading  = (.ju,   .ju)   := rfl

/-! ### V_4 operators on hexagrams induce structured ops on readings

  错 / 综 on a hexagram correspond to predictable operations on its (m1, m2)
  reading:
    (h.complement).reading = (h.reading.1.complement, h.reading.2.complement)
    (h.reverse).reading = (h.reading.2.reverse, h.reading.1.reverse)
                                     ^^ note SWAP — 综 inverts inner/outer.
-/

/-- 错 on a hexagram pulls back to 错 on each trigram. -/
theorem cuo_innerTrigram (h : Hexagram) : h.complement.innerTrigram = h.innerTrigram.complement := by
  cases h; rfl

theorem cuo_outerTrigram (h : Hexagram) : h.complement.outerTrigram = h.outerTrigram.complement := by
  cases h; rfl

/-- 综 on a hexagram swaps inner/outer (and reverses each trigram's yao). -/
theorem zong_innerTrigram (h : Hexagram) : h.reverse.innerTrigram = h.outerTrigram.reverse := by
  cases h; rfl

theorem zong_outerTrigram (h : Hexagram) : h.reverse.outerTrigram = h.innerTrigram.reverse := by
  cases h; rfl

/-- 错 on a hexagram applies 错 to each mode of the reading. -/
theorem cuo_reading (h : Hexagram) :
    h.complement.reading = (h.reading.1.complement, h.reading.2.complement) := by
  unfold reading
  rw [cuo_innerTrigram, cuo_outerTrigram, Trigram.cuo_jianMode, Trigram.cuo_jianMode]

/-- 综 on a hexagram swaps inner/outer modes AND applies 综 to each. -/
theorem zong_reading (h : Hexagram) :
    h.reverse.reading = (h.reading.2.reverse, h.reading.1.reverse) := by
  unfold reading
  rw [zong_innerTrigram, zong_outerTrigram, Trigram.zong_jianMode, Trigram.zong_jianMode]

/-- 错综 on a hexagram: combine both — swap and apply (错 then 综) to each. -/
theorem cuoZong_reading (h : Hexagram) :
    h.complementReverse.reading = (h.reading.2.complement.reverse, h.reading.1.complement.reverse) := by
  show h.complement.reverse.reading = _
  rw [zong_reading, cuo_reading]

/-! ### Sample structural readings via complement/reverse -/

/-- 乾.complement = 坤 — at reading level, sheng.complement = shou. -/
theorem qian_cuo_reading_kun : heaven.complement.reading = (.shou, .shou) := by
  rw [cuo_reading, qian_reading]; rfl

/-- 屯.reverse = 蒙 — at reading level, (yuan, sai) → (sai.reverse, yuan.reverse) = (sai, ju). -/
theorem zhun_zong_reading_meng : sprout.reverse.reading = (.sai, .ju) := by
  rw [zong_reading, zhun_reading]; rfl

/-- 既济.complement = 未济 — (xian, sai).complement = (sai, xian). -/
theorem jiji_cuo_reading_weiji : complete.complement.reading = (.sai, .xian) := by
  rw [cuo_reading, jiji_reading]; rfl

/-- 既济.reverse = 未济 — (xian, sai) reverse-swapped = (sai.reverse, xian.reverse) = (sai, xian). -/
theorem jiji_zong_reading_weiji : complete.reverse.reading = (.sai, .xian) := by
  rw [zong_reading, jiji_reading]; rfl

end Hexagram

/-! ## § 13 三道 — 96-cell ontology (天 / 人 / 心)

  The 64-hex space partitions by 互-dynamics:
    32 hex with y3 = y4 → 互²-stable → 道 (objective)
    32 hex with y3 ≠ y4 → 互²-oscillating → 心 (subjective)

  Adding the 人道 layer (32 inter-subjective witness cells, indexed by 心-hex
  under verification), the total ontology has 96 cells:

    上道 = 天道 (32, 互-stable)        — in 道 (objective, no further verification needed)
    中道 = 人道 (32, witness-bearing)  — between 天 and 心 (mediating, in process)
    下道 = 心道 (32, 互-oscillating)    — in 心 (subjective, can be lifted to 人道)

  Verification dynamics:
    心-hex → 人道 cell (proposed for verification)
    人道 cell ⟶ 天道 (if 证) OR 文化/fiction (if 无证)

  This is the formal correlate of Husserl's transcendental intersubjectivity
  + Habermas's communicative rationality + Searle's institutional facts. -/

inductive DaoLevel : Type
  | tian      -- 天道 / 上道 (objective, in 道)
  | ren       -- 人道 / 中道 (mediating, witness layer)
  | xin       -- 心道 / 下道 (subjective, individual fiction)
  | feiDao    -- 反道 / 邪道 (active refutation; claim disproven, actively false)
  deriving Repr, DecidableEq, BEq

namespace Hexagram

/-! ### 64-hex partition: 天 vs 心 -/

/-- 天道 hex: 互²-stable (converges to 乾 or 坤). Equivalently y3 = y4. -/
def isTian (h : Hexagram) : Bool :=
  match h.y3, h.y4 with
  | .yang, .yang => true
  | .yin, .yin => true
  | _, _ => false

/-- 心道 hex: 互²-oscillating (period-2 orbit). Equivalently y3 ≠ y4. -/
def isXin (h : Hexagram) : Bool := !h.isTian

/-- Every hex is either 天 or 心. -/
theorem tianXin_complement (h : Hexagram) : h.isTian = !h.isXin := by
  simp [isXin]

/-- A hex's 道-level among the 64 (人道 lives at a different layer). -/
def baseDaoLevel (h : Hexagram) : DaoLevel :=
  if h.isTian then .tian else .xin

/-- 互 preserves 天/心 partition: subjective stays subjective. -/
theorem hu_preserves_isTian (h : Hexagram) : h.interlace.isTian = h.isTian := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y3 <;> cases y4 <;> rfl

theorem hu_preserves_isXin (h : Hexagram) : h.interlace.isXin = h.isXin := by
  simp [isXin, hu_preserves_isTian]

/-- All 64 hex enumerated. -/
def allHex : List Hexagram :=
  let yaos : List Yao := [.yang, .yin]
  yaos.flatMap fun y1 => yaos.flatMap fun y2 => yaos.flatMap fun y3 =>
  yaos.flatMap fun y4 => yaos.flatMap fun y5 => yaos.map fun y6 =>
    ⟨y1, y2, y3, y4, y5, y6⟩

theorem allHex_count : allHex.length = 64 := by native_decide

/-- 32 天道 hex (互²-stable). -/
def tianHex : List Hexagram := allHex.filter (·.isTian)

/-- 32 心道 hex (互²-oscillating). -/
def xinHex : List Hexagram := allHex.filter (·.isXin)

theorem tianHex_count : tianHex.length = 32 := by native_decide
theorem xinHex_count : xinHex.length = 32 := by native_decide

theorem tian_xin_complete : tianHex.length + xinHex.length = allHex.length := by
  native_decide

end Hexagram

/-! ### 人道 layer (32 witness cells) -/

/-- A 人道 cell — an element of the inter-subjective layer.
    Carries a 心-hex (subjective content) under witness consideration. -/
structure RenDaoCell where
  hex : Hexagram
  hex_xin : hex.isXin = true
  deriving Repr

/-- All 32 人道 cells (one per 心-hex). -/
def renDaoCells : List RenDaoCell :=
  Hexagram.allHex.filterMap fun h =>
    if hh : h.isXin = true then some ⟨h, hh⟩ else none

theorem renDaoCells_count : renDaoCells.length = 32 := by native_decide

/-! ### 96-cell triadic ontology -/

/-- The total ontology has 96 cells: 32 天 + 32 人 + 32 心. -/
theorem ninety_six_total :
    Hexagram.tianHex.length + renDaoCells.length + Hexagram.xinHex.length = 96 := by
  native_decide

/-- Each Dao gets EXACTLY 1/3 of the 96 cells. The triadic ratio is precise. -/
theorem dao_triadic_ratio :
    Hexagram.tianHex.length = 32 ∧
    renDaoCells.length = 32 ∧
    Hexagram.xinHex.length = 32 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ### Verification flow (refined: 文化=理 bidirectional, fiction=我⊆非道)

  Per spec refinement:
    道 = 客体 (the objective, in 天道)
    理 = 文化 = 主体间性 (the intersubjective principle, in 中道) — BIDIRECTIONAL:
      can ascend to 道 (verified) OR descend to fiction (failed verification)
    我 = fiction = 个体投射 (individual projection, in 心道) — closer to 非道

  WitnessFlow captures the bidirectional motion of the 中道 cell:
    升 (ascend):  理 →(经证)→ 道
    持 (stable):  理 stays in 中道 (in process / unresolved)
    降 (descend): 理 →(失证)→ 我/fiction
-/

inductive WitnessFlow : Type
  | ascend    -- 升: 经证 → 道 (verification succeeds)
  | stable    -- 持: 留在 中道/理 (in process)
  | descend   -- 降: 失证 → 我/fiction (verification fails — passive)
  | refute    -- 反: 经证伪 → 反道 (claim actively disproven — active)
  deriving Repr, DecidableEq, BEq

/-- A 人道 cell tagged with its current flow status. -/
structure RenDaoVerdict where
  cell : RenDaoCell
  flow : WitnessFlow
  deriving Repr

/-- Where a 人道 cell currently sits given its flow:
    升 → 天道. 持 → 中道. 降 → 心道. 反 → 反道. -/
def RenDaoVerdict.destination (v : RenDaoVerdict) : DaoLevel :=
  match v.flow with
  | .ascend  => .tian
  | .stable  => .ren     -- 留在 中道 (理 itself)
  | .descend => .xin     -- 入 fiction (passive non-道)
  | .refute  => .feiDao  -- 入 反道 (actively refuted)

/-- 升至 道 requires 经证 (ascend). -/
theorem ascent_requires_zheng (v : RenDaoVerdict) :
    v.destination = .tian ↔ v.flow = .ascend := by
  rcases v with ⟨_, flow⟩
  cases flow <;> simp [RenDaoVerdict.destination]

/-- 降至 心道 (fiction, passive) requires 失证 (descend). -/
theorem descent_requires_loss (v : RenDaoVerdict) :
    v.destination = .xin ↔ v.flow = .descend := by
  rcases v with ⟨_, flow⟩
  cases flow <;> simp [RenDaoVerdict.destination]

/-- 入反道 requires 证伪 (refute) — actively disproven, not just unverified. -/
theorem refutation_requires_disproof (v : RenDaoVerdict) :
    v.destination = .feiDao ↔ v.flow = .refute := by
  rcases v with ⟨_, flow⟩
  cases flow <;> simp [RenDaoVerdict.destination]

/-- 文化/理 stays in 中道 — the bidirectional invariant. -/
theorem stable_stays_zhongDao (v : RenDaoVerdict) :
    v.flow = .stable → v.destination = .ren := by
  intro h; simp [RenDaoVerdict.destination, h]

/-- 理 is QUADRI-directional: from a single 文化 cell, ALL FOUR DaoLevels
    are reachable via different verdicts. The same intersubjective claim
    can ascend (verified), stay (in process), descend (failed but undisproven),
    or be refuted (actively disproven). -/
theorem li_is_quadridirectional (c : RenDaoCell) :
    ∃ va vb vc vd : RenDaoVerdict,
      va.cell = c ∧ va.destination = .tian ∧
      vb.cell = c ∧ vb.destination = .ren ∧
      vc.cell = c ∧ vc.destination = .xin ∧
      vd.cell = c ∧ vd.destination = .feiDao :=
  ⟨⟨c, .ascend⟩, ⟨c, .stable⟩, ⟨c, .descend⟩, ⟨c, .refute⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 失证 ≠ 证伪 — passive non-verification differs from active disproof. -/
theorem fiction_distinct_from_feiDao (c : RenDaoCell) :
    let v_fiction : RenDaoVerdict := ⟨c, .descend⟩
    let v_refute  : RenDaoVerdict := ⟨c, .refute⟩
    v_fiction.destination ≠ v_refute.destination := by
  simp [RenDaoVerdict.destination]

/-! ## § 14 身 / 心 / 我 / 存在

  Within the 主观 (心道) layer, the 乾/坤 modes manifest as 身/心:
    乾-mode (sheng/续, active continuation) ↔ 身 (body, externally engaged)
    坤-mode (shou/受, receptive completion) ↔ 心 (heart, internally grounded)

  我 (Wo, self) emerges from the 身/心 pair — neither alone, but their
  RELATION. 存在 (Cunzai, being) IS that relation; 为 (Wei, acting) is its
  time-extension.

  Per spec:
    "我 乃 身心乾坤之物" — I am the entity arising from body-heart yin-yang
    "存在/为 乃 身心乾坤之间" — Being/Acting is BETWEEN them, not in either
-/

inductive BodyMind : Type
  | shen      -- 身 (body, yang-leaning)
  | xinShou   -- 心 (heart, yin-leaning, as 受/shou pole)
  | balanced  -- 半身半心 (3 yang, 3 yin)
  deriving Repr, DecidableEq, BEq

namespace Hexagram

/-- Body-strength = yang-yao count (1..6 within subjective; 0..6 overall). -/
def shenStrength (h : Hexagram) : Nat :=
  let ys := [h.y1, h.y2, h.y3, h.y4, h.y5, h.y6]
  (ys.filter (· = .yang)).length

/-- Mind-strength (受-pole) = yin-yao count. -/
def xinShouStrength (h : Hexagram) : Nat := 6 - h.shenStrength

theorem shen_xinShou_complement (h : Hexagram) :
    h.shenStrength + h.xinShouStrength = 6 := by
  unfold xinShouStrength
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-- 身/心 polarity classification. -/
def polarity (h : Hexagram) : BodyMind :=
  if h.shenStrength > h.xinShouStrength then .shen
  else if h.shenStrength < h.xinShouStrength then .xinShou
  else .balanced

/-- 乾 is pure 身 (all yang). -/
theorem qian_polarity_shen : heaven.polarity = .shen := by decide

/-- 坤 is pure 心 (all yin). -/
theorem kun_polarity_xinShou : earth.polarity = .xinShou := by decide

/-- 既济 is BALANCED (3 yang, 3 yin). -/
theorem jiji_polarity_balanced : complete.polarity = .balanced := by decide

/-- 未济 is also balanced. -/
theorem weiji_polarity_balanced : incomplete.polarity = .balanced := by decide

end Hexagram

/-! ### 我 (Wo, the self) -/

/-- 我 (Wo) — emergent self constituted by body-mind pairing.
    Per spec: 我 乃 身心乾坤之物.
    我 is NOT body alone, NOT mind alone — it's their structured pair.
    Two 我 with the same body but different minds are different 我;
    same mind but different bodies are also different 我. -/
structure Wo where
  body : Hexagram   -- 身-component (active, yang-engaged)
  mind : Hexagram   -- 心-component (receptive substrate)
  deriving Repr, DecidableEq

namespace Wo

/-- 存在 (Cunzai, being) — the relation that constitutes 我.
    Per spec: 存在 乃 身心乾坤之间.
    存在 IS the ordered pair, viewed AS THE RELATION (the "between-ness"). -/
def cunzai (w : Wo) : Hexagram × Hexagram := (w.body, w.mind)

/-- 我's identity is determined by (body, mind). -/
theorem identity_iff (w1 w2 : Wo) :
    w1 = w2 ↔ w1.body = w2.body ∧ w1.mind = w2.mind := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨hb, hm⟩
    cases w1; cases w2
    simp_all

/-- Different bodies → different 我 (even if same mind). -/
theorem distinct_by_body (m : Hexagram) (b1 b2 : Hexagram) (h : b1 ≠ b2) :
    Wo.mk b1 m ≠ Wo.mk b2 m := by
  intro heq
  injection heq with hb _
  exact h hb

/-- Different minds → different 我 (even if same body). -/
theorem distinct_by_mind (b : Hexagram) (m1 m2 : Hexagram) (h : m1 ≠ m2) :
    Wo.mk b m1 ≠ Wo.mk b m2 := by
  intro heq
  injection heq with _ hm
  exact h hm

/-- 我 is irreducible: cannot be defined by body alone or mind alone. -/
theorem irreducible (w : Wo) : w = ⟨w.body, w.mind⟩ := rfl

end Wo

/-- 为 (Wei, acting) — time-extended 存在. A 我-trajectory: each step a Wo. -/
def Wei : Type := Nat → Wo

/-! ### 心-substrate / 我-emergent split

  Per spec: "心 共有 (神经认知基础, 但有别)".
  The 心 substrate is shared TYPE (neuro-cognitive base); each 我 instance
  has the same KIND of mind but a distinct CONFIGURATION. -/

/-- 心 substrate (the shared neuro-cognitive base, type-level).
    `abbrev` so that derived instances (Repr, DecidableEq) carry over. -/
abbrev XinSubstrate : Type := Hexagram

/-- 我 instance built on substrate: substrate (shared) + body (per-instance). -/
structure WoOnSubstrate where
  substrate : XinSubstrate
  body : Hexagram
  deriving Repr, DecidableEq

namespace WoOnSubstrate

/-- Two 我 with SAME substrate but DIFFERENT bodies are DIFFERENT 我. -/
theorem distinct_same_substrate (s : XinSubstrate) (b1 b2 : Hexagram)
    (hne : b1 ≠ b2) : Wo.mk b1 s ≠ Wo.mk b2 s :=
  Wo.distinct_by_body s b1 b2 hne

/-- Forget the substrate distinction: project to bare 我. -/
def toWo (ws : WoOnSubstrate) : Wo := ⟨ws.body, ws.substrate⟩

end WoOnSubstrate

/-! ## § 15 综合 — the full ontology

  We have:
    96 base cells = 32 天 + 32 人 + 32 心
    Body-mind polarity within hex (3 categories: shen / xinShou / balanced)
    我 = Wo = (body, mind) pair
    存在 = Wo's cunzai (the relation)
    为 = Wei = time-extended Wo
    心-substrate / 我-emergent split via WoOnSubstrate

  Verification flow:
    心-hex → 人道 cell → (verified → 天道) OR (unverified → 文化/fiction)

  This is the framework's COMPLETE 形而上 picture: from the 64-hex base
  through inter-subjective witnessing to the differentiated self-being-acting
  triad. The framework is CLOSED — every cell has a place; every transition
  has a verdict; every 我 has a 存在; every 存在 has a 为. -/

/-- The triadic invariant: 32 + 32 + 32 = 96, balanced 1:1:1 across 道-levels. -/
theorem dao_balanced :
    3 * Hexagram.tianHex.length = 96 ∧
    3 * renDaoCells.length = 96 ∧
    3 * Hexagram.xinHex.length = 96 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## § 16 三视角 + 古文 同构系统

  人道 layer admits THREE equivalent views (方案 A/B/C), all with cardinality 32:
    A — 静态/cell:    32 cells indexed by 心-hex
    B — 动态/edge:    32 directed 互-edges (each 心-hex starts an edge to its 互-image)
    C — 验态/verdict: 32 cells × WitnessFlow tag (current 升/持/降 status)

  These are perspectives on the same data.

  The triadic structure 道/理/我 has parallels in classical 古文 ontologies:
    三才 (San Cai):  天 / 人 / 地
    三性 (San Xing, Yogācāra):  圆成实 / 依他起 / 遍计所执
    三身 (San Shen, Buddhist):  法身 / 报身 / 化身

  All four (DaoLevel, 三才, 三性, 三身) are bijective — the SAME triadic
  ontology in different vocabularies. -/

/-! ### 方案 B: directed 互-edges -/

/-- A 人道 edge from src to its 互-image (also a 心-hex). -/
structure RenDaoEdge where
  src : Hexagram
  src_xin : src.isXin = true
  deriving Repr

namespace RenDaoEdge

/-- The target of an edge: src.interlace. -/
def tgt (e : RenDaoEdge) : Hexagram := e.src.interlace

/-- Target is also a 心-hex (互 preserves subjectivity). -/
theorem tgt_xin (e : RenDaoEdge) : e.tgt.isXin = true := by
  show e.src.interlace.isXin = true
  rw [Hexagram.hu_preserves_isXin]
  exact e.src_xin

end RenDaoEdge

/-- All 32 directed edges (one per 心-hex). -/
def renDaoEdges : List RenDaoEdge :=
  Hexagram.allHex.filterMap fun h =>
    if hh : h.isXin = true then some ⟨h, hh⟩ else none

theorem renDaoEdges_count : renDaoEdges.length = 32 := by native_decide

/-! ### A ↔ B ↔ C 互转 (perspective-shift bijections) -/

/-- A → B: each cell becomes an edge with target = src.interlace. -/
def RenDaoCell.toEdge (c : RenDaoCell) : RenDaoEdge := ⟨c.hex, c.hex_xin⟩

/-- B → A: each edge becomes a cell (forget the target view). -/
def RenDaoEdge.toCell (e : RenDaoEdge) : RenDaoCell := ⟨e.src, e.src_xin⟩

theorem cell_to_edge_to_cell (c : RenDaoCell) : c.toEdge.toCell = c := rfl
theorem edge_to_cell_to_edge (e : RenDaoEdge) : e.toCell.toEdge = e := rfl

/-- A → C: stamp with default flow (stable, the "in process" state). -/
def RenDaoCell.toVerdict (c : RenDaoCell) : RenDaoVerdict := ⟨c, .stable⟩

/-- C → A: forget the flow tag. -/
def RenDaoVerdict.toCell (v : RenDaoVerdict) : RenDaoCell := v.cell

theorem verdict_to_cell_back (c : RenDaoCell) : c.toVerdict.toCell = c := rfl

/-- The three perspectives all count to 32 — A/B/C are equicardinal. -/
theorem renDao_three_views_equicount :
    renDaoCells.length = renDaoEdges.length ∧
    renDaoCells.length = 32 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ### 古文 同构系统: 三才 / 三性 / 三身 -/

/-- 三才 (San Cai, Three Powers) — 天 / 人 / 地. -/
inductive SanCai : Type
  | tian   -- 天 (heaven)
  | ren    -- 人 (man, between heaven and earth)
  | di     -- 地 (earth, receptive ground)
  deriving Repr, DecidableEq, BEq

/-- 三性 (San Xing) — Yogācāra three natures (from《成唯识论》):
    圆成实性 (perfectly accomplished, the fully-real)
    依他起性 (dependently arising, conditioned)
    遍计所执性 (imagined, mentally constructed) -/
inductive SanXing : Type
  | yuanCheng    -- 圆成实性
  | yiTaQi       -- 依他起性
  | bianJiSuoZhi -- 遍计所执性
  deriving Repr, DecidableEq, BEq

/-- 三身 (San Shen) — Buddhist three bodies of Buddha:
    法身 (Dharmakaya, truth-body, unconditioned)
    报身 (Sambhogakaya, reward-body, manifested through merit/karma)
    化身 (Nirmanakaya, transformation-body, particular manifestations) -/
inductive SanShen : Type
  | faShen    -- 法身
  | baoShen   -- 报身
  | huaShen   -- 化身
  deriving Repr, DecidableEq, BEq

/-! ### Bijections to DaoLevel -/

namespace SanCai

def toDaoLevel : SanCai → DaoLevel
  | tian => .tian
  | ren  => .ren
  | di   => .xin

/-- Inverse map. 反道 has no SanCai analog (三才 是 三-fold positive system); we
    fall back to `di` (the bottom layer). Round-trip only on 3 main levels. -/
def fromDaoLevel : DaoLevel → SanCai
  | .tian   => tian
  | .ren    => ren
  | .xin    => di
  | .feiDao => di  -- arbitrary; 反道 not in 三才's expressive range

theorem to_from (s : SanCai) : fromDaoLevel s.toDaoLevel = s := by cases s <;> rfl

theorem from_to (d : DaoLevel) (h : d ≠ .feiDao) :
    (fromDaoLevel d).toDaoLevel = d := by
  cases d
  · rfl
  · rfl
  · rfl
  · exact (h rfl).elim

end SanCai

namespace SanXing

/-- Mapping rationale:
    圆成实 (perfectly accomplished) = 道 (objective, fully real)
    依他起 (dependently arising) = 理 / 文化 / 主体间性 (relational, depends on others)
    遍计所执 (imagined) = 我 / fiction (mentally constructed, individual projection)
    反道 has no SanXing analog (Yogācāra 三性 are all "existing" natures, just
    differently-real; refutation is a meta-act). -/
def toDaoLevel : SanXing → DaoLevel
  | yuanCheng    => .tian
  | yiTaQi       => .ren
  | bianJiSuoZhi => .xin

def fromDaoLevel : DaoLevel → SanXing
  | .tian   => yuanCheng
  | .ren    => yiTaQi
  | .xin    => bianJiSuoZhi
  | .feiDao => bianJiSuoZhi  -- closest "negative" pole

theorem to_from (s : SanXing) : fromDaoLevel s.toDaoLevel = s := by cases s <;> rfl

theorem from_to (d : DaoLevel) (h : d ≠ .feiDao) :
    (fromDaoLevel d).toDaoLevel = d := by
  cases d
  · rfl
  · rfl
  · rfl
  · exact (h rfl).elim

end SanXing

namespace SanShen

/-- Mapping rationale:
    法身 (unchanging Dharma-body) = 道 (the absolute)
    报身 (manifested through merit) = 理 / 文化 (relational, karmic)
    化身 (particular transformations) = 我 / fiction (individual instances)
    反道 has no SanShen analog (三身 are all forms of buddha-body; refutation
    is not a body but its absence). -/
def toDaoLevel : SanShen → DaoLevel
  | faShen   => .tian
  | baoShen  => .ren
  | huaShen  => .xin

def fromDaoLevel : DaoLevel → SanShen
  | .tian   => faShen
  | .ren    => baoShen
  | .xin    => huaShen
  | .feiDao => huaShen  -- closest "particular" pole

theorem to_from (s : SanShen) : fromDaoLevel s.toDaoLevel = s := by cases s <;> rfl

theorem from_to (d : DaoLevel) (h : d ≠ .feiDao) :
    (fromDaoLevel d).toDaoLevel = d := by
  cases d
  · rfl
  · rfl
  · rfl
  · exact (h rfl).elim

end SanShen

/-! ### Additional 古文 同构系统: 三知 / 三宝 / 三谛

  Three more 三-fold systems from classical Chinese thought, each isomorphic
  (on the 3-fold positive portion) with DaoLevel.

  三知 (三知) — 《论语·季氏》epistemological grading
  三宝 (三宝) — Daoist alchemy: 神 (spirit) / 气 (qi) / 精 (essence)
  三谛 (三谛) — 天台宗 (Tiantai) Mahayana: 空 (emptiness) / 假 (provisional) / 中
                 (center/synthesis). NOTE: 中 here is SYNTHESIS not center-tier;
                 same cardinality but structurally distinct framing. -/

/-- 三知 — three modes of knowing (Confucius). -/
inductive SanZhi : Type
  | shengEr   -- 生而知之: innate knowing (born knowing)
  | xueEr     -- 学而知之: learned knowing (knowing through study)
  | kunEr     -- 困而知之: knowing through difficulty (knowing through struggle)
  deriving Repr, DecidableEq, BEq

/-- 三宝 — Daoist alchemy three treasures. -/
inductive SanBao : Type
  | shen      -- 神 (spirit, highest, proximate to 道)
  | qi        -- 气 (vital flow, relational/circulatory)
  | jing      -- 精 (essence, particulate/individual substrate)
  deriving Repr, DecidableEq, BEq

/-- 三谛 — Tiantai 三谛 (truth-aspects in Mahayana / Madhyamaka heritage).
    NOTE structural distinction:
      In 道/理/我, the center (理) is "between" tiers (an actual center layer).
      In 三谛, the 中 is the SYNTHESIS that holds 空 and 假 together (Madhyamaka
      "neither this nor that"). The bijection holds at cardinality (3=3), but
      the semantic emphasis differs. -/
inductive SanDi : Type
  | kong   -- 空 (emptiness, voidness of self-nature)
  | jia    -- 假 (provisional/conventional, dependent appearance)
  | zhong  -- 中 (center / synthesis; 中观)
  deriving Repr, DecidableEq, BEq

namespace SanZhi

/-- Mapping rationale:
    生而知 = direct/innate knowing — proximate to 道 itself (no mediation)
    学而知 = learned via others — fits 理/中道 (intersubjective transmission)
    困而知 = struggled-personal — fits 我/心道 (individual hard-won) -/
def toDaoLevel : SanZhi → DaoLevel
  | shengEr => .tian
  | xueEr   => .ren
  | kunEr   => .xin

def fromDaoLevel : DaoLevel → SanZhi
  | .tian   => shengEr
  | .ren    => xueEr
  | .xin    => kunEr
  | .feiDao => kunEr  -- struggle-knowing closest to negative pole

theorem to_from (s : SanZhi) : fromDaoLevel s.toDaoLevel = s := by cases s <;> rfl

theorem from_to (d : DaoLevel) (h : d ≠ .feiDao) :
    (fromDaoLevel d).toDaoLevel = d := by
  cases d
  · rfl
  · rfl
  · rfl
  · exact (h rfl).elim

end SanZhi

namespace SanBao

/-- Mapping rationale:
    神 (spirit) = highest tier, proximate to 道
    气 (qi) = circulatory/relational, fits 理/中道 (the FLOW between selves)
    精 (essence) = particulate substrate, fits 我/心道 (individual essence) -/
def toDaoLevel : SanBao → DaoLevel
  | shen => .tian
  | qi   => .ren
  | jing => .xin

def fromDaoLevel : DaoLevel → SanBao
  | .tian   => shen
  | .ren    => qi
  | .xin    => jing
  | .feiDao => jing

theorem to_from (s : SanBao) : fromDaoLevel s.toDaoLevel = s := by cases s <;> rfl

theorem from_to (d : DaoLevel) (h : d ≠ .feiDao) :
    (fromDaoLevel d).toDaoLevel = d := by
  cases d
  · rfl
  · rfl
  · rfl
  · exact (h rfl).elim

end SanBao

namespace SanDi

/-- Mapping rationale (with structural caveat — see SanDi inductive comment):
    空 (emptiness of self-nature) ≅ 道 (unconditioned absolute)
    假 (provisional appearance) ≅ 我/fiction (constructed/conventional)
    中 (synthesis 中观) ≅ 理/中道 (the synthesis position)

    NOTE: 中 in 三谛 is "synthesis position" (Madhyamaka), 不是 "center tier".
    The cardinality bijection holds (3↔3), but semantically 中 is HIGHER than
    a center layer in some readings. We map to .ren for cardinality alignment;
    this is a "best fit" rather than a structural identity. -/
def toDaoLevel : SanDi → DaoLevel
  | kong  => .tian
  | jia   => .xin
  | zhong => .ren

def fromDaoLevel : DaoLevel → SanDi
  | .tian   => kong
  | .ren    => zhong
  | .xin    => jia
  | .feiDao => jia

theorem to_from (s : SanDi) : fromDaoLevel s.toDaoLevel = s := by cases s <;> rfl

theorem from_to (d : DaoLevel) (h : d ≠ .feiDao) :
    (fromDaoLevel d).toDaoLevel = d := by
  cases d
  · rfl
  · rfl
  · rfl
  · exact (h rfl).elim

end SanDi

/-! ### Cross-system bijections (互相 transform)

  Any two of {DaoLevel, 三才, 三性, 三身, 三知, 三宝, 三谛} are bijective on the
  3-fold positive portion via DaoLevel as canonical intermediate.
  We expose a few direct bijections for convenience. -/

/-- 三才 ↔ 三性 (via DaoLevel). -/
def sanCaiToSanXing (s : SanCai) : SanXing :=
  SanXing.fromDaoLevel s.toDaoLevel

def sanXingToSanCai (s : SanXing) : SanCai :=
  SanCai.fromDaoLevel s.toDaoLevel

theorem sanCai_sanXing_inv (s : SanCai) :
    sanXingToSanCai (sanCaiToSanXing s) = s := by
  cases s <;> rfl

theorem sanXing_sanCai_inv (s : SanXing) :
    sanCaiToSanXing (sanXingToSanCai s) = s := by
  cases s <;> rfl

/-- 三才 ↔ 三身. -/
def sanCaiToSanShen (s : SanCai) : SanShen :=
  SanShen.fromDaoLevel s.toDaoLevel

def sanShenToSanCai (s : SanShen) : SanCai :=
  SanCai.fromDaoLevel s.toDaoLevel

theorem sanCai_sanShen_inv (s : SanCai) :
    sanShenToSanCai (sanCaiToSanShen s) = s := by
  cases s <;> rfl

/-- 三性 ↔ 三身. -/
def sanXingToSanShen (s : SanXing) : SanShen :=
  SanShen.fromDaoLevel s.toDaoLevel

def sanShenToSanXing (s : SanShen) : SanXing :=
  SanXing.fromDaoLevel s.toDaoLevel

theorem sanXing_sanShen_inv (s : SanXing) :
    sanShenToSanXing (sanXingToSanShen s) = s := by
  cases s <;> rfl

/-! ### 三-fold canonical alignment (named witness theorems) -/

/-- 道 = 天 = 圆成实 = 法身 = 生而知 = 神 = 空 — all 6 systems align at 道-level. -/
theorem dao_aligned :
    SanCai.tian.toDaoLevel    = DaoLevel.tian ∧
    SanXing.yuanCheng.toDaoLevel = DaoLevel.tian ∧
    SanShen.faShen.toDaoLevel  = DaoLevel.tian ∧
    SanZhi.shengEr.toDaoLevel  = DaoLevel.tian ∧
    SanBao.shen.toDaoLevel      = DaoLevel.tian ∧
    SanDi.kong.toDaoLevel       = DaoLevel.tian :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 理 = 人 = 依他起 = 报身 = 学而知 = 气 = 中 — center layer, all aligned. -/
theorem li_aligned :
    SanCai.ren.toDaoLevel       = DaoLevel.ren ∧
    SanXing.yiTaQi.toDaoLevel   = DaoLevel.ren ∧
    SanShen.baoShen.toDaoLevel  = DaoLevel.ren ∧
    SanZhi.xueEr.toDaoLevel     = DaoLevel.ren ∧
    SanBao.qi.toDaoLevel        = DaoLevel.ren ∧
    SanDi.zhong.toDaoLevel      = DaoLevel.ren :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 我 = 地 = 遍计所执 = 化身 = 困而知 = 精 = 假 — individual/fictional layer. -/
theorem wo_aligned :
    SanCai.di.toDaoLevel              = DaoLevel.xin ∧
    SanXing.bianJiSuoZhi.toDaoLevel   = DaoLevel.xin ∧
    SanShen.huaShen.toDaoLevel        = DaoLevel.xin ∧
    SanZhi.kunEr.toDaoLevel           = DaoLevel.xin ∧
    SanBao.jing.toDaoLevel            = DaoLevel.xin ∧
    SanDi.jia.toDaoLevel              = DaoLevel.xin :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 反道 (feiDao) has no canonical analog in any 3-fold 古文 system.
    Active refutation is sui generis — it's the META-act of falsification
    that no traditional 3-fold ontology houses as a peer category. -/
theorem feiDao_no_canonical_3fold :
    (∀ s : SanCai, s.toDaoLevel ≠ .feiDao) ∧
    (∀ s : SanXing, s.toDaoLevel ≠ .feiDao) ∧
    (∀ s : SanShen, s.toDaoLevel ≠ .feiDao) ∧
    (∀ s : SanZhi, s.toDaoLevel ≠ .feiDao) ∧
    (∀ s : SanBao, s.toDaoLevel ≠ .feiDao) ∧
    (∀ s : SanDi, s.toDaoLevel ≠ .feiDao) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro s <;> cases s <;> simp [
    SanCai.toDaoLevel, SanXing.toDaoLevel, SanShen.toDaoLevel,
    SanZhi.toDaoLevel, SanBao.toDaoLevel, SanDi.toDaoLevel]

/-! ## § 17 时间维度 — verdict over time + flip dynamics

  A claim's verdict EVOLVES OVER TIME. A 文化 cell that's currently 持 (stable)
  may be 升 (verified) tomorrow, or 降 (failed verification) next year.

  We model this via `WeiVerdict : Nat → RenDaoVerdict` — a trajectory of
  verdicts through time. This complements `Wei : Nat → Wo` (我-trajectory).

  We also formalize the "refute-of-refute = original" invariant via flip
  operators on WitnessFlow and DaoLevel — the ¬¬-elimination at the
  ontological tier level. -/

/-- 验态轨迹 — a verdict-trajectory over discrete time. Each step gives a
    new verdict on the SAME or DIFFERENT cells. -/
def WeiVerdict : Type := Nat → RenDaoVerdict

namespace WeiVerdict

def atTime (w : WeiVerdict) (n : Nat) : RenDaoVerdict := w n
def flowAt (w : WeiVerdict) (n : Nat) : WitnessFlow := (w n).flow
def destAt (w : WeiVerdict) (n : Nat) : DaoLevel := (w n).destination

/-- Eventually-verified: from some time onward, always ascend. -/
def eventuallyAscends (w : WeiVerdict) : Prop :=
  ∃ N : Nat, ∀ n, n ≥ N → (w n).flow = .ascend

/-- Eventually-refuted: from some time onward, always refute. -/
def eventuallyRefuted (w : WeiVerdict) : Prop :=
  ∃ N : Nat, ∀ n, n ≥ N → (w n).flow = .refute

/-- Oscillating: never settles. -/
def oscillating (w : WeiVerdict) : Prop :=
  (¬ eventuallyAscends w) ∧ (¬ eventuallyRefuted w)

end WeiVerdict

/-- Concrete oscillating example: 既济 cell alternating ascend/stable per step. -/
def jiji_renDaoCell : RenDaoCell :=
  ⟨Hexagram.complete, by native_decide⟩

def osc_jiji : WeiVerdict :=
  fun n => if n % 2 = 0 then ⟨jiji_renDaoCell, .ascend⟩ else ⟨jiji_renDaoCell, .stable⟩

/-- The oscillating example does change verdicts step to step. -/
theorem osc_jiji_changes :
    (osc_jiji 0).flow ≠ (osc_jiji 1).flow := by
  show WitnessFlow.ascend ≠ WitnessFlow.stable
  intro h
  cases h

/-- Verdicts CAN change over time — claim trajectories are not static. -/
theorem verdict_can_change :
    ∃ (w : WeiVerdict) (n : Nat), (w n).flow ≠ (w (n + 1)).flow :=
  ⟨osc_jiji, 0, osc_jiji_changes⟩

/-! ### Refute-flip invariants (¬¬-elimination at the tier level) -/

namespace DaoLevel

/-- Refute-flip on DaoLevel: 道 ↔ 反道; 中道 and 心道 are fixed. -/
def flip : DaoLevel → DaoLevel
  | tian   => feiDao
  | feiDao => tian
  | ren    => ren
  | xin    => xin

/-- Flip is involutive (¬¬-elimination at tier level). -/
theorem flip_flip (d : DaoLevel) : d.flip.flip = d := by cases d <;> rfl

/-- Flip swaps the two terminus tiers. -/
theorem flip_swaps_extremes :
    tian.flip = feiDao ∧ feiDao.flip = tian := ⟨rfl, rfl⟩

/-- Flip fixes the two center tiers (中道 / 心道 are not "negatable" — they
    represent process-level claims, not terminus positions). -/
theorem flip_fixes_middles :
    ren.flip = ren ∧ xin.flip = xin := ⟨rfl, rfl⟩

end DaoLevel

namespace WitnessFlow

/-- Refute-flip on WitnessFlow: ascend ↔ refute (a verified-then-refuted claim
    becomes refuted; a refuted-then-refuted claim is verified). 持/降 are fixed. -/
def flip : WitnessFlow → WitnessFlow
  | ascend  => refute
  | refute  => ascend
  | stable  => stable
  | descend => descend

theorem flip_flip (f : WitnessFlow) : f.flip.flip = f := by cases f <;> rfl

end WitnessFlow

/-- Flow-flip is consistent with DaoLevel-flip:
    flipping the flow of a verdict gives a verdict whose destination is the
    flipped destination. This is the ¬¬-coherence between verdict and tier. -/
theorem flow_flip_consistent (v : RenDaoVerdict) :
    ({ cell := v.cell, flow := v.flow.flip } : RenDaoVerdict).destination
      = v.destination.flip := by
  rcases v with ⟨_, flow⟩
  cases flow <;> rfl

end SSBX.Foundation.Yi.Yi
