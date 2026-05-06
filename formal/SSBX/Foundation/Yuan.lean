/-
# 元 → 多元 → 道 = 太极 = 大同

  Formalizes the chain (per user's 文言 statement):

    元 乃 爻 也, 乃 易 也, 乃 根, 乃 源, 乃 源头 也也,
    因此 原因, 因此 因果, 因此 多元 也,
    世界 多元, 为 道 也, 为 太极, 为 大同.

  Structural reading:

    元 = 爻        (definitional: Yuan := Yao)
    元 = 易        (carries the flip, 易 IS the bit's change-principle)
    元 = 根/源    (architectural: Yao is the leaf primitive, no type below)
    多元           (compositions of 元 = sequences/Hexagrams)
    道             (the totality space of 多元 of degree 6 — 64 hexagrams)
    太极           (the primitive that generates 两仪 — Yuan reflexively)
    大同           (the totality is closed under 易; diversity IS unity)

  The chain has three movements:
    1. 元 = 爻 = 易 = 根/源              (identifications of the foundation)
    2. 源 → 因 → 果 → 多元               (multiplicity emerges from origin)
    3. 多元 = 道 = 太极 = 大同           (the resulting totality is unity)
-/

import SSBX.Foundation.Yi

namespace SSBX.Foundation.Yuan

open SSBX.Foundation.Yi

/-! ## § 1 元 = 爻 -/

/-- 元 (yuán, the foundational unit). 元 IS 爻 — at the bottom of the hierarchy
    the primitive unit of generation IS the yao (yang/yin line). -/
abbrev Yuan : Type := Yao

/-- 元 = 爻 (definitional). -/
theorem yuan_eq_yao : Yuan = Yao := rfl

/-! ## § 2 元 = 易 — the primitive carries change

  《系辞》"生生之谓易". The 爻's defining feature is that it CAN flip.
  易 is not external to 元 — it IS 元's automorphism. -/

/-- 易 (yì) on 元: the flip operation (alias for `Yao.neg`). -/
def yi : Yuan → Yuan := Yao.neg

/-- 易 之 易 = id. The bit-flip is involutive — 易 carries no preferred direction. -/
theorem yi_involutive (y : Yuan) : yi (yi y) = y := Yao.neg_neg y

/-- 元 has exactly two values, witnessing 两仪 = the duality of yang/yin. -/
theorem yuan_two_values : ∀ y : Yuan, y = .yang ∨ y = .yin := by
  intro y; cases y
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- 易 swaps the two 元 values (no fixed point). -/
theorem yi_no_fixed_point (y : Yuan) : yi y ≠ y := by
  cases y <;> intro h <;> cases h

/-! ## § 3 元 = 根/源/源头

  Architectural commitment: `Yao` is the leaf inductive type — no primitive
  below it. Every higher structure (Trigram, Hexagram, hexagram-cell) has
  fields of type `Yao`. We witness this by reading the field types below;
  the compiler statically enforces that the hierarchy bottoms out at 元. -/

/-- Trigram's fields are all 元 (witness of "源" via field types). -/
example (t : Trigram) : Yuan := t.y1
example (t : Trigram) : Yuan := t.y2
example (t : Trigram) : Yuan := t.y3

/-- Hexagram's fields are all 元. Each yao position projects to 元. -/
example (h : Hexagram) : Yuan := h.y1
example (h : Hexagram) : Yuan := h.y6

/-! ## § 4 由 元 → 多元: composition gives multiplicity

  A single 元 is one bit; 多元 (many 元) emerges by composition. The canonical
  6-deep composition is `Hexagram` — already defined in `Foundation.Yi` and
  enumerated as `allHex` (64 elements). -/

/-- 多元: many 元 stacked. -/
abbrev DuoYuan : Type := List Yuan

/-- The 6-yao 多元 specialization is `Hexagram` (a structured 多元). -/
abbrev DuoYuan6 : Type := Hexagram

end SSBX.Foundation.Yuan

/-- A Hexagram, once unpacked, IS a 6-tuple of 元. Defined in
    `Yi.Hexagram` namespace for dot notation. -/
def SSBX.Foundation.Yi.Hexagram.toDuoYuan (h : SSBX.Foundation.Yi.Hexagram) :
    List SSBX.Foundation.Yi.Yao :=
  [h.y1, h.y2, h.y3, h.y4, h.y5, h.y6]

namespace SSBX.Foundation.Yuan

open SSBX.Foundation.Yi

theorem hex_toDuoYuan_length (h : Hexagram) : h.toDuoYuan.length = 6 := rfl

/-- 因/果 chains: a 多元 is read causally as a sequence of 元-states.
    The simplest causal arrow: each step's `yi` produces the next state. -/
def causalChain : Nat → Yuan → List Yuan
  | 0, y => [y]
  | n+1, y => y :: causalChain n (yi y)

theorem causalChain_length (n : Nat) (y : Yuan) :
    (causalChain n y).length = n + 1 := by
  induction n generalizing y with
  | zero => rfl
  | succ k ih => simp [causalChain, ih]

/-! ## § 5 多元 = 道

  The space of all 多元 (specifically: 6-yao Hexagrams) IS 道 — the totality. -/

/-- 道: the 64-Hexagram totality (= the canonical 多元-space).
    Use `abbrev` so membership reduces transparently. -/
abbrev Dao : List Hexagram := Hexagram.allHex

/-- 道 has 64 elements (64 distinct 多元 of degree 6). -/
theorem dao_count : Dao.length = 64 := Hexagram.allHex_count

end SSBX.Foundation.Yuan

/-- Bool-valued membership in 道 (avoids needing a `Decidable (· ∈ ·)` instance).
    Defined in `Yi.Hexagram` namespace for dot notation. -/
def SSBX.Foundation.Yi.Hexagram.inDao (h : SSBX.Foundation.Yi.Hexagram) : Bool :=
  SSBX.Foundation.Yuan.Dao.contains h

namespace SSBX.Foundation.Yuan

open SSBX.Foundation.Yi

/-- Every Hexagram passes the Bool-membership check (the 64-enumeration is total). -/
theorem hex_in_dao_bool (h : Hexagram) : h.inDao = true := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    <;> native_decide

/-! ## § 6 道 = 太极: the primitive reflexively generates the totality

  《系辞》"易有太极, 是生两仪, 两仪生四象, 四象生八卦".
  太极 IS 元 (the primitive that contains the duality), unfolded n times
  produces 2ⁿ states. At n=6 we recover the 64-hex totality = 道. -/

/-- 太极 (tài jí): the supreme ultimate. Identified with 元 (the duality-carrier). -/
abbrev TaiJi : Type := Yuan

/-- 太极 IS 元 (definitional). -/
theorem taiji_eq_yuan : TaiJi = Yuan := rfl

/-- 太极 → 两仪: the two yao values are TaiJi unfolded once. -/
def liangYi : List TaiJi := [.yang, .yin]

theorem liangYi_count : liangYi.length = 2 := rfl

/-- TaiJi unfolded n times yields 2ⁿ length-n yao sequences. -/
def taijiUnfold : Nat → List (List Yuan)
  | 0 => [[]]
  | n+1 => taijiUnfold n |>.flatMap fun s => [s ++ [.yang], s ++ [.yin]]

theorem taijiUnfold_0 : taijiUnfold 0 = [[]] := rfl
theorem taijiUnfold_1 : (taijiUnfold 1).length = 2 := by native_decide
theorem taijiUnfold_2 : (taijiUnfold 2).length = 4 := by native_decide      -- 四象
theorem taijiUnfold_3 : (taijiUnfold 3).length = 8 := by native_decide      -- 八卦
theorem taijiUnfold_6 : (taijiUnfold 6).length = 64 := by native_decide     -- 64卦 = 道

/-- 太极 之 6-unfolding ≅ 道 in cardinality (64 = |Dao|). -/
theorem taiji_unfolds_to_dao : (taijiUnfold 6).length = Dao.length := by
  rw [taijiUnfold_6, dao_count]

/-! ## § 7 道 = 大同: closure under 易 — diversity IS unity

  《礼运》"大道之行也, 天下为公". Formal version: 道 is closed under
  every transformation. Every 易-act on a 多元 lands back in 道.
  Diversity (the 64 distinct hexagrams) is unity (a single closed orbit space). -/

/-- 易 lifted to Hexagram: yao-wise flip. This is `Hexagram.cuo`. -/
def yiHex : Hexagram → Hexagram := Hexagram.cuo

/-- 易 (hex) is involutive — same as `cuo_cuo`. -/
theorem yiHex_involutive (h : Hexagram) : yiHex (yiHex h) = h := Hexagram.cuo_cuo h

/-- 大同 (dà tóng): 道 is closed under 易 — diversity reduces to a single
    closed transformation-space. Every transformed hex lands in 道. -/
theorem daTong (h : Hexagram) : (yiHex h).inDao = true := hex_in_dao_bool (yiHex h)

/-- Stronger 大同: closure under 综 too. -/
theorem daTong_zong (h : Hexagram) : h.zong.inDao = true := hex_in_dao_bool h.zong

/-- Strongest 大同: closure under any V_4 element (cuo, zong, cuoZong, id).
    The whole Klein-4 group action stays in 道. -/
theorem daTong_v4 (h : Hexagram) :
    h.cuo.inDao = true ∧ h.zong.inDao = true ∧
    h.cuoZong.inDao = true ∧ h.inDao = true :=
  ⟨hex_in_dao_bool h.cuo, hex_in_dao_bool h.zong,
   hex_in_dao_bool h.cuoZong, hex_in_dao_bool h⟩

/-- 大同 by enumeration: every Hexagram (without precondition) is in 道.
    Diversity (64 distinct elements) and unity (one closed space) coincide. -/
theorem daTong_total (h : Hexagram) : h.inDao = true := hex_in_dao_bool h

/-! ## § 8 The chain as a single statement

  元 (= 爻 = 易 = 根/源) → 多元 → 道 = 太极 = 大同.

  At the type level: the foundational primitive 元 (with its automorphism 易)
  generates, via 6-fold unfolding, a 64-element totality 道 that is
  V_4-closed (大同) and equals 太极's 6-unfolding. -/

/-- The full chain as a conjunction of structural facts. -/
theorem chain_yuan_to_datong :
    -- 元 = 爻
    (Yuan = Yao) ∧
    -- 元 carries 易 (involutive, no fixed point)
    (∀ y : Yuan, yi (yi y) = y ∧ yi y ≠ y) ∧
    -- 太极 = 元
    (TaiJi = Yuan) ∧
    -- 太极's 6-unfolding has the same cardinality as 道
    ((taijiUnfold 6).length = Dao.length) ∧
    -- 道 has 64 elements
    (Dao.length = 64) ∧
    -- 大同: 道 is V_4-closed (Bool membership)
    (∀ h : Hexagram, h.cuo.inDao = true ∧ h.zong.inDao = true) := by
  refine ⟨rfl, ?_, rfl, taiji_unfolds_to_dao, dao_count, ?_⟩
  · intro y
    exact ⟨yi_involutive y, yi_no_fixed_point y⟩
  · intro h
    exact ⟨hex_in_dao_bool h.cuo, hex_in_dao_bool h.zong⟩

end SSBX.Foundation.Yuan
