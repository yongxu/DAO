/-
# ShuSuan — 数算 · 项目自字之 ℕ 算术

Companion document: `义理/数与算术 · 从元到数.md`

This file formalizes the **数与算术** 衍 file's mapping from project single-character
operators (元 / 一 / 续 / 合 / 损 / 重 / 除 / 反 / 空) to standard Nat / Int arithmetic,
plus a few project-specific theorems:

  § 1   项目单字 (project aliases): one, zero, successor, combine, decrement, multiply
  § 2   Peano lemmas with project names (via Nat lemmas)
  § 3   损 ⊣ 合 之 Galois adjoint（截断减之伴随）
  § 4   |Trigram| = 2³ + |Hexagram| = 2⁶ via project multiply (重)
  § 5   (Z/2)² ≄ Z/4：群序论证之 Lean 形式

## 道理二分立场
This file is entirely **理层** (object-theory): defines and proves project-specific
arithmetic. The use of `Nat` / `Int` from Lean's stdlib is **道层** support
(the meta-theory provides arithmetic ground). The proofs go through standard Nat lemmas.

The single-axiom-free, native-decide-free goal is upheld throughout.
-/
import SSBX.Foundation.Bagua.BaguaAlgebra
import SSBX.Foundation.Yi.Yi

namespace SSBX.Foundation.Eight.ShuSuan

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 1 项目单字别名 -/

/-- **数 (Shu)**：项目自然数类型，等同于 Lean 内置 `Nat`。 -/
abbrev Shu : Type := Nat

/-- **空 (zero)**：零；Empty 之 cardinality 类同。 -/
def zero : Shu := 0

/-- **一 (one)**：壹；Unit 之 cardinality 类同。 -/
def one : Shu := 1

/-- **生 (successor)**：后继 succ；与 `Sheng.step` 同名同义。 -/
def successor : Shu → Shu := Nat.succ

/-- **合 (combine)**：加 +；项目主用字。 -/
def combine (a b : Shu) : Shu := a + b

/-- **损 (decrement)**：截断减 ∸（ℕ 内不可逆）。 -/
def decrement (a b : Shu) : Shu := a - b

/-- **重 (multiply)**：乘 ×；与 G 之"八卦相重"同字异作用。 -/
def multiply (a b : Shu) : Shu := a * b

/-- **反 (fan)**：在 ℤ 上 negate；ℕ 截断版退化为 trivial。 -/
def negate (a : Int) : Int := -a

/-! ## § 2 Peano 性质（以项目单字证）

为避免与 Lean stdlib 之 `Sum`/`Mul` 之 `⊕`/`⊗` notation 冲突，
本节内皆用函数式风格 `combine a b`/`multiply a b` 等，不引入新 infix。 -/

theorem he_kong (a : Shu) : combine a zero = a := Nat.add_zero a

theorem kong_he (a : Shu) : combine zero a = a := Nat.zero_add a

theorem he_sheng (a b : Shu) : combine a (successor b) = successor (combine a b) := rfl

theorem sheng_he (a b : Shu) : combine (successor a) b = successor (combine a b) := by
  unfold successor combine
  exact Nat.succ_add a b

theorem he_comm (a b : Shu) : combine a b = combine b a := Nat.add_comm a b

theorem he_assoc (a b c : Shu) : combine (combine a b) c = combine a (combine b c) := Nat.add_assoc a b c

theorem chong_kong (a : Shu) : multiply a zero = zero := Nat.mul_zero a

theorem kong_chong (a : Shu) : multiply zero a = zero := Nat.zero_mul a

theorem chong_yi (a : Shu) : multiply a one = a := Nat.mul_one a

theorem one_multiply (a : Shu) : multiply one a = a := Nat.one_mul a

theorem chong_comm (a b : Shu) : multiply a b = multiply b a := Nat.mul_comm a b

theorem chong_assoc (a b c : Shu) : multiply (multiply a b) c = multiply a (multiply b c) :=
  Nat.mul_assoc a b c

theorem chong_distrib_he (a b c : Shu) : multiply a (combine b c) = combine (multiply a b) (multiply a c) :=
  Nat.mul_add a b c

theorem he_chong_distrib (a b c : Shu) : multiply (combine a b) c = combine (multiply a c) (multiply b c) :=
  Nat.add_mul a b c

theorem sun_kong (a : Shu) : decrement a zero = a := Nat.sub_zero a

theorem kong_sun (a : Shu) : decrement zero a = zero := Nat.zero_sub a

theorem sun_self (a : Shu) : decrement a a = zero := Nat.sub_self a

/-! ## § 3 损 ⊣ 合 之 Galois 伴随

数与算术.md §6 之核心结果：截断减作为加之 left adjoint。 -/

/-- **Galois 连接**：`decrement a b ≤ c ⟺ a ≤ combine c b`. -/
theorem galois_sun_he (a b c : Shu) : decrement a b ≤ c ↔ a ≤ combine c b := by
  unfold decrement combine
  exact Nat.sub_le_iff_le_add

/-- **逆方向恒等**：decrement (combine a b) b = a 永真. -/
theorem he_sun_cancel (a b : Shu) : decrement (combine a b) b = a := by
  simp only [combine, decrement]
  exact Nat.add_sub_cancel a b

/-- **顺方向恒等**：当 b ≤ a 时，combine (decrement a b) b = a。 -/
theorem sun_he_cancel (a b : Shu) (h : b ≤ a) : combine (decrement a b) b = a := by
  simp only [combine, decrement]
  exact Nat.sub_add_cancel h

/-- **伴随之 unit**：a ≤ decrement (combine a b) b（保下界）。 -/
theorem he_sun_le (a b : Shu) : a ≤ decrement (combine a b) b := by
  rw [he_sun_cancel]
  exact Nat.le.refl

/-! ## § 4 卡数定理：|Trigram| = 2³，|Hexagram| = 2⁶ -/

/-- **|Trigram| = 8 = 2 × 2 × 2**：八卦之卡数定理（用项目 multiply）。 -/
theorem trigram_card : Trigram.all.length = multiply (multiply 2 2) 2 := by
  show Trigram.all.length = (2 * 2) * 2
  decide

/-- **|Hexagram| = 64 = 2⁶**：六十四卦之卡数定理（用项目 multiply）。 -/
theorem hexagram_card :
    Hexagram.allHex.length = multiply (multiply (multiply (multiply (multiply 2 2) 2) 2) 2) 2 := by
  show Hexagram.allHex.length = ((((2 * 2) * 2) * 2) * 2) * 2
  decide

/-- **multiply 三次 2 = 8**：项目 multiply 之具体值。 -/
theorem chong_2_3 : multiply (multiply (2 : Shu) 2) 2 = 8 := rfl

/-- **multiply 六次 2 = 64**：64 卦之 cardinality。 -/
theorem chong_2_6 :
    multiply (multiply (multiply (multiply (multiply (2 : Shu) 2) 2) 2) 2) 2 = 64 := rfl

/-! ## § 5 (Z/2)² ≄ Z/4：群序论证

数与算术.md §13 之核心非平凡结果。
策略：双倍每个元素——
  - 在 (Bool × Bool) 上，双倍 (XOR-self) = (false, false) for all.
  - 在 Fin 4 上，双倍 1 = 2 ≠ 0.
故任何同构皆失败——element orders 不匹配。 -/

/-- (Z/2)² 之元素：每个元 XOR 自己 = identity。即所有非零元 order ≤ 2。 -/
theorem z2sq_double_id (x : Bool × Bool) :
    (xor x.1 x.1, xor x.2 x.2) = (false, false) := by
  cases x; simp

/-- Z/4 之元素 1：1 + 1 = 2 ≠ 0（mod 4）。即 1 之 order > 2。 -/
theorem z4_double_one : ((1 : Fin 4) + 1) ≠ 0 := by decide

/-- 满射性（不依赖 Mathlib 之 Function.Bijective）。 -/
def Surjective {α β : Type} (f : α → β) : Prop := ∀ y, ∃ x, f x = y

/-- **(Z/2)² 与 Z/4 之非同构**（核心非平凡结果）：

不存在保 0 + 加法之满射 f : (Bool × Bool) → Fin 4。

证明梗概：若 f 保 doubling，则对每 x：
  f(x XOR-self) = f(x) + f(x)
左侧 = f((false, false)) = 0（保 0）；
故对每 x，f(x) + f(x) = 0。但 Fin 4 中 (1 : Fin 4) + (1 : Fin 4) = 2 ≠ 0，
故无 x 可映到 1——满射矛盾。 -/
theorem z2sq_ne_z4 :
    ¬ ∃ f : (Bool × Bool) → Fin 4,
        Surjective f ∧
        f (false, false) = 0 ∧
        ∀ x : Bool × Bool, f (xor x.1 x.1, xor x.2 x.2) = f x + f x := by
  intro ⟨f, hsurj, hzero, hdouble⟩
  -- 对所有 x，f x + f x = 0
  have h_double_zero : ∀ x : Bool × Bool, f x + f x = 0 := by
    intro x
    have := hdouble x
    rw [z2sq_double_id x] at this
    rw [hzero] at this
    exact this.symm
  -- 但 1 ∈ Fin 4 必有原像 x₀
  obtain ⟨x₀, hx₀⟩ := hsurj (1 : Fin 4)
  -- 故 1 + 1 = f x₀ + f x₀ = 0，矛盾 z4_double_one
  have : (1 : Fin 4) + 1 = 0 := by rw [← hx₀]; exact h_double_zero x₀
  exact z4_double_one this

/-! ## § 6 与 BaguaAlgebra Sheng 之桥

Sheng inductive 之深度 n 等同于 List Yao 长度 n，
其卡数依 multiply 累乘 = 2ⁿ。BaguaAlgebra 已证 `Sheng 3 ≃ Trigram`
（`toTrigram_ofTrigram` + `ofTrigram_toTrigram`）。
此处仅用项目 multiply 字面陈述卡数定理。 -/

/-- **Sheng 之 round-trip on Trigram** —— 仅 wrap BaguaAlgebra 既有定理。 -/
theorem sheng_trigram_roundtrip (t : Trigram) :
    Sheng.toTrigram (Sheng.ofTrigram t) = t :=
  Sheng.toTrigram_ofTrigram t

theorem trigram_sheng_roundtrip (s : Sheng 3) :
    Sheng.ofTrigram (Sheng.toTrigram s) = s :=
  Sheng.ofTrigram_toTrigram s

/-- **卡数定理之单字陈述**：8 = multiply 三次 2。 -/
theorem trigram_card_chong : Trigram.all.length = multiply (multiply 2 2) 2 :=
  trigram_card

/-! ## § 7 公开摘要 -/

/-- **数算总摘要**：项目自字之 ℕ 算术性质 + 关键非平凡结果。 -/
theorem shusuan_summary :
    -- (1) 合 (combine) 之交换 + 结合 + 单位
    (∀ a b : Shu, combine a b = combine b a)
    ∧ (∀ a b c : Shu, combine (combine a b) c = combine a (combine b c))
    ∧ (∀ a : Shu, combine a zero = a)
    -- (2) 重 (multiply) 之交换 + 结合 + 分配
    ∧ (∀ a b : Shu, multiply a b = multiply b a)
    ∧ (∀ a b c : Shu, multiply a (combine b c) = combine (multiply a b) (multiply a c))
    -- (3) 损 ⊣ 合 之 Galois
    ∧ (∀ a b c : Shu, decrement a b ≤ c ↔ a ≤ combine c b)
    -- (4) 八卦卡数定理
    ∧ (Trigram.all.length = multiply (multiply (2 : Shu) 2) 2)
    -- (5) (Z/2)² ≄ Z/4
    ∧ (¬ ∃ f : (Bool × Bool) → Fin 4,
          Surjective f ∧ f (false, false) = 0 ∧
          ∀ x, f (xor x.1 x.1, xor x.2 x.2) = f x + f x) :=
  ⟨he_comm, he_assoc, he_kong,
   chong_comm, chong_distrib_he,
   galois_sun_he,
   trigram_card,
   z2sq_ne_z4⟩

end SSBX.Foundation.Eight.ShuSuan
