/-
# Foundation.Atlas.Yi.Bagua — the 8 trigram names on R 3

Per `wen-algebra` v0.6 §9 and `v4-foundation` v0.5 §15:

    八卦 : 8 named elements of `R 3 = Fin 3 → Bool`

Convention (project standard, `o = false = yang`, `x = true = yin`):

| Name (Pinyin) | Han | Symbol | Bit pattern (y1, y2, y3) | English |
|---------------|-----|--------|---------------------------|---------|
| `qian`        | 乾  | ☰      | (o, o, o) = all yang      | heaven  |
| `dui`         | 兌  | ☱      | (o, o, x)                 | lake    |
| `li`          | 離  | ☲      | (o, x, o)                 | fire    |
| `zhen`        | 震  | ☳      | (o, x, x)                 | thunder |
| `xun`         | 巽  | ☴      | (x, o, o)                 | wind    |
| `kan`         | 坎  | ☵      | (x, o, x)                 | water   |
| `gen`         | 艮  | ☶      | (x, x, o)                 | mountain|
| `kun`         | 坤  | ☷      | (x, x, x) = all yin       | earth   |

Each name is a `@[match_pattern] def : Trigram` so existing pattern
matches `| .qian => ...` continue to work.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §1.4 (R 3 readings).
* `v4-foundation.md` v0.5 §15.3 (Bagua binding).
-/

import SSBX.Foundation.Atlas.Yi.Names

namespace SSBX.Foundation.Atlas.Yi

open SSBX.Foundation.R
open Yao (yang yin)

namespace Trigram

/-! ## § 1 The 8 named trigrams -/

/-- ☰ 乾 (qián) — all yang.  "Heaven". -/
@[match_pattern] def qian : Trigram := mk yang yang yang

/-- ☱ 兌 (duì) — (yang, yang, yin).  "Lake". -/
@[match_pattern] def dui : Trigram := mk yang yang yin

/-- ☲ 離 (lí) — (yang, yin, yang).  "Fire". -/
@[match_pattern] def li : Trigram := mk yang yin yang

/-- ☳ 震 (zhèn) — (yang, yin, yin).  "Thunder". -/
@[match_pattern] def zhen : Trigram := mk yang yin yin

/-- ☴ 巽 (xùn) — (yin, yang, yang).  "Wind". -/
@[match_pattern] def xun : Trigram := mk yin yang yang

/-- ☵ 坎 (kǎn) — (yin, yang, yin).  "Water". -/
@[match_pattern] def kan : Trigram := mk yin yang yin

/-- ☶ 艮 (gèn) — (yin, yin, yang).  "Mountain". -/
@[match_pattern] def gen : Trigram := mk yin yin yang

/-- ☷ 坤 (kūn) — all yin.  "Earth". -/
@[match_pattern] def kun : Trigram := mk yin yin yin

/-- The 8 trigrams listed in the standard Wén Wáng (King Wen) order. -/
def bagua : List Trigram :=
  [qian, dui, li, zhen, xun, kan, gen, kun]

/-- |八卦| = 8. -/
theorem bagua_length : bagua.length = 8 := rfl

/-! ## § 2 Distinctness of the 8 trigrams -/

theorem qian_ne_dui : (qian : Trigram) ≠ dui := by
  intro h; have := congrFun h ⟨2, by decide⟩; cases this

theorem qian_ne_kun : (qian : Trigram) ≠ kun := by
  intro h; have := congrFun h ⟨0, by decide⟩; cases this

/-- Encode a trigram as a 3-bit `Nat` for use in distinctness proofs. -/
def toNat (t : Trigram) : Nat :=
  (if t.y1 then 4 else 0) + (if t.y2 then 2 else 0) + (if t.y3 then 1 else 0)

@[simp] theorem toNat_qian : toNat qian = 0 := rfl
@[simp] theorem toNat_dui  : toNat dui  = 1 := rfl
@[simp] theorem toNat_li   : toNat li   = 2 := rfl
@[simp] theorem toNat_zhen : toNat zhen = 3 := rfl
@[simp] theorem toNat_xun  : toNat xun  = 4 := rfl
@[simp] theorem toNat_kan  : toNat kan  = 5 := rfl
@[simp] theorem toNat_gen  : toNat gen  = 6 := rfl
@[simp] theorem toNat_kun  : toNat kun  = 7 := rfl

/-- The 8 named trigrams have 8 distinct `toNat` values. -/
theorem bagua_nodup : bagua.Nodup := by
  have : (bagua.map toNat).Nodup := by
    show ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).Nodup
    decide
  exact List.Nodup.of_map _ this

/-! ## § 3 Coverage: every `R 3` is one of the 8 trigrams -/

/-- Every trigram is in `bagua`. -/
theorem mem_bagua (t : Trigram) : t ∈ bagua := by
  have h0 := t.y1
  have h1 := t.y2
  have h2 := t.y3
  have ht : t = mk t.y1 t.y2 t.y3 := by
    apply ext <;> rfl
  rw [ht]
  unfold bagua
  rcases t.y1 with _ | _ <;> rcases t.y2 with _ | _ <;> rcases t.y3 with _ | _ <;>
    simp [qian, dui, li, zhen, xun, kan, gen, kun, yang, yin]

/-! ## § 4 Legacy English name aliases

These aliases preserve the English-language column from the bagua name
table so legacy consumers can refer to a trigram by its translated noun.
Each alias is a `def`-level synonym — the underlying value is the
canonical pinyin entry. -/

/-- ☰ 乾 — "heaven" alias of `qian`. -/
def heaven : Trigram := qian

/-- ☱ 兌 — "lake" alias of `dui`. -/
def lake : Trigram := dui

/-- ☲ 離 — "fire" alias of `li`. -/
def fire : Trigram := li

/-- ☳ 震 — "thunder" alias of `zhen`. -/
def thunder : Trigram := zhen

/-- ☴ 巽 — "wind" alias of `xun`. -/
def wind : Trigram := xun

/-- ☵ 坎 — "water" alias of `kan`. -/
def water : Trigram := kan

/-- ☶ 艮 — "mountain" alias of `gen`. -/
def mountain : Trigram := gen

/-- ☷ 坤 — "earth" alias of `kun`. -/
def earth : Trigram := kun

end Trigram

end SSBX.Foundation.Atlas.Yi
