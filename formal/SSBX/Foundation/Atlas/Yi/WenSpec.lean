/-
# Foundation.Atlas.Yi.WenSpec — Wenyan token specification on R-Family Atlas

This is the **clean-stack port** of `Atlas/Yi/Classical/Computation/BaguaWenSpec.lean`
onto the new `Atlas/Yi/` overlay (types live in `Names.lean`, `Bagua.lean`,
`Hexagrams.lean`, `ShiV4.lean`).  No legacy `Yi.Yi` or `Bagua.BaguaTuring`
import — everything is expressed against the R-Family atlas.

The 23 reserved tokens carry the same `baguaWen` doctrine (per
`notes/baguaWen-spec.md`):

  · `primaryTokens`  — 12 verb tokens (the core wenyan action vocabulary)
  · `shiTokens`      —  4 时态 tokens (V₄: 道 / 已 / 今 / 未)
  · `yaoTokens`      —  6 爻位 tokens (初爻 … 上爻)
  · `atKeyword`      —  「至」 (jump-target marker)

Total = 12 + 4 + 6 + 1 = 23 tokens.  All length / nodup / coverage
lemmas are verified by `native_decide`.

This file also ports the `JianMode` 8-element 间生论 ontological mode
classification and the `Trigram.jianMode` selector, restated against
the R-Family `Trigram` (= `R 3`) of `Atlas/Yi/Names.lean`.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9 (Atlas separation).
* `v4-foundation.md` v0.5 §15 (external traditions), §4 (Shi V₄).
* `notes/baguaWen-spec.md` (frozen 22→23 reserved set).
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Bagua
import SSBX.Foundation.Atlas.Yi.ShiV4

namespace SSBX.Foundation.Atlas.Yi.WenSpec

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1  12 主字 (verb tokens)

The 12 canonical wenyan verb tokens that ground the `baguaWen` L0
internal kernel.  The order is the legacy order from `BaguaWenSpec`
(aligned to the 12 `YiInstr` constructors of the classical stack).
On the new stack these 12 strings stand on their own as the reserved
verb vocabulary; no constructor binding is enforced here.  -/

/-- 12 主字之表（去重，序与 legacy YiInstr tag 对齐）。 -/
def primaryTokens : List String :=
  ["不动", "设时", "翻爻", "互", "错", "综",
   "比爻", "比时", "跳", "推", "取", "终"]

theorem primaryTokens_length : primaryTokens.length = 12 := by native_decide

theorem primaryTokens_nodup : primaryTokens.Nodup := by native_decide

/-! ## § 2  4 时态 tokens (V₄ Klein)

The 4 时态 names on `Shi = R 2` (V₄ Klein group).  The `道` token
denotes the V₄ identity (永真 / cross-temporal anchor). -/

/-- Wenyan token for each named V₄ element.  Lifted from `ShiV4.lean`. -/
def shiToken (s : Shi) : String :=
  if s = Shi.dao then "道"
  else if s = Shi.ji  then "已"
  else if s = Shi.jin then "今"
  else "未"  -- s = Shi.wei

/-- 时态四字 (V₄). -/
def shiTokens : List String := ["道", "已", "今", "未"]

theorem shiTokens_length : shiTokens.length = 4 := by native_decide

theorem shiTokens_nodup : shiTokens.Nodup := by native_decide

/-! ## § 3  6 爻位 tokens (line positions) -/

/-- 爻位六字。 -/
def yaoTokens : List String :=
  ["初爻", "二爻", "三爻", "四爻", "五爻", "上爻"]

theorem yaoTokens_length : yaoTokens.length = 6 := by native_decide

theorem yaoTokens_nodup : yaoTokens.Nodup := by native_decide

/-! ## § 4  关键字与全保留集 -/

/-- 跳转目标关键字。 -/
def atKeyword : String := "至"

/-- Predicate: does `s` equal the at-keyword 「至」? -/
def isAtKeyword (s : String) : Bool := s = atKeyword

@[simp] theorem isAtKeyword_atKeyword : isAtKeyword atKeyword = true := by
  decide

@[simp] theorem isAtKeyword_iff (s : String) :
    isAtKeyword s = true ↔ s = atKeyword := by
  unfold isAtKeyword
  exact decide_eq_true_iff

/-- 全部保留 token（不含数词）。Parser 遇任何不在此表的 CJK token 即拒。

    23 = 12 主字 + 4 时态 (V₄) + 6 爻位 + 1 关键字「至」. -/
def reservedTokens : List String :=
  primaryTokens ++ shiTokens ++ yaoTokens ++ [atKeyword]

theorem reservedTokens_length : reservedTokens.length = 23 := by native_decide

theorem reservedTokens_nodup : reservedTokens.Nodup := by native_decide

/-! ## § 5  Coverage lemmas

`shiToken` is total on the V₄ named elements; lift to membership. -/

/-- `shiToken` of any of the 4 named V₄ elements lies in `shiTokens`. -/
theorem shiToken_dao_mem : shiToken Shi.dao ∈ shiTokens := by
  simp [shiToken, shiTokens]

theorem shiToken_ji_mem : shiToken Shi.ji ∈ shiTokens := by
  unfold shiToken
  have : Shi.ji ≠ Shi.dao := by
    intro h; have := congrFun h ⟨0, by decide⟩; cases this
  simp [this, shiTokens]

theorem shiToken_jin_mem : shiToken Shi.jin ∈ shiTokens := by
  unfold shiToken
  have h1 : Shi.jin ≠ Shi.dao := by
    intro h; have := congrFun h ⟨0, by decide⟩; cases this
  have h2 : Shi.jin ≠ Shi.ji := by
    intro h; have := congrFun h ⟨1, by decide⟩; cases this
  simp [h1, h2, shiTokens]

theorem shiToken_wei_mem : shiToken Shi.wei ∈ shiTokens := by
  unfold shiToken
  have h1 : Shi.wei ≠ Shi.dao := by
    intro h; have := congrFun h ⟨1, by decide⟩; cases this
  have h2 : Shi.wei ≠ Shi.ji := by
    intro h; have := congrFun h ⟨0, by decide⟩; cases this
  have h3 : Shi.wei ≠ Shi.jin := by
    intro h; have := congrFun h ⟨0, by decide⟩; cases this
  simp [h1, h2, h3, shiTokens]

/-! ## § 6  数词范围 -/

/-- 数词上界 (与 Hexagram 索引共域：1..64). -/
def maxNumeral : Nat := 64

theorem maxNumeral_eq : maxNumeral = 64 := rfl

/-! ## § 7  JianMode — 间生论 ontological mode (8 atoms)

  Per `Classical/Core/Yi.lean` §11, the 8 trigrams admit an ontological
  reading:

    乾 ☰ 健 ↔ 续/生/sheng    (continuation, generation)
    坤 ☷ 顺 ↔ 受/成/shou     (reception, form-completion)
    震 ☳ 动 ↔ 元-几/yuan     (initial motion, trace)
    巽 ☴ 入 ↔ 因-渗/shen     (cause, penetration)
    坎 ☵ 陷 ↔ 塞/sai         (blockage, obstruction)
    离 ☲ 丽 ↔ 显-心/xian     (manifestation, heart)
    艮 ☶ 止 ↔ 聚-形/ju       (gathering, form-fix)
    兑 ☱ 悦 ↔ 开-通-美/kai   (opening, flow, beauty)

  This is a bijection — 8 trigrams ↔ 8 modes. -/

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
  | sheng => Trigram.qian
  | shou  => Trigram.kun
  | yuan  => Trigram.zhen
  | shen  => Trigram.xun
  | sai   => Trigram.kan
  | xian  => Trigram.li
  | ju    => Trigram.gen
  | kai   => Trigram.dui

/-- The 8 modes in canonical order. -/
def all : List JianMode := [sheng, shou, yuan, shen, sai, xian, ju, kai]

theorem all_length : all.length = 8 := rfl

/-- Wenyan token for each mode (pinyin form; an L1 reading aid). -/
def token : JianMode → String
  | sheng => "生"
  | shou  => "受"
  | yuan  => "元"
  | shen  => "渗"
  | sai   => "塞"
  | xian  => "显"
  | ju    => "聚"
  | kai   => "开"

end JianMode

/-! ## § 8  `jianMode` selector — Trigram → JianMode

  The selector reads each named trigram into its ontological mode.
  On the 8 named trigrams this is a complete bijection.

  Since `Trigram = Fin 3 → Bool` is a function type (not a structure),
  we route the selector through the 3-bit `toNat` encoding (which
  delivers a `Fin 8` discriminant). -/

/-- 间生论 mode of a trigram via its 3-bit `toNat` encoding.
    The pattern matches use the `Bagua.toNat` table:
      qian=0, dui=1, li=2, zhen=3, xun=4, kan=5, gen=6, kun=7. -/
def jianMode (t : Trigram) : JianMode :=
  match t.toNat with
  | 0 => .sheng  -- qian
  | 1 => .kai    -- dui
  | 2 => .xian   -- li
  | 3 => .yuan   -- zhen
  | 4 => .shen   -- xun
  | 5 => .sai    -- kan
  | 6 => .ju     -- gen
  | _ => .shou   -- kun (toNat = 7) and unreachable defaults

/-! ### Per-trigram mode -/

theorem qian_jianMode : jianMode Trigram.qian = .sheng := rfl
theorem dui_jianMode  : jianMode Trigram.dui  = .kai   := rfl
theorem li_jianMode   : jianMode Trigram.li   = .xian  := rfl
theorem zhen_jianMode : jianMode Trigram.zhen = .yuan  := rfl
theorem xun_jianMode  : jianMode Trigram.xun  = .shen  := rfl
theorem kan_jianMode  : jianMode Trigram.kan  = .sai   := rfl
theorem gen_jianMode  : jianMode Trigram.gen  = .ju    := rfl
theorem kun_jianMode  : jianMode Trigram.kun  = .shou  := rfl

/-! ### Round-trip lemma: left-inverse on JianMode -/

/-- Every mode's trigram round-trips through `jianMode`. -/
theorem toTrigram_jianMode (m : JianMode) : jianMode m.toTrigram = m := by
  cases m <;> rfl

end SSBX.Foundation.Atlas.Yi.WenSpec
