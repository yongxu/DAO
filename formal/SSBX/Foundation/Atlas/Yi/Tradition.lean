/-
# Foundation.Atlas.Yi.Tradition — classical named tradition values on R-Family

Per `wen-algebra` v0.6 §9 (Atlas separation) and `v4-foundation` v0.5
§15 (external traditions), this module ports the classical named
tradition values from `Atlas/Yi/Classical/Core/Yi.lean` onto the
R-Family carriers introduced in `Atlas/Yi/Names.lean`:

    Yao      ≃ Bool         = R 1
    Trigram  ≃ Fin 3 → Bool = R 3
    Hexagram ≃ Fin 6 → Bool = R 6
    Shi (V₄) ≃ Fin 2 → Bool = R 2

The traditions ported here:

* `DaoLevel`  (4 cases: 天/人/心/反道)        — encoded as `R 2`.
* `SanCai`    (三才, 3 cases: 天/人/地)        — encoded as `Fin 3`.
* `SanXing`   (三性, 3 cases, Yogācāra)       — encoded as `Fin 3`.
* `SanShen`   (三身, 3 cases, Buddhist)       — encoded as `Fin 3`.
* `SanZhi`    (三知, 3 cases, Confucius)       — encoded as `Fin 3`.
* `SanBao`    (三宝, 3 cases, Daoist)         — encoded as `Fin 3`.
* `SanDi`     (三谛, 3 cases, Tiantai)        — encoded as `Fin 3`.
* `JianMode`  (间生论, 8 cases on bagua)       — encoded as `Trigram = R 3`.

Each classical `inductive` becomes an `abbrev` over a finite R-Family
carrier; the constructors become `@[match_pattern] def`s so that
pattern-matching `| .tian => …` continues to work for the `Fin n`-
backed traditions, and `R N` traditions get plain `def` constants
plus a `DecidableEq`-driven inverse.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9 (Atlas separation).
* `v4-foundation.md` v0.5 §15 (external-tradition bindings).
* `Atlas/Yi/Classical/Core/Yi.lean` §13–§14 (classical source).
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Bagua

namespace SSBX.Foundation.Atlas.Yi.Tradition

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 DaoLevel — 四道层级 on `R 2`

  Four levels (天/人/心/反道); encode on `R 2` using the V₄ bit layout:

    (false, false) = .tian    (天道 / 上道, objective)
    (true,  false) = .ren     (人道 / 中道, witness layer)
    (true,  true)  = .xin     (心道 / 下道, subjective)
    (false, true)  = .feiDao  (反道 / 邪道, refuted)
-/

/-- 道层级 (DaoLevel): the four-level partition of 道. -/
abbrev DaoLevel : Type := R 2

namespace DaoLevel

/-- 天道 / 上道 — objective, "in 道". -/
def tian : DaoLevel := fun _ => false

/-- 人道 / 中道 — mediating, witness layer. -/
def ren : DaoLevel := fun i => decide (i.val = 0)

/-- 心道 / 下道 — subjective, individual fiction. -/
def xin : DaoLevel := fun _ => true

/-- 反道 / 邪道 — active refutation; claim disproven. -/
def feiDao : DaoLevel := fun i => decide (i.val = 1)

/-- The four `DaoLevel` values in canonical order. -/
def all : List DaoLevel := [tian, ren, xin, feiDao]

@[simp] theorem all_length : all.length = 4 := rfl

/-- 2-bit `Nat` encoding (for distinctness proofs). -/
def toNat (d : DaoLevel) : Nat :=
  (if d ⟨0, by decide⟩ then 1 else 0) + (if d ⟨1, by decide⟩ then 2 else 0)

@[simp] theorem toNat_tian   : tian.toNat   = 0 := rfl
@[simp] theorem toNat_ren    : ren.toNat    = 1 := rfl
@[simp] theorem toNat_xin    : xin.toNat    = 3 := rfl
@[simp] theorem toNat_feiDao : feiDao.toNat = 2 := rfl

/-- The 4 named DaoLevel values are distinct. -/
theorem all_nodup : all.Nodup := by
  have : (all.map toNat).Nodup := by
    show ([0, 1, 3, 2] : List Nat).Nodup
    decide
  exact List.Nodup.of_map _ this

end DaoLevel

/-! ## § 2 SanCai (三才) — 天/人/地 on `Fin 3` -/

/-- 三才 (San Cai, Three Powers) — 天 / 人 / 地. -/
abbrev SanCai : Type := Fin 3

namespace SanCai

/-- 天 (heaven). -/
@[match_pattern] def tian : SanCai := ⟨0, by decide⟩
/-- 人 (man, between heaven and earth). -/
@[match_pattern] def ren  : SanCai := ⟨1, by decide⟩
/-- 地 (earth, receptive ground). -/
@[match_pattern] def di   : SanCai := ⟨2, by decide⟩

def all : List SanCai := [tian, ren, di]

@[simp] theorem all_length : all.length = 3 := rfl

/-- 三才 → DaoLevel mapping rationale: 天 → 天道, 人 → 人道, 地 → 心道.
    反道 has no SanCai analog (三才 is a 3-fold positive system). -/
def toDaoLevel : SanCai → DaoLevel
  | ⟨0, _⟩ => DaoLevel.tian
  | ⟨1, _⟩ => DaoLevel.ren
  | _      => DaoLevel.xin

/-- DaoLevel → 三才 inverse. 反道 falls back to 地 (the bottom layer). -/
def fromDaoLevel (d : DaoLevel) : SanCai :=
  if d = DaoLevel.tian then tian
  else if d = DaoLevel.ren then ren
  else di

@[simp] theorem toDaoLevel_tian : toDaoLevel tian = DaoLevel.tian := rfl
@[simp] theorem toDaoLevel_ren  : toDaoLevel ren  = DaoLevel.ren  := rfl
@[simp] theorem toDaoLevel_di   : toDaoLevel di   = DaoLevel.xin  := rfl

theorem to_from (s : SanCai) : fromDaoLevel (toDaoLevel s) = s := by
  match s with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

end SanCai

/-! ## § 3 SanXing (三性) — Yogācāra three natures on `Fin 3` -/

/-- 三性 (San Xing) — Yogācāra three natures (《成唯识论》):
    圆成实性 / 依他起性 / 遍计所执性. -/
abbrev SanXing : Type := Fin 3

namespace SanXing

/-- 圆成实性 (perfectly accomplished, fully-real). -/
@[match_pattern] def yuanCheng    : SanXing := ⟨0, by decide⟩
/-- 依他起性 (dependently arising, conditioned). -/
@[match_pattern] def yiTaQi       : SanXing := ⟨1, by decide⟩
/-- 遍计所执性 (imagined, mentally constructed). -/
@[match_pattern] def bianJiSuoZhi : SanXing := ⟨2, by decide⟩

def all : List SanXing := [yuanCheng, yiTaQi, bianJiSuoZhi]

@[simp] theorem all_length : all.length = 3 := rfl

/-- 三性 → DaoLevel: 圆成 → 天道, 依他 → 人道, 遍计 → 心道. -/
def toDaoLevel : SanXing → DaoLevel
  | ⟨0, _⟩ => DaoLevel.tian
  | ⟨1, _⟩ => DaoLevel.ren
  | _      => DaoLevel.xin

def fromDaoLevel (d : DaoLevel) : SanXing :=
  if d = DaoLevel.tian then yuanCheng
  else if d = DaoLevel.ren then yiTaQi
  else bianJiSuoZhi

@[simp] theorem toDaoLevel_yuanCheng    : toDaoLevel yuanCheng    = DaoLevel.tian := rfl
@[simp] theorem toDaoLevel_yiTaQi       : toDaoLevel yiTaQi       = DaoLevel.ren  := rfl
@[simp] theorem toDaoLevel_bianJiSuoZhi : toDaoLevel bianJiSuoZhi = DaoLevel.xin  := rfl

theorem to_from (s : SanXing) : fromDaoLevel (toDaoLevel s) = s := by
  match s with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

end SanXing

/-! ## § 4 SanShen (三身) — Buddhist trikāya on `Fin 3` -/

/-- 三身 (San Shen) — Buddhist three bodies: 法身 / 报身 / 化身. -/
abbrev SanShen : Type := Fin 3

namespace SanShen

/-- 法身 (Dharmakāya, truth-body, unconditioned). -/
@[match_pattern] def faShen  : SanShen := ⟨0, by decide⟩
/-- 报身 (Saṃbhogakāya, reward-body, merit-manifested). -/
@[match_pattern] def baoShen : SanShen := ⟨1, by decide⟩
/-- 化身 (Nirmāṇakāya, transformation-body, particular). -/
@[match_pattern] def huaShen : SanShen := ⟨2, by decide⟩

def all : List SanShen := [faShen, baoShen, huaShen]

@[simp] theorem all_length : all.length = 3 := rfl

/-- 三身 → DaoLevel: 法 → 天道, 报 → 人道, 化 → 心道. -/
def toDaoLevel : SanShen → DaoLevel
  | ⟨0, _⟩ => DaoLevel.tian
  | ⟨1, _⟩ => DaoLevel.ren
  | _      => DaoLevel.xin

def fromDaoLevel (d : DaoLevel) : SanShen :=
  if d = DaoLevel.tian then faShen
  else if d = DaoLevel.ren then baoShen
  else huaShen

@[simp] theorem toDaoLevel_faShen  : toDaoLevel faShen  = DaoLevel.tian := rfl
@[simp] theorem toDaoLevel_baoShen : toDaoLevel baoShen = DaoLevel.ren  := rfl
@[simp] theorem toDaoLevel_huaShen : toDaoLevel huaShen = DaoLevel.xin  := rfl

theorem to_from (s : SanShen) : fromDaoLevel (toDaoLevel s) = s := by
  match s with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

end SanShen

/-! ## § 5 SanZhi (三知) — Confucian knowing on `Fin 3` -/

/-- 三知 — three modes of knowing (《论语·季氏》). -/
abbrev SanZhi : Type := Fin 3

namespace SanZhi

/-- 生而知之 — innate / born knowing. -/
@[match_pattern] def shengEr : SanZhi := ⟨0, by decide⟩
/-- 学而知之 — knowing through study. -/
@[match_pattern] def xueEr   : SanZhi := ⟨1, by decide⟩
/-- 困而知之 — knowing through struggle. -/
@[match_pattern] def kunEr   : SanZhi := ⟨2, by decide⟩

def all : List SanZhi := [shengEr, xueEr, kunEr]

@[simp] theorem all_length : all.length = 3 := rfl

/-- 三知 → DaoLevel: 生而知 → 天道, 学而知 → 人道, 困而知 → 心道. -/
def toDaoLevel : SanZhi → DaoLevel
  | ⟨0, _⟩ => DaoLevel.tian
  | ⟨1, _⟩ => DaoLevel.ren
  | _      => DaoLevel.xin

def fromDaoLevel (d : DaoLevel) : SanZhi :=
  if d = DaoLevel.tian then shengEr
  else if d = DaoLevel.ren then xueEr
  else kunEr

@[simp] theorem toDaoLevel_shengEr : toDaoLevel shengEr = DaoLevel.tian := rfl
@[simp] theorem toDaoLevel_xueEr   : toDaoLevel xueEr   = DaoLevel.ren  := rfl
@[simp] theorem toDaoLevel_kunEr   : toDaoLevel kunEr   = DaoLevel.xin  := rfl

theorem to_from (s : SanZhi) : fromDaoLevel (toDaoLevel s) = s := by
  match s with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

end SanZhi

/-! ## § 6 SanBao (三宝) — Daoist alchemy treasures on `Fin 3` -/

/-- 三宝 — Daoist alchemy: 神 / 气 / 精. -/
abbrev SanBao : Type := Fin 3

namespace SanBao

/-- 神 (spirit, highest, proximate to 道). -/
@[match_pattern] def shen : SanBao := ⟨0, by decide⟩
/-- 气 (qì, vital flow, relational). -/
@[match_pattern] def qi   : SanBao := ⟨1, by decide⟩
/-- 精 (essence, particulate substrate). -/
@[match_pattern] def jing : SanBao := ⟨2, by decide⟩

def all : List SanBao := [shen, qi, jing]

@[simp] theorem all_length : all.length = 3 := rfl

/-- 三宝 → DaoLevel: 神 → 天道, 气 → 人道, 精 → 心道. -/
def toDaoLevel : SanBao → DaoLevel
  | ⟨0, _⟩ => DaoLevel.tian
  | ⟨1, _⟩ => DaoLevel.ren
  | _      => DaoLevel.xin

def fromDaoLevel (d : DaoLevel) : SanBao :=
  if d = DaoLevel.tian then shen
  else if d = DaoLevel.ren then qi
  else jing

@[simp] theorem toDaoLevel_shen : toDaoLevel shen = DaoLevel.tian := rfl
@[simp] theorem toDaoLevel_qi   : toDaoLevel qi   = DaoLevel.ren  := rfl
@[simp] theorem toDaoLevel_jing : toDaoLevel jing = DaoLevel.xin  := rfl

theorem to_from (s : SanBao) : fromDaoLevel (toDaoLevel s) = s := by
  match s with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

end SanBao

/-! ## § 7 SanDi (三谛) — Tiantai three truths on `Fin 3` -/

/-- 三谛 — Tiantai 三谛 (Madhyamaka heritage): 空 / 假 / 中.

    NOTE: 中 is the SYNTHESIS aspect (Madhyamaka "neither this nor
    that"), not the center-tier of 道/理/我.  The bijection holds at
    cardinality 3 ↔ 3 but the semantic emphasis differs. -/
abbrev SanDi : Type := Fin 3

namespace SanDi

/-- 空 (emptiness, voidness of self-nature). -/
@[match_pattern] def kong  : SanDi := ⟨0, by decide⟩
/-- 假 (provisional / conventional, dependent appearance). -/
@[match_pattern] def jia   : SanDi := ⟨1, by decide⟩
/-- 中 (synthesis / 中观). -/
@[match_pattern] def zhong : SanDi := ⟨2, by decide⟩

def all : List SanDi := [kong, jia, zhong]

@[simp] theorem all_length : all.length = 3 := rfl

/-- 三谛 → DaoLevel: 空 → 天道, 假 → 心道, 中 → 人道.
    Note 假 maps to 心 (provisional/constructed); 中 maps to 人 (synthesis tier). -/
def toDaoLevel : SanDi → DaoLevel
  | ⟨0, _⟩ => DaoLevel.tian
  | ⟨1, _⟩ => DaoLevel.xin
  | _      => DaoLevel.ren

def fromDaoLevel (d : DaoLevel) : SanDi :=
  if d = DaoLevel.tian then kong
  else if d = DaoLevel.ren then zhong
  else jia

@[simp] theorem toDaoLevel_kong  : toDaoLevel kong  = DaoLevel.tian := rfl
@[simp] theorem toDaoLevel_jia   : toDaoLevel jia   = DaoLevel.xin  := rfl
@[simp] theorem toDaoLevel_zhong : toDaoLevel zhong = DaoLevel.ren  := rfl

theorem to_from (s : SanDi) : fromDaoLevel (toDaoLevel s) = s := by
  match s with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

end SanDi

/-! ## § 8 JianMode (间生论) — 8 modes on `Trigram = R 3`

  Bijection 八卦 ↔ 8 ontological modes of inter-spatial existence:

    乾 ☰ 健 ↔ 续 / 生  (sheng — continuation, generation)
    坤 ☷ 顺 ↔ 受 / 成  (shou  — reception, form-completion)
    震 ☳ 动 ↔ 元 / 几  (yuan  — initial motion, trace)
    巽 ☴ 入 ↔ 因 / 渗  (shen  — cause, penetration)
    坎 ☵ 陷 ↔ 塞 / 闭  (sai   — blockage, obstruction)
    离 ☲ 丽 ↔ 显 / 心  (xian  — manifestation, heart-shine)
    艮 ☶ 止 ↔ 聚 / 形  (ju    — gathering, form-fix)
    兑 ☱ 悦 ↔ 开 / 通  (kai   — opening, flow, beauty)
-/

/-- 间生论 ontological mode — fundamental category of inter-spatial
    existence.  As a type, `JianMode = Trigram = R 3`; the 8 named modes
    are paired with the 8 trigrams via `toTrigram` / `ofTrigram`. -/
abbrev JianMode : Type := Trigram

namespace JianMode

/-! ### § 8.1 The 8 named modes — bit patterns inherited from bagua -/

/-- 乾健 续/生 (continuation, generation) — same bits as 乾 (all yang). -/
def sheng : JianMode := Trigram.qian

/-- 坤顺 受/成 (reception, completion) — same bits as 坤 (all yin). -/
def shou  : JianMode := Trigram.kun

/-- 震动 元/几 (initial motion, trace) — same bits as 震. -/
def yuan  : JianMode := Trigram.zhen

/-- 巽入 因/渗 (cause, penetration) — same bits as 巽. -/
def shen  : JianMode := Trigram.xun

/-- 坎陷 塞/闭 (blockage) — same bits as 坎. -/
def sai   : JianMode := Trigram.kan

/-- 离丽 显/心 (manifestation, heart-shine) — same bits as 离. -/
def xian  : JianMode := Trigram.li

/-- 艮止 聚/形 (gathering, form-fix) — same bits as 艮. -/
def ju    : JianMode := Trigram.gen

/-- 兑悦 开/通/美 (opening, flow) — same bits as 兑. -/
def kai   : JianMode := Trigram.dui

/-- The 8 modes in canonical Wenwang-ish order (乾/坤/震/巽/坎/离/艮/兑). -/
def all : List JianMode := [sheng, shou, yuan, shen, sai, xian, ju, kai]

@[simp] theorem all_length : all.length = 8 := rfl

/-! ### § 8.2 Bijection JianMode ↔ Trigram

  Because `JianMode = Trigram`, the bijection is literal identity; we
  expose explicit names mirroring the classical API for downstream
  consumers. -/

/-- Mode → trigram (identity at the underlying-type level). -/
def toTrigram (m : JianMode) : Trigram := m

/-- Trigram → mode (identity at the underlying-type level). -/
def ofTrigram (t : Trigram) : JianMode := t

@[simp] theorem ofTrigram_toTrigram (m : JianMode) :
    ofTrigram (toTrigram m) = m := rfl

@[simp] theorem toTrigram_ofTrigram (t : Trigram) :
    toTrigram (ofTrigram t) = t := rfl

/-! ### § 8.3 Per-mode trigram readings -/

theorem toTrigram_sheng : toTrigram sheng = Trigram.heaven  := rfl
theorem toTrigram_shou  : toTrigram shou  = Trigram.earth   := rfl
theorem toTrigram_yuan  : toTrigram yuan  = Trigram.thunder := rfl
theorem toTrigram_shen  : toTrigram shen  = Trigram.wind    := rfl
theorem toTrigram_sai   : toTrigram sai   = Trigram.water   := rfl
theorem toTrigram_xian  : toTrigram xian  = Trigram.fire    := rfl
theorem toTrigram_ju    : toTrigram ju    = Trigram.mountain := rfl
theorem toTrigram_kai   : toTrigram kai   = Trigram.lake    := rfl

/-! ### § 8.4 V₄ operators on JianMode

  错 (complement) on modes — 4 错-dual pairs:
    续/受 (sheng/shou)   元/因 (yuan/shen)
    塞/显 (sai/xian)     聚/开 (ju/kai)

  综 (reverse) on modes — fixes 4 modes (乾/坤/坎/离 are 综-self),
  swaps 2 pairs:
    震 ↔ 艮 (yuan ↔ ju)   巽 ↔ 兑 (shen ↔ kai)
-/

/-- 错 on a mode (the yao-flipped dual). -/
def complement (m : JianMode) : JianMode :=
  Trigram.mk (Yao.neg m.y1) (Yao.neg m.y2) (Yao.neg m.y3)

/-- 综 on a mode (yao-reverse dual). -/
def reverse (m : JianMode) : JianMode :=
  Trigram.mk m.y3 m.y2 m.y1

@[simp] theorem complement_sheng : complement sheng = shou := by
  apply Trigram.ext <;> rfl

@[simp] theorem complement_shou : complement shou = sheng := by
  apply Trigram.ext <;> rfl

@[simp] theorem complement_yuan : complement yuan = shen := by
  apply Trigram.ext <;> rfl

@[simp] theorem complement_shen : complement shen = yuan := by
  apply Trigram.ext <;> rfl

@[simp] theorem complement_sai : complement sai = xian := by
  apply Trigram.ext <;> rfl

@[simp] theorem complement_xian : complement xian = sai := by
  apply Trigram.ext <;> rfl

@[simp] theorem complement_ju : complement ju = kai := by
  apply Trigram.ext <;> rfl

@[simp] theorem complement_kai : complement kai = ju := by
  apply Trigram.ext <;> rfl

@[simp] theorem reverse_sheng : reverse sheng = sheng := by
  apply Trigram.ext <;> rfl

@[simp] theorem reverse_shou : reverse shou = shou := by
  apply Trigram.ext <;> rfl

@[simp] theorem reverse_sai : reverse sai = sai := by
  apply Trigram.ext <;> rfl

@[simp] theorem reverse_xian : reverse xian = xian := by
  apply Trigram.ext <;> rfl

@[simp] theorem reverse_yuan : reverse yuan = ju := by
  apply Trigram.ext <;> rfl

@[simp] theorem reverse_ju : reverse ju = yuan := by
  apply Trigram.ext <;> rfl

@[simp] theorem reverse_shen : reverse shen = kai := by
  apply Trigram.ext <;> rfl

@[simp] theorem reverse_kai : reverse kai = shen := by
  apply Trigram.ext <;> rfl

/-- 错 is involutive. -/
theorem complement_involutive (m : JianMode) : complement (complement m) = m := by
  apply Trigram.ext
  · show Yao.neg (Yao.neg _) = _; rw [Yao.neg_neg]
  · show Yao.neg (Yao.neg _) = _; rw [Yao.neg_neg]
  · show Yao.neg (Yao.neg _) = _; rw [Yao.neg_neg]

/-- 综 is involutive. -/
theorem reverse_involutive (m : JianMode) : reverse (reverse m) = m := by
  apply Trigram.ext <;> rfl

/-- 错 ∘ 综 = 综 ∘ 错 (V₄ commutativity). -/
theorem complement_reverse_comm (m : JianMode) :
    complement (reverse m) = reverse (complement m) := by
  apply Trigram.ext <;> rfl

/-- The 4 错-dual pairs (as a single conjunction). -/
theorem cuo_pairs :
    complement sheng = shou ∧ complement yuan = shen ∧
    complement sai = xian ∧ complement ju = kai :=
  ⟨complement_sheng, complement_yuan, complement_sai, complement_ju⟩

/-- The 4 综-fixed modes. -/
theorem zong_fixed :
    reverse sheng = sheng ∧ reverse shou = shou ∧
    reverse sai = sai ∧ reverse xian = xian :=
  ⟨reverse_sheng, reverse_shou, reverse_sai, reverse_xian⟩

/-- The 2 综-swap pairs. -/
theorem zong_swaps :
    reverse yuan = ju ∧ reverse ju = yuan ∧
    reverse shen = kai ∧ reverse kai = shen :=
  ⟨reverse_yuan, reverse_ju, reverse_shen, reverse_kai⟩

end JianMode

end SSBX.Foundation.Atlas.Yi.Tradition
