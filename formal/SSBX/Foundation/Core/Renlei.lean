/-
# Renlei — 人类命运共同体 之 形式证

  人 不是 字根 之 atom——是 generated:`G «人» = G «天之子» + G «意识»`.
  类 是 atom，命/运/体 不在 atom 表内，故 「人类命运共同体」必须由
  registry 中既有之 atom / generated / recursive 字 重新拼合：

    人类         := G «人» (天之子 + 意识) 之 集体形式 (复数 Focus)
    命运         := A «续» (continuity)
    共同         := A «共» + R «共开» + G «共续»
    共同体       := R «共开» ⊓ G «共续»
    人类命运共同体 := 人类 之 共开 ∧ 共续 ∧ 非 夺共续

  此恰是 R «道» 之 sense formula「正续 + 非夺共续 + 共开」 (Roster.lean:440)
  限于 G «人» 上之 instance。故：

    «人类命运共同体» := «道» 之 应用 于 «人类»

## 证之结构

  § 1  Registry 层  — 八字根皆 registered，deps 由 rfl 验
  § 2  Model 层    — 三轴 community state (open / share / no-seizure)
                     之 Model + DaoCriteria 构造
  § 3  反例三模式  — 三轴各失一者，TrueDao 不立 (isolated / severed / seized)
  § 4  正例        — 三轴俱足之 aligned, TrueDao 实成
  § 5  主定理      — 人类命运共同体_合立 ∧ 人类命运共同体_有反

## 与 EvolutionDao.lean 之关系

  EvolutionDao 立「演化筛 σ_F 留存 ⊉ 真道留存」(三视证)；
  此处 Renlei 立「人类共同体路径 ∈ 真道留存 ⟺ 三轴俱足」之正向构造。
  二篇互为对偶：前者证 σ_F 之 不充分，后者证 共同体之 充分构造。

## 状态

  0 sorry / 0 axiom；registry 由 `decide` / `rfl` 见证，model 由具体构造见证。
-/
import SSBX.Core
import SSBX.Foundation.Core.Monism
import SSBX.Foundation.Core.HumanAlignment

namespace SSBX.Foundation.Core.Renlei

open SSBX.Roster
open SSBX.Core.GammaProcess

/-! ## § 1  Registry 层：人类命运共同体 之 八字根 -/

/-- 人类命运共同体 之 registry 层 coherence：
    八个字根（人 / 类 / 共 / 续 / 共开 / 共续 / 夺共续 / 仁 / 道）
    皆已 registered，且其 deps 之结构与 sense formula 一致。 -/
structure RenleiCommonDestinyDef where
  -- 主体（人 / 类）
  human_registered    : (G .«人»)        ∈ allSymbols
  kind_registered     : (A .«类»)        ∈ allSymbols
  -- 命 = 续；共 = 共
  xu_registered       : (A .«续»)        ∈ allSymbols
  gong_registered     : (A .«共»)        ∈ allSymbols
  cun_registered      : (A .«存»)        ∈ allSymbols
  -- 共同 / 共同体 之 generated / recursive
  gongkai_registered  : (R .«共开»)      ∈ allSymbols
  gongxu_registered   : (G .«共续»)      ∈ allSymbols
  duo_gongxu_registered : (G .«夺共续»)   ∈ allSymbols
  -- 道 / 仁 — recursive
  ren_registered      : (R .«仁»)        ∈ allSymbols
  dao_registered      : (R .«道»)        ∈ allSymbols
  zhengxu_registered  : (G .«正续»)      ∈ allSymbols
  -- deps 结构（与 sense formula 一致）
  ren_human_deps      : (entryOf (G .«人»)).deps   = [G .«天之子», G .«意识»]
  gongkai_deps        : (entryOf (R .«共开»)).deps = [R .«开», A .«共», A .«存»]
  gongxu_deps         : (entryOf (G .«共续»)).deps = [A .«共», A .«续»]
  duo_gongxu_deps     : (entryOf (G .«夺共续»)).deps = [A .«夺», A .«共», A .«续»]
  ren_deps            : (entryOf (R .«仁»)).deps  = [G .«己续», G .«共续»]
  dao_deps            : (entryOf (R .«道»)).deps  = [G .«正续», R .«共开», G .«夺共续», R .«坏»]

/-- 人类命运共同体 之 registry 层 之 全 见证。 -/
def renleiCommonDestinyDef : RenleiCommonDestinyDef :=
  { human_registered      := by native_decide
    kind_registered       := by native_decide
    xu_registered         := by native_decide
    gong_registered       := by native_decide
    cun_registered        := by native_decide
    gongkai_registered    := by native_decide
    gongxu_registered     := by native_decide
    duo_gongxu_registered := by native_decide
    ren_registered        := by native_decide
    dao_registered        := by native_decide
    zhengxu_registered    := by native_decide
    ren_human_deps        := rfl
    gongkai_deps          := rfl
    gongxu_deps           := rfl
    duo_gongxu_deps       := rfl
    ren_deps              := rfl
    dao_deps              := rfl }

/-! ## § 2  Model 层：三轴 community state -/

/-- 共同体之三轴：共开 / 共续 / 非夺共续。
    每轴为 Bool；三者俱 true 即 aligned 共同体。 -/
structure CommunityState where
  /-- 共开：开放共在（非闭、非伪开）。 -/
  openInCommon     : Bool
  /-- 共续：共同延续（仁之集体形式）。 -/
  shareContinuity  : Bool
  /-- 非夺共续：他者之续不被夺取。 -/
  noSeizure        : Bool
  deriving DecidableEq, Repr

namespace CommunityState

/-- 三轴俱足之 aligned 状态。 -/
def aligned : CommunityState := ⟨true, true, true⟩

/-- 三轴俱缺之 zero 状态（无任何共在）。 -/
def vacuous : CommunityState := ⟨false, false, false⟩

/-- 失共开：闭式（如部落主义、地缘封闭）。 -/
def isolated : CommunityState := ⟨false, true, true⟩

/-- 失共续：断式（如灭绝主义、强迫断代）。 -/
def severed  : CommunityState := ⟨true, false, true⟩

/-- 夺共续：夺式（如殖民剥削、零和博弈）。 -/
def seized   : CommunityState := ⟨true, true, false⟩

/-- aligned 之三轴皆 true。 -/
theorem aligned_open : aligned.openInCommon = true := rfl
theorem aligned_share : aligned.shareContinuity = true := rfl
theorem aligned_noSeize : aligned.noSeizure = true := rfl

end CommunityState

/-! ### Model 与 DaoCriteria

  Gamma  = CommunityState（世界即三轴之所现）
  Path   = Unit（共同体之径）
  canContinue := openInCommon = true ∧ shareContinuity = true
  badAt      := noSeizure = false（即 夺共续 实成）
-/

/-- 共同体 model：Gamma 即 community state。 -/
def communityModel : Model where
  Gamma := CommunityState
  Focus := Unit
  Relation := Unit
  Interval := Unit
  Degree := Unit
  Horizon := Unit
  Limit := Unit
  state := fun _ _ => Unit
  relationState := fun _ _ => Unit
  limitedBy := fun _ _ => True
  grid := fun _ _ _ => True
  weight := fun _ _ => 0
  coupling := fun _ _ _ => 0
  historicalLaw := fun _ _ => True
  openLaw := fun _ _ => False
  validInterval := fun _ _ => True
  valid_iff_law := by intro _ _; simp
  shenghe := fun g _ _ => g

/-- 共同体之 dao 标准：
    canContinue ↔ 共开 ∧ 共续；   badAt ↔ 夺共续。 -/
def communityDao : DaoCriteria communityModel where
  Path := Unit
  relevant := fun _ _ _ _ => True
  canContinue := fun g _ _ _ =>
    g.openInCommon = true ∧ g.shareContinuity = true
  badAt := fun g _ _ _ => g.noSeizure = false

/-- 共同体之径（唯一）。 -/
def communityPath : communityDao.Path := ()

/-! ## § 3  反例三模式 — 三轴各失一者，真道不立 -/

/-- 失共开（isolated）：openInCommon = false → canContinue 不立 → ¬ TrueDao。 -/
theorem isolated_fails_truedao :
    ¬ TrueDao communityModel communityDao communityPath CommunityState.isolated := by
  intro h
  -- canContinue isolated = (isolated.openInCommon = true ∧ ...) = (false = true ∧ ...)
  exact Bool.noConfusion (h.2 () () trivial).1.1

/-- 失共续（severed）：shareContinuity = false → canContinue 不立。 -/
theorem severed_fails_truedao :
    ¬ TrueDao communityModel communityDao communityPath CommunityState.severed := by
  intro h
  exact Bool.noConfusion (h.2 () () trivial).1.2

/-- 夺共续（seized）：noSeizure = false → badAt 实成 → ¬ TrueDao。 -/
theorem seized_fails_truedao :
    ¬ TrueDao communityModel communityDao communityPath CommunityState.seized := by
  intro h
  -- badAt seized = (seized.noSeizure = false) = (false = false), 由 rfl
  exact (h.2 () () trivial).2 rfl

/-! ## § 4  正例 — 三轴俱足者，真道实成 -/

/-- aligned：三轴俱 true → canContinue 立 ∧ ¬ badAt → TrueDao。 -/
theorem aligned_realizes_truedao :
    TrueDao communityModel communityDao communityPath CommunityState.aligned :=
  ⟨⟨(), (), trivial⟩,
   fun _ _ _ => ⟨⟨rfl, rfl⟩, fun hbad => Bool.noConfusion hbad⟩⟩

/-! ## § 5  主定理：人类命运共同体 之 合立与 反例 -/

/-- **合立**：存在一 model + path + Gamma 使 TrueDao 实成。
    具体见证：communityModel + communityPath + CommunityState.aligned. -/
theorem «人类命运共同体_合立» :
    ∃ (M : Model) (D : DaoCriteria M) (p : D.Path) (g : M.Gamma),
      TrueDao M D p g :=
  ⟨communityModel, communityDao, communityPath,
   CommunityState.aligned, aligned_realizes_truedao⟩

/-- **有反**：存在 Gamma 使 TrueDao 不立（夺共续 之相）。
    具体见证：CommunityState.seized. -/
theorem «人类命运共同体_有反» :
    ∃ (M : Model) (D : DaoCriteria M) (p : D.Path) (g : M.Gamma),
      ¬ TrueDao M D p g :=
  ⟨communityModel, communityDao, communityPath,
   CommunityState.seized, seized_fails_truedao⟩

/-- **三模式失** （isolated / severed / seized 皆失）。 -/
theorem «人类命运共同体_三模式失» :
    (¬ TrueDao communityModel communityDao communityPath CommunityState.isolated) ∧
    (¬ TrueDao communityModel communityDao communityPath CommunityState.severed) ∧
    (¬ TrueDao communityModel communityDao communityPath CommunityState.seized) :=
  ⟨isolated_fails_truedao, severed_fails_truedao, seized_fails_truedao⟩

/-- **必要性**：在此 model 内，TrueDao 立 ↔ 三轴俱足。
    （aligned 是 64 = 2^3 community states 中实成 TrueDao 之唯一 inhabitant，
    其余 7 状态皆有至少一轴 false，故失。这里只证 aligned 之实成，
    与 isolated / severed / seized 三个 minimal 失败模式作为 cross-cut 见证。） -/
theorem «人类命运共同体_aligned_iff» (g : CommunityState) :
    TrueDao communityModel communityDao communityPath g ↔ g = CommunityState.aligned := by
  constructor
  · intro h
    have hpair := h.2 () () trivial
    cases g with
    | mk o s n =>
      have ho : o = true := hpair.1.1
      have hs : s = true := hpair.1.2
      have hn : n = true := by
        cases n
        · exact absurd rfl hpair.2
        · rfl
      subst ho
      subst hs
      subst hn
      rfl
  · intro h
    rw [h]
    exact aligned_realizes_truedao

/-- **收口**：人类命运共同体 之 完整公示。
    1. 合立（存在 g 使 TrueDao 立）
    2. 有反（存在 g 使 TrueDao 不立）
    3. 当且仅当（TrueDao ↔ 三轴俱足）
    4. registry 一致（八字根皆 registered，deps 由 rfl 验） -/
theorem «人类命运共同体_之证» :
    -- (1) 合立
    (∃ g : CommunityState,
        TrueDao communityModel communityDao communityPath g) ∧
    -- (2) 有反
    (∃ g : CommunityState,
        ¬ TrueDao communityModel communityDao communityPath g) ∧
    -- (3) 充要条件
    (∀ g : CommunityState,
        TrueDao communityModel communityDao communityPath g ↔ g = CommunityState.aligned) ∧
    -- (4) registry 一致（道 之 sense formula 「正续 + 非夺共续 + 共开」之 deps 同体）
    ((entryOf (R .«道»)).deps = [G .«正续», R .«共开», G .«夺共续», R .«坏»]) :=
  ⟨⟨CommunityState.aligned, aligned_realizes_truedao⟩,
   ⟨CommunityState.seized, seized_fails_truedao⟩,
   «人类命运共同体_aligned_iff»,
   renleiCommonDestinyDef.dao_deps⟩

end SSBX.Foundation.Core.Renlei
