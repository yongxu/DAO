/-
# Jian ↔ Yi Bridge — cross-layer mapping

  The 14-字 particle kernel (Jian) and the 96-cell ontology (Yi) live at
  different layers:
    Jian   = syntactic/computational layer (operators on 文 / Wen)
    Yi     = ontological layer (hexagrams / DaoLevel partition)

  This file connects them via the dimension axis:
    Op → Dimension (already in Jian.lean)
    Dimension → DaoLevel (defined here, re-opens Jian.Dimension namespace)
    Op → DaoLevel  (composition)

  Heuristic mapping rationale (per dimension):
    D1 关联 (composition):    structural — 道 (objective form)
    D2 指 (reference):        deictic — 中道 (intersubjective pointing)
    D3 量 (quantification):   universals — 道 (objective scope)
    D4 时序 (temporality):    individual time — 心道 (subjective anchoring)
    D5 言态 (mood):           speech-act — 中道 (communicative)
    D6 真值 (polarity):       truth — 道 (objective valuation)

  This is a HEURISTIC — different particles within the same dim may have
  different ontological flavors. The dim-level mapping is the first-order
  approximation; refine per-Op as needed.
-/

import SSBX.Foundation.Jian.Jian
import SSBX.Foundation.Atlas.YiLegacy.Yi

/-! ## § 1 Dimension → DaoLevel

  Defined inside `SSBX.Foundation.Jian.Jian.Dimension` to enable dot notation. -/

namespace SSBX.Foundation.Jian.Jian.Dimension

open SSBX.Foundation.Yi.Yi (DaoLevel)

/-- Each linguistic dimension's dominant ontological tier. -/
def daoLevel : SSBX.Foundation.Jian.Jian.Dimension → DaoLevel
  | .D1 => DaoLevel.tian   -- 关联: structural composition lives in 道-form
  | .D2 => DaoLevel.ren    -- 指: deictic reference is intersubjective
  | .D3 => DaoLevel.tian   -- 量: universal scope is 道-level
  | .D4 => DaoLevel.xin    -- 时序: temporal anchoring is individual
  | .D5 => DaoLevel.ren    -- 言态: mood/speech-act is communicative
  | .D6 => DaoLevel.tian   -- 真值: truth claims are 道-level

end SSBX.Foundation.Jian.Jian.Dimension

/-! ## § 2 Op → DaoLevel (via Dimension)

  Defined inside `SSBX.Foundation.Jian.Jian.Op` to enable dot notation. -/

namespace SSBX.Foundation.Jian.Jian.Op

open SSBX.Foundation.Yi.Yi (DaoLevel)

/-- Each operator's dominant ontological tier (via its dimension). -/
def daoLevel (o : SSBX.Foundation.Jian.Jian.Op) : DaoLevel := o.dim.daoLevel

end SSBX.Foundation.Jian.Jian.Op

/-! ## § 3 Verification + Wen-level reading -/

namespace SSBX.Foundation.Jian.JianYiBridge

open SSBX.Foundation.Jian.Jian
open SSBX.Foundation.Yi.Yi

/-! ### Per-Op tier verification -/

theorem zhi_dao     : Op.zhi.daoLevel    = DaoLevel.tian := rfl
theorem zhe_dao     : Op.zhe.daoLevel    = DaoLevel.tian := rfl
theorem er_dao      : Op.er.daoLevel     = DaoLevel.tian := rfl
theorem ti_dao      : Op.ti.daoLevel     = DaoLevel.tian := rfl
theorem qu_dao      : Op.qu.daoLevel     = DaoLevel.tian := rfl
theorem ji_dao      : Op.ji.daoLevel     = DaoLevel.ren  := rfl
theorem shi_dao     : Op.shi.daoLevel    = DaoLevel.ren  := rfl
theorem fan_dao     : Op.fan.daoLevel    = DaoLevel.tian := rfl
theorem fang_dao    : Op.fang.daoLevel   = DaoLevel.xin  := rfl
theorem yiAnter_dao : Op.yiAnter.daoLevel = DaoLevel.xin := rfl
theorem yiCos_dao   : Op.yiCos.daoLevel  = DaoLevel.xin  := rfl
theorem ye_dao      : Op.ye.daoLevel     = DaoLevel.ren  := rfl
theorem ling_dao    : Op.ling.daoLevel   = DaoLevel.ren  := rfl
theorem fei_dao     : Op.fei.daoLevel    = DaoLevel.tian := rfl

/-! ### Coverage and counts -/

/-- Each Dao tier (positive 3) gets at least one dimension. -/
theorem dao_coverage :
    (∃ d : Dimension, d.daoLevel = DaoLevel.tian) ∧
    (∃ d : Dimension, d.daoLevel = DaoLevel.ren) ∧
    (∃ d : Dimension, d.daoLevel = DaoLevel.xin) :=
  ⟨⟨.D1, rfl⟩, ⟨.D2, rfl⟩, ⟨.D4, rfl⟩⟩

/-- Operators mapping to each DaoLevel. -/
def opsAtTian : List Op := Op.allOps.filter (fun o => o.daoLevel == DaoLevel.tian)
def opsAtRen  : List Op := Op.allOps.filter (fun o => o.daoLevel == DaoLevel.ren)
def opsAtXin  : List Op := Op.allOps.filter (fun o => o.daoLevel == DaoLevel.xin)
def opsAtFeiDao : List Op := Op.allOps.filter (fun o => o.daoLevel == DaoLevel.feiDao)

/-- 7 ops at 道-tier: D1 (5: zhi/zhe/er/ti/qu) + D3 (1: fan) + D6 (1: fei). -/
theorem tian_ops_count : opsAtTian.length = 7 := by native_decide

/-- 4 ops at 中道-tier: D2 (2: ji/shi) + D5 (2: ye/ling). -/
theorem ren_ops_count : opsAtRen.length = 4 := by native_decide

/-- 3 ops at 心道-tier: D4 (3: fang/yiAnter/yiCos). -/
theorem xin_ops_count : opsAtXin.length = 3 := by native_decide

/-- The 14 ops partition cleanly across the 3 main tiers (反道 has no ops). -/
theorem op_partition_sums :
    opsAtTian.length + opsAtRen.length + opsAtXin.length = Op.allOps.length := by
  native_decide

/-- 反道 (feiDao) has NO operator analog. The kernel doesn't natively express
    active refutation as an atom — it would have to be derived (e.g., via 非
    composed with proof-of-claim, or via stepwise refutation). -/
theorem feiDao_no_op : opsAtFeiDao.length = 0 := by native_decide

/-! ## § 4 Wen → DaoLevel reading

  A 文 (Wen term) has a dominant DaoLevel based on its TOP-LEVEL Op.
  Atoms are tier-neutral (no dominant op); pairs whose left side is an Op
  carry that Op's tier. -/

/-- Top-level Op of a Wen term. -/
def wenTopOp : Wen → Option Op
  | .atom _ => none
  | .op o => some o
  | .pair (.op o) _ => some o
  | .pair _ _ => none

/-- A Wen's dominant DaoLevel (Option, since atoms have none). -/
def wenDaoLevel (w : Wen) : Option DaoLevel :=
  (wenTopOp w).map Op.daoLevel

/-! ### Worked examples -/

theorem zhe_form_dao (b : String) (body : Wen) :
    wenDaoLevel (Wen.Zhe b body) = some DaoLevel.tian := rfl

theorem fan_form_dao (b : String) (body : Wen) :
    wenDaoLevel (Wen.Fan b body) = some DaoLevel.tian := rfl

theorem fang_form_xin (x : Wen) :
    wenDaoLevel (Wen.Fang x) = some DaoLevel.xin := rfl

theorem ye_form_ren (x : Wen) :
    wenDaoLevel (Wen.Ye x) = some DaoLevel.ren := rfl

theorem fei_form_dao (x : Wen) :
    wenDaoLevel (Wen.Fei x) = some DaoLevel.tian := rfl

theorem ji_form_ren (x y : Wen) :
    wenDaoLevel (Wen.Ji x y) = some DaoLevel.ren := rfl

theorem ti_form_dao (x : Wen) :
    wenDaoLevel (Wen.Ti x) = some DaoLevel.tian := rfl

theorem qu_form_dao (x : Wen) :
    wenDaoLevel (Wen.Qu x) = some DaoLevel.tian := rfl

theorem yiAnter_form_xin (x : Wen) :
    wenDaoLevel (Wen.YiAnter x) = some DaoLevel.xin := rfl

theorem yiCos_form_xin (x : Wen) :
    wenDaoLevel (Wen.YiCos x) = some DaoLevel.xin := rfl

theorem shi_form_ren (x : Wen) :
    wenDaoLevel (Wen.Shi x) = some DaoLevel.ren := rfl

theorem ling_form_ren (b : String) (val body : Wen) :
    wenDaoLevel (Wen.Ling b val body) = some DaoLevel.ren := rfl

/-! ## § 5 Refute graph + ¬¬-elimination bridge

  非 (Wen.Fei) is the refute operator. Reduction rule 3 (否之约) collapses
  `[非 [非 x]] → x` after a single root step. This connects the syntactic
  particle layer to the ontological refutation flow:

    syntactic:    [非 [非 x]] reduces to x (rule 3, root)
    flow:         WitnessFlow.refute.flip = .ascend (involutive)
    tier:         DaoLevel.feiDao.flip = .tian (involutive)

  All three encode the same ¬¬-elimination intuition at three layers:
  particle / process / position. -/

/-- 非 as the canonical refute Wen-builder. Alias for `Wen.Fei`. -/
def Wen.refute (x : Wen) : Wen := Wen.Fei x

/-- ¬¬-elimination at the Wen level: `[非 [非 x]]` reduces to `x` in one step. -/
theorem refute_refute_reduces (x : Wen) :
    reduceN 1 (Wen.refute (Wen.refute x)) = x := by
  show reduceN 1 (Wen.Fei (Wen.Fei x)) = x
  rfl

/-- Doubled refute is at the 道 tier (top-level Op is 非). -/
theorem refute_refute_dao (x : Wen) :
    wenDaoLevel (Wen.refute (Wen.refute x)) = some DaoLevel.tian := rfl

/-- Single 非 is at the 道 tier (Op.fei.daoLevel = .tian). -/
theorem refute_dao (x : Wen) :
    wenDaoLevel (Wen.refute x) = some DaoLevel.tian := rfl

/-- Bridge: applying refute twice and applying DaoLevel.flip twice both restore
    the original. The particle-level rule 3 mirrors the tier-level involution. -/
theorem refute_flip_correspondence (d : DaoLevel) :
    d.flip.flip = d := DaoLevel.flip_flip d

/-- Bridge: WitnessFlow.flip is also involutive — refute-of-refute = identity
    in flow space. -/
theorem witness_flip_correspondence (f : WitnessFlow) :
    f.flip.flip = f := WitnessFlow.flip_flip f

/-! ## § 6 Cross-tabulation: hex × op claim space

  A "claim" is a (hexagram-position, operator) pair. The total claim space
  has 64 × 14 = 896 raw pairings; the 96-cell ontology refines this to
  96 × 14 = 1344 cell-level claims (since 中道-cells double-count via
  内/外 readings).

  Per-tier cardinalities (hex tier × op tier):
    tian × tian = 32 × 7 = 224
    tian × ren  = 32 × 4 = 128
    tian × xin  = 32 × 3 = 96
    xin  × tian = 32 × 7 = 224
    xin  × ren  = 32 × 4 = 128
    xin  × xin  = 32 × 3 = 96
  Total over (天 + 心) hex: 896 = 64 × 14. -/

/-! ### Cardinality theorems -/

theorem hex_op_total : Hexagram.allHex.length * Op.allOps.length = 896 := by
  native_decide

theorem hex_op_cross_tian_tian :
    Hexagram.tianHex.length * opsAtTian.length = 224 := by native_decide

theorem hex_op_cross_tian_ren :
    Hexagram.tianHex.length * opsAtRen.length = 128 := by native_decide

theorem hex_op_cross_tian_xin :
    Hexagram.tianHex.length * opsAtXin.length = 96 := by native_decide

theorem hex_op_cross_xin_tian :
    Hexagram.xinHex.length * opsAtTian.length = 224 := by native_decide

theorem hex_op_cross_xin_ren :
    Hexagram.xinHex.length * opsAtRen.length = 128 := by native_decide

theorem hex_op_cross_xin_xin :
    Hexagram.xinHex.length * opsAtXin.length = 96 := by native_decide

/-- 96-cell × 14-op total: 1344 (cell-level claims). -/
theorem cell_op_total :
    (Hexagram.tianHex.length + renDaoCells.length + Hexagram.xinHex.length)
      * Op.allOps.length = 1344 := by native_decide

/-! ### Claim archetype: 3 × 3 grid of hex-tier × op-tier

  For every (hex-tier, op-tier) combination there is a distinct archetypal
  claim shape: who is making what kind of claim about which kind of state. -/

/-- 9 archetypes for a (hex-tier × op-tier) cell. -/
inductive ClaimArchetype : Type
  | pureTian   -- 道 hex + 道 op:    objective claim about objective state
  | tianRen    -- 道 hex + 中道 op:  intersubjective act on objective state
  | tianXin    -- 道 hex + 心道 op:  subjective stance toward objective state
  | renTian    -- 中道 hex + 道 op:  objective claim about intersubjective state
  | pureRen    -- 中道 hex + 中道 op: pure intersubjective (合道-readings)
  | renXin     -- 中道 hex + 心道 op: subjective inflection of intersubjective
  | xinTian    -- 心道 hex + 道 op:  objective claim about subjective state
  | xinRen     -- 心道 hex + 中道 op: intersubjective act on subjective state
  | pureXin    -- 心道 hex + 心道 op: pure subjective claim
  deriving Repr, DecidableEq, BEq

/-- Map a (hex-tier, op-tier) pair to its archetype. -/
def claimArchetype (hexTier opTier : DaoLevel) : Option ClaimArchetype :=
  match hexTier, opTier with
  | .tian, .tian => some .pureTian
  | .tian, .ren  => some .tianRen
  | .tian, .xin  => some .tianXin
  | .ren,  .tian => some .renTian
  | .ren,  .ren  => some .pureRen
  | .ren,  .xin  => some .renXin
  | .xin,  .tian => some .xinTian
  | .xin,  .ren  => some .xinRen
  | .xin,  .xin  => some .pureXin
  | _, _         => none  -- 反道 cells / ops would land here, but neither
                          -- have positive analogs in our 9-grid

/-- 9 archetypes correspond bijectively to the 3×3 (hex-tier × op-tier) grid. -/
theorem archetype_pure_tian :
    claimArchetype .tian .tian = some .pureTian := rfl

theorem archetype_pure_xin :
    claimArchetype .xin .xin = some .pureXin := rfl

theorem archetype_pure_ren :
    claimArchetype .ren .ren = some .pureRen := rfl

theorem archetype_subj_on_obj :
    claimArchetype .tian .xin = some .tianXin := rfl

theorem archetype_obj_on_subj :
    claimArchetype .xin .tian = some .xinTian := rfl

/-! ## § 7 Wen analyzer: per-Wen layered analysis

  A Wen term, once we have its top-level Op, projects through every
  古文-system layer at once. The `WenAnalysis` structure aggregates
  these projections in a single record. -/

/-- All-layers analysis of a Wen term. Atoms (no top Op) leave every field
    `none`; pair/op forms with a top Op fill all positive-tier fields. -/
structure WenAnalysis where
  topOp     : Option Op
  dim       : Option Dimension
  daoLevel  : Option DaoLevel
  sanCai    : Option SanCai
  sanXing   : Option SanXing
  sanShen   : Option SanShen
  sanZhi    : Option SanZhi
  sanBao    : Option SanBao
  sanDi     : Option SanDi
  deriving Repr

/-- Lift a DaoLevel to each 三-system, with `none` for the negative tier. -/
def daoToSan (d : DaoLevel) :
    Option SanCai × Option SanXing × Option SanShen
      × Option SanZhi × Option SanBao × Option SanDi :=
  match d with
  | .feiDao => (none, none, none, none, none, none)
  | d       => (some (SanCai.fromDaoLevel d),
                some (SanXing.fromDaoLevel d),
                some (SanShen.fromDaoLevel d),
                some (SanZhi.fromDaoLevel d),
                some (SanBao.fromDaoLevel d),
                some (SanDi.fromDaoLevel d))

/-- Project a Wen through every layer. -/
def analyzeWen (w : Wen) : WenAnalysis :=
  let op := wenTopOp w
  let dim := op.map Op.dim
  let dao := op.map Op.daoLevel
  match dao with
  | none =>
      ⟨op, dim, none, none, none, none, none, none, none⟩
  | some d =>
      let (cai, xing, shen, zhi, bao, di) := daoToSan d
      ⟨op, dim, some d, cai, xing, shen, zhi, bao, di⟩

/-! ### Worked examples -/

/-- 者-form is at 道 tier across every system. -/
theorem analyze_zhe (b : String) (body : Wen) :
    (analyzeWen (Wen.Zhe b body)).daoLevel = some DaoLevel.tian ∧
    (analyzeWen (Wen.Zhe b body)).sanCai   = some SanCai.tian ∧
    (analyzeWen (Wen.Zhe b body)).sanXing  = some SanXing.yuanCheng ∧
    (analyzeWen (Wen.Zhe b body)).sanShen  = some SanShen.faShen ∧
    (analyzeWen (Wen.Zhe b body)).sanZhi   = some SanZhi.shengEr ∧
    (analyzeWen (Wen.Zhe b body)).sanBao   = some SanBao.shen :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 方-form (D4 时序 续) is at 心道 tier across every system. -/
theorem analyze_fang (x : Wen) :
    (analyzeWen (Wen.Fang x)).daoLevel = some DaoLevel.xin ∧
    (analyzeWen (Wen.Fang x)).sanCai   = some SanCai.di ∧
    (analyzeWen (Wen.Fang x)).sanXing  = some SanXing.bianJiSuoZhi ∧
    (analyzeWen (Wen.Fang x)).sanShen  = some SanShen.huaShen ∧
    (analyzeWen (Wen.Fang x)).sanZhi   = some SanZhi.kunEr ∧
    (analyzeWen (Wen.Fang x)).sanBao   = some SanBao.jing :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 也-form (D5 言态) is at 中道 tier across every system. -/
theorem analyze_ye (x : Wen) :
    (analyzeWen (Wen.Ye x)).daoLevel = some DaoLevel.ren ∧
    (analyzeWen (Wen.Ye x)).sanCai   = some SanCai.ren ∧
    (analyzeWen (Wen.Ye x)).sanXing  = some SanXing.yiTaQi ∧
    (analyzeWen (Wen.Ye x)).sanShen  = some SanShen.baoShen ∧
    (analyzeWen (Wen.Ye x)).sanZhi   = some SanZhi.xueEr ∧
    (analyzeWen (Wen.Ye x)).sanBao   = some SanBao.qi :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Atoms have no analysis (no top Op). -/
theorem analyze_atom (n : String) :
    (analyzeWen (.atom n)).topOp = none ∧
    (analyzeWen (.atom n)).daoLevel = none :=
  ⟨rfl, rfl⟩

/-- The dimension is recoverable when there is a top Op. -/
theorem analyze_zhe_dim (b : String) (body : Wen) :
    (analyzeWen (Wen.Zhe b body)).dim = some Dimension.D1 := rfl

theorem analyze_fang_dim (x : Wen) :
    (analyzeWen (Wen.Fang x)).dim = some Dimension.D4 := rfl

theorem analyze_fei_dim (x : Wen) :
    (analyzeWen (Wen.Fei x)).dim = some Dimension.D6 := rfl

end SSBX.Foundation.Jian.JianYiBridge
