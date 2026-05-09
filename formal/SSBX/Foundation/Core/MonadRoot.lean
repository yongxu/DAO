/-
Monad root layer.

This module is the single-root generative layer.  The roster graph remains a
registry/dependency graph and may have many lexical roots.  Here every formal
SSBX item must return to the unique root `一元` through a face and a single
registered glyph.
-/
import SSBX.Foundation.Core.Monism
import SSBX.Foundation.Bagua.BenZheng
import SSBX.Truth.ClaimLedger

namespace SSBX.Foundation.Core.MonadRoot

open SSBX.Roster
open SSBX.Truth
open SSBX.Truth.ClaimLedger
open SSBX.Foundation.Core.Monism
open SSBX.Foundation.Bagua.BenZheng  -- Ben / Zheng / Mian / Quadrant 新核心

-- DELETED 2026-05-10 (P5b): `inductive Face` 12-枚举 + `Face.label` + `allFaces` + `all_faces_complete` + `Face.toMian`
-- 全部被 `Mian = Ben × Zheng = 16` 取代 (见 SSBX.Foundation.Bagua.BenZheng).
-- 旧 face 名 (物面/生面/etc.) 通过 (Ben, Zheng) 元组直接表达：
--   物面=(.wu,.jiFaint), 注意面=(.wu,.shiForce), 模面=(.wu,.jiOccasion), 文面=(.wu,.shiTime),
--   生面=(.dong,.jiFaint), 心面=(.dong,.shiForce), 理面=(.dong,.jiOccasion), 价值面=(.dong,.shiTime),
--   人面=(.jian,.jiFaint), 审校面=(.jian,.shiForce), 证明面=(.jian,.jiOccasion), 真理面=(.jian,.shiTime).
-- 4 个 事-row cells (兆/趋/变/史) 留作未来 事-substrate atoms 注册。


/-- Core glyphs are the compressed lexical layer between faces and all registered atoms. -/
inductive CoreAtom where
  | «一»
  | «元»
  | «之»
  | «法»
  | «行»
  | «成»
  | «序»
  | «物»
  | «场»
  | «形»
  | «动»
  | «变»
  | «生»
  | «续»
  | «开»
  | «闭»
  | «审»
  | «校»
  | «证»
  | «真»
  | «正»
  | «邪»
  | «夺»
  | «共»
  | «仁»
  | «道»
  | «模»
  | «度»
  | «期»
  | «算»
  | «理»
  | «心»
  | «聚»
  | «焦»
  | «意»
  | «识»
  | «注»
  | «人»
  | «做»
  | «齐»
  | «控»
  | «天»
  | «子»
  deriving DecidableEq, Repr

namespace CoreAtom

def label : CoreAtom -> String
  | .«一» => "一"
  | .«元» => "元"
  | .«之» => "之"
  | .«法» => "法"
  | .«行» => "行"
  | .«成» => "成"
  | .«序» => "序"
  | .«物» => "物"
  | .«场» => "场"
  | .«形» => "形"
  | .«动» => "动"
  | .«变» => "变"
  | .«生» => "生"
  | .«续» => "续"
  | .«开» => "开"
  | .«闭» => "闭"
  | .«审» => "审"
  | .«校» => "校"
  | .«证» => "证"
  | .«真» => "真"
  | .«正» => "正"
  | .«邪» => "邪"
  | .«夺» => "夺"
  | .«共» => "共"
  | .«仁» => "仁"
  | .«道» => "道"
  | .«模» => "模"
  | .«度» => "度"
  | .«期» => "期"
  | .«算» => "算"
  | .«理» => "理"
  | .«心» => "心"
  | .«聚» => "聚"
  | .«焦» => "焦"
  | .«意» => "意"
  | .«识» => "识"
  | .«注» => "注"
  | .«人» => "人"
  | .«做» => "做"
  | .«齐» => "齐"
  | .«控» => "控"
  | .«天» => "天"
  | .«子» => "子"

/-- Every core atom is represented by an already registered single glyph. -/
def glyph : CoreAtom -> AtomName
  | .«一» => .«一»
  | .«元» => .«元»
  | .«之» => .«之»
  | .«法» => .«法»
  | .«行» => .«行»
  | .«成» => .«成»
  | .«序» => .«序»
  | .«物» => .«物»
  | .«场» => .«场»
  | .«形» => .«形»
  | .«动» => .«动»
  | .«变» => .«变»
  | .«生» => .«生»
  | .«续» => .«续»
  | .«开» => .«开»
  | .«闭» => .«闭»
  | .«审» => .«审»
  | .«校» => .«校»
  | .«证» => .«证»
  | .«真» => .«真»
  | .«正» => .«正»
  | .«邪» => .«邪»
  | .«夺» => .«夺»
  | .«共» => .«共»
  | .«仁» => .«仁»
  | .«道» => .«道»
  | .«模» => .«模»
  | .«度» => .«度»
  | .«期» => .«期»
  | .«算» => .«算»
  | .«理» => .«理»
  | .«心» => .«心»
  | .«聚» => .«聚»
  | .«焦» => .«焦»
  | .«意» => .«意»
  | .«识» => .«识»
  | .«注» => .«注»
  | .«人» => .«人»
  | .«做» => .«做»
  | .«齐» => .«齐»
  | .«控» => .«控»
  | .«天» => .«天»
  | .«子» => .«子»

end CoreAtom

def allCoreAtoms : List CoreAtom :=
  [.«一», .«元», .«之», .«法», .«行», .«成», .«序», .«物», .«场», .«形», .«动», .«变», .«生», .«续», .«开», .«闭», .«审», .«校», .«证», .«真», .«正», .«邪», .«夺», .«共», .«仁», .«道», .«模», .«度», .«期», .«算», .«理», .«心», .«聚», .«焦», .«意», .«识», .«注», .«人», .«做», .«齐», .«控», .«天», .«子»]

theorem all_core_atoms_complete (c : CoreAtom) : c ∈ allCoreAtoms := by
  cases c <;> decide

theorem core_atom_glyph_registered (c : CoreAtom) : CoreAtom.glyph c ∈ allAtoms := by
  cases c <;> decide

/-- Every registered atom is derived from exactly one core atom. -/
def atomCore : AtomName -> CoreAtom
  | .«显» => .«法»
  | .«未» => .«法»
  | .«尽» => .«法»
  | .«间» => .«法»
  | .«可» => .«法»
  | .«生» => .«生»
  | .«续» => .«续»
  | .«开» => .«开»
  | .«闭» => .«闭»
  | .«绝» => .«闭»
  | .«断» => .«闭»
  | .«达» => .«生»
  | .«候» => .«法»
  | .«新» => .«法»
  | .«场» => .«场»
  | .«焦» => .«焦»
  | .«物» => .«物»
  | .«境» => .«物»
  | .«系» => .«物»
  | .«心» => .«心»
  | .«身» => .«物»
  | .«态» => .«物»
  | .«状» => .«物»
  | .«维» => .«生»
  | .«形» => .«形»
  | .«相» => .«物»
  | .«因» => .«物»
  | .«结» => .«物»
  | .«据» => .«物»
  | .«证» => .«证»
  | .«迹» => .«物»
  | .«史» => .«物»
  | .«积» => .«物»
  | .«精» => .«物»
  | .«气» => .«物»
  | .«耦» => .«模»
  | .«神» => .«物»
  | .«合» => .«法»
  | .«法» => .«法»
  | .«悖» => .«法»
  | .«入» => .«法»
  | .«待» => .«法»
  | .«行» => .«行»
  | .«成» => .«成»
  | .«冻» => .«生»
  | .«修» => .«生»
  | .«复» => .«生»
  | .«转» => .«生»
  | .«动» => .«动»
  | .«元» => .«元»
  | .«几» => .«物»
  | .«权» => .«模»
  | .«重» => .«模»
  | .«差» => .«模»
  | .«势» => .«模»
  | .«强» => .«模»
  | .«向» => .«模»
  | .«临» => .«物»
  | .«岐» => .«物»
  | .«机» => .«模»
  | .«扰» => .«物»
  | .«变» => .«变»
  | .«应» => .«生»
  | .«伤» => .«物»
  | .«散» => .«物»
  | .«坍» => .«物»
  | .«径» => .«物»
  | .«返» => .«物»
  | .«限» => .«生»
  | .«暂» => .«生»
  | .«稳» => .«生»
  | .«展» => .«生»
  | .«审» => .«审»
  | .«校» => .«校»
  | .«验» => .«校»
  | .«异» => .«审»
  | .«众» => .«审»
  | .«互» => .«审»
  | .«受» => .«审»
  | .«独» => .«审»
  | .«查» => .«审»
  | .«源» => .«审»
  | .«执» => .«审»
  | .«著» => .«审»
  | .«黜» => .«审»
  | .«蔽» => .«审»
  | .«程» => .«审»
  | .«败» => .«审»
  | .«伪» => .«审»
  | .«似» => .«审»
  | .«实» => .«审»
  | .«真» => .«真»
  | .«通» => .«生»
  | .«流» => .«生»
  | .«和» => .«生»
  | .«平» => .«生»
  | .«危» => .«正»
  | .«正» => .«正»
  | .«邪» => .«邪»
  | .«夺» => .«夺»
  | .«依» => .«夺»
  | .«压» => .«夺»
  | .«护» => .«生»
  | .«存» => .«生»
  | .«偏» => .«夺»
  | .«同» => .«共»
  | .«筛» => .«夺»
  | .«放» => .«夺»
  | .«抑» => .«夺»
  | .«汰» => .«夺»
  | .«益» => .«夺»
  | .«损» => .«夺»
  | .«险» => .«夺»
  | .«率» => .«模»
  | .«阈» => .«模»
  | .«效» => .«模»
  | .«责» => .«模»
  | .«好» => .«正»
  | .«坏» => .«正»
  | .«自» => .«物»
  | .«由» => .«正»
  | .«繁» => .«正»
  | .«荣» => .«正»
  | .«义» => .«正»
  | .«善» => .«正»
  | .«己» => .«共»
  | .«共» => .«共»
  | .«仁» => .«仁»
  | .«道» => .«道»
  | .«度» => .«度»
  | .«期» => .«期»
  | .«及» => .«法»
  | .«外» => .«法»
  | .«序» => .«序»
  | .«周» => .«真»
  | .«回» => .«审»
  | .«观» => .«审»
  | .«照» => .«审»
  | .«辨» => .«理»
  | .«识» => .«识»
  | .«知» => .«理»
  | .«智» => .«理»
  | .«感» => .«心»
  | .«择» => .«心»
  | .«情» => .«心»
  | .«礼» => .«人»
  | .«信» => .«人»
  | .«性» => .«人»
  | .«能» => .«生»
  | .«归» => .«证»
  | .«轨» => .«理»
  | .«息» => .«生»
  | .«迫» => .«夺»
  | .«替» => .«物»
  | .«基» => .«物»
  | .«线» => .«物»
  | .«域» => .«物»
  | .«试» => .«真»
  | .«定» => .«真»
  | .«再» => .«生»
  | .«关» => .«生»
  | .«格» => .«物»
  | .«模» => .«模»
  | .«面» => .«模»
  | .«评» => .«模»
  | .«价» => .«模»
  | .«础» => .«模»
  | .«科» => .«模»
  | .«学» => .«模»
  | .«逻» => .«理»
  | .«辑» => .«理»
  | .«构» => .«理»
  | .«造» => .«理»
  | .«纳» => .«理»
  | .«一» => .«一»
  | .«论» => .«理»
  | .«普» => .«理»
  | .«遍» => .«理»
  | .«理» => .«理»
  | .«算» => .«算»
  | .«演» => .«算»
  | .«明» => .«理»
  | .«天» => .«天»
  | .«子» => .«子»
  | .«之» => .«之»
  | .«人» => .«人»
  | .«世» => .«物»
  | .«界» => .«物»
  | .«对» => .«物»
  | .«聚» => .«聚»
  | .«意» => .«意»
  | .«图» => .«意»
  | .«控» => .«控»
  | .«齐» => .«齐»
  | .«做» => .«做»
  | .«目» => .«人»
  | .«标» => .«人»
  | .«为» => .«法»
  | .«制» => .«人»
  | .«层» => .«人»
  | .«注» => .«注»
  | .«调» => .«注»
  | .«门» => .«注»
  | .«分» => .«注»
  | .«配» => .«注»
  | .«持» => .«注»
  | .«竞» => .«注»
  | .«争» => .«注»
  | .«记» => .«注»
  | .«忆» => .«注»
  | .«上» => .«注»
  | .«下» => .«注»
  | .«而» => .«法»
  | .«工» => .«注»
  | .«作» => .«做»
  | .«底» => .«物»
  | .«露» => .«法»
  | .«隙» => .«法»
  | .«发» => .«生»
  | .«凝» => .«物»
  | .«剖» => .«模»
  | .«所» => .«之»
  | .«是» => .«真»
  | .«洽» => .«法»
  | .«者» => .«法»
  | .«也» => .«法»
  | .«于» => .«法»
  | .«於» => .«法»
  | .«已» => .«法»
  | .«七» => .«算»
  | .«三» => .«算»
  | .«不» => .«法»
  | .«与» => .«法»
  | .«中» => .«正»
  | .«乃» => .«法»
  | .«九» => .«算»
  | .«事» => .«物»
  | .«二» => .«算»
  | .«五» => .«算»
  | .«亦» => .«法»
  | .«仍» => .«续»
  | .«以» => .«法»
  | .«件» => .«物»
  | .«位» => .«模»
  | .«例» => .«物»
  | .«保» => .«正»
  | .«值» => .«度»
  | .«全» => .«算»
  | .«八» => .«算»
  | .«六» => .«算»
  | .«其» => .«法»
  | .«册» => .«法»
  | .«冒» => .«审»
  | .«准» => .«证»
  | .«凡» => .«法»
  | .«出» => .«成»
  | .«判» => .«审»
  | .«别» => .«法»
  | .«前» => .«法»
  | .«十» => .«算»
  | .«卷» => .«法»
  | .«原» => .«元»
  | .«口» => .«法»
  | .«古» => .«法»
  | .«句» => .«法»
  | .«只» => .«法»
  | .«名» => .«法»
  | .«含» => .«法»
  | .«四» => .«算»
  | .«型» => .«模»
  | .«增» => .«生»
  | .«始» => .«元»
  | .«字» => .«法»
  | .«守» => .«法»
  | .«完» => .«成»
  | .«导» => .«理»
  | .«尺» => .«度»
  | .«常» => .«法»
  | .«式» => .«证»
  | .«当» => .«法»
  | .«录» => .«法»
  | .«律» => .«法»
  | .«得» => .«成»
  | .«微» => .«变»
  | .«德» => .«正»
  | .«指» => .«理»
  | .«推» => .«理»
  | .«收» => .«成»
  | .«故» => .«法»
  | .«整» => .«成»
  | .«文» => .«法»
  | .«易» => .«变»
  | .«有» => .«法»
  | .«本» => .«元»
  | .«束» => .«成»
  | .«极» => .«度»
  | .«染» => .«法»
  | .«根» => .«一»
  | .«此» => .«法»
  | .«渲» => .«法»
  | .«版» => .«法»
  | .«皆» => .«法»
  | .«空» => .«模»
  | .«立» => .«成»
  | .«箱» => .«法»
  | .«篇» => .«法»
  | .«籍» => .«法»
  | .«类» => .«模»
  | .«终» => .«续»
  | .«经» => .«理»
  | .«缺» => .«法»
  | .«美» => .«正»
  | .«背» => .«邪»
  | .«致» => .«理»
  | .«补» => .«法»
  | .«表» => .«法»
  | .«见» => .«审»
  | .«言» => .«法»
  | .«语» => .«法»
  | .«诸» => .«法»
  | .«谓» => .«法»
  | .«象» => .«模»
  | .«连» => .«续»
  | .«述» => .«法»
  | .«递» => .«理»
  | .«遇» => .«心»
  | .«量» => .«算»
  | .«锚» => .«证»
  | .«随» => .«续»
  | .«非» => .«法»
  | .«项» => .«模»
  | .«高» => .«模»
  | .«黑» => .«法»
  | .«恶» => .«邪»
  -- BenZheng-related (14 new): default cores for R3 mode + R4 flip + R5 shi + 16-grid sub-modes
  | .«健» => .«法»  -- R3 乾 mode (健行不息)
  | .«悦» => .«心»  -- R3 兑 mode (悦感)
  | .«起» => .«动»  -- R3 震 mode (起动)
  | .«止» => .«闭»  -- R3 艮 mode (止息)
  | .«顺» => .«法»  -- R3 坤 mode (顺势)
  | .«改» => .«变»  -- R4 flip y1
  | .«化» => .«变»  -- R4 flip y2
  | .«迁» => .«动»  -- R5 shiNext
  | .«溯» => .«动»  -- R5 shiPrev
  | .«萌» => .«生»  -- 16-grid 動之微
  | .«长» => .«续»  -- 16-grid 動之进
  | .«缘» => .«法»  -- 16-grid 間之微
  | .«兆» => .«法»  -- 16-grid 事之微
  | .«趋» => .«模»  -- 16-grid 事之进

def CoreDerives (c : CoreAtom) (a : AtomName) : Prop :=
  atomCore a = c

theorem all_atoms_have_core (a : AtomName) : ∃ c, CoreDerives c a :=
  ⟨atomCore a, rfl⟩

theorem atom_core_glyph_registered (a : AtomName) : CoreAtom.glyph (atomCore a) ∈ allAtoms := by
  cases a <;> decide

/-- The enforced primary face of every registered single glyph. -/
def atomPrimaryMian : AtomName -> Mian
  | .«显» => ((.wu, .shiTime) : Mian)
  | .«未» => ((.wu, .shiTime) : Mian)
  | .«尽» => ((.wu, .shiTime) : Mian)
  | .«间» => ((.wu, .shiTime) : Mian)
  | .«可» => ((.wu, .shiTime) : Mian)
  | .«生» => ((.dong, .jiFaint) : Mian)
  | .«续» => ((.dong, .jiFaint) : Mian)
  | .«开» => ((.dong, .jiFaint) : Mian)
  | .«闭» => ((.dong, .jiFaint) : Mian)
  | .«绝» => ((.dong, .jiFaint) : Mian)
  | .«断» => ((.dong, .jiFaint) : Mian)
  | .«达» => ((.dong, .jiFaint) : Mian)
  | .«候» => ((.wu, .shiTime) : Mian)
  | .«新» => ((.wu, .shiTime) : Mian)
  | .«场» => ((.wu, .jiFaint) : Mian)
  | .«焦» => ((.dong, .shiForce) : Mian)
  | .«物» => ((.wu, .jiFaint) : Mian)
  | .«境» => ((.wu, .jiFaint) : Mian)
  | .«系» => ((.wu, .jiFaint) : Mian)
  | .«心» => ((.dong, .shiForce) : Mian)
  | .«身» => ((.wu, .jiFaint) : Mian)
  | .«态» => ((.wu, .jiFaint) : Mian)
  | .«状» => ((.wu, .jiFaint) : Mian)
  | .«维» => ((.dong, .jiFaint) : Mian)
  | .«形» => ((.wu, .jiFaint) : Mian)
  | .«相» => ((.wu, .jiFaint) : Mian)
  | .«因» => ((.wu, .jiFaint) : Mian)
  | .«结» => ((.wu, .jiFaint) : Mian)
  | .«据» => ((.wu, .jiFaint) : Mian)
  | .«证» => ((.jian, .jiOccasion) : Mian)
  | .«迹» => ((.wu, .jiFaint) : Mian)
  | .«史» => ((.wu, .jiFaint) : Mian)
  | .«积» => ((.wu, .jiFaint) : Mian)
  | .«精» => ((.wu, .jiFaint) : Mian)
  | .«气» => ((.wu, .jiFaint) : Mian)
  | .«耦» => ((.wu, .jiOccasion) : Mian)
  | .«神» => ((.wu, .jiFaint) : Mian)
  | .«合» => ((.wu, .shiTime) : Mian)
  | .«法» => ((.wu, .shiTime) : Mian)
  | .«悖» => ((.wu, .shiTime) : Mian)
  | .«入» => ((.wu, .shiTime) : Mian)
  | .«待» => ((.wu, .shiTime) : Mian)
  | .«行» => ((.wu, .shiTime) : Mian)
  | .«成» => ((.wu, .shiTime) : Mian)
  | .«冻» => ((.dong, .jiFaint) : Mian)
  | .«修» => ((.dong, .jiFaint) : Mian)
  | .«复» => ((.dong, .jiFaint) : Mian)
  | .«转» => ((.dong, .jiFaint) : Mian)
  | .«动» => ((.wu, .jiFaint) : Mian)
  | .«元» => ((.jian, .jiOccasion) : Mian)
  | .«几» => ((.wu, .jiFaint) : Mian)
  | .«权» => ((.wu, .jiOccasion) : Mian)
  | .«重» => ((.wu, .jiOccasion) : Mian)
  | .«差» => ((.wu, .jiOccasion) : Mian)
  | .«势» => ((.wu, .jiOccasion) : Mian)
  | .«强» => ((.wu, .jiOccasion) : Mian)
  | .«向» => ((.wu, .jiOccasion) : Mian)
  | .«临» => ((.wu, .jiFaint) : Mian)
  | .«岐» => ((.wu, .jiFaint) : Mian)
  | .«机» => ((.wu, .jiOccasion) : Mian)
  | .«扰» => ((.wu, .jiFaint) : Mian)
  | .«变» => ((.wu, .jiFaint) : Mian)
  | .«应» => ((.dong, .jiFaint) : Mian)
  | .«伤» => ((.wu, .jiFaint) : Mian)
  | .«散» => ((.wu, .jiFaint) : Mian)
  | .«坍» => ((.wu, .jiFaint) : Mian)
  | .«径» => ((.wu, .jiFaint) : Mian)
  | .«返» => ((.wu, .jiFaint) : Mian)
  | .«限» => ((.dong, .jiFaint) : Mian)
  | .«暂» => ((.dong, .jiFaint) : Mian)
  | .«稳» => ((.dong, .jiFaint) : Mian)
  | .«展» => ((.dong, .jiFaint) : Mian)
  | .«审» => ((.jian, .shiForce) : Mian)
  | .«校» => ((.jian, .shiForce) : Mian)
  | .«验» => ((.jian, .shiForce) : Mian)
  | .«异» => ((.jian, .shiForce) : Mian)
  | .«众» => ((.jian, .shiForce) : Mian)
  | .«互» => ((.jian, .shiForce) : Mian)
  | .«受» => ((.jian, .shiForce) : Mian)
  | .«独» => ((.jian, .shiForce) : Mian)
  | .«查» => ((.jian, .shiForce) : Mian)
  | .«源» => ((.jian, .shiForce) : Mian)
  | .«执» => ((.jian, .shiForce) : Mian)
  | .«著» => ((.jian, .shiForce) : Mian)
  | .«黜» => ((.jian, .shiForce) : Mian)
  | .«蔽» => ((.jian, .shiForce) : Mian)
  | .«程» => ((.jian, .shiForce) : Mian)
  | .«败» => ((.jian, .shiForce) : Mian)
  | .«伪» => ((.jian, .shiForce) : Mian)
  | .«似» => ((.jian, .shiForce) : Mian)
  | .«实» => ((.jian, .shiForce) : Mian)
  | .«真» => ((.jian, .shiTime) : Mian)
  | .«通» => ((.dong, .jiFaint) : Mian)
  | .«流» => ((.dong, .jiFaint) : Mian)
  | .«和» => ((.dong, .jiFaint) : Mian)
  | .«平» => ((.dong, .jiFaint) : Mian)
  | .«危» => ((.dong, .shiTime) : Mian)
  | .«正» => ((.dong, .shiTime) : Mian)
  | .«邪» => ((.dong, .shiTime) : Mian)
  | .«夺» => ((.dong, .shiTime) : Mian)
  | .«依» => ((.dong, .shiTime) : Mian)
  | .«压» => ((.dong, .shiTime) : Mian)
  | .«护» => ((.dong, .jiFaint) : Mian)
  | .«存» => ((.dong, .jiFaint) : Mian)
  | .«偏» => ((.dong, .shiTime) : Mian)
  | .«同» => ((.dong, .shiTime) : Mian)
  | .«筛» => ((.dong, .shiTime) : Mian)
  | .«放» => ((.dong, .shiTime) : Mian)
  | .«抑» => ((.dong, .shiTime) : Mian)
  | .«汰» => ((.dong, .shiTime) : Mian)
  | .«益» => ((.dong, .shiTime) : Mian)
  | .«损» => ((.dong, .shiTime) : Mian)
  | .«险» => ((.dong, .shiTime) : Mian)
  | .«率» => ((.wu, .jiOccasion) : Mian)
  | .«阈» => ((.wu, .jiOccasion) : Mian)
  | .«效» => ((.wu, .jiOccasion) : Mian)
  | .«责» => ((.wu, .jiOccasion) : Mian)
  | .«好» => ((.dong, .shiTime) : Mian)
  | .«坏» => ((.dong, .shiTime) : Mian)
  | .«自» => ((.wu, .jiFaint) : Mian)
  | .«由» => ((.dong, .shiTime) : Mian)
  | .«繁» => ((.dong, .shiTime) : Mian)
  | .«荣» => ((.dong, .shiTime) : Mian)
  | .«义» => ((.dong, .shiTime) : Mian)
  | .«善» => ((.dong, .shiTime) : Mian)
  | .«己» => ((.dong, .shiTime) : Mian)
  | .«共» => ((.dong, .shiTime) : Mian)
  | .«仁» => ((.dong, .shiTime) : Mian)
  | .«道» => ((.dong, .shiTime) : Mian)
  | .«度» => ((.jian, .shiTime) : Mian)
  | .«期» => ((.jian, .shiTime) : Mian)
  | .«及» => ((.wu, .shiTime) : Mian)
  | .«外» => ((.wu, .shiTime) : Mian)
  | .«序» => ((.wu, .shiTime) : Mian)
  | .«周» => ((.jian, .shiTime) : Mian)
  | .«回» => ((.jian, .shiForce) : Mian)
  | .«观» => ((.jian, .shiForce) : Mian)
  | .«照» => ((.jian, .shiForce) : Mian)
  | .«辨» => ((.dong, .jiOccasion) : Mian)
  | .«识» => ((.dong, .jiOccasion) : Mian)
  | .«知» => ((.dong, .jiOccasion) : Mian)
  | .«智» => ((.dong, .jiOccasion) : Mian)
  | .«感» => ((.dong, .shiForce) : Mian)
  | .«择» => ((.dong, .shiForce) : Mian)
  | .«情» => ((.dong, .shiForce) : Mian)
  | .«礼» => ((.jian, .jiFaint) : Mian)
  | .«信» => ((.jian, .jiFaint) : Mian)
  | .«性» => ((.jian, .jiFaint) : Mian)
  | .«能» => ((.dong, .jiFaint) : Mian)
  | .«归» => ((.jian, .jiOccasion) : Mian)
  | .«轨» => ((.dong, .jiOccasion) : Mian)
  | .«息» => ((.dong, .jiFaint) : Mian)
  | .«迫» => ((.dong, .shiTime) : Mian)
  | .«替» => ((.wu, .jiFaint) : Mian)
  | .«基» => ((.wu, .jiFaint) : Mian)
  | .«线» => ((.wu, .jiFaint) : Mian)
  | .«域» => ((.wu, .jiFaint) : Mian)
  | .«试» => ((.jian, .shiTime) : Mian)
  | .«定» => ((.jian, .shiTime) : Mian)
  | .«再» => ((.dong, .jiFaint) : Mian)
  | .«关» => ((.dong, .jiFaint) : Mian)
  | .«格» => ((.wu, .jiFaint) : Mian)
  | .«模» => ((.wu, .jiOccasion) : Mian)
  | .«面» => ((.wu, .jiOccasion) : Mian)
  | .«评» => ((.wu, .jiOccasion) : Mian)
  | .«价» => ((.wu, .jiOccasion) : Mian)
  | .«础» => ((.wu, .jiOccasion) : Mian)
  | .«科» => ((.wu, .jiOccasion) : Mian)
  | .«学» => ((.wu, .jiOccasion) : Mian)
  | .«逻» => ((.jian, .jiOccasion) : Mian)
  | .«辑» => ((.jian, .jiOccasion) : Mian)
  | .«构» => ((.jian, .jiOccasion) : Mian)
  | .«造» => ((.jian, .jiOccasion) : Mian)
  | .«纳» => ((.jian, .jiOccasion) : Mian)
  | .«一» => ((.jian, .jiOccasion) : Mian)
  | .«论» => ((.jian, .jiOccasion) : Mian)
  | .«普» => ((.jian, .jiOccasion) : Mian)
  | .«遍» => ((.jian, .jiOccasion) : Mian)
  | .«理» => ((.jian, .jiOccasion) : Mian)
  | .«算» => ((.jian, .jiOccasion) : Mian)
  | .«演» => ((.jian, .jiOccasion) : Mian)
  | .«明» => ((.jian, .jiOccasion) : Mian)
  | .«天» => ((.jian, .shiTime) : Mian)
  | .«子» => ((.dong, .jiFaint) : Mian)
  | .«之» => ((.wu, .shiTime) : Mian)
  | .«人» => ((.jian, .jiFaint) : Mian)
  | .«世» => ((.wu, .jiFaint) : Mian)
  | .«界» => ((.wu, .jiFaint) : Mian)
  | .«对» => ((.wu, .jiFaint) : Mian)
  | .«聚» => ((.dong, .shiForce) : Mian)
  | .«意» => ((.dong, .shiForce) : Mian)
  | .«图» => ((.dong, .shiForce) : Mian)
  | .«控» => ((.jian, .jiFaint) : Mian)
  | .«齐» => ((.jian, .jiFaint) : Mian)
  | .«做» => ((.jian, .jiFaint) : Mian)
  | .«目» => ((.jian, .jiFaint) : Mian)
  | .«标» => ((.jian, .jiFaint) : Mian)
  | .«为» => ((.wu, .shiTime) : Mian)
  | .«制» => ((.jian, .jiFaint) : Mian)
  | .«层» => ((.jian, .jiFaint) : Mian)
  | .«注» => ((.wu, .shiForce) : Mian)
  | .«调» => ((.wu, .shiForce) : Mian)
  | .«门» => ((.wu, .shiForce) : Mian)
  | .«分» => ((.wu, .shiForce) : Mian)
  | .«配» => ((.wu, .shiForce) : Mian)
  | .«持» => ((.wu, .shiForce) : Mian)
  | .«竞» => ((.wu, .shiForce) : Mian)
  | .«争» => ((.wu, .shiForce) : Mian)
  | .«记» => ((.wu, .shiForce) : Mian)
  | .«忆» => ((.wu, .shiForce) : Mian)
  | .«上» => ((.wu, .shiForce) : Mian)
  | .«下» => ((.wu, .shiForce) : Mian)
  | .«而» => ((.wu, .shiTime) : Mian)
  | .«工» => ((.wu, .shiForce) : Mian)
  | .«作» => ((.wu, .shiForce) : Mian)
  | .«底» => ((.wu, .jiFaint) : Mian)
  | .«露» => ((.wu, .shiTime) : Mian)
  | .«隙» => ((.wu, .shiTime) : Mian)
  | .«发» => ((.dong, .jiFaint) : Mian)
  | .«凝» => ((.wu, .jiFaint) : Mian)
  | .«剖» => ((.wu, .jiOccasion) : Mian)
  | .«所» => ((.wu, .shiTime) : Mian)
  | .«是» => ((.jian, .shiTime) : Mian)
  | .«洽» => ((.wu, .shiTime) : Mian)
  | .«者» => ((.wu, .shiTime) : Mian)
  | .«也» => ((.wu, .shiTime) : Mian)
  | .«于» => ((.wu, .shiTime) : Mian)
  | .«於» => ((.wu, .shiTime) : Mian)
  | .«已» => ((.wu, .shiTime) : Mian)
  | .«七» => ((.wu, .jiOccasion) : Mian)
  | .«三» => ((.wu, .jiOccasion) : Mian)
  | .«不» => ((.wu, .shiTime) : Mian)
  | .«与» => ((.wu, .shiTime) : Mian)
  | .«中» => ((.dong, .shiTime) : Mian)
  | .«乃» => ((.wu, .shiTime) : Mian)
  | .«九» => ((.wu, .jiOccasion) : Mian)
  | .«事» => ((.wu, .jiFaint) : Mian)
  | .«二» => ((.wu, .jiOccasion) : Mian)
  | .«五» => ((.wu, .jiOccasion) : Mian)
  | .«亦» => ((.wu, .shiTime) : Mian)
  | .«仍» => ((.wu, .shiTime) : Mian)
  | .«以» => ((.wu, .shiTime) : Mian)
  | .«件» => ((.wu, .jiFaint) : Mian)
  | .«位» => ((.wu, .jiOccasion) : Mian)
  | .«例» => ((.wu, .jiFaint) : Mian)
  | .«保» => ((.dong, .shiTime) : Mian)
  | .«值» => ((.wu, .jiOccasion) : Mian)
  | .«全» => ((.wu, .jiOccasion) : Mian)
  | .«八» => ((.wu, .jiOccasion) : Mian)
  | .«六» => ((.wu, .jiOccasion) : Mian)
  | .«其» => ((.wu, .shiTime) : Mian)
  | .«册» => ((.wu, .shiTime) : Mian)
  | .«冒» => ((.jian, .shiForce) : Mian)
  | .«准» => ((.jian, .jiOccasion) : Mian)
  | .«凡» => ((.wu, .shiTime) : Mian)
  | .«出» => ((.dong, .jiFaint) : Mian)
  | .«判» => ((.jian, .shiForce) : Mian)
  | .«别» => ((.wu, .shiTime) : Mian)
  | .«前» => ((.wu, .shiTime) : Mian)
  | .«十» => ((.wu, .jiOccasion) : Mian)
  | .«卷» => ((.wu, .shiTime) : Mian)
  | .«原» => ((.jian, .jiOccasion) : Mian)
  | .«口» => ((.wu, .shiTime) : Mian)
  | .«古» => ((.wu, .shiTime) : Mian)
  | .«句» => ((.wu, .shiTime) : Mian)
  | .«只» => ((.wu, .shiTime) : Mian)
  | .«名» => ((.wu, .shiTime) : Mian)
  | .«含» => ((.wu, .shiTime) : Mian)
  | .«四» => ((.wu, .jiOccasion) : Mian)
  | .«型» => ((.wu, .jiOccasion) : Mian)
  | .«增» => ((.dong, .jiFaint) : Mian)
  | .«始» => ((.jian, .jiOccasion) : Mian)
  | .«字» => ((.wu, .shiTime) : Mian)
  | .«守» => ((.wu, .shiTime) : Mian)
  | .«完» => ((.jian, .jiOccasion) : Mian)
  | .«导» => ((.dong, .jiOccasion) : Mian)
  | .«尺» => ((.wu, .jiOccasion) : Mian)
  | .«常» => ((.dong, .shiTime) : Mian)
  | .«式» => ((.jian, .jiOccasion) : Mian)
  | .«当» => ((.wu, .shiTime) : Mian)
  | .«录» => ((.wu, .shiTime) : Mian)
  | .«律» => ((.wu, .shiTime) : Mian)
  | .«得» => ((.jian, .jiOccasion) : Mian)
  | .«微» => ((.dong, .jiOccasion) : Mian)
  | .«德» => ((.dong, .shiTime) : Mian)
  | .«指» => ((.dong, .jiOccasion) : Mian)
  | .«推» => ((.dong, .jiOccasion) : Mian)
  | .«收» => ((.jian, .jiOccasion) : Mian)
  | .«故» => ((.wu, .shiTime) : Mian)
  | .«整» => ((.jian, .jiOccasion) : Mian)
  | .«文» => ((.wu, .shiTime) : Mian)
  | .«易» => ((.dong, .jiOccasion) : Mian)
  | .«有» => ((.wu, .shiTime) : Mian)
  | .«本» => ((.wu, .shiTime) : Mian)
  | .«束» => ((.jian, .jiOccasion) : Mian)
  | .«极» => ((.wu, .jiOccasion) : Mian)
  | .«染» => ((.wu, .shiTime) : Mian)
  | .«根» => ((.jian, .jiOccasion) : Mian)
  | .«此» => ((.wu, .shiTime) : Mian)
  | .«渲» => ((.wu, .shiTime) : Mian)
  | .«版» => ((.wu, .shiTime) : Mian)
  | .«皆» => ((.wu, .shiTime) : Mian)
  | .«空» => ((.wu, .jiOccasion) : Mian)
  | .«立» => ((.jian, .jiOccasion) : Mian)
  | .«箱» => ((.wu, .shiTime) : Mian)
  | .«篇» => ((.wu, .shiTime) : Mian)
  | .«籍» => ((.wu, .shiTime) : Mian)
  | .«类» => ((.wu, .jiOccasion) : Mian)
  | .«终» => ((.wu, .shiTime) : Mian)
  | .«经» => ((.dong, .jiOccasion) : Mian)
  | .«缺» => ((.wu, .shiTime) : Mian)
  | .«美» => ((.dong, .shiTime) : Mian)
  | .«背» => ((.dong, .shiTime) : Mian)
  | .«致» => ((.dong, .jiOccasion) : Mian)
  | .«补» => ((.wu, .shiTime) : Mian)
  | .«表» => ((.wu, .shiTime) : Mian)
  | .«见» => ((.jian, .shiForce) : Mian)
  | .«言» => ((.wu, .shiTime) : Mian)
  | .«语» => ((.wu, .shiTime) : Mian)
  | .«诸» => ((.wu, .shiTime) : Mian)
  | .«谓» => ((.wu, .shiTime) : Mian)
  | .«象» => ((.wu, .jiOccasion) : Mian)
  | .«连» => ((.dong, .jiOccasion) : Mian)
  | .«述» => ((.wu, .shiTime) : Mian)
  | .«递» => ((.jian, .jiOccasion) : Mian)
  | .«遇» => ((.dong, .shiForce) : Mian)
  | .«量» => ((.wu, .jiOccasion) : Mian)
  | .«锚» => ((.jian, .jiOccasion) : Mian)
  | .«随» => ((.dong, .jiOccasion) : Mian)
  | .«非» => ((.wu, .shiTime) : Mian)
  | .«项» => ((.wu, .jiOccasion) : Mian)
  | .«高» => ((.wu, .jiOccasion) : Mian)
  | .«黑» => ((.wu, .shiTime) : Mian)
  | .«恶» => ((.dong, .shiTime) : Mian)
  -- BenZheng-related (14 new): primary face under existing 12-Mian system
  -- (P5 will rework to Mian = Ben × Zheng = 16; this is interim for build)
  | .«健» => ((.jian, .shiTime) : Mian)  -- 乾健 = 真理性
  | .«悦» => ((.dong, .shiForce) : Mian)     -- 兑悦 = 心之喜
  | .«起» => ((.wu, .jiFaint) : Mian)     -- 震起 = 物之初动
  | .«止» => ((.wu, .shiTime) : Mian)     -- 艮止 = 律法止息
  | .«顺» => ((.jian, .shiTime) : Mian)  -- 坤顺 = 顺道
  | .«改» => ((.wu, .jiFaint) : Mian)     -- R4 flip y1 = 改物
  | .«化» => ((.wu, .jiFaint) : Mian)     -- R4 flip y2 = 化物
  | .«迁» => ((.wu, .jiFaint) : Mian)     -- 时迁
  | .«溯» => ((.wu, .jiFaint) : Mian)     -- 时溯
  | .«萌» => ((.dong, .jiFaint) : Mian)     -- 萌动 = 生之始
  | .«长» => ((.dong, .jiFaint) : Mian)     -- 长 = 生之续
  | .«缘» => ((.wu, .shiTime) : Mian)     -- 缘 = 关系律法
  | .«兆» => ((.wu, .shiTime) : Mian)     -- 兆 = 事兆
  | .«趋» => ((.wu, .jiOccasion) : Mian)     -- 趋势 = 模型/向

/-- Extra faces record polysemy and cross-domain reuse without breaking single-root reachability. -/
def atomExtraMians : AtomName -> List Mian
  | .«生» => [((.dong, .shiTime) : Mian), ((.wu, .jiOccasion) : Mian)]
  | .«开» => [((.dong, .shiTime) : Mian), ((.jian, .shiTime) : Mian)]
  | .«闭» => [((.dong, .shiTime) : Mian), ((.jian, .shiTime) : Mian)]
  | .«正» => [((.jian, .shiForce) : Mian), ((.jian, .shiTime) : Mian)]
  | .«邪» => [((.jian, .shiForce) : Mian), ((.jian, .shiTime) : Mian)]
  | .«真» => [((.jian, .shiForce) : Mian), ((.dong, .shiTime) : Mian)]
  | .«道» => [((.dong, .shiTime) : Mian), ((.jian, .shiTime) : Mian)]
  | .«人» => [((.dong, .shiForce) : Mian), ((.dong, .shiTime) : Mian)]
  | .«聚» => [((.wu, .shiForce) : Mian)]
  | .«焦» => [((.wu, .shiForce) : Mian)]
  | .«意» => [((.wu, .shiForce) : Mian), ((.dong, .shiTime) : Mian)]
  | .«识» => [((.wu, .shiForce) : Mian), ((.jian, .shiForce) : Mian)]
  | .«注» => [((.dong, .shiForce) : Mian)]
  | .«模» => [((.wu, .jiFaint) : Mian), ((.jian, .jiOccasion) : Mian)]
  | .«证» => [((.jian, .shiForce) : Mian), ((.jian, .shiTime) : Mian)]
  | .«理» => [((.jian, .shiTime) : Mian)]
  | .«一» => [((.jian, .shiTime) : Mian)]
  | .«元» => [((.jian, .shiTime) : Mian)]
  | .«面» => [((.jian, .jiOccasion) : Mian)]
  | .«天» => [((.dong, .jiFaint) : Mian), ((.wu, .jiFaint) : Mian)]
  | .«子» => [((.wu, .jiFaint) : Mian), ((.dong, .shiForce) : Mian), ((.jian, .jiFaint) : Mian)]
  | .«之» => [((.jian, .jiOccasion) : Mian)]
  | .«所» => [((.jian, .shiTime) : Mian)]
  | .«是» => [((.wu, .shiTime) : Mian)]
  | .«洽» => [((.jian, .shiForce) : Mian)]
  | _ => []

def atomMians (a : AtomName) : List Mian :=
  atomPrimaryMian a :: atomExtraMians a

def BelongsToMian (a : AtomName) (m : Mian) : Prop :=
  m ∈ atomMians a

theorem atom_primary_mian_mem (a : AtomName) :
    BelongsToMian a (atomPrimaryMian a) := by
  simp [BelongsToMian, atomMians]

theorem all_atoms_have_mian (a : AtomName) :
    ∃ m, BelongsToMian a m :=
  ⟨atomPrimaryMian a, atom_primary_mian_mem a⟩

/-- Formal non-atom roster nodes.  Atom symbols are represented by `MonadNode.atom`. -/
inductive FormalNode where
  | generated : GenName -> FormalNode
  | primitive : PrimName -> FormalNode
  | recursive : RecName -> FormalNode
  | pending : PendingName -> FormalNode
  deriving DecidableEq, Repr

namespace FormalNode

def label : FormalNode -> String
  | .generated g => GenName.label g
  | .primitive p => PrimName.label p
  | .recursive r => RecName.label r
  | .pending u => PendingName.label u

end FormalNode

/-- The single-root DAG node universe. -/
inductive MonadNode where
  | root : MonadNode
  | mian : Mian -> MonadNode
  | core : CoreAtom -> MonadNode
  | atom : AtomName -> MonadNode
  | formal : FormalNode -> MonadNode
  | construction : ConstructionId -> MonadNode
  | claim : ClaimId -> MonadNode
  deriving DecidableEq, Repr

/-- The unique root.  This is not `一` or `一元论`; it is the source node itself. -/
def «一元» : MonadNode := .root

/-- The whole theory as a generated formal node. -/
def «生生不息论» : MonadNode := .formal (.generated .«生生不息»)

def nodeOfSymbol : Symbol -> MonadNode
  | Symbol.atom a => .atom a
  | Symbol.generated g => .formal (.generated g)
  | Symbol.primitive p => .formal (.primitive p)
  | Symbol.recursive r => .formal (.recursive r)
  | Symbol.pending u => .formal (.pending u)

def symbolToAtom? : Symbol -> Option AtomName
  | Symbol.atom a => some a
  | _ => none

def symbolListAtoms (xs : List Symbol) : List AtomName :=
  xs.filterMap symbolToAtom?

def primitiveAtoms : PrimName -> List AtomName
  | .«域» => [.«域»]
  | .«格» => [.«格»]
  | .«权» => [.«权»]
  | .«生» => [.«生»]
  | .«校» => [.«校»]

def recursiveAtoms : RecName -> List AtomName
  | .«开» => [.«开», .«生»]
  | .«闭» => [.«闭»]
  | .«正» => [.«正»]
  | .«邪» => [.«邪»]
  | .«共开» => [.«共», .«开»]
  | .«好» => [.«好»]
  | .«坏» => [.«坏»]
  | .«自由» => [.«自», .«由»]
  | .«义» => [.«义»]
  | .«善» => [.«善»]
  | .«仁» => [.«仁»]
  | .«道» => [.«道»]
  | .«真» => [.«真»]

def pendingAtoms : PendingName -> List AtomName
  | .«邪续» => [.«邪», .«续»]
  | .«开势投影» => [.«开», .«势»]
  | .«审校数据» => [.«审», .«校», .«据»]
  | .«正邪阈值» => [.«正», .«邪», .«阈»]
  | .«度期计算» => [.«度», .«期», .«算»]
  | .«经验校准» => [.«验», .«校»]

def formalAtoms : FormalNode -> List AtomName
  | .generated g => symbolListAtoms (rootsOfGenerated g)
  | .primitive p => primitiveAtoms p
  | .recursive r => recursiveAtoms r
  | .pending u => pendingAtoms u

def firstAtomOrFallback : List AtomName -> AtomName
  | a :: _ => a
  | [] => .«未»

def formalPrimaryAtom (n : FormalNode) : AtomName :=
  firstAtomOrFallback (formalAtoms n)

/-- If this theorem fails, a formal non-atom node has no single-glyph anchor. -/
theorem formal_primary_atom_mem (n : FormalNode) :
    formalPrimaryAtom n ∈ formalAtoms n := by
  cases n with
  | generated g => cases g <;> native_decide
  | primitive p => cases p <;> native_decide
  | recursive r => cases r <;> native_decide
  | pending u => cases u <;> native_decide

theorem all_formal_nodes_have_atom (n : FormalNode) :
    ∃ a, a ∈ formalAtoms n :=
  ⟨formalPrimaryAtom n, formal_primary_atom_mem n⟩

/-- Every high-level construction stage also returns to a single registered glyph. -/
def constructionPrimaryAtom : ConstructionId -> AtomName
  | .gammaFieldRoot => .«场»
  | .jianRoot => .«间»
  | .aspectTriad => .«位»
  | .yuanTriad => .«几»
  | .systemDynamics => .«机»
  | .universalProofPrinciple => .«证»
  | .openCloseCore => .«开»
  | .auditCore => .«审»
  | .valueCore => .«道»
  | .actionCore => .«行»
  | .attentionCore => .«注»
  | .humanAlignmentCore => .«人»
  | .modelAdequacyCore => .«模»
  | .truthCore => .«真»
  | .cicAsFormalModel => .«构»
  | .ssbxTheory => .«生»

def claimPrimaryFormal : ClaimId -> FormalNode
  | .openDefinition => .recursive .«开»
  | .closeDefinition => .recursive .«闭»
  | .rightDefinition => .recursive .«正»
  | .wrongDefinition => .recursive .«邪»
  | .goodDefinition => .recursive .«好»
  | .badDefinition => .recursive .«坏»
  | .freedomDefinition => .recursive .«自由»
  | .flourishingDefinition => .generated .«繁荣»
  | .yiDefinition => .recursive .«义»
  | .shanDefinition => .recursive .«善»
  | .renDefinition => .recursive .«仁»
  | .daoDefinition => .recursive .«道»
  | .trueDaoDefinition => .generated .«真道»
  | .auditUnbrokenDefinition => .generated .«审校不败»
  | .omegaInterface => .primitive .«权»
  | .omegaBInterface => .primitive .«权»
  | .piOpenInterface => .primitive .«校»
  | .thresholdProtocol => .pending .«正邪阈值»
  | .triValueConservativity => .generated .«未定»
  | .generatedRootsDiscipline => .generated .«可生»
  | .recursiveSemanticsDiscipline => .recursive .«开»
  | .rosterTextComplete => .generated .«生生不息»
  | .wenyanOperatorTableComplete => .generated .«可校»
  | .sourceTextClaimMapping => .generated .«生生不息»
  | .openValueAxiomClaim => .recursive .«开»
  | .auditReliabilityAxiomClaim => .generated .«审校不败»
  | .omegaAdequacyAxiomClaim => .primitive .«权»
  | .omegaBAdequacyAxiomClaim => .primitive .«权»
  | .piOpenAdequacyAxiomClaim => .primitive .«校»
  | .truthPathAxiomClaim => .generated .«真道»
  | .recommendationI1Evil => .generated .«邪行»
  | .recommendationI2Right => .generated .«正行»
  | .recommendationI2Ren => .recursive .«仁»
  | .recommendationI2CandidateTrueDao => .generated .«真道»
  | .recommendationI3ProtectiveClosure => .generated .«护闭»
  | .semanticAdequacyClaim => .generated .«可校»
  | .absoluteTruthClaim => .generated .«生生不息»
  | .rootToSsbxLiClaim => .generated .«生生不息»

def claimPrimaryAtom (c : ClaimId) : AtomName :=
  formalPrimaryAtom (claimPrimaryFormal c)

def claimNodes (c : ClaimId) : List MonadNode :=
  [.formal (claimPrimaryFormal c)]

/-- A uniform view of every non-face structure that must return to a glyph. -/
inductive StructureNode where
  | formal : FormalNode -> StructureNode
  | construction : ConstructionId -> StructureNode
  | claim : ClaimId -> StructureNode
  deriving DecidableEq, Repr

namespace StructureNode

def node : StructureNode -> MonadNode
  | .formal n => .formal n
  | .construction k => .construction k
  | .claim c => .claim c

def primaryAtom : StructureNode -> AtomName
  | .formal n => formalPrimaryAtom n
  | .construction k => constructionPrimaryAtom k
  | .claim c => claimPrimaryAtom c

end StructureNode

/-- Immediate edges of the single-root DAG. -/
def DirectEdge : MonadNode -> MonadNode -> Prop
  | .root, .mian _ => True
  | .mian f, .core c => f ∈ atomMians (CoreAtom.glyph c)
  | .core c, .atom a => atomCore a = c
  | .atom a, .formal n => a ∈ formalAtoms n
  | .atom a, .construction k => a = constructionPrimaryAtom k
  | .atom a, .claim c => a = claimPrimaryAtom c
  | .formal n, .claim c => n = claimPrimaryFormal c
  | _, _ => False

inductive Reachable : MonadNode -> MonadNode -> Prop
  | refl (n : MonadNode) : Reachable n n
  | tail {a b c : MonadNode} : Reachable a b -> DirectEdge b c -> Reachable a c

/-- Root-to-face path. -/
def mianRootPath (f : Mian) : Reachable «一元» (.mian f) :=
  Reachable.tail (Reachable.refl «一元») (by simp [«一元», DirectEdge])

/-- Root-to-core-atom path via the core glyph's primary face. -/
def coreRootPath (c : CoreAtom) : Reachable «一元» (.core c) :=
  Reachable.tail (mianRootPath (atomPrimaryMian (CoreAtom.glyph c)))
    (by simp [DirectEdge, atomMians])

/-- Root-to-atom path via the atom's core atom. -/
def atomRootPath (a : AtomName) : Reachable «一元» (.atom a) :=
  Reachable.tail (coreRootPath (atomCore a)) (by simp [DirectEdge])

/-- Root-to-formal-node path via a registered single-glyph anchor. -/
def formalRootPath (n : FormalNode) : Reachable «一元» (.formal n) :=
  Reachable.tail (atomRootPath (formalPrimaryAtom n))
    (by simpa [DirectEdge] using formal_primary_atom_mem n)

/-- Root-to-construction-stage path via the stage's primary glyph. -/
def constructionRootPath (k : ConstructionId) : Reachable «一元» (.construction k) :=
  Reachable.tail (atomRootPath (constructionPrimaryAtom k)) (by simp [DirectEdge])

/-- Root-to-claim path via the claim's primary glyph. -/
def claimRootPath (c : ClaimId) : Reachable «一元» (.claim c) :=
  Reachable.tail (atomRootPath (claimPrimaryAtom c)) (by simp [DirectEdge, claimPrimaryAtom])

theorem formal_nodes_return_single_atom (n : FormalNode) :
    DirectEdge (.atom (formalPrimaryAtom n)) (.formal n) := by
  simpa [DirectEdge] using formal_primary_atom_mem n

theorem construction_nodes_return_single_atom (k : ConstructionId) :
    DirectEdge (.atom (constructionPrimaryAtom k)) (.construction k) := by
  simp [DirectEdge]

theorem claims_return_single_atom (c : ClaimId) :
    DirectEdge (.atom (claimPrimaryAtom c)) (.claim c) := by
  simp [DirectEdge, claimPrimaryAtom]

theorem structures_return_single_atom (s : StructureNode) :
    DirectEdge (.atom (StructureNode.primaryAtom s)) (StructureNode.node s) := by
  cases s with
  | formal n => exact formal_nodes_return_single_atom n
  | construction k => exact construction_nodes_return_single_atom k
  | claim c => exact claims_return_single_atom c

theorem structures_return_atom_and_root (s : StructureNode) :
    Reachable «一元» (.atom (StructureNode.primaryAtom s)) ∧
    Reachable «一元» (StructureNode.node s) := by
  constructor
  · exact atomRootPath (StructureNode.primaryAtom s)
  · exact Reachable.tail (atomRootPath (StructureNode.primaryAtom s))
      (structures_return_single_atom s)

theorem all_mians_from_root : ∀ f : Mian, Reachable «一元» (.mian f) :=
  mianRootPath

theorem all_core_atoms_reachable_from_root : ∀ c : CoreAtom, Reachable «一元» (.core c) :=
  coreRootPath

theorem all_atoms_reachable_from_root : ∀ a : AtomName, Reachable «一元» (.atom a) :=
  atomRootPath

theorem all_atoms_return_through_core (a : AtomName) :
    Reachable «一元» (.core (atomCore a)) ∧
    DirectEdge (.core (atomCore a)) (.atom a) ∧
    Reachable «一元» (.atom a) := by
  exact ⟨coreRootPath (atomCore a), by simp [DirectEdge], atomRootPath a⟩

theorem all_formal_nodes_reachable_from_root :
    ∀ n : FormalNode, Reachable «一元» (.formal n) :=
  formalRootPath

theorem all_construction_nodes_reachable_from_root :
    ∀ k : ConstructionId, Reachable «一元» (.construction k) :=
  constructionRootPath

theorem all_symbols_reachable_from_root :
    ∀ s : Symbol, Reachable «一元» (nodeOfSymbol s) := by
  intro s
  cases s with
  | atom a => exact atomRootPath a
  | generated g => exact formalRootPath (.generated g)
  | primitive p => exact formalRootPath (.primitive p)
  | recursive r => exact formalRootPath (.recursive r)
  | pending u => exact formalRootPath (.pending u)

theorem all_claims_reachable_from_root :
    ∀ c : ClaimId, Reachable «一元» (.claim c) :=
  claimRootPath

def FormalSymbol (s : Symbol) : Prop :=
  s ∈ allSymbols

theorem no_unrooted_symbol {s : Symbol} :
    FormalSymbol s -> Reachable «一元» (nodeOfSymbol s) :=
  fun _ => all_symbols_reachable_from_root s

theorem ssbx_reachable_from_root : Reachable «一元» «生生不息论» :=
  formalRootPath (.generated .«生生不息»)

def allFormalNodes : List FormalNode :=
  (allGenerated.map FormalNode.generated) ++
  (allPrimitives.map FormalNode.primitive) ++
  (allRecursive.map FormalNode.recursive) ++
  (allPending.map FormalNode.pending)

theorem all_formal_nodes_complete (n : FormalNode) : n ∈ allFormalNodes := by
  cases n with
  | generated g => cases g <;> decide
  | primitive p => cases p <;> decide
  | recursive r => cases r <;> decide
  | pending u => cases u <;> decide

def allMonadNodes : List MonadNode :=
  [.root] ++
  (Mian.all.map MonadNode.mian) ++
  (allCoreAtoms.map MonadNode.core) ++
  (allAtoms.map MonadNode.atom) ++
  (allFormalNodes.map MonadNode.formal) ++
  (allConstructionIds.map MonadNode.construction) ++
  (allClaimIds.map MonadNode.claim)

def MonadDAG : List MonadNode :=
  allMonadNodes

def HasIncoming (n : MonadNode) : Prop :=
  ∃ p, DirectEdge p n

def OnlyRoot (dag : List MonadNode) (rootNode : MonadNode) : Prop :=
  rootNode ∈ dag ∧ ¬ HasIncoming rootNode ∧ ∀ n, n ∈ dag -> ¬ HasIncoming n -> n = rootNode

theorem unique_root : OnlyRoot MonadDAG «一元» := by
  constructor
  · decide
  constructor
  · intro h
    rcases h with ⟨p, hp⟩
    cases p <;> simp [DirectEdge, «一元»] at hp
  · intro n _ hn
    cases n with
    | root => rfl
    | mian m =>
        exfalso
        exact hn ⟨.root, by simp [DirectEdge]⟩
    | core c =>
        exfalso
        exact hn ⟨.mian (atomPrimaryMian (CoreAtom.glyph c)), by simp [DirectEdge, atomMians]⟩
    | atom a =>
        exfalso
        exact hn ⟨.core (atomCore a), by simp [DirectEdge]⟩
    | formal fn =>
        exfalso
        exact hn ⟨.atom (formalPrimaryAtom fn), by simpa [DirectEdge] using formal_primary_atom_mem fn⟩
    | construction k =>
        exfalso
        exact hn ⟨.atom (constructionPrimaryAtom k), by simp [DirectEdge]⟩
    | claim c =>
        exfalso
        exact hn ⟨.atom (claimPrimaryAtom c), by simp [DirectEdge, claimPrimaryAtom]⟩

def distance : MonadNode -> Nat
  | .root => 0
  | .mian _ => 1
  | .core _ => 2
  | .atom _ => 3
  | .formal _ => 4
  | .construction _ => 4
  | .claim _ => 5

def IsMian : MonadNode -> Prop
  | .mian _ => True
  | _ => False

def IsCoreAtom : MonadNode -> Prop
  | .core _ => True
  | _ => False

def IsAtom : MonadNode -> Prop
  | .atom _ => True
  | _ => False

theorem near_root_constraint (x : MonadNode) :
    distance x ≤ 2 -> x = «一元» ∨ IsMian x ∨ IsCoreAtom x := by
  intro h
  cases x <;> simp [distance, IsMian, IsCoreAtom, «一元»] at h ⊢

/-- Acyclicity witness: every direct edge strictly increases monadic distance. -/
def AcyclicByRank (_dag : List MonadNode) : Prop :=
  ∀ {a b : MonadNode}, DirectEdge a b -> distance a < distance b

theorem direct_edge_rank_lt {a b : MonadNode} (h : DirectEdge a b) :
    distance a < distance b := by
  cases a <;> cases b <;> simp [DirectEdge, distance] at h ⊢

theorem monad_dag_acyclic : AcyclicByRank MonadDAG :=
  fun h => direct_edge_rank_lt h

end SSBX.Foundation.Core.MonadRoot
