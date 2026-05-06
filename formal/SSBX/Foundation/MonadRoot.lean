/-
Monad root layer.

This module is the single-root generative layer.  The roster graph remains a
registry/dependency graph and may have many lexical roots.  Here every formal
SSBX item must return to the unique root `一元` through a face and a single
registered glyph.
-/
import SSBX.Foundation.Monism
import SSBX.Truth.ClaimLedger

namespace SSBX.Foundation.MonadRoot

open SSBX.Roster
open SSBX.Truth
open SSBX.Truth.ClaimLedger
open SSBX.Foundation.Monism

/-- `Face` is not a second root.  It is a projection of the one root. -/
inductive Face where
  | «文面» | «物面» | «生面» | «理面» | «心面» | «人面»
  | «模面» | «审校面» | «价值面» | «证明面» | «注意面» | «真理面»
  deriving DecidableEq, Repr

namespace Face

def label : Face -> String
  | .«文面» => "文面"
  | .«物面» => "物面"
  | .«生面» => "生面"
  | .«理面» => "理面"
  | .«心面» => "心面"
  | .«人面» => "人面"
  | .«模面» => "模面"
  | .«审校面» => "审校面"
  | .«价值面» => "价值面"
  | .«证明面» => "证明面"
  | .«注意面» => "注意面"
  | .«真理面» => "真理面"

end Face

def allFaces : List Face :=
  [.«文面», .«物面», .«生面», .«理面», .«心面», .«人面»,
   .«模面», .«审校面», .«价值面», .«证明面», .«注意面», .«真理面»]

theorem all_faces_complete (f : Face) : f ∈ allFaces := by
  cases f <;> decide


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

def CoreDerives (c : CoreAtom) (a : AtomName) : Prop :=
  atomCore a = c

theorem all_atoms_have_core (a : AtomName) : ∃ c, CoreDerives c a :=
  ⟨atomCore a, rfl⟩

theorem atom_core_glyph_registered (a : AtomName) : CoreAtom.glyph (atomCore a) ∈ allAtoms := by
  cases a <;> decide

/-- The enforced primary face of every registered single glyph. -/
def atomPrimaryFace : AtomName -> Face
  | .«显» => .«文面»
  | .«未» => .«文面»
  | .«尽» => .«文面»
  | .«间» => .«文面»
  | .«可» => .«文面»
  | .«生» => .«生面»
  | .«续» => .«生面»
  | .«开» => .«生面»
  | .«闭» => .«生面»
  | .«绝» => .«生面»
  | .«断» => .«生面»
  | .«达» => .«生面»
  | .«候» => .«文面»
  | .«新» => .«文面»
  | .«场» => .«物面»
  | .«焦» => .«心面»
  | .«物» => .«物面»
  | .«境» => .«物面»
  | .«系» => .«物面»
  | .«心» => .«心面»
  | .«身» => .«物面»
  | .«态» => .«物面»
  | .«状» => .«物面»
  | .«维» => .«生面»
  | .«形» => .«物面»
  | .«相» => .«物面»
  | .«因» => .«物面»
  | .«结» => .«物面»
  | .«据» => .«物面»
  | .«证» => .«证明面»
  | .«迹» => .«物面»
  | .«史» => .«物面»
  | .«积» => .«物面»
  | .«精» => .«物面»
  | .«气» => .«物面»
  | .«耦» => .«模面»
  | .«神» => .«物面»
  | .«合» => .«文面»
  | .«法» => .«文面»
  | .«悖» => .«文面»
  | .«入» => .«文面»
  | .«待» => .«文面»
  | .«行» => .«文面»
  | .«成» => .«文面»
  | .«冻» => .«生面»
  | .«修» => .«生面»
  | .«复» => .«生面»
  | .«转» => .«生面»
  | .«动» => .«物面»
  | .«元» => .«证明面»
  | .«几» => .«物面»
  | .«权» => .«模面»
  | .«重» => .«模面»
  | .«差» => .«模面»
  | .«势» => .«模面»
  | .«强» => .«模面»
  | .«向» => .«模面»
  | .«临» => .«物面»
  | .«岐» => .«物面»
  | .«机» => .«模面»
  | .«扰» => .«物面»
  | .«变» => .«物面»
  | .«应» => .«生面»
  | .«伤» => .«物面»
  | .«散» => .«物面»
  | .«坍» => .«物面»
  | .«径» => .«物面»
  | .«返» => .«物面»
  | .«限» => .«生面»
  | .«暂» => .«生面»
  | .«稳» => .«生面»
  | .«展» => .«生面»
  | .«审» => .«审校面»
  | .«校» => .«审校面»
  | .«验» => .«审校面»
  | .«异» => .«审校面»
  | .«众» => .«审校面»
  | .«互» => .«审校面»
  | .«受» => .«审校面»
  | .«独» => .«审校面»
  | .«查» => .«审校面»
  | .«源» => .«审校面»
  | .«执» => .«审校面»
  | .«著» => .«审校面»
  | .«黜» => .«审校面»
  | .«蔽» => .«审校面»
  | .«程» => .«审校面»
  | .«败» => .«审校面»
  | .«伪» => .«审校面»
  | .«似» => .«审校面»
  | .«实» => .«审校面»
  | .«真» => .«真理面»
  | .«通» => .«生面»
  | .«流» => .«生面»
  | .«和» => .«生面»
  | .«平» => .«生面»
  | .«危» => .«价值面»
  | .«正» => .«价值面»
  | .«邪» => .«价值面»
  | .«夺» => .«价值面»
  | .«依» => .«价值面»
  | .«压» => .«价值面»
  | .«护» => .«生面»
  | .«存» => .«生面»
  | .«偏» => .«价值面»
  | .«同» => .«价值面»
  | .«筛» => .«价值面»
  | .«放» => .«价值面»
  | .«抑» => .«价值面»
  | .«汰» => .«价值面»
  | .«益» => .«价值面»
  | .«损» => .«价值面»
  | .«险» => .«价值面»
  | .«率» => .«模面»
  | .«阈» => .«模面»
  | .«效» => .«模面»
  | .«责» => .«模面»
  | .«好» => .«价值面»
  | .«坏» => .«价值面»
  | .«自» => .«物面»
  | .«由» => .«价值面»
  | .«繁» => .«价值面»
  | .«荣» => .«价值面»
  | .«义» => .«价值面»
  | .«善» => .«价值面»
  | .«己» => .«价值面»
  | .«共» => .«价值面»
  | .«仁» => .«价值面»
  | .«道» => .«价值面»
  | .«度» => .«真理面»
  | .«期» => .«真理面»
  | .«及» => .«文面»
  | .«外» => .«文面»
  | .«序» => .«文面»
  | .«周» => .«真理面»
  | .«回» => .«审校面»
  | .«观» => .«审校面»
  | .«照» => .«审校面»
  | .«辨» => .«理面»
  | .«识» => .«理面»
  | .«知» => .«理面»
  | .«智» => .«理面»
  | .«感» => .«心面»
  | .«择» => .«心面»
  | .«情» => .«心面»
  | .«礼» => .«人面»
  | .«信» => .«人面»
  | .«性» => .«人面»
  | .«能» => .«生面»
  | .«归» => .«证明面»
  | .«轨» => .«理面»
  | .«息» => .«生面»
  | .«迫» => .«价值面»
  | .«替» => .«物面»
  | .«基» => .«物面»
  | .«线» => .«物面»
  | .«域» => .«物面»
  | .«试» => .«真理面»
  | .«定» => .«真理面»
  | .«再» => .«生面»
  | .«关» => .«生面»
  | .«格» => .«物面»
  | .«模» => .«模面»
  | .«面» => .«模面»
  | .«评» => .«模面»
  | .«价» => .«模面»
  | .«础» => .«模面»
  | .«科» => .«模面»
  | .«学» => .«模面»
  | .«逻» => .«证明面»
  | .«辑» => .«证明面»
  | .«构» => .«证明面»
  | .«造» => .«证明面»
  | .«纳» => .«证明面»
  | .«一» => .«证明面»
  | .«论» => .«证明面»
  | .«普» => .«证明面»
  | .«遍» => .«证明面»
  | .«理» => .«证明面»
  | .«算» => .«证明面»
  | .«演» => .«证明面»
  | .«明» => .«证明面»
  | .«天» => .«真理面»
  | .«子» => .«生面»
  | .«之» => .«文面»
  | .«人» => .«人面»
  | .«世» => .«物面»
  | .«界» => .«物面»
  | .«对» => .«物面»
  | .«聚» => .«心面»
  | .«意» => .«心面»
  | .«图» => .«心面»
  | .«控» => .«人面»
  | .«齐» => .«人面»
  | .«做» => .«人面»
  | .«目» => .«人面»
  | .«标» => .«人面»
  | .«为» => .«文面»
  | .«制» => .«人面»
  | .«层» => .«人面»
  | .«注» => .«注意面»
  | .«调» => .«注意面»
  | .«门» => .«注意面»
  | .«分» => .«注意面»
  | .«配» => .«注意面»
  | .«持» => .«注意面»
  | .«竞» => .«注意面»
  | .«争» => .«注意面»
  | .«记» => .«注意面»
  | .«忆» => .«注意面»
  | .«上» => .«注意面»
  | .«下» => .«注意面»
  | .«而» => .«文面»
  | .«工» => .«注意面»
  | .«作» => .«注意面»
  | .«底» => .«物面»
  | .«露» => .«文面»
  | .«隙» => .«文面»
  | .«发» => .«生面»
  | .«凝» => .«物面»
  | .«剖» => .«模面»
  | .«所» => .«文面»
  | .«是» => .«真理面»
  | .«洽» => .«文面»
  | .«者» => .«文面»
  | .«也» => .«文面»
  | .«于» => .«文面»
  | .«於» => .«文面»
  | .«已» => .«文面»
  | .«七» => .«模面»
  | .«三» => .«模面»
  | .«不» => .«文面»
  | .«与» => .«文面»
  | .«中» => .«价值面»
  | .«乃» => .«文面»
  | .«九» => .«模面»
  | .«事» => .«物面»
  | .«二» => .«模面»
  | .«五» => .«模面»
  | .«亦» => .«文面»
  | .«仍» => .«文面»
  | .«以» => .«文面»
  | .«件» => .«物面»
  | .«位» => .«模面»
  | .«例» => .«物面»
  | .«保» => .«价值面»
  | .«值» => .«模面»
  | .«全» => .«模面»
  | .«八» => .«模面»
  | .«六» => .«模面»
  | .«其» => .«文面»
  | .«册» => .«文面»
  | .«冒» => .«审校面»
  | .«准» => .«证明面»
  | .«凡» => .«文面»
  | .«出» => .«生面»
  | .«判» => .«审校面»
  | .«别» => .«文面»
  | .«前» => .«文面»
  | .«十» => .«模面»
  | .«卷» => .«文面»
  | .«原» => .«证明面»
  | .«口» => .«文面»
  | .«古» => .«文面»
  | .«句» => .«文面»
  | .«只» => .«文面»
  | .«名» => .«文面»
  | .«含» => .«文面»
  | .«四» => .«模面»
  | .«型» => .«模面»
  | .«增» => .«生面»
  | .«始» => .«证明面»
  | .«字» => .«文面»
  | .«守» => .«文面»
  | .«完» => .«证明面»
  | .«导» => .«理面»
  | .«尺» => .«模面»
  | .«常» => .«价值面»
  | .«式» => .«证明面»
  | .«当» => .«文面»
  | .«录» => .«文面»
  | .«律» => .«文面»
  | .«得» => .«证明面»
  | .«微» => .«理面»
  | .«德» => .«价值面»
  | .«指» => .«理面»
  | .«推» => .«理面»
  | .«收» => .«证明面»
  | .«故» => .«文面»
  | .«整» => .«证明面»
  | .«文» => .«文面»
  | .«易» => .«理面»
  | .«有» => .«文面»
  | .«本» => .«文面»
  | .«束» => .«证明面»
  | .«极» => .«模面»
  | .«染» => .«文面»
  | .«根» => .«证明面»
  | .«此» => .«文面»
  | .«渲» => .«文面»
  | .«版» => .«文面»
  | .«皆» => .«文面»
  | .«空» => .«模面»
  | .«立» => .«证明面»
  | .«箱» => .«文面»
  | .«篇» => .«文面»
  | .«籍» => .«文面»
  | .«类» => .«模面»
  | .«终» => .«文面»
  | .«经» => .«理面»
  | .«缺» => .«文面»
  | .«美» => .«价值面»
  | .«背» => .«价值面»
  | .«致» => .«理面»
  | .«补» => .«文面»
  | .«表» => .«文面»
  | .«见» => .«审校面»
  | .«言» => .«文面»
  | .«语» => .«文面»
  | .«诸» => .«文面»
  | .«谓» => .«文面»
  | .«象» => .«模面»
  | .«连» => .«理面»
  | .«述» => .«文面»
  | .«递» => .«证明面»
  | .«遇» => .«心面»
  | .«量» => .«模面»
  | .«锚» => .«证明面»
  | .«随» => .«理面»
  | .«非» => .«文面»
  | .«项» => .«模面»
  | .«高» => .«模面»
  | .«黑» => .«文面»
  | .«恶» => .«价值面»

/-- Extra faces record polysemy and cross-domain reuse without breaking single-root reachability. -/
def atomExtraFaces : AtomName -> List Face
  | .«生» => [.«价值面», .«模面»]
  | .«开» => [.«价值面», .«真理面»]
  | .«闭» => [.«价值面», .«真理面»]
  | .«正» => [.«审校面», .«真理面»]
  | .«邪» => [.«审校面», .«真理面»]
  | .«真» => [.«审校面», .«价值面»]
  | .«道» => [.«价值面», .«真理面»]
  | .«人» => [.«心面», .«价值面»]
  | .«聚» => [.«注意面»]
  | .«焦» => [.«注意面»]
  | .«意» => [.«注意面», .«价值面»]
  | .«识» => [.«注意面», .«审校面»]
  | .«注» => [.«心面»]
  | .«模» => [.«物面», .«证明面»]
  | .«证» => [.«审校面», .«真理面»]
  | .«理» => [.«真理面»]
  | .«一» => [.«真理面»]
  | .«元» => [.«真理面»]
  | .«面» => [.«证明面»]
  | .«天» => [.«生面», .«物面»]
  | .«子» => [.«物面», .«心面», .«人面»]
  | .«之» => [.«证明面»]
  | .«所» => [.«真理面»]
  | .«是» => [.«文面»]
  | .«洽» => [.«审校面»]
  | _ => []

def atomFaces (a : AtomName) : List Face :=
  atomPrimaryFace a :: atomExtraFaces a

def BelongsToFace (a : AtomName) (f : Face) : Prop :=
  f ∈ atomFaces a

theorem atom_primary_face_mem (a : AtomName) :
    BelongsToFace a (atomPrimaryFace a) := by
  simp [BelongsToFace, atomFaces]

theorem all_atoms_have_face (a : AtomName) :
    ∃ f, BelongsToFace a f :=
  ⟨atomPrimaryFace a, atom_primary_face_mem a⟩

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
  | face : Face -> MonadNode
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
  | .root, .face _ => True
  | .face f, .core c => f ∈ atomFaces (CoreAtom.glyph c)
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
def faceRootPath (f : Face) : Reachable «一元» (.face f) :=
  Reachable.tail (Reachable.refl «一元») (by simp [«一元», DirectEdge])

/-- Root-to-core-atom path via the core glyph's primary face. -/
def coreRootPath (c : CoreAtom) : Reachable «一元» (.core c) :=
  Reachable.tail (faceRootPath (atomPrimaryFace (CoreAtom.glyph c)))
    (by simp [DirectEdge, atomFaces])

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

theorem all_faces_from_root : ∀ f : Face, Reachable «一元» (.face f) :=
  faceRootPath

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
  (allFaces.map MonadNode.face) ++
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
    | face f =>
        exfalso
        exact hn ⟨.root, by simp [DirectEdge]⟩
    | core c =>
        exfalso
        exact hn ⟨.face (atomPrimaryFace (CoreAtom.glyph c)), by simp [DirectEdge, atomFaces]⟩
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
  | .face _ => 1
  | .core _ => 2
  | .atom _ => 3
  | .formal _ => 4
  | .construction _ => 4
  | .claim _ => 5

def IsFace : MonadNode -> Prop
  | .face _ => True
  | _ => False

def IsCoreAtom : MonadNode -> Prop
  | .core _ => True
  | _ => False

def IsAtom : MonadNode -> Prop
  | .atom _ => True
  | _ => False

theorem near_root_constraint (x : MonadNode) :
    distance x ≤ 2 -> x = «一元» ∨ IsFace x ∨ IsCoreAtom x := by
  intro h
  cases x <;> simp [distance, IsFace, IsCoreAtom, «一元»] at h ⊢

/-- Acyclicity witness: every direct edge strictly increases monadic distance. -/
def AcyclicByRank (_dag : List MonadNode) : Prop :=
  ∀ {a b : MonadNode}, DirectEdge a b -> distance a < distance b

theorem direct_edge_rank_lt {a b : MonadNode} (h : DirectEdge a b) :
    distance a < distance b := by
  cases a <;> cases b <;> simp [DirectEdge, distance] at h ⊢

theorem monad_dag_acyclic : AcyclicByRank MonadDAG :=
  fun h => direct_edge_rank_lt h

end SSBX.Foundation.MonadRoot
