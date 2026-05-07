/-
Context-sensitive readings for polysemous wenyan glyphs.

This layer sits between raw glyph senses (`GlyphSense`) and catalogue operators
(`OperatorId`). It does not extend the executable baguaWen parser; it records
how a surface glyph such as 之 can expose multiple readings, then lets syntax
and expected type cues select a reading when the context is strong enough.
-/
import SSBX.Text.WenyanOperators

namespace SSBX.Text.OperatorReadings

open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators

inductive Fixity where
  | prefix
  | infix
  | suffix
  | construction
  deriving DecidableEq, Repr

inductive ContextCue where
  | controlledToken
  | instructionContext
  | explicitSense
  | betweenNominals
  | betweenActions
  | contrastive
  | afterVerb
  | beforeMotionVerb
  | beforeYou
  | wholeConstruction
  | asConstruction
  | nominalizerConstruction
  | finalAssertion
  | expectedFunction
  | expectedProp
  | expectedPath
  | expectedObject
  | expectedOperator
  | expectedAction
  | expectedNominal
  | expectedPredicate
  | quantifierDomain
  | modalFrame
  | abilityContext
  | permissionContext
  | normativeContext
  | positionTimeContext
  | instrumentalContext
  | purposeContext
  | identityContext
  | geometryContext
  | innerOuterContext
  | emotionContext
  | legalContext
  | governanceContext
  | strategyContext
  | militaryContext
  | medicalContext
  | ritualContext
  | mohistContext
  | namesSchoolContext
  | xunziContext
  | zhuangziContext
  | chuciContext
  | guanziContext
  | huainanContext
  | aspectContext
  | boundaryMotionContext
  | qiFlowContext
  | roleContext
  | argumentContext
  | temporalRange
  | focusAdverb
  deriving DecidableEq, Repr

inductive ReadingStatus where
  | catalogue
  | contextual
  | construction
  | pending
  deriving DecidableEq, Repr

structure OperatorReading where
  sense : GlyphSense
  operator? : Option OperatorId
  label : String
  gloss : String
  fixity : Fixity
  cues : List ContextCue
  status : ReadingStatus
  deriving DecidableEq, Repr

structure SurfaceReadings where
  surface : Glyph
  readings : List OperatorReading
  deriving DecidableEq, Repr

structure BareGlyphRule where
  priority : Nat
  label : String
  cues : List ContextCue
  keepsCandidates : Bool
  deriving DecidableEq, Repr

def readingMatches (ctx : List ContextCue) (r : OperatorReading) : Bool :=
  ctx.any (fun c => r.cues.contains c)

def catalogueReading (surface code gloss : String) (operator? : Option OperatorId)
    (fixity : Fixity) (cues : List ContextCue) : OperatorReading where
  sense := senseOfGlyph surface
  operator? := operator?
  label := surface ++ "-" ++ code
  gloss := gloss
  fixity := fixity
  cues := cues
  status := if operator?.isSome then .catalogue else .pending

def pendingReading (surface code gloss : String) (fixity : Fixity)
    (cues : List ContextCue) : OperatorReading :=
  catalogueReading surface code gloss none fixity cues

def surfaceReadings (surface : Glyph) (readings : List OperatorReading) : SurfaceReadings :=
  { surface := surface, readings := readings }

def «之属格读法» : OperatorReading where
  sense := «之1»
  operator? := some .S_1
  label := "之1"
  gloss := "属格 / 投影 / function application"
  fixity := .infix
  cues := [.betweenNominals, .expectedFunction]
  status := .catalogue

def «之代指读法» : OperatorReading where
  sense := «之2»
  operator? := none
  label := "之2"
  gloss := "代指 / 虚词承接 / discourse anaphora"
  fixity := .suffix
  cues := [.afterVerb]
  status := .contextual

def «之路径读法» : OperatorReading where
  sense := «之3»
  operator? := none
  label := "之3"
  gloss := "生成来源 / 路径所从 / source binding"
  fixity := .infix
  cues := [.beforeMotionVerb, .expectedPath]
  status := .contextual

def «之又构式» : OperatorReading where
  sense := «之1»
  operator? := none
  label := "之又"
  gloss := "迭代构式 marker, as in X 之又 X"
  fixity := .construction
  cues := [.beforeYou]
  status := .construction

def «或存在读法» : OperatorReading where
  sense := «或1»
  operator? := some .Q_5
  label := "或1-Q"
  gloss := "不定 / 存在量化"
  fixity := .prefix
  cues := [.expectedProp]
  status := .catalogue

def «或可能读法» : OperatorReading where
  sense := «或1»
  operator? := some .M_2
  label := "或1-M"
  gloss := "可能模态"
  fixity := .prefix
  cues := [.expectedProp]
  status := .catalogue

def «故因果读法» : OperatorReading where
  sense := «故1»
  operator? := some .K_1
  label := "故1-K"
  gloss := "因果根据 / because-therefore"
  fixity := .infix
  cues := [.expectedProp]
  status := .catalogue

def «故序贯读法» : OperatorReading where
  sense := «故1»
  operator? := some .S_7
  label := "故1-S"
  gloss := "证明步 / therefore connective"
  fixity := .infix
  cues := [.expectedProp]
  status := .catalogue

def «自来源读法» : OperatorReading where
  sense := «自1»
  operator? := some .K_3
  label := "自1-K"
  gloss := "始于 / from"
  fixity := .prefix
  cues := [.expectedPath]
  status := .catalogue

def «自反身读法» : OperatorReading where
  sense := «自1»
  operator? := some .Z_32
  label := "自1-Z"
  gloss := "自身 / reflexive identity"
  fixity := .prefix
  cues := [.expectedFunction]
  status := .catalogue

def «故墨经读法» : OperatorReading where
  sense := «故1»
  operator? := some .P_1
  label := "故1-P"
  gloss := "墨经小故 / 大故, necessary / sufficient condition"
  fixity := .infix
  cues := [.mohistContext, .expectedProp]
  status := .catalogue

def coreMultiReadingTable : List SurfaceReadings := [
  surfaceReadings "之" [«之属格读法», «之代指读法», «之路径读法», «之又构式»]
]

def catalogueHomographGroups : List (List Glyph) := [
  ["中"], ["別", "别"], ["一"], ["勢", "势"], ["反"], ["名"], ["因"], ["實", "实"],
  ["平"], ["應", "应"], ["故"], ["方"], ["正"], ["法"], ["知"], ["虛", "虚"],
  ["降"], ["靜", "静"], ["與", "与"], ["令"], ["位"], ["體", "体"], ["入"], ["兼"],
  ["出"], ["分"], ["制"], ["動", "动"], ["化"], ["升"], ["合"], ["同"], ["名分"],
  ["和"], ["唯"], ["復", "复"], ["守"], ["將", "将"], ["嘗", "尝"], ["已"],
  ["異", "异"], ["或"], ["推"], ["未"], ["止"], ["遊", "游"], ["然"], ["益"],
  ["積", "积"], ["精"], ["終", "终"], ["自"], ["致"], ["節", "节"], ["表"], ["解"],
  ["調", "调"], ["辭", "辞"], ["辯", "辨", "辩"], ["通"]
]

def catalogueHomographReadings : List SurfaceReadings := [
  surfaceReadings "中" [
    catalogueReading "中" "R-5" "取中" (some .R_5) .prefix [.geometryContext],
    catalogueReading "中" "C-4" "内部" (some .C_4) .prefix [.innerOuterContext],
    catalogueReading "中" "P-12" "墨经等距中心" (some .P_12) .prefix [.geometryContext, .mohistContext],
    catalogueReading "中" "LIJ-7" "未发平衡" (some .LIJ_7) .prefix [.emotionContext, .ritualContext]
  ],
  surfaceReadings "別" [
    catalogueReading "別" "N-8" "区别" (some .N_8) .prefix [.expectedObject],
    catalogueReading "別" "I-8" "分类" (some .I_8) .prefix [.expectedPredicate],
    catalogueReading "別" "G-9" "名家区分" (some .G_9) .prefix [.namesSchoolContext],
    catalogueReading "別" "X-8" "荀子等级划分" (some .X_8) .prefix [.ritualContext, .xunziContext]
  ],
  surfaceReadings "别" [
    catalogueReading "别" "N-8" "区别" (some .N_8) .prefix [.expectedObject],
    catalogueReading "别" "I-8" "分类" (some .I_8) .prefix [.expectedPredicate],
    catalogueReading "别" "G-9" "名家区分" (some .G_9) .prefix [.namesSchoolContext],
    catalogueReading "别" "X-8" "荀子等级划分" (some .X_8) .prefix [.ritualContext, .xunziContext]
  ],
  surfaceReadings "一" [
    catalogueReading "一" "I-2" "归一" (some .I_2) .prefix [.identityContext],
    catalogueReading "一" "D-1" "数词统一" (some .D_1) .prefix [.expectedNominal],
    catalogueReading "一" "L-13" "法令统一" (some .L_13) .prefix [.legalContext]
  ],
  surfaceReadings "勢" [
    catalogueReading "勢" "H-3" "结构趋势" (some .H_3) .prefix [.expectedObject],
    catalogueReading "勢" "L-3" "位置权力" (some .L_3) .prefix [.governanceContext],
    catalogueReading "勢" "SUN-2" "兵法势能" (some .SUN_2) .prefix [.militaryContext]
  ],
  surfaceReadings "势" [
    catalogueReading "势" "H-3" "结构趋势" (some .H_3) .prefix [.expectedObject],
    catalogueReading "势" "L-3" "位置权力" (some .L_3) .prefix [.governanceContext],
    catalogueReading "势" "SUN-2" "兵法势能" (some .SUN_2) .prefix [.militaryContext]
  ],
  surfaceReadings "反" [
    catalogueReading "反" "T-6" "反转" (some .T_6) .prefix [.expectedObject],
    catalogueReading "反" "N-6" "命题 / 对偶取反" (some .N_6) .prefix [.expectedProp],
    catalogueReading "反" "Z-31" "算子取逆" (some .Z_31) .prefix [.expectedOperator]
  ],
  surfaceReadings "名" [
    catalogueReading "名" "H-7" "命名" (some .H_7) .prefix [.expectedObject],
    catalogueReading "名" "P-19" "墨经三类名" (some .P_19) .prefix [.mohistContext],
    catalogueReading "名" "G-3" "名家名实绑定" (some .G_3) .prefix [.namesSchoolContext]
  ],
  surfaceReadings "因" [
    catalogueReading "因" "L-7" "借势利用" (some .L_7) .prefix [.strategyContext, .legalContext],
    catalogueReading "因" "Z-1" "一般因果 / 依凭 / 顺应" (some .Z_1) .prefix [.expectedProp],
    catalogueReading "因" "ZHU-7" "因其势理" (some .ZHU_7) .prefix [.zhuangziContext]
  ],
  surfaceReadings "實" [
    catalogueReading "實" "G-4" "实在对象" (some .G_4) .prefix [.namesSchoolContext],
    catalogueReading "實" "Y-15" "虚实容量态" (some .Y_15) .prefix [.medicalContext],
    catalogueReading "實" "SUN-4" "实处强度" (some .SUN_4) .prefix [.militaryContext]
  ],
  surfaceReadings "实" [
    catalogueReading "实" "G-4" "实在对象" (some .G_4) .prefix [.namesSchoolContext],
    catalogueReading "实" "Y-15" "虚实容量态" (some .Y_15) .prefix [.medicalContext],
    catalogueReading "实" "SUN-4" "实处强度" (some .SUN_4) .prefix [.militaryContext]
  ],
  surfaceReadings "平" [
    catalogueReading "平" "P-14" "等高" (some .P_14) .prefix [.geometryContext],
    catalogueReading "平" "Y-17" "治疗平衡" (some .Y_17) .prefix [.medicalContext],
    catalogueReading "平" "LIJ-14" "平天下" (some .LIJ_14) .prefix [.governanceContext, .ritualContext]
  ],
  surfaceReadings "應" [
    catalogueReading "應" "R-7" "共振对应" (some .R_7) .infix [.expectedObject],
    catalogueReading "應" "M-8" "应然" (some .M_8) .prefix [.normativeContext, .expectedProp],
    catalogueReading "應" "ZA-10" "兵略响应" (some .ZA_10) .prefix [.militaryContext]
  ],
  surfaceReadings "应" [
    catalogueReading "应" "R-7" "共振对应" (some .R_7) .infix [.expectedObject],
    catalogueReading "应" "M-8" "应然" (some .M_8) .prefix [.normativeContext, .expectedProp],
    catalogueReading "应" "ZA-10" "兵略响应" (some .ZA_10) .prefix [.militaryContext]
  ],
  surfaceReadings "故" [«故因果读法», «故序贯读法», «故墨经读法»],
  surfaceReadings "方" [
    catalogueReading "方" "S-11" "正在" (some .S_11) .prefix [.aspectContext],
    catalogueReading "方" "A-19" "进行相" (some .A_19) .prefix [.aspectContext],
    catalogueReading "方" "ZHU-10" "庄子事件展开" (some .ZHU_10) .prefix [.zhuangziContext]
  ],
  surfaceReadings "正" [
    catalogueReading "正" "R-6" "端正" (some .R_6) .prefix [.expectedObject],
    catalogueReading "正" "G-6" "名实校准" (some .G_6) .prefix [.namesSchoolContext],
    catalogueReading "正" "SUN-6" "正兵" (some .SUN_6) .prefix [.militaryContext]
  ],
  surfaceReadings "法" [
    catalogueReading "法" "H-5" "法度 / 取模" (some .H_5) .prefix [.expectedObject],
    catalogueReading "法" "P-18" "墨经法则" (some .P_18) .prefix [.mohistContext],
    catalogueReading "法" "L-1" "法家制度机制" (some .L_1) .prefix [.legalContext]
  ],
  surfaceReadings "知" [
    catalogueReading "知" "P-20" "墨经三类知" (some .P_20) .prefix [.mohistContext],
    catalogueReading "知" "Z-40" "一般知识获取" (some .Z_40) .prefix [.expectedObject],
    catalogueReading "知" "SUN-14" "情报闭环" (some .SUN_14) .prefix [.militaryContext]
  ],
  surfaceReadings "虛" [
    catalogueReading "虛" "Y-15" "虚实容量态" (some .Y_15) .prefix [.medicalContext],
    catalogueReading "虛" "SUN-3" "敌弱点" (some .SUN_3) .prefix [.militaryContext],
    catalogueReading "虛" "ZA-1" "心术虚心" (some .ZA_1) .prefix [.guanziContext]
  ],
  surfaceReadings "虚" [
    catalogueReading "虚" "Y-15" "虚实容量态" (some .Y_15) .prefix [.medicalContext],
    catalogueReading "虚" "SUN-3" "敌弱点" (some .SUN_3) .prefix [.militaryContext],
    catalogueReading "虚" "ZA-1" "心术虚心" (some .ZA_1) .prefix [.guanziContext]
  ],
  surfaceReadings "降" [
    catalogueReading "降" "F-6" "垂直下降" (some .F_6) .prefix [.boundaryMotionContext],
    catalogueReading "降" "Y-10" "医家气机降" (some .Y_10) .prefix [.medicalContext, .qiFlowContext],
    catalogueReading "降" "CHU-6" "降临" (some .CHU_6) .prefix [.chuciContext]
  ],
  surfaceReadings "靜" [
    catalogueReading "靜" "F-11" "归静" (some .F_11) .prefix [.expectedObject],
    catalogueReading "靜" "L-10" "君静" (some .L_10) .prefix [.governanceContext],
    catalogueReading "靜" "ZA-2" "心术静得" (some .ZA_2) .prefix [.guanziContext]
  ],
  surfaceReadings "静" [
    catalogueReading "静" "F-11" "归静" (some .F_11) .prefix [.expectedObject],
    catalogueReading "静" "L-10" "君静" (some .L_10) .prefix [.governanceContext],
    catalogueReading "静" "ZA-2" "心术静得" (some .ZA_2) .prefix [.guanziContext]
  ],
  surfaceReadings "與" [
    catalogueReading "與" "R-14" "协同并列" (some .R_14) .infix [.betweenNominals, .betweenActions],
    catalogueReading "與" "E-6" "春秋认可" (some .E_6) .prefix [.ritualContext]
  ],
  surfaceReadings "与" [
    catalogueReading "与" "R-14" "协同并列" (some .R_14) .infix [.betweenNominals, .betweenActions],
    catalogueReading "与" "E-6" "春秋认可" (some .E_6) .prefix [.ritualContext]
  ],
  surfaceReadings "令" [
    catalogueReading "令" "K-7" "命令致使" (some .K_7) .prefix [.expectedAction],
    catalogueReading "令" "ZA-7" "月令" (some .ZA_7) .prefix [.huainanContext]
  ],
  surfaceReadings "位" [
    catalogueReading "位" "G-5" "proper place" (some .G_5) .prefix [.positionTimeContext],
    catalogueReading "位" "LIJ-4" "礼制角色位置" (some .LIJ_4) .prefix [.roleContext, .ritualContext]
  ],
  surfaceReadings "體" [
    catalogueReading "體" "H-8" "体用本质" (some .H_8) .prefix [.expectedObject],
    catalogueReading "體" "P-2" "墨经取部分" (some .P_2) .prefix [.mohistContext]
  ],
  surfaceReadings "体" [
    catalogueReading "体" "H-8" "体用本质" (some .H_8) .prefix [.expectedObject],
    catalogueReading "体" "P-2" "墨经取部分" (some .P_2) .prefix [.mohistContext]
  ],
  surfaceReadings "入" [
    catalogueReading "入" "F-8" "入界" (some .F_8) .prefix [.boundaryMotionContext],
    catalogueReading "入" "Y-26" "医家气机入" (some .Y_26) .prefix [.medicalContext, .qiFlowContext]
  ],
  surfaceReadings "兼" [
    catalogueReading "兼" "P-3" "parts-to-whole 整合" (some .P_3) .prefix [.mohistContext],
    catalogueReading "兼" "G-8" "名家复合名" (some .G_8) .prefix [.namesSchoolContext]
  ],
  surfaceReadings "出" [
    catalogueReading "出" "F-7" "出界" (some .F_7) .prefix [.boundaryMotionContext],
    catalogueReading "出" "Y-26" "医家气机出" (some .Y_26) .prefix [.medicalContext, .qiFlowContext]
  ],
  surfaceReadings "分" [
    catalogueReading "分" "I-6" "分割" (some .I_6) .prefix [.expectedObject],
    catalogueReading "分" "X-5" "荀子群内角色分化" (some .X_5) .prefix [.xunziContext, .roleContext]
  ],
  surfaceReadings "制" [
    catalogueReading "制" "L-14" "模式成制度" (some .L_14) .prefix [.legalContext],
    catalogueReading "制" "X-9" "需求设制度" (some .X_9) .prefix [.xunziContext]
  ],
  surfaceReadings "動" [
    catalogueReading "動" "F-10" "启动" (some .F_10) .prefix [.expectedAction],
    catalogueReading "動" "P-8" "墨经空间移动" (some .P_8) .prefix [.mohistContext, .boundaryMotionContext]
  ],
  surfaceReadings "动" [
    catalogueReading "动" "F-10" "启动" (some .F_10) .prefix [.expectedAction],
    catalogueReading "动" "P-8" "墨经空间移动" (some .P_8) .prefix [.mohistContext, .boundaryMotionContext]
  ],
  surfaceReadings "化" [
    catalogueReading "化" "T-1" "渐变 / 类型变化" (some .T_1) .prefix [.expectedObject],
    catalogueReading "化" "X-11" "荀子环境教化" (some .X_11) .prefix [.xunziContext]
  ],
  surfaceReadings "升" [
    catalogueReading "升" "F-5" "垂直上升" (some .F_5) .prefix [.boundaryMotionContext],
    catalogueReading "升" "Y-10" "医家气机升" (some .Y_10) .prefix [.medicalContext, .qiFlowContext]
  ],
  surfaceReadings "合" [
    catalogueReading "合" "I-7" "合并" (some .I_7) .prefix [.expectedObject],
    catalogueReading "合" "G-8" "名家复合名" (some .G_8) .prefix [.namesSchoolContext]
  ],
  surfaceReadings "同" [
    catalogueReading "同" "I-1" "相等" (some .I_1) .prefix [.identityContext],
    catalogueReading "同" "P-4" "墨经四类同" (some .P_4) .prefix [.mohistContext]
  ],
  surfaceReadings "名分" [
    catalogueReading "名分" "X-12" "身份角色权限三元组" (some .X_12) .construction [.roleContext, .xunziContext],
    catalogueReading "名分" "ZA-19" "名称分域" (some .ZA_19) .construction [.namesSchoolContext]
  ],
  surfaceReadings "和" [
    catalogueReading "和" "Y-18" "系统动态协调" (some .Y_18) .prefix [.medicalContext],
    catalogueReading "和" "LIJ-8" "已发情感调和" (some .LIJ_8) .prefix [.emotionContext, .ritualContext]
  ],
  surfaceReadings "唯" [
    catalogueReading "唯" "Q-8" "唯一量化" (some .Q_8) .prefix [.quantifierDomain],
    catalogueReading "唯" "A-14" "唯独副词" (some .A_14) .prefix [.focusAdverb]
  ],
  surfaceReadings "復" [
    catalogueReading "復" "T-7" "复归" (some .T_7) .prefix [.expectedObject],
    catalogueReading "復" "A-5" "再次" (some .A_5) .prefix [.aspectContext]
  ],
  surfaceReadings "复" [
    catalogueReading "复" "T-7" "复归" (some .T_7) .prefix [.expectedObject],
    catalogueReading "复" "A-5" "再次" (some .A_5) .prefix [.aspectContext]
  ],
  surfaceReadings "守" [
    catalogueReading "守" "L-9" "守角色" (some .L_9) .prefix [.roleContext, .legalContext],
    catalogueReading "守" "Z-12" "一般持守" (some .Z_12) .prefix [.expectedObject]
  ],
  surfaceReadings "將" [
    catalogueReading "將" "S-10" "将要" (some .S_10) .prefix [.aspectContext],
    catalogueReading "將" "A-18" "prospective aspect" (some .A_18) .prefix [.aspectContext]
  ],
  surfaceReadings "将" [
    catalogueReading "将" "S-10" "将要" (some .S_10) .prefix [.aspectContext],
    catalogueReading "将" "A-18" "prospective aspect" (some .A_18) .prefix [.aspectContext]
  ],
  surfaceReadings "嘗" [
    catalogueReading "嘗" "S-12" "曾经" (some .S_12) .prefix [.aspectContext],
    catalogueReading "嘗" "A-20" "experiential past" (some .A_20) .prefix [.aspectContext]
  ],
  surfaceReadings "尝" [
    catalogueReading "尝" "S-12" "曾经" (some .S_12) .prefix [.aspectContext],
    catalogueReading "尝" "A-20" "experiential past" (some .A_20) .prefix [.aspectContext]
  ],
  surfaceReadings "已" [
    catalogueReading "已" "S-18" "已经 / 完成" (some .S_18) .prefix [.expectedProp],
    catalogueReading "已" "A-16" "完成相" (some .A_16) .prefix [.aspectContext]
  ],
  surfaceReadings "異" [
    catalogueReading "異" "N-7" "不同" (some .N_7) .prefix [.expectedObject],
    catalogueReading "異" "P-5" "墨经四类异" (some .P_5) .prefix [.mohistContext]
  ],
  surfaceReadings "异" [
    catalogueReading "异" "N-7" "不同" (some .N_7) .prefix [.expectedObject],
    catalogueReading "异" "P-5" "墨经四类异" (some .P_5) .prefix [.mohistContext]
  ],
  surfaceReadings "或" [«或存在读法», «或可能读法»],
  surfaceReadings "推" [
    catalogueReading "推" "T-10" "对象推进" (some .T_10) .prefix [.expectedObject],
    catalogueReading "推" "Z-29" "算子外推" (some .Z_29) .prefix [.expectedOperator]
  ],
  surfaceReadings "未" [
    catalogueReading "未" "S-17" "尚未命题" (some .S_17) .prefix [.expectedProp],
    catalogueReading "未" "A-17" "not-yet aspect" (some .A_17) .prefix [.aspectContext]
  ],
  surfaceReadings "止" [
    catalogueReading "止" "B-4" "停止" (some .B_4) .prefix [.expectedAction],
    catalogueReading "止" "P-9" "墨经止" (some .P_9) .prefix [.mohistContext]
  ],
  surfaceReadings "遊" [
    catalogueReading "遊" "ZHU-2" "庄子游行" (some .ZHU_2) .prefix [.zhuangziContext],
    catalogueReading "遊" "CHU-3" "楚辞游历" (some .CHU_3) .prefix [.chuciContext]
  ],
  surfaceReadings "游" [
    catalogueReading "游" "ZHU-2" "庄子游行" (some .ZHU_2) .prefix [.zhuangziContext],
    catalogueReading "游" "CHU-3" "楚辞游历" (some .CHU_3) .prefix [.chuciContext]
  ],
  surfaceReadings "然" [
    catalogueReading "然" "S-6" "如此 / 然而" (some .S_6) .prefix [.contrastive],
    catalogueReading "然" "G-10" "谓词系动" (some .G_10) .infix [.expectedPredicate]
  ],
  surfaceReadings "益" [
    catalogueReading "益" "T-13" "增益" (some .T_13) .prefix [.expectedObject],
    catalogueReading "益" "A-9" "更加" (some .A_9) .prefix [.aspectContext]
  ],
  surfaceReadings "積" [
    catalogueReading "積" "X-14" "行动累积生能力" (some .X_14) .prefix [.xunziContext],
    catalogueReading "積" "Z-19" "一般积累" (some .Z_19) .prefix [.expectedObject]
  ],
  surfaceReadings "积" [
    catalogueReading "积" "X-14" "行动累积生能力" (some .X_14) .prefix [.xunziContext],
    catalogueReading "积" "Z-19" "一般积累" (some .Z_19) .prefix [.expectedObject]
  ],
  surfaceReadings "精" [
    catalogueReading "精" "Y-8" "根本储藏能量" (some .Y_8) .prefix [.medicalContext],
    catalogueReading "精" "ZA-5" "内业精化" (some .ZA_5) .prefix [.guanziContext]
  ],
  surfaceReadings "終" [
    catalogueReading "終" "B-2" "终点" (some .B_2) .prefix [.expectedObject],
    catalogueReading "終" "D-9" "全程量化" (some .D_9) .prefix [.temporalRange]
  ],
  surfaceReadings "终" [
    catalogueReading "终" "B-2" "终点" (some .B_2) .prefix [.expectedObject],
    catalogueReading "终" "D-9" "全程量化" (some .D_9) .prefix [.temporalRange]
  ],
  surfaceReadings "自" [«自来源读法», «自反身读法»],
  surfaceReadings "致" [
    catalogueReading "致" "T-11" "推至目标" (some .T_11) .prefix [.expectedObject],
    catalogueReading "致" "K-5" "因果 / 知识达到" (some .K_5) .prefix [.expectedPath, .expectedProp]
  ],
  surfaceReadings "節" [
    catalogueReading "節" "B-8" "节点 / 离散标记" (some .B_8) .prefix [.expectedObject],
    catalogueReading "節" "LIJ-6" "分寸约束" (some .LIJ_6) .prefix [.ritualContext]
  ],
  surfaceReadings "节" [
    catalogueReading "节" "B-8" "节点 / 离散标记" (some .B_8) .prefix [.expectedObject],
    catalogueReading "节" "LIJ-6" "分寸约束" (some .LIJ_6) .prefix [.ritualContext]
  ],
  surfaceReadings "表" [
    catalogueReading "表" "C-7" "表面" (some .C_7) .prefix [.innerOuterContext],
    catalogueReading "表" "Y-13" "医家表里病位" (some .Y_13) .prefix [.medicalContext]
  ],
  surfaceReadings "解" [
    catalogueReading "解" "X-13" "解蔽" (some .X_13) .prefix [.xunziContext],
    catalogueReading "解" "ZHU-8" "顺节分解" (some .ZHU_8) .prefix [.zhuangziContext]
  ],
  surfaceReadings "調" [
    catalogueReading "調" "Y-19" "参数调节" (some .Y_19) .prefix [.medicalContext],
    catalogueReading "調" "ZA-12" "淮南调合" (some .ZA_12) .prefix [.huainanContext]
  ],
  surfaceReadings "调" [
    catalogueReading "调" "Y-19" "参数调节" (some .Y_19) .prefix [.medicalContext],
    catalogueReading "调" "ZA-12" "淮南调合" (some .ZA_12) .prefix [.huainanContext]
  ],
  surfaceReadings "辭" [
    catalogueReading "辭" "P-21" "命题 / 论辩发言" (some .P_21) .prefix [.argumentContext],
    catalogueReading "辭" "LIJ-3" "辞令" (some .LIJ_3) .prefix [.ritualContext]
  ],
  surfaceReadings "辞" [
    catalogueReading "辞" "P-21" "命题 / 论辩发言" (some .P_21) .prefix [.argumentContext],
    catalogueReading "辞" "LIJ-3" "辞令" (some .LIJ_3) .prefix [.ritualContext]
  ],
  surfaceReadings "辯" [
    catalogueReading "辯" "P-23" "辯析 / 判别" (some .P_23) .prefix [.argumentContext],
    catalogueReading "辯" "ZA-20" "名称事实角色分辨" (some .ZA_20) .prefix [.namesSchoolContext]
  ],
  surfaceReadings "辨" [
    catalogueReading "辨" "P-23" "辯析 / 判别" (some .P_23) .prefix [.argumentContext],
    catalogueReading "辨" "ZA-20" "名称事实角色分辨" (some .ZA_20) .prefix [.namesSchoolContext]
  ],
  surfaceReadings "辩" [
    catalogueReading "辩" "P-23" "辯析 / 判别" (some .P_23) .prefix [.argumentContext],
    catalogueReading "辩" "ZA-20" "名称事实角色分辨" (some .ZA_20) .prefix [.namesSchoolContext]
  ],
  surfaceReadings "通" [
    catalogueReading "通" "F-12" "通达 / 穿透" (some .F_12) .prefix [.expectedPath],
    catalogueReading "通" "Y-23" "医家通滞诊断" (some .Y_23) .prefix [.medicalContext]
  ]
]

def allSurfaceReadings : List SurfaceReadings :=
  coreMultiReadingTable ++ catalogueHomographReadings

def bareGlyphDisambiguationRules : List BareGlyphRule := [
  { priority := 1, label := "受控文 token «... » 优先", cues := [.controlledToken],
    keepsCandidates := true },
  { priority := 2, label := "baguaWen 指令上下文优先", cues := [.instructionContext],
    keepsCandidates := true },
  { priority := 3, label := "显式编号义位优先", cues := [.explicitSense],
    keepsCandidates := true },
  { priority := 4, label := "复合构式整体识别优先", cues := [.wholeConstruction, .asConstruction,
      .nominalizerConstruction, .beforeYou],
    keepsCandidates := true },
  { priority := 5, label := "句尾也只在无待闭合构式时闭句", cues := [.finalAssertion],
    keepsCandidates := true },
  { priority := 6, label := "虚字按类型 / 邻接 cue 解析", cues := [.expectedFunction,
      .betweenActions, .expectedProp, .expectedPath],
    keepsCandidates := true },
  { priority := 7, label := "剩余同字多义交给类型检查", cues := [.expectedObject,
      .expectedOperator, .expectedPredicate],
    keepsCandidates := true }
]

def readingsForGlyph : Glyph -> List OperatorReading
  | glyph =>
      (allSurfaceReadings.filter (fun entry => entry.surface == glyph)).foldr
        (fun entry readings => entry.readings ++ readings) []

def contextualReadings (glyph : Glyph) (ctx : List ContextCue) : List OperatorReading :=
  let rs := readingsForGlyph glyph
  if ctx.isEmpty then rs else rs.filter (readingMatches ctx)

def uniquelyResolved (glyph : Glyph) (ctx : List ContextCue) : Prop :=
  (contextualReadings glyph ctx).length = 1

instance uniquelyResolvedDecidable (glyph : Glyph) (ctx : List ContextCue) :
    Decidable (uniquelyResolved glyph ctx) := by
  unfold uniquelyResolved
  infer_instance

theorem zhi_between_nominals_unique :
    uniquelyResolved "之" [.betweenNominals] := by
  native_decide

theorem zhi_after_verb_unique :
    uniquelyResolved "之" [.afterVerb] := by
  native_decide

theorem zhi_before_motion_unique :
    uniquelyResolved "之" [.beforeMotionVerb] := by
  native_decide

theorem zhi_before_you_unique :
    uniquelyResolved "之" [.beforeYou] := by
  native_decide

theorem zhi_expected_function_unique :
    uniquelyResolved "之" [.expectedFunction] := by
  native_decide

theorem zhi_expected_path_unique :
    uniquelyResolved "之" [.expectedPath] := by
  native_decide

theorem zhi_no_context_ambiguous :
    ¬ uniquelyResolved "之" [] := by
  native_decide

theorem huo_prop_context_still_ambiguous :
    ¬ uniquelyResolved "或" [.expectedProp] := by
  native_decide

theorem core_multi_reading_table_count :
    coreMultiReadingTable.length = 1 := by
  native_decide

theorem all_surface_readings_count :
    allSurfaceReadings.length = 82 := by
  native_decide

theorem readings_for_zhi_count :
    (readingsForGlyph "之").length = 4 := by
  native_decide

theorem zhi_no_context_reading_count :
    (contextualReadings "之" []).length = 4 := by
  native_decide

theorem readings_for_zhong_count :
    (readingsForGlyph "中").length = 4 := by
  native_decide

theorem readings_for_gu_count :
    (readingsForGlyph "故").length = 3 := by
  native_decide

theorem readings_for_huo_count :
    (readingsForGlyph "或").length = 2 := by
  native_decide

theorem readings_for_mingfen_count :
    (readingsForGlyph "名分").length = 2 := by
  native_decide

theorem catalogue_homograph_group_count :
    catalogueHomographGroups.length = 60 := by
  native_decide

theorem catalogue_homograph_surface_count :
    catalogueHomographReadings.length = 81 := by
  native_decide

theorem catalogue_homograph_total_reading_count :
    (catalogueHomographReadings.map (fun e => e.readings.length)).foldl Nat.add 0 = 189 := by
  native_decide

theorem all_surface_total_reading_count :
    (allSurfaceReadings.map (fun e => e.readings.length)).foldl Nat.add 0 = 193 := by
  native_decide

theorem catalogue_homograph_readings_all_linked :
    catalogueHomographReadings.all
      (fun entry => entry.readings.all (fun reading => reading.operator?.isSome)) = true := by
  native_decide

theorem bare_glyph_rule_count :
    bareGlyphDisambiguationRules.length = 7 := by
  native_decide

theorem bare_glyph_rules_keep_candidates :
    bareGlyphDisambiguationRules.all (fun rule => rule.keepsCandidates) = true := by
  native_decide

theorem zhong_no_context_ambiguous :
    ¬ uniquelyResolved "中" [] := by
  native_decide

theorem zhong_inner_outer_unique :
    uniquelyResolved "中" [.innerOuterContext] := by
  native_decide

theorem zhong_geometry_context_still_ambiguous :
    ¬ uniquelyResolved "中" [.geometryContext] := by
  native_decide

theorem fan_operator_unique :
    uniquelyResolved "反" [.expectedOperator] := by
  native_decide

theorem fan_prop_unique :
    uniquelyResolved "反" [.expectedProp] := by
  native_decide

theorem gu_mohist_unique :
    uniquelyResolved "故" [.mohistContext] := by
  native_decide

theorem gu_prop_context_still_ambiguous :
    ¬ uniquelyResolved "故" [.expectedProp] := by
  native_decide

theorem bian_simplified_no_context_ambiguous :
    ¬ uniquelyResolved "辩" [] := by
  native_decide

theorem mingfen_role_unique :
    uniquelyResolved "名分" [.roleContext] := by
  native_decide

theorem tui_operator_unique :
    uniquelyResolved "推" [.expectedOperator] := by
  native_decide

theorem wei_quantifier_unique :
    uniquelyResolved "唯" [.quantifierDomain] := by
  native_decide

theorem wei_focus_unique :
    uniquelyResolved "唯" [.focusAdverb] := by
  native_decide

theorem zi_source_unique :
    uniquelyResolved "自" [.expectedPath] := by
  native_decide

theorem zi_reflexive_unique :
    uniquelyResolved "自" [.expectedFunction] := by
  native_decide

theorem fang_aspect_context_still_ambiguous :
    ¬ uniquelyResolved "方" [.aspectContext] := by
  native_decide

theorem jiang_aspect_context_still_ambiguous :
    ¬ uniquelyResolved "將" [.aspectContext] := by
  native_decide

theorem yi_prop_unique :
    uniquelyResolved "已" [.expectedProp] := by
  native_decide

theorem yi_aspect_unique :
    uniquelyResolved "已" [.aspectContext] := by
  native_decide

end SSBX.Text.OperatorReadings
