/-
Text-facing glyph and numbered-sense registry.
-/
import SSBX.Roster

namespace SSBX.Text.Glyph

abbrev Glyph := String
abbrev SenseNo := Nat

inductive LexKind where
  | glyph
  | operator
  | generated
  | particle
  | modal
  | formal
  | pending
  deriving DecidableEq, Repr

structure GlyphSense where
  glyph : Glyph
  sense : SenseNo
  kind : LexKind
  deriving DecidableEq, Repr

structure SenseEntry where
  key : GlyphSense
  label : String
  gloss : String
  role : String
  deriving DecidableEq, Repr

def mk (glyph : Glyph) (sense : SenseNo) (kind : LexKind) : GlyphSense :=
  { glyph := glyph, sense := sense, kind := kind }

def canonicalKind (glyph : Glyph) : LexKind :=
  match glyph with
  | "之" | "真" | "是" | "自" | "由" | "似" | "行" | "校" | "合" | "法" | "洽" | "复"
  | "生" | "和" | "故" | "以" | "为" | "為" | "乃" | "即" | "然" | "系" | "的" | "地" => .operator
  | "可" | "能" | "当" | "當" | "宜" | "或" => .modal
  | "所" | "者" | "也" | "于" | "於" | "未" | "已" | "不" | "非" | "无" | "無"
  | "凡" | "皆" | "有" | "若" | "则" | "則"
  | "乎" | "矣" | "哉" | "兮" => .particle
  | _ => .glyph

def senseOfGlyph (glyph : Glyph) : GlyphSense :=
  mk glyph 1 (canonicalKind glyph)

def senseOfChar (c : Char) : GlyphSense :=
  senseOfGlyph c.toString

def textToSenses (s : String) : List GlyphSense :=
  s.toList.map senseOfChar

def formalSense (token : String) : GlyphSense :=
  mk token 1 .formal

def senseKey (s : GlyphSense) : String :=
  s.glyph ++ toString s.sense

def «生1» : GlyphSense := senseOfGlyph "生"
def «生2» : GlyphSense := mk "生" 2 .operator
def «生3» : GlyphSense := mk "生" 3 .generated

def «之1» : GlyphSense := senseOfGlyph "之"
def «之2» : GlyphSense := mk "之" 2 .particle
def «之3» : GlyphSense := mk "之" 3 .operator

def «真1» : GlyphSense := senseOfGlyph "真"
def «真2» : GlyphSense := mk "真" 2 .generated
def «是1» : GlyphSense := senseOfGlyph "是"
def «系1» : GlyphSense := senseOfGlyph "系"
def «的1» : GlyphSense := senseOfGlyph "的"
def «地1» : GlyphSense := senseOfGlyph "地"
def «所1» : GlyphSense := senseOfGlyph "所"
def «自1» : GlyphSense := senseOfGlyph "自"
def «由1» : GlyphSense := senseOfGlyph "由"
def «似1» : GlyphSense := senseOfGlyph "似"
def «可1» : GlyphSense := senseOfGlyph "可"
def «行1» : GlyphSense := senseOfGlyph "行"
def «校1» : GlyphSense := senseOfGlyph "校"
def «合1» : GlyphSense := senseOfGlyph "合"
def «法1» : GlyphSense := senseOfGlyph "法"
def «洽1» : GlyphSense := senseOfGlyph "洽"
def «复1» : GlyphSense := senseOfGlyph "复"
def «和1» : GlyphSense := senseOfGlyph "和"
def «者1» : GlyphSense := mk "者" 1 .particle
def «也1» : GlyphSense := mk "也" 1 .particle
def «于1» : GlyphSense := mk "于" 1 .particle
def «於1» : GlyphSense := mk "於" 1 .particle
def «未1» : GlyphSense := senseOfGlyph "未"
def «已1» : GlyphSense := mk "已" 1 .particle
def «乎1» : GlyphSense := mk "乎" 1 .particle
def «矣1» : GlyphSense := mk "矣" 1 .particle
def «哉1» : GlyphSense := mk "哉" 1 .particle
def «兮1» : GlyphSense := mk "兮" 1 .particle
def «不1» : GlyphSense := senseOfGlyph "不"
def «息1» : GlyphSense := senseOfGlyph "息"
def «非1» : GlyphSense := senseOfGlyph "非"
def «无1» : GlyphSense := senseOfGlyph "无"
def «無1» : GlyphSense := senseOfGlyph "無"
def «凡1» : GlyphSense := senseOfGlyph "凡"
def «皆1» : GlyphSense := senseOfGlyph "皆"
def «有1» : GlyphSense := senseOfGlyph "有"
def «或1» : GlyphSense := senseOfGlyph "或"
def «若1» : GlyphSense := senseOfGlyph "若"
def «则1» : GlyphSense := senseOfGlyph "则"
def «則1» : GlyphSense := senseOfGlyph "則"
def «故1» : GlyphSense := senseOfGlyph "故"
def «能1» : GlyphSense := senseOfGlyph "能"
def «当1» : GlyphSense := senseOfGlyph "当"
def «當1» : GlyphSense := senseOfGlyph "當"
def «宜1» : GlyphSense := senseOfGlyph "宜"
def «以1» : GlyphSense := senseOfGlyph "以"
def «为1» : GlyphSense := senseOfGlyph "为"
def «為1» : GlyphSense := senseOfGlyph "為"
def «乃1» : GlyphSense := senseOfGlyph "乃"
def «即1» : GlyphSense := senseOfGlyph "即"
def «然1» : GlyphSense := senseOfGlyph "然"

def coreSenseEntries : List SenseEntry := [
  { key := «真1», label := "真1", gloss := "言合所是", role := "truth-correspondence" },
  { key := «真2», label := "真2", gloss := "度期周且审校不败", role := "audited-truth" },
  { key := «是1», label := "是1", gloss := "此境如此之所是", role := "what-is" },
  { key := «系1», label := "系1", gloss := "关系连接、诸分成网", role := "relational-connection" },
  { key := «的1», label := "的1", gloss := "现代属格或投影绑定，之1之今别名", role := "modern-genitive-binding" },
  { key := «地1», label := "地1", gloss := "境位所依、成立之地", role := "situated-ground" },
  { key := «然1», label := "然1", gloss := "如此成立、谓述成真", role := "affirmation-predication" },
  { key := «所1», label := "所1", gloss := "名物化或集合化", role := "nominalizer" },
  { key := «之1», label := "之1", gloss := "属格或投影绑定", role := "genitive-binding" },
  { key := «之2», label := "之2", gloss := "代指或虚词承接", role := "particle-anaphora" },
  { key := «之3», label := "之3", gloss := "生成来源或路径所从", role := "source-binding" },
  { key := «自1», label := "自1", gloss := "由内在结构回返自身", role := "reflexive-source" },
  { key := «由1», label := "由1", gloss := "所从、所因、所经之路径", role := "path-cause" },
  { key := «似1», label := "似1", gloss := "形同而位异", role := "shape-similarity" },
  { key := «可1», label := "可1", gloss := "有法之可能", role := "lawful-possibility" },
  { key := «行1», label := "行1", gloss := "择间而令境续", role := "action" },
  { key := «校1», label := "校1", gloss := "与境、史、果、众应相较而受正", role := "audit" },
  { key := «合1», label := "合1", gloss := "相承而不相坏", role := "compatibility" },
  { key := «法1», label := "法1", gloss := "可承、可续、可校之判", role := "admissible-rule" },
  { key := «洽1», label := "洽1", gloss := "诸分相合而无相害", role := "coherence" },
  { key := «复1», label := "复1", gloss := "失后能返，断后能再接", role := "return-after-loss" },
  { key := «生1», label := "生1", gloss := "开出新续", role := "generation" },
  { key := «和1», label := "和1", gloss := "诸开相通而不相吞", role := "harmony" },
  { key := «者1», label := "者1", gloss := "定义、抽象、谓词封装", role := "definition-wrapper" },
  { key := «也1», label := "也1", gloss := "断定、类型闭合、命题完成", role := "assertion-close" },
  { key := «于1», label := "于1", gloss := "境域绑定", role := "context-binding" },
  { key := «於1», label := "於1", gloss := "境域绑定", role := "context-binding" },
  { key := «未1», label := "未1", gloss := "尚未而留未来开口", role := "not-yet" },
  { key := «已1», label := "已1", gloss := "已经完成或稳定", role := "perfective" },
  { key := «乎1», label := "乎1", gloss := "句末疑问、提问之闭合", role := "interrogative-final" },
  { key := «矣1», label := "矣1", gloss := "句末完成、变化已至", role := "perfective-final" },
  { key := «哉1», label := "哉1", gloss := "句末感叹、惊异之闭合", role := "exclamatory-final" },
  { key := «兮1», label := "兮1", gloss := "句末抒情、韵律之闭合", role := "lyrical-final" }
]

def coreNumberedSenses : List GlyphSense :=
  coreSenseEntries.map (fun e => e.key)

def recoveredMissingGlyphSenses : List GlyphSense := [
  senseOfGlyph "七", senseOfGlyph "三", senseOfGlyph "不", senseOfGlyph "与", senseOfGlyph "中", senseOfGlyph "乃", senseOfGlyph "九", senseOfGlyph "事", senseOfGlyph "二", senseOfGlyph "五",
  senseOfGlyph "亦", senseOfGlyph "仍", senseOfGlyph "以", senseOfGlyph "件", senseOfGlyph "位", senseOfGlyph "例", senseOfGlyph "保", senseOfGlyph "值", senseOfGlyph "全", senseOfGlyph "八",
  senseOfGlyph "六", senseOfGlyph "其", senseOfGlyph "册", senseOfGlyph "冒", senseOfGlyph "准", senseOfGlyph "凡", senseOfGlyph "出", senseOfGlyph "判", senseOfGlyph "别", senseOfGlyph "前",
  senseOfGlyph "十", senseOfGlyph "卷", senseOfGlyph "原", senseOfGlyph "口", senseOfGlyph "古", senseOfGlyph "句", senseOfGlyph "只", senseOfGlyph "名", senseOfGlyph "含", senseOfGlyph "四",
  senseOfGlyph "型", senseOfGlyph "增", senseOfGlyph "始", senseOfGlyph "字", senseOfGlyph "守", senseOfGlyph "完", senseOfGlyph "导", senseOfGlyph "尺", senseOfGlyph "常", senseOfGlyph "式",
  senseOfGlyph "当", senseOfGlyph "录", senseOfGlyph "律", senseOfGlyph "得", senseOfGlyph "微", senseOfGlyph "德", senseOfGlyph "指", senseOfGlyph "推", senseOfGlyph "收", senseOfGlyph "故",
  senseOfGlyph "整", senseOfGlyph "文", senseOfGlyph "易", senseOfGlyph "有", senseOfGlyph "本", senseOfGlyph "束", senseOfGlyph "极", senseOfGlyph "染", senseOfGlyph "根", senseOfGlyph "此",
  senseOfGlyph "渲", senseOfGlyph "版", senseOfGlyph "皆", senseOfGlyph "空", senseOfGlyph "立", senseOfGlyph "箱", senseOfGlyph "篇", senseOfGlyph "籍", senseOfGlyph "类", senseOfGlyph "终",
  senseOfGlyph "经", senseOfGlyph "缺", senseOfGlyph "美", senseOfGlyph "背", senseOfGlyph "致", senseOfGlyph "补", senseOfGlyph "表", senseOfGlyph "见", senseOfGlyph "言", senseOfGlyph "语",
  senseOfGlyph "诸", senseOfGlyph "谓", senseOfGlyph "象", senseOfGlyph "连", senseOfGlyph "述", senseOfGlyph "递", senseOfGlyph "遇", senseOfGlyph "量", senseOfGlyph "锚", senseOfGlyph "随",
  senseOfGlyph "非", senseOfGlyph "项", senseOfGlyph "高", senseOfGlyph "黑",
  senseOfGlyph "恶", senseOfGlyph "辭", senseOfGlyph "辞", senseOfGlyph "說", senseOfGlyph "说", senseOfGlyph "辯", senseOfGlyph "辩", senseOfGlyph "類", senseOfGlyph "命", senseOfGlyph "筆",
  senseOfGlyph "笔", senseOfGlyph "褒", senseOfGlyph "貶", senseOfGlyph "贬", senseOfGlyph "过", senseOfGlyph "治", senseOfGlyph "學", senseOfGlyph "教"
]

/-- Total glyph-sense table for the v15 roster and the v16 wenyan operator catalogue. -/
def glyphSenses : List GlyphSense :=
  [
  senseOfGlyph "未", senseOfGlyph "尽", senseOfGlyph "显", senseOfGlyph "间", senseOfGlyph "可", senseOfGlyph "生", senseOfGlyph "续", senseOfGlyph "开", senseOfGlyph "闭", senseOfGlyph "绝",
  senseOfGlyph "断", senseOfGlyph "达", senseOfGlyph "候", senseOfGlyph "新", senseOfGlyph "场", senseOfGlyph "焦", senseOfGlyph "物", senseOfGlyph "境", senseOfGlyph "系", senseOfGlyph "心", senseOfGlyph "身",
  senseOfGlyph "間", senseOfGlyph "動", senseOfGlyph "場", senseOfGlyph "際", senseOfGlyph "幾", senseOfGlyph "勢", senseOfGlyph "機", senseOfGlyph "開", senseOfGlyph "閉", senseOfGlyph "網", senseOfGlyph "网", senseOfGlyph "體", senseOfGlyph "体",
  senseOfGlyph "态", senseOfGlyph "状", senseOfGlyph "维", senseOfGlyph "形", senseOfGlyph "相", senseOfGlyph "因", senseOfGlyph "结", senseOfGlyph "据", senseOfGlyph "证", senseOfGlyph "迹",
  senseOfGlyph "史", senseOfGlyph "积", senseOfGlyph "精", senseOfGlyph "气", senseOfGlyph "耦", senseOfGlyph "神", senseOfGlyph "合", senseOfGlyph "法", senseOfGlyph "悖", senseOfGlyph "入", senseOfGlyph "待",
  senseOfGlyph "行", senseOfGlyph "成", senseOfGlyph "冻", senseOfGlyph "修", senseOfGlyph "复", senseOfGlyph "转", senseOfGlyph "动", senseOfGlyph "元", senseOfGlyph "几", senseOfGlyph "权",
  senseOfGlyph "重", senseOfGlyph "差", senseOfGlyph "势", senseOfGlyph "强", senseOfGlyph "向", senseOfGlyph "临", senseOfGlyph "岐", senseOfGlyph "机", senseOfGlyph "扰", senseOfGlyph "变",
  senseOfGlyph "应", senseOfGlyph "伤", senseOfGlyph "散", senseOfGlyph "坍", senseOfGlyph "径", senseOfGlyph "返", senseOfGlyph "限", senseOfGlyph "暂", senseOfGlyph "稳", senseOfGlyph "展",
  senseOfGlyph "审", senseOfGlyph "校", senseOfGlyph "验", senseOfGlyph "异", senseOfGlyph "众", senseOfGlyph "互", senseOfGlyph "受", senseOfGlyph "独", senseOfGlyph "查", senseOfGlyph "源",
  senseOfGlyph "执", senseOfGlyph "著", senseOfGlyph "黜", senseOfGlyph "蔽", senseOfGlyph "程", senseOfGlyph "败", senseOfGlyph "伪", senseOfGlyph "似", senseOfGlyph "实", senseOfGlyph "真",
  senseOfGlyph "通", senseOfGlyph "流", senseOfGlyph "和", senseOfGlyph "平", senseOfGlyph "危", senseOfGlyph "正", senseOfGlyph "邪", senseOfGlyph "夺", senseOfGlyph "依", senseOfGlyph "压",
  senseOfGlyph "护", senseOfGlyph "存", senseOfGlyph "偏", senseOfGlyph "同", senseOfGlyph "筛", senseOfGlyph "放", senseOfGlyph "抑", senseOfGlyph "汰", senseOfGlyph "益", senseOfGlyph "损",
  senseOfGlyph "险", senseOfGlyph "率", senseOfGlyph "阈", senseOfGlyph "效", senseOfGlyph "责", senseOfGlyph "好", senseOfGlyph "坏", senseOfGlyph "自", senseOfGlyph "由", senseOfGlyph "繁",
  senseOfGlyph "荣", senseOfGlyph "义", senseOfGlyph "善", senseOfGlyph "己", senseOfGlyph "共", senseOfGlyph "仁", senseOfGlyph "道", senseOfGlyph "度", senseOfGlyph "期", senseOfGlyph "及",
  senseOfGlyph "外", senseOfGlyph "序", senseOfGlyph "周", senseOfGlyph "回", senseOfGlyph "观", senseOfGlyph "照", senseOfGlyph "辨", senseOfGlyph "识", senseOfGlyph "知", senseOfGlyph "智",
  senseOfGlyph "感", senseOfGlyph "择", senseOfGlyph "情", senseOfGlyph "礼", senseOfGlyph "信", senseOfGlyph "性", senseOfGlyph "能", senseOfGlyph "归", senseOfGlyph "轨", senseOfGlyph "息",
  senseOfGlyph "迫", senseOfGlyph "替", senseOfGlyph "基", senseOfGlyph "线", senseOfGlyph "域", senseOfGlyph "试", senseOfGlyph "定", senseOfGlyph "再", senseOfGlyph "关", senseOfGlyph "格",
  senseOfGlyph "模", senseOfGlyph "面", senseOfGlyph "评", senseOfGlyph "价", senseOfGlyph "础", senseOfGlyph "科", senseOfGlyph "学", senseOfGlyph "逻", senseOfGlyph "辑", senseOfGlyph "构",
  senseOfGlyph "造", senseOfGlyph "纳",
    senseOfGlyph "一", senseOfGlyph "论", senseOfGlyph "普", senseOfGlyph "遍", senseOfGlyph "理", senseOfGlyph "算", senseOfGlyph "演", senseOfGlyph "明", senseOfGlyph "天", senseOfGlyph "子",
  senseOfGlyph "人", senseOfGlyph "世", senseOfGlyph "界", senseOfGlyph "对", senseOfGlyph "聚", senseOfGlyph "意", senseOfGlyph "图", senseOfGlyph "控", senseOfGlyph "齐", senseOfGlyph "做",
  senseOfGlyph "目", senseOfGlyph "标", senseOfGlyph "为", senseOfGlyph "制", senseOfGlyph "层",
  senseOfGlyph "注", senseOfGlyph "调", senseOfGlyph "门", senseOfGlyph "分", senseOfGlyph "配", senseOfGlyph "持", senseOfGlyph "竞", senseOfGlyph "争", senseOfGlyph "记", senseOfGlyph "忆",
  senseOfGlyph "上", senseOfGlyph "下", senseOfGlyph "而", senseOfGlyph "工", senseOfGlyph "作", senseOfGlyph "底",
  senseOfGlyph "露", senseOfGlyph "隙", senseOfGlyph "发", senseOfGlyph "凝", senseOfGlyph "剖",
  senseOfGlyph "所", senseOfGlyph "洽", senseOfGlyph "者", senseOfGlyph "也", senseOfGlyph "于", senseOfGlyph "於", senseOfGlyph "已",
  senseOfGlyph "不", senseOfGlyph "被", senseOfGlyph "投", senseOfGlyph "影", senseOfGlyph "数", senseOfGlyph "值", senseOfGlyph "计", senseOfGlyph "算", senseOfGlyph "经", senseOfGlyph "准",
  senseOfGlyph "在", senseOfGlyph "屬", senseOfGlyph "属", senseOfGlyph "際", senseOfGlyph "际", senseOfGlyph "間", senseOfGlyph "中", senseOfGlyph "應", senseOfGlyph "比", senseOfGlyph "承",
  senseOfGlyph "乘", senseOfGlyph "對", senseOfGlyph "对", senseOfGlyph "偶", senseOfGlyph "耦", senseOfGlyph "並", senseOfGlyph "并", senseOfGlyph "與", senseOfGlyph "与", senseOfGlyph "偕",
  senseOfGlyph "含", senseOfGlyph "包", senseOfGlyph "容", senseOfGlyph "內", senseOfGlyph "内", senseOfGlyph "表", senseOfGlyph "裡", senseOfGlyph "里", senseOfGlyph "化", senseOfGlyph "變",
  senseOfGlyph "易", senseOfGlyph "革", senseOfGlyph "改", senseOfGlyph "反", senseOfGlyph "復", senseOfGlyph "還", senseOfGlyph "还", senseOfGlyph "轉", senseOfGlyph "推", senseOfGlyph "致",
  senseOfGlyph "損", senseOfGlyph "屈", senseOfGlyph "伸", senseOfGlyph "往", senseOfGlyph "來", senseOfGlyph "来", senseOfGlyph "進", senseOfGlyph "进", senseOfGlyph "退", senseOfGlyph "升",
  senseOfGlyph "降", senseOfGlyph "出", senseOfGlyph "動", senseOfGlyph "靜", senseOfGlyph "静", senseOfGlyph "始", senseOfGlyph "終", senseOfGlyph "终", senseOfGlyph "起", senseOfGlyph "止",
  senseOfGlyph "立", senseOfGlyph "極", senseOfGlyph "极", senseOfGlyph "節", senseOfGlyph "节", senseOfGlyph "凡", senseOfGlyph "皆", senseOfGlyph "各", senseOfGlyph "莫", senseOfGlyph "或",
  senseOfGlyph "有", senseOfGlyph "無", senseOfGlyph "无", senseOfGlyph "唯", senseOfGlyph "故", senseOfGlyph "至", senseOfGlyph "使", senseOfGlyph "令", senseOfGlyph "以", senseOfGlyph "必",
  senseOfGlyph "當", senseOfGlyph "当", senseOfGlyph "宜", senseOfGlyph "得", senseOfGlyph "非", senseOfGlyph "弗", senseOfGlyph "勿", senseOfGlyph "毋", senseOfGlyph "異", senseOfGlyph "別",
  senseOfGlyph "别", senseOfGlyph "一", senseOfGlyph "即", senseOfGlyph "是", senseOfGlyph "為", senseOfGlyph "为", senseOfGlyph "分", senseOfGlyph "之", senseOfGlyph "而", senseOfGlyph "則",
  senseOfGlyph "则", senseOfGlyph "若", senseOfGlyph "雖", senseOfGlyph "虽", senseOfGlyph "然", senseOfGlyph "乃", senseOfGlyph "既", senseOfGlyph "將", senseOfGlyph "将", senseOfGlyph "方",
  senseOfGlyph "嘗", senseOfGlyph "尝", senseOfGlyph "理", senseOfGlyph "勢", senseOfGlyph "機", senseOfGlyph "象", senseOfGlyph "名", senseOfGlyph "體", senseOfGlyph "体", senseOfGlyph "用",
  senseOfGlyph "兼", senseOfGlyph "久", senseOfGlyph "宇", senseOfGlyph "端", senseOfGlyph "尺", senseOfGlyph "圜", senseOfGlyph "圆", senseOfGlyph "攖", senseOfGlyph "撄", senseOfGlyph "仳",
  senseOfGlyph "次", senseOfGlyph "指", senseOfGlyph "實", senseOfGlyph "位", senseOfGlyph "離", senseOfGlyph "离", senseOfGlyph "漸", senseOfGlyph "渐", senseOfGlyph "驟", senseOfGlyph "骤",
  senseOfGlyph "忽", senseOfGlyph "遂", senseOfGlyph "又", senseOfGlyph "屢", senseOfGlyph "屡", senseOfGlyph "愈", senseOfGlyph "寖", senseOfGlyph "浸", senseOfGlyph "且", senseOfGlyph "但",
  senseOfGlyph "亦", senseOfGlyph "三", senseOfGlyph "兩", senseOfGlyph "两", senseOfGlyph "倍", senseOfGlyph "半", senseOfGlyph "全", senseOfGlyph "餘", senseOfGlyph "余", senseOfGlyph "過",
  senseOfGlyph "大", senseOfGlyph "書", senseOfGlyph "书", senseOfGlyph "曰", senseOfGlyph "稱", senseOfGlyph "称", senseOfGlyph "諱", senseOfGlyph "讳", senseOfGlyph "譏", senseOfGlyph "讥",
  senseOfGlyph "削", senseOfGlyph "術", senseOfGlyph "术", senseOfGlyph "參", senseOfGlyph "参", senseOfGlyph "二", senseOfGlyph "柄", senseOfGlyph "任", senseOfGlyph "守", senseOfGlyph "利",
  senseOfGlyph "制", senseOfGlyph "罰", senseOfGlyph "赏", senseOfGlyph "陰", senseOfGlyph "阴", senseOfGlyph "陽", senseOfGlyph "阳", senseOfGlyph "五", senseOfGlyph "克", senseOfGlyph "侮",
  senseOfGlyph "氣", senseOfGlyph "血", senseOfGlyph "開", senseOfGlyph "闔", senseOfGlyph "樞", senseOfGlyph "經", senseOfGlyph "絡", senseOfGlyph "络", senseOfGlyph "寒", senseOfGlyph "熱",
  senseOfGlyph "虛", senseOfGlyph "補", senseOfGlyph "瀉", senseOfGlyph "泻", senseOfGlyph "調", senseOfGlyph "调", senseOfGlyph "順", senseOfGlyph "逆", senseOfGlyph "標", senseOfGlyph "本",
  senseOfGlyph "營", senseOfGlyph "营", senseOfGlyph "衛", senseOfGlyph "卫", senseOfGlyph "滯", senseOfGlyph "运", senseOfGlyph "六", senseOfGlyph "上", senseOfGlyph "工", senseOfGlyph "下",
  senseOfGlyph "偽", senseOfGlyph "群", senseOfGlyph "義", senseOfGlyph "隆", senseOfGlyph "殺", senseOfGlyph "解", senseOfGlyph "積", senseOfGlyph "交", senseOfGlyph "錯", senseOfGlyph "错",
  senseOfGlyph "綜", senseOfGlyph "综", senseOfGlyph "雜", senseOfGlyph "杂", senseOfGlyph "隱", senseOfGlyph "隐", senseOfGlyph "顯", senseOfGlyph "藏", senseOfGlyph "露", senseOfGlyph "持",
  senseOfGlyph "居", senseOfGlyph "處", senseOfGlyph "处", senseOfGlyph "聚", senseOfGlyph "集", senseOfGlyph "引", senseOfGlyph "攝", senseOfGlyph "摄", senseOfGlyph "蘊", senseOfGlyph "蕴",
  senseOfGlyph "萌", senseOfGlyph "兆", senseOfGlyph "苗", senseOfGlyph "占", senseOfGlyph "卜", senseOfGlyph "演", senseOfGlyph "譬", senseOfGlyph "喻", senseOfGlyph "觀", senseOfGlyph "察",
  senseOfGlyph "明", senseOfGlyph "悟", senseOfGlyph "識",
  ] ++ recoveredMissingGlyphSenses ++
  [
  mk "生" 2 .operator, mk "生" 3 .generated, mk "之" 2 .particle, mk "之" 3 .operator, mk "真" 2 .generated, mk "中" 2 .operator, mk "正" 2 .operator, mk "行" 2 .operator,
  mk "法" 2 .operator, mk "道" 2 .operator, mk "反" 2 .operator, mk "同" 2 .operator, mk "一" 2 .operator, mk "可" 2 .modal,
  mk "为" 2 .operator, mk "為" 2 .operator, mk "与" 2 .operator, mk "與" 2 .operator, mk "故" 2 .operator, mk "或" 2 .modal,
  mk "应" 2 .modal, mk "應" 2 .modal, mk "体" 2 .operator, mk "體" 2 .operator, mk "用" 2 .operator, mk "名" 2 .operator,
  mk "分" 2 .operator, mk "化" 2 .operator,
  ] ++ coreNumberedSenses ++
  [
  formalSense "I_F", formalSense "K_Γ", formalSense "w_Γ", formalSense "D_KΓ", formalSense "norm_KΓ", formalSense "oplus_F",
  formalSense "κ", formalSense "κ_star", formalSense "Ω", formalSense "Ω_B", formalSense "μ", formalSense "Pr",
  formalSense "Φ_形", formalSense "Φ_因", formalSense "Φ_结", formalSense "Π_开", formalSense "Q_audit", formalSense "Θ", formalSense "Attention",
  formalSense "域", formalSense "格", formalSense "权", formalSense "生", formalSense "校",
  ]

def RegisteredSense (s : GlyphSense) : Prop :=
  s ∈ glyphSenses

instance registeredSenseDecidable (s : GlyphSense) : Decidable (RegisteredSense s) := by
  unfold RegisteredSense
  infer_instance

def registeredForms (xs : List GlyphSense) : Bool :=
  xs.all (fun s => decide (RegisteredSense s))

def RegisteredForms (xs : List GlyphSense) : Prop :=
  registeredForms xs = true

instance registeredFormsDecidable (xs : List GlyphSense) : Decidable (RegisteredForms xs) := by
  unfold RegisteredForms
  infer_instance

def CoveredForms (xs : List GlyphSense) : Prop :=
  xs ≠ [] ∧ RegisteredForms xs

instance coveredFormsDecidable (xs : List GlyphSense) : Decidable (CoveredForms xs) := by
  unfold CoveredForms
  infer_instance

structure Coverage where
  forms : List GlyphSense
  nonempty : forms ≠ []
  registered : RegisteredForms forms

/--
Glyph aliases for primitive model interfaces.

These are text-facing anchors, not derivations: the primitive keeps its formal
interface token while also being readable through five registered core glyphs.
-/
inductive PrimitiveCoreInterface where
  | domain
  | structure
  | weight
  | generation
  | audit
  deriving DecidableEq, Repr

namespace PrimitiveCoreInterface

def glyph : PrimitiveCoreInterface -> Glyph
  | .domain => "域"
  | .structure => "格"
  | .weight => "权"
  | .generation => "生"
  | .audit => "校"

def sense (c : PrimitiveCoreInterface) : GlyphSense :=
  senseOfGlyph c.glyph

end PrimitiveCoreInterface

def primitiveCoreInterface : SSBX.Roster.PrimName -> PrimitiveCoreInterface
  | .«域» => .domain
  | .«格» => .structure
  | .«权» => .weight
  | .«生» => .generation
  | .«校» => .audit

def primitiveGlyphAliases (p : SSBX.Roster.PrimName) : List GlyphSense :=
  [(primitiveCoreInterface p).sense]

def interfaceRhsOperatorGlyphs : List Glyph :=
  ["域", "格", "权", "生", "校", "形", "因", "结"]

inductive DerivedInterface where
  | I_F | K_Γ | w_Γ | D_KΓ | norm_KΓ | oplus_F
  | κ | κ_star | Ω | Ω_B | μ | Pr
  | «Φ_形» | «Φ_因» | «Φ_结» | «Π_开»
  | Q_audit | Θ | Attention
  deriving DecidableEq, Repr

namespace DerivedInterface

def label : DerivedInterface -> String
  | .I_F => "I_F"
  | .K_Γ => "K_Γ"
  | .w_Γ => "w_Γ"
  | .D_KΓ => "D_KΓ"
  | .norm_KΓ => "norm_KΓ"
  | .oplus_F => "oplus_F"
  | .κ => "κ"
  | .κ_star => "κ_star"
  | .Ω => "Ω"
  | .Ω_B => "Ω_B"
  | .μ => "μ"
  | .Pr => "Pr"
  | .«Φ_形» => "Φ_形"
  | .«Φ_因» => "Φ_因"
  | .«Φ_结» => "Φ_结"
  | .«Π_开» => "Π_开"
  | .Q_audit => "Q_audit"
  | .Θ => "Θ"
  | .Attention => "Attention"

def formula : DerivedInterface -> String
  | .I_F => "域"
  | .K_Γ => "格"
  | .w_Γ => "权"
  | .D_KΓ => "格权"
  | .norm_KΓ => "权格"
  | .oplus_F => "生"
  | .κ => "格权"
  | .κ_star => "格权校"
  | .Ω => "权"
  | .Ω_B => "权校"
  | .μ => "权"
  | .Pr => "权校"
  | .«Φ_形» => "校形"
  | .«Φ_因» => "校因"
  | .«Φ_结» => "校结"
  | .«Π_开» => "校权"
  | .Q_audit => "校"
  | .Θ => "校权"
  | .Attention => "权"

def rhsGlyphs (i : DerivedInterface) : List GlyphSense :=
  textToSenses i.formula

def lhsToken (i : DerivedInterface) : GlyphSense :=
  formalSense i.label

def assignment (i : DerivedInterface) : String :=
  i.label ++ " := " ++ i.formula

end DerivedInterface

def allDerivedInterfaces : List DerivedInterface := [
  .I_F, .K_Γ, .w_Γ, .D_KΓ, .norm_KΓ, .oplus_F,
  .κ, .κ_star, .Ω, .Ω_B, .μ, .Pr,
  .«Φ_形», .«Φ_因», .«Φ_结», .«Π_开»,
  .Q_audit, .Θ, .Attention
]

def CoveredDerivedInterface (i : DerivedInterface) : Prop :=
  RegisteredSense i.lhsToken ∧ CoveredForms i.rhsGlyphs

instance coveredDerivedInterfaceDecidable (i : DerivedInterface) :
    Decidable (CoveredDerivedInterface i) := by
  unfold CoveredDerivedInterface
  infer_instance

def rhsUsesSingleGlyphOperators (i : DerivedInterface) : Bool :=
  i.rhsGlyphs.all (fun s => decide (s.glyph ∈ interfaceRhsOperatorGlyphs))

def RhsUsesSingleGlyphOperators (i : DerivedInterface) : Prop :=
  rhsUsesSingleGlyphOperators i = true

instance rhsUsesSingleGlyphOperatorsDecidable (i : DerivedInterface) :
    Decidable (RhsUsesSingleGlyphOperators i) := by
  unfold RhsUsesSingleGlyphOperators
  infer_instance

def CoveredPrimitiveAlias (p : SSBX.Roster.PrimName) : Prop :=
  CoveredForms (primitiveGlyphAliases p)

instance coveredPrimitiveAliasDecidable (p : SSBX.Roster.PrimName) :
    Decidable (CoveredPrimitiveAlias p) := by
  unfold CoveredPrimitiveAlias
  infer_instance

/-- Textual senses for a v15 symbol. Primitive model interfaces are kept as formal tokens. -/
def symbolGlyphSenses (s : SSBX.Roster.Symbol) : List GlyphSense :=
  match s with
  | SSBX.Roster.Symbol.primitive p => [formalSense (SSBX.Roster.PrimName.label p)]
  | _ => textToSenses (SSBX.Roster.Symbol.label s)

/-- Display aliases add glyph anchors for primitive symbols without replacing formal tokens. -/
def symbolGlyphAliases (s : SSBX.Roster.Symbol) : List GlyphSense :=
  match s with
  | SSBX.Roster.Symbol.primitive p => primitiveGlyphAliases p
  | _ => symbolGlyphSenses s

def CoveredSymbol (s : SSBX.Roster.Symbol) : Prop :=
  CoveredForms (symbolGlyphSenses s)

instance coveredSymbolDecidable (s : SSBX.Roster.Symbol) : Decidable (CoveredSymbol s) := by
  unfold CoveredSymbol
  infer_instance

end SSBX.Text.Glyph
