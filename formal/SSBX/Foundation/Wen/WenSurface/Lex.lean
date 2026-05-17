/-
# WenSurface.Lex — 文表层之词法

将受控文 (wenyan source) 字符串切分为 GlyphTok 流，为后续 reading 消歧
与算子 elaborate 做准备。

## 与 baguaWen 之关系

baguaWen (M1/M3) 之 lex/parse 已封顶且完全独立 — 本文不调用、不修改其
任何函数与定理，避免污染 lex inversion 主柱。WenSurface 仅消费 raw
String，产出独立的 GlyphTok 流。

## 多字 surface 词典

来源：surface catalogue 复词、显式构式，以及 Reading 层完整卦名/alias。
`multiCharSurfaces` 保持为最长前缀表：Lex 不依赖 Reading，Reading/Coverage
反向用 native_decide 例子守住多字卦名与 alias 的单 token 行为。

## 状态

0 sorry / 0 axiom / 总函数 (fuel-bounded). 关键例由 native_decide 见证.
-/
import SSBX.Text.WenyanOperators

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Text.WenyanOperators

/-! ## § 1  Glyph token 类型 -/

/-- 文表层之 token。surface 为 1-N 个 codepoint；startCol 为 0-indexed
    codepoint 位置；width 为 codepoint 数；isMulti = (width > 1). -/
structure GlyphTok where
  surface  : String
  startCol : Nat
  width    : Nat
  isMulti  : Bool
deriving DecidableEq, Repr

/-- 词法错误。 -/
inductive LexErr where
  | unexpected     (col : Nat) (ch : Char) : LexErr
  | fuelExhausted                          : LexErr
deriving DecidableEq, Repr

/-! ## § 2  Char 分类 -/

/-- 基本 CJK Unified Ideographs (U+4E00..U+9FFF). 涵盖现代汉语 + 多数
    古汉语字符（含 simp/trad 变体）。Extension A/B 等暂不进入 surface 前端。 -/
def isCJKBasic (c : Char) : Bool :=
  let n := c.toNat
  Nat.ble 0x4E00 n && Nat.ble n 0x9FFF

/-- ASCII 空白：space / tab / newline / CR. -/
def isAsciiSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- WenSurface whitespace includes ASCII whitespace plus ideographic space. -/
def isWenSpace (c : Char) : Bool :=
  isAsciiSpace c || c == '　'

/-- Grouping & quoting punctuation accepted by the WenSurface parser.

  · `（）()`     — value grouping (parses inside as ordinary expression)
  · `「」`       — quote brackets (wen-2.0 ⑩); inside parses to Tm but wraps
                  in `Tm.quote` — body is data, not evaluated. Pairs with ⑥ 曰.
  · `『』`       — secondary / nested quote brackets (same semantics as `「」`).
                  Useful in classical Chinese for quotes inside quotes.

  All four open/close pairs use the same lexer 1-char branch.  Disambiguation
  between value grouping and quote happens at `Reading.matchingCloseBracket?`
  and `Syntax.SurfaceExpr.grouped` (the open token's surface is preserved). -/
def isBracketChar (c : Char) : Bool :=
  c == '（' || c == '）' || c == '(' || c == ')'
    || c == '「' || c == '」' || c == '『' || c == '』'

/-! ## § 3  多字 surface 词典 -/

/-- Conservatively curated multi-character catalogue surfaces.
    `operatorForms` stores glyph senses, so multi-character technical terms
    need this explicit table rather than being inferred from concatenated
    simplified/traditional glyph alternatives. -/
def operatorCompoundSurfaceIds : List (String × OperatorId) :=
  [ ("上工中工下工", .Y_25), ("五运六气", .Y_24), ("五運六氣", .Y_24)
  , ("開闔樞", .Y_11), ("开阖枢", .Y_11), ("無己名", .ZHU_3), ("无己名", .ZHU_3)
  , ("陰与陽", .Y_1), ("阴与阳", .Y_1), ("陰陽", .Y_1), ("阴阳", .Y_1)
  , ("體与用", .H_8), ("体与用", .H_8), ("體用", .H_8), ("体用", .H_8)
  , ("過半", .D_10), ("过半", .D_10), ("大半", .D_10)
  , ("褒貶", .E_9), ("褒贬", .E_9), ("形名", .L_4)
  , ("參同", .L_5), ("参同", .L_5), ("二柄", .L_6)
  , ("無為", .L_11), ("无为", .L_11), ("罰賞", .L_16), ("罚赏", .L_16)
  , ("五行", .Y_2), ("相生", .Y_3), ("相克", .Y_4), ("相侮", .Y_5)
  , ("反侮", .Y_5), ("升降", .Y_10), ("經絡", .Y_12), ("经络", .Y_12)
  , ("經与絡", .Y_12), ("经与络", .Y_12)
  , ("表裡", .Y_13), ("表里", .Y_13), ("寒熱", .Y_14), ("寒热", .Y_14)
  , ("虛實", .Y_15), ("虚实", .Y_15), ("補瀉", .Y_16), ("补泻", .Y_16)
  , ("順逆", .Y_20), ("顺逆", .Y_20), ("標本", .Y_21), ("标本", .Y_21)
  , ("營衛", .Y_22), ("营卫", .Y_22), ("營与衛", .Y_22), ("营与卫", .Y_22)
  , ("通滯", .Y_23), ("通滞", .Y_23), ("上工", .Y_25), ("中工", .Y_25)
  , ("下工", .Y_25), ("出入", .Y_26), ("化性", .X_3)
  , ("隆殺", .X_10), ("隆杀", .X_10)
  , ("名分", .X_12), ("譬喻", .Z_30), ("自反", .Z_33), ("反自", .Z_33)
  , ("物化", .ZHU_6), ("天理", .ZHU_9), ("致人", .SUN_11), ("分合", .SUN_12)
  , ("上下", .CHU_2), ("未變", .CHU_10), ("未变", .CHU_10)
  , ("大一", .ZA_13), ("同異", .ZA_16), ("同异", .ZA_16)
  , ("兩可", .ZA_17), ("两可", .ZA_17), ("正名", .ZA_18)
  , ("不動", .L_10), ("不动", .L_10)
  , ("錯綜", .I_8), ("错综", .I_8), ("綜錯", .I_8), ("综错", .I_8)
  , ("反覆", .Z_33), ("反复", .Z_33), ("交錯", .Z_33), ("交错", .Z_33)
  , ("歸一", .T_7), ("归一", .T_7), ("歸極", .T_7), ("归极", .T_7)
  , ("總歸", .T_7), ("总归", .T_7), ("復歸", .T_7), ("复归", .T_7)
  , ("展開", .T_15), ("展开", .T_15)
  , ("動初", .T_5), ("动初", .T_5), ("初動", .T_5), ("初动", .T_5)
  , ("初變", .T_5), ("初变", .T_5)
  , ("翻初", .T_5)
  , ("動中", .T_1), ("动中", .T_1), ("動二", .T_1), ("动二", .T_1)
  , ("二變", .T_1), ("二变", .T_1), ("承變", .T_1), ("承变", .T_1)
  , ("中化", .T_1), ("中變", .T_1), ("中变", .T_1)
  , ("翻中", .T_1)
  , ("動上", .T_2), ("动上", .T_2), ("動三", .T_2), ("动三", .T_2)
  , ("三變", .T_2), ("三变", .T_2), ("際變", .T_2), ("际变", .T_2)
  , ("內極", .T_2), ("内极", .T_2), ("上變", .T_2), ("上变", .T_2)
  , ("翻上", .T_2) ]

/-- 多字 wenyan surface。
    包含构式/目录复词，以及完整卦名中不能被拆为单字的 surface。
    扩充时按长度降序排列（最长前缀优先匹配）；同长度内顺序无关.

    B-2 / B-6: 多字 builtin Tm surfaces (`初爻..上爻` 与 `列一..列三`) — 各自
    映射到 `WenDef` 之 `flip{1..6}H` / `list{1,2,3}H` Tm 原语，由
    [Reading.resolveBuiltinSurface](Reading.lean) 解析为 `.builtinTm`
    atom（不进 OperatorId 表）.  B-3 (`加`) 是单字，无需进此表. -/
def multiCharSurfaces : List String :=
  [ "之所以"  -- wen-2.0 ⑧ reason-extraction marker: `Y 之所以 X`
  , "之又"
  , "小畜", "同人", "大有", "噬嗑", "无妄", "無妄", "大畜", "大过", "大過"
  , "明夷", "家人", "大壮", "大壯", "归妹", "歸妹", "中孚", "小过", "小過"
  , "既济", "既濟", "未济", "未濟"
    -- B-2: yao-flip builtin surfaces (per `WenDef.flip{1..6}H`).
  , "初爻", "二爻", "三爻", "四爻", "五爻", "上爻"
    -- B-6: Hex list-construction builtin surfaces (per `WenDef.list{1,2,3}H`).
  , "列一", "列二", "列三" ]
    ++ operatorCompoundSurfaceIds.map Prod.fst

/-- 检查 prefix 是否为 cs 之前缀（字符级）。 -/
def listIsPrefix : List Char → List Char → Bool
  | [],          _              => true
  | _ :: _,      []             => false
  | p :: prest,  c :: crest     => p == c && listIsPrefix prest crest

/-- 在多字词典中找匹配前缀。返回 (匹配 surface, codepoint 数, 余下 char list)。 -/
def matchMulti (cs : List Char) : Option (String × Nat × List Char) :=
  multiCharSurfaces.findSome? fun s =>
    let pl := s.toList
    if listIsPrefix pl cs then
      some (s, pl.length, cs.drop pl.length)
    else
      none

/-! ## § 4  词法主函数 -/

/-- Fuel-bounded 词法器。fuel ≥ cs.length + 1 时与无穷 fuel 同效。
    总函数（结构递归 on fuel）。 -/
def lexFuel : Nat → Nat → List Char → Except LexErr (List GlyphTok)
  | 0,     _,   _              => .error .fuelExhausted
  | _+1,   _,   []             => .ok []
  | n+1,   col, c :: rest      =>
    if isWenSpace c then
      lexFuel n (col + 1) rest
    else if isBracketChar c then
      match lexFuel n (col + 1) rest with
      | .ok ts   => .ok (⟨c.toString, col, 1, false⟩ :: ts)
      | .error e => .error e
    else
      match matchMulti (c :: rest) with
      | some (s, w, rest') =>
        match lexFuel n (col + w) rest' with
        | .ok ts   => .ok (⟨s, col, w, true⟩ :: ts)
        | .error e => .error e
      | none =>
        if isCJKBasic c then
          match lexFuel n (col + 1) rest with
          | .ok ts   => .ok (⟨c.toString, col, 1, false⟩ :: ts)
          | .error e => .error e
        else
          .error (.unexpected col c)

/-- 顶层 entry：String → GlyphTok 流。fuel = codepoint 数 + 1，足够。 -/
def lexWen (s : String) : Except LexErr (List GlyphTok) :=
  let cs := s.toList
  lexFuel (cs.length + 1) 0 cs

/-! ## § 5  Sanity 例子 (native_decide via toOption) -/

/-- 单字 CJK：「推」一字一 token. -/
example :
    (lexWen "推").toOption = some [⟨"推", 0, 1, false⟩] := by native_decide

/-- 双 CJK 之间空格 skip：col 因空格 +1. -/
example :
    (lexWen "推 一").toOption = some [⟨"推", 0, 1, false⟩, ⟨"一", 2, 1, false⟩] :=
  by native_decide

/-- 全角空格也按 WenSurface 空白处理，col 仍按 codepoint 前进. -/
example :
    (lexWen "推　一").toOption = some [⟨"推", 0, 1, false⟩, ⟨"一", 2, 1, false⟩] :=
  by native_decide

/-- 三字相邻无空格. -/
example :
    (lexWen "推一生").toOption
      = some [⟨"推", 0, 1, false⟩, ⟨"一", 1, 1, false⟩, ⟨"生", 2, 1, false⟩] :=
  by native_decide

/-- 多字 surface 「名分」最长匹配优先. -/
example :
    (lexWen "名分推").toOption
      = some [⟨"名分", 0, 2, true⟩, ⟨"推", 2, 1, false⟩] :=
  by native_decide

/-- 较长 compound surface 优先于其内部短 token. -/
example :
    (lexWen "上工中工下工").toOption = some [⟨"上工中工下工", 0, 6, true⟩] :=
  by native_decide

theorem operatorCompoundSurfaces_lex_as_single :
    (operatorCompoundSurfaceIds.map Prod.fst).all
        (fun s =>
          match lexWen s with
          | .ok [tok] =>
              (tok.surface == s)
                && (tok.startCol == 0)
                && (tok.width == s.toList.length)
                && (tok.isMulti == decide (s.toList.length > 1))
          | _ => false) = true := by
  native_decide

/-- 多字卦名保持单 token. -/
example :
    (lexWen "小过").toOption = some [⟨"小过", 0, 2, true⟩] :=
  by native_decide

/-- 多字 surface 「之又」单独 lex 为 1 token，width = 2，isMulti = true. -/
example :
    (lexWen "之又").toOption = some [⟨"之又", 0, 2, true⟩] := by native_decide

/-- 「之又 推 一」：之又 + 推 + 一 三 token；空格调整 col. -/
example :
    (lexWen "之又 推 一").toOption
      = some [⟨"之又", 0, 2, true⟩, ⟨"推", 3, 1, false⟩, ⟨"一", 5, 1, false⟩] :=
  by native_decide

/-- 仅「名」（不接「分」）保持单字读. -/
example :
    (lexWen "名也").toOption = some [⟨"名", 0, 1, false⟩, ⟨"也", 1, 1, false⟩] :=
  by native_decide

/-- 空串. -/
example : (lexWen "").toOption = some [] := by native_decide

/-- ASCII 字母（非 CJK 非 whitespace）→ error. -/
example : (lexWen "x").toOption = none := by native_decide

/-- Grouping punctuation is tokenized even though it is not CJK. -/
example :
    (lexWen "（推 一）").toOption
      = some [⟨"（", 0, 1, false⟩, ⟨"推", 1, 1, false⟩,
              ⟨"一", 3, 1, false⟩, ⟨"）", 4, 1, false⟩] :=
  by native_decide

example :
    (lexWen "(推 一)").toOption
      = some [⟨"(", 0, 1, false⟩, ⟨"推", 1, 1, false⟩,
              ⟨"一", 3, 1, false⟩, ⟨")", 4, 1, false⟩] :=
  by native_decide

/-- wen-2.0 ⑩: `「`/`」` 引语括号 lex 为独立 1-char tokens. -/
example :
    (lexWen "「学」").toOption
      = some [⟨"「", 0, 1, false⟩, ⟨"学", 1, 1, false⟩, ⟨"」", 2, 1, false⟩] :=
  by native_decide

/-- wen-2.0 ⑩: `『`/`』` 次级引语括号 lex 为独立 1-char tokens. -/
example :
    (lexWen "『学』").toOption
      = some [⟨"『", 0, 1, false⟩, ⟨"学", 1, 1, false⟩, ⟨"』", 2, 1, false⟩] :=
  by native_decide

/-- Nested quote brackets lex correctly. -/
example :
    (lexWen "「『一』」").toOption
      = some [⟨"「", 0, 1, false⟩, ⟨"『", 1, 1, false⟩, ⟨"一", 2, 1, false⟩,
              ⟨"』", 3, 1, false⟩, ⟨"」", 4, 1, false⟩] :=
  by native_decide

/-- 全空白. -/
example : (lexWen "   ").toOption = some [] := by native_decide

example : (lexWen "　").toOption = some [] := by native_decide

/-- Wenyan punctuation is still rejected until the parser has an explicit policy. -/
example :
    (["。", "，", "、", "；", "：", "？", "！"].all
      (fun p => (lexWen ("推" ++ p ++ "一")).toOption.isNone)) = true :=
  by native_decide

/-- Stdlib 6 算子 surface 各自单独 lex. -/
example :
    (lexWen "推 比 不 必 同 凡").toOption
      = some [⟨"推", 0, 1, false⟩, ⟨"比", 2, 1, false⟩, ⟨"不", 4, 1, false⟩,
              ⟨"必", 6, 1, false⟩, ⟨"同", 8, 1, false⟩, ⟨"凡", 10, 1, false⟩] :=
  by native_decide

/-! ## § 6  结构性引理 -/

/-- 空 char list 之 lex（fuel ≥ 1）皆 .ok []. -/
theorem lexFuel_nil (n col : Nat) (h : 1 ≤ n) :
    lexFuel n col [] = .ok [] := by
  cases n with
  | zero    => omega
  | succ _  => rfl

/-- GlyphTok well-formedness：surface 之 codepoint 长度 = width，且
    isMulti 与 width > 1 一致. -/
def GlyphTok.wellFormed (t : GlyphTok) : Bool :=
  decide (t.surface.toList.length = t.width)
    && (t.isMulti == decide (t.width > 1))

/-- lex 之产出 token 皆 well-formed（spike 范围内的代表例）. -/
example :
    ((lexWen "推 一 名分 生").map (·.all GlyphTok.wellFormed)).toOption
      = some true :=
  by native_decide

/-- listIsPrefix 之自反性. -/
theorem listIsPrefix_self (cs : List Char) : listIsPrefix cs cs = true := by
  induction cs with
  | nil       => rfl
  | cons c cs ih =>
    simp [listIsPrefix, ih]

/-- listIsPrefix [] _ = true（base case）. -/
theorem listIsPrefix_nil_left (cs : List Char) : listIsPrefix [] cs = true := by
  rfl

end SSBX.Foundation.Wen.WenSurface
