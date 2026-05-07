/-
# WenSurface.Lex — 文表层之词法

将受控文 (wenyan source) 字符串切分为 GlyphTok 流，为后续 reading 消歧
与算子 elaborate 做准备。

## 与 baguaWen 之关系

baguaWen (M1/M3) 之 lex/parse 已封顶且完全独立 — 本文不调用、不修改其
任何函数与定理，避免污染 lex inversion 主柱。WenSurface 仅消费 raw
String，产出独立的 GlyphTok 流。

## 多字 surface 词典

来源：OperatorReadings.lean 之 `surfaceReadings` keys。
spike 2026-05-08 实证：当前 82 个 surface 中唯一多字 surface 为「名分」，
其余 81 皆单 CJK 字（含简繁变体）。故 `multiCharSurfaces = ["名分"]`。

## 状态

0 sorry / 0 axiom / 总函数 (fuel-bounded). 关键例由 native_decide 见证.
-/

namespace SSBX.Foundation.Wen.WenSurface

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
    古汉语字符（含 simp/trad 变体）。Extension A/B 等不含 — v1 范围足。 -/
def isCJKBasic (c : Char) : Bool :=
  let n := c.toNat
  Nat.ble 0x4E00 n && Nat.ble n 0x9FFF

/-- ASCII 空白：space / tab / newline / CR. -/
def isAsciiSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-! ## § 3  多字 surface 词典 -/

/-- 多字 wenyan surface — 来自 OperatorReadings spike 2026-05-08。
    当前唯一多字 entry：「名分」。
    扩充时按长度降序排列（最长前缀优先匹配）。 -/
def multiCharSurfaces : List String := ["名分"]

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
    if isAsciiSpace c then
      lexFuel n (col + 1) rest
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

/-- 仅「名」（不接「分」）保持单字读. -/
example :
    (lexWen "名也").toOption = some [⟨"名", 0, 1, false⟩, ⟨"也", 1, 1, false⟩] :=
  by native_decide

/-- 空串. -/
example : (lexWen "").toOption = some [] := by native_decide

/-- ASCII 字母（非 CJK 非 whitespace）→ error. -/
example : (lexWen "x").toOption = none := by native_decide

/-- 全空白. -/
example : (lexWen "   ").toOption = some [] := by native_decide

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
