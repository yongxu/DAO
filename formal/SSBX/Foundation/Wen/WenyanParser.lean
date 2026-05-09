/-
# WenyanParser — String → List YiInstr (受控文 baguaWen 之解析 + 印 + 反向)

Path 丙 § M1：parse + print baguaWen 受控文。

受控语法见 `notes/baguaWen-spec.md` § 6。
Token 集见 `Bagua.BaguaWenSpec.reservedTokens`。

## Pipeline

```
  String                  ──[ lex ]──→  List Tok
  List Tok                ──[ parseProg ]──→  Option (List YiInstr)
  List YiInstr            ──[ printProg ]──→  String
```

顶层别名 `«解程»` (parse) + `«印程»` (print) 直接吃 String / 出 String。

## 语法（即 spec § 6）

```
程     ::= 句*
句     ::= 命 sep
sep    ::= 「；」 | 「;」
命     ::= «不动» | «互» | «错» | «综» | «易» | «推» | «取» | «终»
        | «设时» 时
        | «翻爻» 爻
        | «比爻» 爻 爻 «至» 数
        | «比时» 时 «至» 数
        | «跳» «至» 数
时     ::= «已» | «今» | «未»
爻     ::= «初爻» | «二爻» | «三爻» | «四爻» | «五爻» | «上爻»
数     ::= 中文数字 1..64
```

## 状态

- 0 sorry / 0 axiom
- `lexAux` / `parseProg` 为总函数；`lexAux` 以输入长度终止，
  `parseProg` 经内部 fuel 辅助终止
- 关键 round-trip 由 `native_decide` 在具体程序与全合法单指令宇宙上见证
- 一般性 `parse_print` 定理之真实前提为 `validProg p = true`；
  Nat target 只在 1..64 内可逆，0/>64 会印成 `«?»`
-/
import SSBX.Foundation.Bagua.BaguaTuring
import SSBX.Foundation.Bagua.BaguaWenSpec

-- 项目中 `YiInstr` 仅 `deriving Repr`；为使 round-trip native_decide 可决定性，
-- 在原 namespace 内补派生 `DecidableEq`（参数皆 DecidableEq 故可派）。
namespace SSBX.Foundation.Bagua.BaguaTuring
deriving instance DecidableEq for YiInstr
end SSBX.Foundation.Bagua.BaguaTuring

namespace SSBX.Foundation.Wen.WenyanParser

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring

/-! ## § 1  Token 类型 -/

/-- 词元：«»内的 CJK 标识符，或语句分隔符（；/ ;）。 -/
inductive Tok : Type
  | cjk : String → Tok
  | sep : Tok
deriving DecidableEq, Repr

/-! ## § 2  Lexer -/

/-- 切分至下一个 »：返回 (内层字符表, 含 » 之剩余)。 -/
def splitOnClose : List Char → List Char × List Char
  | [] => ([], [])
  | '»' :: rest => ([], '»' :: rest)
  | c :: rest =>
      let (inner, after) := splitOnClose rest
      (c :: inner, after)

/-- `splitOnClose` 返回之 suffix 不长于原输入。用于 lexer 终止性。 -/
theorem splitOnClose_after_length_le (xs : List Char) :
    (splitOnClose xs).2.length ≤ xs.length := by
  induction xs with
  | nil => simp [splitOnClose]
  | cons c rest ih =>
      by_cases h : c = '»'
      · subst h
        simp [splitOnClose]
      · simp [splitOnClose]
        omega

/-- 字符流之词法分析。返回 none 表示非法输入（未闭 «、未识别字符等）。 -/
def lexAux : List Char → Option (List Tok)
  | [] => some []
  | c :: rest =>
      if c = ' ' || c = '\t' || c = '\n' || c = '\r' then
        lexAux rest
      else if c = '«' then
        match hsplit : splitOnClose rest with
        | (inner, after) =>
            let _ := hsplit
            match after with
            | '»' :: rs =>
                match lexAux rs with
                | some toks => some (Tok.cjk (String.ofList inner) :: toks)
                | none      => none
            | _ => none  -- unmatched «
      else if c = ';' || c = '；' then
        match lexAux rest with
        | some toks => some (Tok.sep :: toks)
        | none      => none
      else
        none  -- unexpected char
termination_by xs => xs.length
decreasing_by
  all_goals simp_wf
  have hle : ('»' :: rs).length ≤ rest.length := by
    have h := splitOnClose_after_length_le rest
    rw [hsplit] at h
    exact h
  simp at hle
  omega

def lex (s : String) : Option (List Tok) := lexAux s.toList

/-! ## § 3  时态 / 爻位 / 数词 -/

def parseShi : String → Option Shi
  | "已" => some .ji
  | "今" => some .jin
  | "未" => some .wei
  | _    => none

def parseYao : String → Option (Fin 6)
  | "初爻" => some ⟨0, by omega⟩
  | "二爻" => some ⟨1, by omega⟩
  | "三爻" => some ⟨2, by omega⟩
  | "四爻" => some ⟨3, by omega⟩
  | "五爻" => some ⟨4, by omega⟩
  | "上爻" => some ⟨5, by omega⟩
  | _      => none

/-- 中文一字数字 1-9. -/
def parseChar1to9 : Char → Option Nat
  | '一' => some 1 | '二' => some 2 | '三' => some 3
  | '四' => some 4 | '五' => some 5 | '六' => some 6
  | '七' => some 7 | '八' => some 8 | '九' => some 9
  | _    => none

/-- 中文数词 1-64. -/
def parseNumeral (s : String) : Option Nat :=
  match s.toList with
  | ['十'] => some 10              -- 必先于 [c] 否则被遮
  | [c] => parseChar1to9 c
  | ['十', d] =>
      match parseChar1to9 d with
      | some k => some (10 + k)
      | none   => none
  | [t, '十'] =>
      match parseChar1to9 t with
      | some k => if k ≥ 2 ∧ k ≤ 6 then some (k * 10) else none
      | none   => none
  | [t, '十', d] =>
      match parseChar1to9 t, parseChar1to9 d with
      | some kt, some kd =>
          if kt ≥ 2 ∧ kt ≤ 6 ∧ (kt * 10 + kd) ≤ 64 then
            some (kt * 10 + kd)
          else none
      | _, _ => none
  | _ => none

/-! ## § 4  Parser -/

def isNopAlias : String → Bool
  | "不動" | "静" | "靜" | "恒" | "常" | "守" | "定"
  | "止" | "安" | "寂" | "息" | "平" | "和" | "一"
  | "正" | "立" | "成" | "還" | "还" => true
  | _ => false

def isSetShiAlias : String → Bool
  | "設時" | "设" | "設" | "置" | "置时" | "置時" | "定时" | "定時"
  | "定" | "令" | "更" | "易" | "移" | "转" | "轉" | "调" | "調"
  | "时" | "時" => true
  | _ => false

def isFlipYaoAlias : String → Bool
  | "翻" | "動" | "动" | "動爻" | "动爻" | "變" | "变" | "變爻" | "变爻"
  | "易" | "改" | "反" | "转" | "轉" | "换" | "換" | "倒" | "更" => true
  | _ => false

def isBranchYaoEqAlias : String → Bool
  | "侔" | "比" | "同" | "等" | "伦" | "倫" | "校" | "较" | "較" => true
  | _ => false

def isBranchShiEqAlias : String → Bool
  | "会" | "會" | "侔" | "比" | "同" | "等" => true
  | _ => false

/-- Alias parser for the newer single-glyph/default instruction names.
    Canonical tokens are still handled by the direct clauses below, so the
    pretty-printer round-trip remains stable. -/
def parseInstrAlias (op : String) (rest : List Tok) : Option (YiInstr × List Tok) :=
  match rest with
  | .cjk yi :: .cjk yj :: .cjk "至" :: .cjk n :: rest' =>
      if isBranchYaoEqAlias op then
        match parseYao yi, parseYao yj, parseNumeral n with
        | some i, some j, some t => some (.branchYaoEq i j t, rest')
        | _, _, _ => none
      else none
  | .cjk s :: .cjk "至" :: .cjk n :: rest' =>
      if isBranchShiEqAlias op then
        match parseShi s, parseNumeral n with
        | some shi, some t => some (.branchShiEq shi t, rest')
        | _, _ => none
      else none
  | .cjk a :: rest' =>
      match (if isSetShiAlias op then parseShi a else none) with
      | some shi => some (.setShi shi, rest')
      | none =>
          match (if isFlipYaoAlias op then parseYao a else none) with
          | some yao => some (.flipYao yao, rest')
          | none =>
              if isNopAlias op then some (.nop, rest) else none
  | _ =>
      if isNopAlias op then some (.nop, rest) else none

/-- 解析单条指令。返回 (指令, 剩余 tokens)。结构匹配 13 主字。 -/
def parseInstr : List Tok → Option (YiInstr × List Tok)
  | .cjk "不动" :: rest => some (.nop, rest)
  | .cjk "互"   :: rest => some (.hu, rest)
  | .cjk "错"   :: rest => some (.cuo, rest)
  | .cjk "综"   :: rest => some (.zong, rest)
  | .cjk "易"   :: rest => some (.swap, rest)
  | .cjk "推"   :: rest => some (.push, rest)
  | .cjk "取"   :: rest => some (.pop, rest)
  | .cjk "终"   :: rest => some (.halt, rest)
  | .cjk "设时" :: .cjk s :: rest =>
      match parseShi s with
      | some shi => some (.setShi shi, rest)
      | none     => none
  | .cjk "翻爻" :: .cjk y :: rest =>
      match parseYao y with
      | some yao => some (.flipYao yao, rest)
      | none     => none
  | .cjk "比爻" :: .cjk yi :: .cjk yj :: .cjk "至" :: .cjk n :: rest =>
      match parseYao yi, parseYao yj, parseNumeral n with
      | some i, some j, some t => some (.branchYaoEq i j t, rest)
      | _, _, _ => none
  | .cjk "比时" :: .cjk s :: .cjk "至" :: .cjk n :: rest =>
      match parseShi s, parseNumeral n with
      | some shi, some t => some (.branchShiEq shi t, rest)
      | _, _ => none
  | .cjk "跳" :: .cjk "至" :: .cjk n :: rest =>
      match parseNumeral n with
      | some t => some (.jump t, rest)
      | none   => none
  | .cjk op :: rest => parseInstrAlias op rest
  | _ => none

/-- Fuel-bounded program parser. Public `parseProg` supplies `toks.length` fuel. -/
def parseProgFuel : Nat → List Tok → Option (List YiInstr)
  | 0, [] => some []
  | 0, _ => none
  | fuel + 1, toks =>
      match toks with
      | [] => some []
      | _ =>
          match parseInstr toks with
          | some (i, rest) =>
              match rest with
              | [] => some [i]
              | .sep :: [] => some [i]
              | .sep :: rs =>
                  match parseProgFuel fuel rs with
                  | some is => some (i :: is)
                  | none => none
              | _ => none
          | none => none

/-- 解析程序：连续指令以 sep 分隔，尾随 sep 可选。 -/
def parseProg (toks : List Tok) : Option (List YiInstr) :=
  parseProgFuel toks.length toks

/-- 顶层入口：String → Option (List YiInstr)。 -/
def «解程» (s : String) : Option (List YiInstr) :=
  (lex s).bind parseProg

example : «解程» "«静»" = some [.nop] := by native_decide
example : «解程» "«一»" = some [.nop] := by native_decide
example : «解程» "«置» «今»" = some [.setShi .jin] := by native_decide
example : «解程» "«翻» «三爻»" = some [.flipYao ⟨2, by omega⟩] := by native_decide
example :
    «解程» "«侔» «三爻» «四爻» «至» «三»" =
      some [.branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ 3] := by
  native_decide
example :
    «解程» "«会» «今» «至» «三»" =
      some [.branchShiEq .jin 3] := by
  native_decide

/-! ## § 5  Pretty-printer (印) -/

def digitChar : Nat → String
  | 1 => "一" | 2 => "二" | 3 => "三"
  | 4 => "四" | 5 => "五" | 6 => "六"
  | 7 => "七" | 8 => "八" | 9 => "九"
  | _ => "?"

def printNumeral (n : Nat) : String :=
  if n = 0 then "«?»"
  else if n ≤ 9 then "«" ++ digitChar n ++ "»"
  else if n = 10 then "«十»"
  else if n ≤ 19 then "«十" ++ digitChar (n - 10) ++ "»"
  else if n ≤ 64 then
    let t := n / 10
    let r := n % 10
    if r = 0 then "«" ++ digitChar t ++ "十»"
    else "«" ++ digitChar t ++ "十" ++ digitChar r ++ "»"
  else "«?»"

def printShi : Shi → String
  | .ji  => "«已»"
  | .jin => "«今»"
  | .wei => "«未»"

def printYao : Fin 6 → String
  | ⟨0, _⟩ => "«初爻»" | ⟨1, _⟩ => "«二爻»"
  | ⟨2, _⟩ => "«三爻»" | ⟨3, _⟩ => "«四爻»"
  | ⟨4, _⟩ => "«五爻»" | ⟨5, _⟩ => "«上爻»"
  | _ => "«?»"

def printInstr : YiInstr → String
  | .nop  => "«不动»"
  | .hu   => "«互»"
  | .cuo  => "«错»"
  | .zong => "«综»"
  | .swap => "«易»"
  | .push => "«推»"
  | .pop  => "«取»"
  | .halt => "«终»"
  | .setShi s    => "«设时» " ++ printShi s
  | .flipYao i   => "«翻爻» " ++ printYao i
  | .branchYaoEq i j t =>
      "«比爻» " ++ printYao i ++ " " ++ printYao j ++ " «至» " ++ printNumeral t
  | .branchShiEq s t =>
      "«比时» " ++ printShi s ++ " «至» " ++ printNumeral t
  | .jump t =>
      "«跳» «至» " ++ printNumeral t

def printProg : List YiInstr → String
  | []         => ""
  | [i]        => printInstr i
  | i :: rest  => printInstr i ++ "；" ++ printProg rest

/-- 顶层印：List YiInstr → String. -/
def «印程» : List YiInstr → String := printProg

/-! ## § 6  合度判定 (validity for round-trip) -/

/-- 一条指令之合度：Nat 参数（target / jump 跳）在 1..64 范围内。 -/
def validInstr : YiInstr → Bool
  | .branchYaoEq _ _ t => decide (1 ≤ t ∧ t ≤ 64)
  | .branchShiEq _ t   => decide (1 ≤ t ∧ t ≤ 64)
  | .jump t            => decide (1 ≤ t ∧ t ≤ 64)
  | .swap              => true
  | _ => true

/-- 整程合度：每条指令皆合度。 -/
def validProg (p : List YiInstr) : Bool := p.all validInstr

/-! ## § 7  具体范例：daoJudgeProg 之 round-trip -/

/-- daoJudgeProg 全程合度（target=3 ∈ 1..64）。 -/
theorem daoJudgeProg_valid : validProg daoJudgeProg = true := by native_decide

/-- daoJudgeProg 之印为预期文言串。 -/
theorem daoJudgeProg_print :
    «印程» daoJudgeProg
      = "«比爻» «三爻» «四爻» «至» «三»；«设时» «未»；«终»；«设时» «已»；«终»" := by
  native_decide

/-- daoJudgeProg 之印再解后等于自身（句法 round-trip）。 -/
theorem daoJudgeProg_roundtrip :
    «解程» («印程» daoJudgeProg) = some daoJudgeProg := by native_decide

/-! ## § 8  扩展 round-trip：所有 13 构造子 + 全 param 值 -/

/-- 13 构造子之代表（每构造子至少一例，含全部 6 爻位 / 3 时态 / 范围内 Nat 参数）。 -/
def allKindReprs : List YiInstr := [
  .nop,
  .hu, .cuo, .zong, .swap,
  .push, .pop,
  .halt,
  .setShi .ji, .setShi .jin, .setShi .wei,
  .flipYao ⟨0, by omega⟩, .flipYao ⟨1, by omega⟩, .flipYao ⟨2, by omega⟩,
  .flipYao ⟨3, by omega⟩, .flipYao ⟨4, by omega⟩, .flipYao ⟨5, by omega⟩,
  .branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩ 1,
  .branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ 64,
  .branchShiEq .ji 1,   .branchShiEq .jin 32, .branchShiEq .wei 64,
  .jump 1, .jump 10, .jump 32, .jump 64
]

/-- 13 构造子代表之单例 round-trip：每例 print 后 parse 回原指令. -/
theorem allKindReprs_singleton_roundtrip :
    allKindReprs.all (fun i => «解程» (printInstr i) = some [i]) = true := by
  native_decide

/-- 1..64 之中文数词在 jump 中之 round-trip（覆盖全数词范围）. -/
def numeralRange : List Nat := (List.range 64).map (· + 1)

/-- 所有合法爻位。用于穷尽合法单指令 universe。 -/
def yaoRange : List (Fin 6) := [
  ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
  ⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩
]

/-- 所有时态。用于穷尽合法单指令 universe。 -/
def shiRange : List Shi := [.ji, .jin, .wei]

/-- 所有合度单指令，共 2577 条。

构成：
  * 8 条无参指令
  * 3 条 `setShi`
  * 6 条 `flipYao`
  * 6 * 6 * 64 条 `branchYaoEq`
  * 3 * 64 条 `branchShiEq`
  * 64 条 `jump`
-/
def validInstrUniverse : List YiInstr :=
  [.nop, .hu, .cuo, .zong, .swap, .push, .pop, .halt]
  ++ shiRange.map .setShi
  ++ yaoRange.map .flipYao
  ++ (List.flatMap
        (fun i =>
          List.flatMap
            (fun j => numeralRange.map fun n => YiInstr.branchYaoEq i j n)
            yaoRange)
        yaoRange)
  ++ (List.flatMap
        (fun s => numeralRange.map fun n => YiInstr.branchShiEq s n)
        shiRange)
  ++ numeralRange.map YiInstr.jump

theorem validInstrUniverse_length :
    validInstrUniverse.length = 2577 := by native_decide

theorem validInstrUniverse_all_valid :
    validInstrUniverse.all validInstr = true := by native_decide

theorem validInstrUniverse_singleton_roundtrip :
    validInstrUniverse.all (fun i => «解程» (printInstr i) = some [i]) = true := by
  native_decide

/-- Boundary witness: target 0 prints as `«?»`, hence cannot parse back. -/
theorem jump_zero_print_not_roundtrip :
    «解程» (printInstr (.jump 0)) = none := by
  native_decide

/-- Boundary witness: target >64 prints as `«?»`, hence cannot parse back. -/
theorem jump_65_print_not_roundtrip :
    «解程» (printInstr (.jump 65)) = none := by
  native_decide

theorem numeralRange_jump_roundtrip :
    numeralRange.all (fun n =>
      «解程» (printInstr (.jump n)) = some [.jump n]) = true := by
  native_decide

theorem numeralRange_branchYaoEq_roundtrip :
    numeralRange.all (fun n =>
      «解程» (printInstr (.branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ n))
        = some [.branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ n]) = true := by
  native_decide

theorem numeralRange_branchShiEq_roundtrip :
    numeralRange.all (fun n =>
      «解程» (printInstr (.branchShiEq .wei n)) = some [.branchShiEq .wei n]) = true := by
  native_decide

/-- 多构造子组合程序之 round-trip 测试集. -/
def testPrograms : List (List YiInstr) := [
  daoJudgeProg,
  [.nop, .halt],
  [.push, .pop, .halt],
  [.hu, .cuo, .zong, .halt],
  [.flipYao ⟨0, by omega⟩, .flipYao ⟨5, by omega⟩, .halt],
  [.setShi .ji, .setShi .jin, .setShi .wei, .halt],
  [.branchYaoEq ⟨0, by omega⟩ ⟨1, by omega⟩ 5, .halt, .nop, .nop, .nop, .halt],
  [.jump 2, .halt, .nop, .halt],
  [.branchShiEq .ji 3, .setShi .wei, .halt, .setShi .ji, .halt]
]

theorem testPrograms_all_valid :
    testPrograms.all validProg = true := by native_decide

/-- **测试集 round-trip 主公示**：所有合度测试程序 print 后 parse 回原程序. -/
theorem testPrograms_roundtrip :
    testPrograms.all (fun p => «解程» («印程» p) = some p) = true := by native_decide

/-! ## § 9  完全一般之 round-trip 定理（v3 之事）

  形式: `∀ p, validProg p = true → «解程» («印程» p) = some p`

  证明思路（待 v3 实施）:
    · 引理 1: parseShi (printShi 之 inner) = some s   （case analysis on Shi）
    · 引理 2: parseYao (printYao 之 inner) = some i   （case analysis on Fin 6）
    · 引理 3: parseNumeral (printNumeral 之 inner) = some n  当 n ∈ [1, 64]
              （n ∈ [1,9] / n=10 / n ∈ [11,19] / n ∈ [20,60] (multiples) / n ∈ [21,64] 五例）
    · 引理 4: lex 之 concatenation: lex (s₁ ++ "；" ++ s₂) = lex s₁ ++ [.sep] ++ lex s₂
    · 引理 5: parseInstr 之 print-逆: 13 构造子各一证
    · 主定理: 由引理 4-5 + induction on List YiInstr

  当前以 native_decide 见证测试集（足覆盖 13 构造子 + 全 1..64 数词），
  足够实用；完全一般化留待 v3.
-/

end SSBX.Foundation.Wen.WenyanParser
