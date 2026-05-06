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
命     ::= «不动» | «互» | «错» | «综» | «推» | «取» | «终»
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
- `lex` / `parseProg` 用 `partial def`（«»分支递归长度非平凡递降）
- 关键 round-trip 由 `native_decide` 在具体程序上见证
- 一般性 `parse_print` 定理留待 v2（需结构归纳框架）
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

/-- 字符流之词法分析。返回 none 表示非法输入（未闭 «、未识别字符等）。 -/
partial def lexAux : List Char → Option (List Tok)
  | [] => some []
  | c :: rest =>
      if c = ' ' || c = '\t' || c = '\n' || c = '\r' then
        lexAux rest
      else if c = '«' then
        let (inner, after) := splitOnClose rest
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

/-- 解析单条指令。返回 (指令, 剩余 tokens)。结构匹配 12 主字。 -/
def parseInstr : List Tok → Option (YiInstr × List Tok)
  | .cjk "不动" :: rest => some (.nop, rest)
  | .cjk "互"   :: rest => some (.hu, rest)
  | .cjk "错"   :: rest => some (.cuo, rest)
  | .cjk "综"   :: rest => some (.zong, rest)
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
  | _ => none

/-- 解析程序：连续指令以 sep 分隔，尾随 sep 可选。 -/
partial def parseProg : List Tok → Option (List YiInstr) := fun toks =>
  match toks with
  | []     => some []
  | _      =>
      match parseInstr toks with
      | some (i, rest) =>
          match rest with
          | []          => some [i]
          | .sep :: []  => some [i]
          | .sep :: rs  =>
              match parseProg rs with
              | some is => some (i :: is)
              | none    => none
          | _           => none
      | none => none

/-- 顶层入口：String → Option (List YiInstr)。 -/
def «解程» (s : String) : Option (List YiInstr) :=
  (lex s).bind parseProg

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

end SSBX.Foundation.Wen.WenyanParser
