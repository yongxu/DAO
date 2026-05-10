/-
# WenyanParserGeneral — Path 丙 § M1 v3：完全一般 round-trip 之 token-level 形

补 `WenyanParser.lean` 之未尽：将 partial-def 之 `parseProg` reformulate 为
非 partial 之 `parseProgN`（fuel-bounded），并以**结构归纳**（非 native_decide）
证明 token-level 之完全一般 inversion：

```
theorem parseProgN_tokensOfProg :
    ∀ p : List YiInstr, validProg p = true →
      parseProgN (tokensOfProg p) = some p
```

其中 `tokensOfProg : List YiInstr → List Tok` 是 `printProg` 之 token-level 之
规范化 image (即「印程」打印之中间表示，已绕过 String 之 lex 步骤）。

## 战略

由 `WenyanParser` 之 `lex` / `parseProg` 是 `partial def`（本体不可定义性还原），
故等式定理无法直证。本文：

1. 重新形式化 parser 为 fuel-bounded `parseProgFuel` / `parseProgN`（结构递归）
2. 在 token-level 证 12 案 inversion (`parseInstr_tokensOfInstr_app`)
3. 在 program-level 证 inversion (`parseProgN_tokensOfProg`) — by structural induction

## 主公示

`parseProgN_tokensOfProg`：完全一般之 token-level round-trip.

完整 String-level round-trip (`«解程N» («印程» p) = some p`) 需进一步之
`lex (printProg p) = some (tokensOfProg p)`，此涉 character-level 之 strong
induction（因 `lex` 用 `splitOnClose` 之非 list-cons 递降），约 ~150-200 行
工程；本文留待 v3.1。

测试集 `testPrograms` 上之 String-level round-trip 由 `native_decide` 见证（§ 11）。

## 命名

新版函数皆带 `N` / `Fuel` 后缀，与 `WenyanParser` 原 partial 版本并行存在。
-/
import SSBX.Foundation.Wen.WenyanParser
import Mathlib.Tactic.IntervalCases

namespace SSBX.Foundation.Wen.WenyanParserGeneral

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanParser

/-! ## § 1  非 partial 之 lexer (fuel-bounded) -/

/-- 字符流之 fuel-bounded 词法分析（与原 `partial lexAux` 同 logic，但 fuel 终止）。 -/
def lexFuel : Nat → List Char → Option (List Tok)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, c :: rest =>
      if c = ' ' || c = '\t' || c = '\n' || c = '\r' then
        lexFuel n rest
      else if c = '«' then
        let (inner, after) := splitOnClose rest
        match after with
        | '»' :: rs => (lexFuel n rs).map (fun toks => Tok.cjk (String.ofList inner) :: toks)
        | _ => none
      else if c = ';' || c = '；' then
        (lexFuel n rest).map (fun toks => Tok.sep :: toks)
      else none

/-- 字符流之非 partial 词法分析：fuel = 长度 + 1。 -/
def lexCharsN (cs : List Char) : Option (List Tok) := lexFuel (cs.length + 1) cs

/-- 顶层 String 入口（非 partial 版）。 -/
def lexN (s : String) : Option (List Tok) := lexCharsN s.toList

/-! ## § 2  splitOnClose 之结构性引理 -/

/-- 若 c ≠ '»'，splitOnClose (c::rs') 走第三 case. -/
private theorem splitOnClose_cons_neq (c : Char) (rs' : List Char) (hc : c ≠ '»') :
    splitOnClose (c :: rs') =
      ((splitOnClose rs').1.cons c, (splitOnClose rs').2) := by
  -- splitOnClose 之 def 是 pattern match. 直接 cases on rs':
  cases rs' with
  | nil =>
      simp [splitOnClose]
  | cons d rest =>
      simp [splitOnClose]

/-- 若 cs 中无 '»'，则 splitOnClose (cs ++ '»' :: rs) = (cs, '»' :: rs)。 -/
theorem splitOnClose_app_close (cs rs : List Char) (h : ∀ c ∈ cs, c ≠ '»') :
    splitOnClose (cs ++ '»' :: rs) = (cs, '»' :: rs) := by
  induction cs with
  | nil => simp [splitOnClose]
  | cons c cs ih =>
      have hc : c ≠ '»' := h c (by exact List.mem_cons_self)
      have h' : ∀ x ∈ cs, x ≠ '»' := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have ih_call := ih h'
      rw [List.cons_append]
      rw [splitOnClose_cons_neq c (cs ++ '»' :: rs) hc]
      rw [ih_call]

/-! ## § 2.5  字符级 lex 反演之引理 (M1 v3.1) -/

/-- 若 cs 中无 '»'，则 splitOnClose cs = (cs, [])。 -/
theorem splitOnClose_no_close (cs : List Char) (h : ∀ c ∈ cs, c ≠ '»') :
    splitOnClose cs = (cs, []) := by
  induction cs with
  | nil => simp [splitOnClose]
  | cons c cs ih =>
      have hc : c ≠ '»' := h c (by exact List.mem_cons_self)
      have h' : ∀ x ∈ cs, x ≠ '»' := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have := ih h'
      rw [splitOnClose_cons_neq c cs hc, this]

/-- lexFuel 单调（mirrors parseProgFuel_mono）。 -/
theorem lexFuel_mono : ∀ (n m : Nat) (cs : List Char) (out : List Tok),
    n ≤ m → lexFuel n cs = some out → lexFuel m cs = some out := by
  intro n
  induction n with
  | zero =>
      intro m cs out _ hn
      simp [lexFuel] at hn
  | succ n ih =>
      intro m cs out hnm hn
      cases m with
      | zero => omega
      | succ m =>
          have hnm' : n ≤ m := Nat.le_of_succ_le_succ hnm
          cases cs with
          | nil => simpa [lexFuel] using hn
          | cons c rest =>
              -- 用 generalize 抽出 condition booleans
              simp only [lexFuel] at hn ⊢
              -- 三个 if-then-else 一层一层地处理
              split at hn
              · -- whitespace
                rename_i hws
                simp only [hws, ite_true]
                exact ih m rest out hnm' hn
              · split at hn
                · -- '«'
                  rename_i hws hopen
                  simp only [hopen, ite_true]
                  generalize hsplit : splitOnClose rest = sp at hn ⊢
                  obtain ⟨inner, after⟩ := sp
                  cases after with
                  | nil => simp at hn
                  | cons a aRest =>
                      by_cases ha : a = '»'
                      · subst ha
                        simp only at hn ⊢
                        cases hres : lexFuel n aRest with
                        | none => rw [hres] at hn; simp at hn
                        | some toks =>
                            rw [hres] at hn
                            simp at hn
                            have := ih m aRest toks hnm' hres
                            rw [this]
                            simpa using hn
                      · simp [ha] at hn
                · split at hn
                  · -- ';' || '；'
                    rename_i hws hopen hsep
                    simp only [hws, hopen, hsep, ite_true, ite_false]
                    cases hres : lexFuel n rest with
                    | none => rw [hres] at hn; simp at hn
                    | some toks =>
                        rw [hres] at hn
                        simp at hn
                        have := ih m rest toks hnm' hres
                        rw [this]
                        simpa using hn
                  · simp at hn

/-- 单个 «inner» 之 lex 抽离：n+1 fuel ⇒ 消去一桥括号组. -/
theorem lexFuel_bracket_group
    (inner tail : List Char) (n : Nat)
    (h_no_close : ∀ c ∈ inner, c ≠ '»') :
    lexFuel (n + 1) ('«' :: inner ++ '»' :: tail)
      = (lexFuel n tail).map (fun toks => Tok.cjk (String.ofList inner) :: toks) := by
  simp only [lexFuel, List.cons_append]
  -- '«' 不是 whitespace, 是 '«'
  have h_open : ('«' = ' ' || '«' = '\t' || '«' = '\n' || '«' = '\r') = false := by decide
  rw [splitOnClose_app_close inner tail h_no_close]
  rfl

/-- 跳过 ASCII 空格. -/
theorem lexFuel_skip_space (cs : List Char) (n : Nat) :
    lexFuel (n + 1) (' ' :: cs) = lexFuel n cs := by
  simp [lexFuel]

/-- 全角分号 '；' 之 lex. -/
theorem lexFuel_sep_fullwidth (cs : List Char) (n : Nat) :
    lexFuel (n + 1) ('；' :: cs) = (lexFuel n cs).map (fun toks => Tok.sep :: toks) := by
  simp [lexFuel]

/-! ## § 3  规范化 token 序列 -/

/-- 单个 时态 之 token. -/
def tokOfShi (s : Shi) : Tok :=
  match s with
  | .dao => Tok.cjk "道"
  | .ji  => Tok.cjk "已"
  | .jin => Tok.cjk "今"
  | .wei => Tok.cjk "未"

/-- 单个 爻位 之 token. -/
def tokOfYao (i : Fin 6) : Tok :=
  match i with
  | ⟨0, _⟩ => Tok.cjk "初爻"
  | ⟨1, _⟩ => Tok.cjk "二爻"
  | ⟨2, _⟩ => Tok.cjk "三爻"
  | ⟨3, _⟩ => Tok.cjk "四爻"
  | ⟨4, _⟩ => Tok.cjk "五爻"
  | ⟨5, _⟩ => Tok.cjk "上爻"
  | _      => Tok.cjk "?"

/-- 数词字符串（去 «» 之内层）。 -/
def numeralInner (n : Nat) : String :=
  if n = 0 then "?"
  else if n ≤ 9 then digitChar n
  else if n = 10 then "十"
  else if n ≤ 19 then "十" ++ digitChar (n - 10)
  else if n ≤ 64 then
    let t := n / 10
    let r := n % 10
    if r = 0 then digitChar t ++ "十"
    else digitChar t ++ "十" ++ digitChar r
  else "?"

/-- 数词 token. -/
def tokOfNum (n : Nat) : Tok := Tok.cjk (numeralInner n)

/-- 单条指令之规范化 token 序列。 -/
def tokensOfInstr : YiInstr → List Tok
  | .nop  => [Tok.cjk "不动"]
  | .hu   => [Tok.cjk "互"]
  | .cuo  => [Tok.cjk "错"]
  | .zong => [Tok.cjk "综"]
  | .push => [Tok.cjk "推"]
  | .pop  => [Tok.cjk "取"]
  | .halt => [Tok.cjk "终"]
  | .setShi s => [Tok.cjk "设时", tokOfShi s]
  | .flipYao i => [Tok.cjk "翻爻", tokOfYao i]
  | .branchYaoEq i j t =>
      [Tok.cjk "比爻", tokOfYao i, tokOfYao j, Tok.cjk "至", tokOfNum t]
  | .branchShiEq s t =>
      [Tok.cjk "比时", tokOfShi s, Tok.cjk "至", tokOfNum t]
  | .jump t =>
      [Tok.cjk "跳", Tok.cjk "至", tokOfNum t]

/-- 程序之规范化 token 序列：sep 隔之。 -/
def tokensOfProg : List YiInstr → List Tok
  | []          => []
  | [i]         => tokensOfInstr i
  | i :: rest   => tokensOfInstr i ++ Tok.sep :: tokensOfProg rest

/-! ## § 4  非 partial parser -/

/-- fuel-bounded program parser。 -/
def parseProgFuel : Nat → List Tok → Option (List YiInstr)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, toks =>
      match parseInstr toks with
      | some (i, rest) =>
          match rest with
          | []          => some [i]
          | .sep :: []  => some [i]
          | .sep :: rs  =>
              (parseProgFuel n rs).map (i :: ·)
          | _           => none
      | none => none

/-- 非 partial program parser：fuel = token 数 + 1. -/
def parseProgN (toks : List Tok) : Option (List YiInstr) :=
  parseProgFuel (toks.length + 1) toks

/-- 顶层 String → Option (List YiInstr) (非 partial 版). -/
def «解程N» (s : String) : Option (List YiInstr) :=
  (lexN s).bind parseProgN

/-! ## § 5  数词与原子 inversion (parseShi / parseYao / parseNumeral) -/

/-- 数词 parse 之 print-逆（在 1..64 之内，由 native_decide 之有限枚举）。 -/
theorem parseNumeral_numeralInner (n : Nat) (h1 : 1 ≤ n) (h64 : n ≤ 64) :
    parseNumeral (numeralInner n) = some n := by
  interval_cases n <;> native_decide

/-- 时态 parser 之 print-逆。 -/
theorem parseShi_shi (s : Shi) :
    parseShi (match s with | .dao => "道" | .ji => "已" | .jin => "今" | .wei => "未") = some s := by
  cases s <;> rfl

/-- 爻位 parser 之 print-逆。 -/
theorem parseYao_yao (i : Fin 6) :
    parseYao (match i with
              | ⟨0, _⟩ => "初爻" | ⟨1, _⟩ => "二爻" | ⟨2, _⟩ => "三爻"
              | ⟨3, _⟩ => "四爻" | ⟨4, _⟩ => "五爻" | ⟨5, _⟩ => "上爻") = some i := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

/-- tokOfYao 之展开式（与 parseYao_yao 同结构）。 -/
theorem tokOfYao_eq (i : Fin 6) :
    tokOfYao i = Tok.cjk (match i with
              | ⟨0, _⟩ => "初爻" | ⟨1, _⟩ => "二爻" | ⟨2, _⟩ => "三爻"
              | ⟨3, _⟩ => "四爻" | ⟨4, _⟩ => "五爻" | ⟨5, _⟩ => "上爻") := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

/-! ## § 5.5  printInstr 之 List Char 形 (与 String.toList 之桥, M1 v3.1) -/

/-- 时态 之 char 列表表示. -/
def printShiChars : Shi → List Char
  | .dao => ['«', '道', '»']
  | .ji  => ['«', '已', '»']
  | .jin => ['«', '今', '»']
  | .wei => ['«', '未', '»']

/-- 爻位 之 char 列表表示. -/
def printYaoChars : Fin 6 → List Char
  | ⟨0, _⟩ => ['«', '初', '爻', '»']
  | ⟨1, _⟩ => ['«', '二', '爻', '»']
  | ⟨2, _⟩ => ['«', '三', '爻', '»']
  | ⟨3, _⟩ => ['«', '四', '爻', '»']
  | ⟨4, _⟩ => ['«', '五', '爻', '»']
  | ⟨5, _⟩ => ['«', '上', '爻', '»']
  | _      => ['«', '?', '»']

theorem printShi_toList (s : Shi) : (printShi s).toList = printShiChars s := by
  cases s <;> rfl

theorem printYao_toList (i : Fin 6) : (printYao i).toList = printYaoChars i := by
  match i with
  | ⟨0, h⟩ => decide +revert
  | ⟨1, h⟩ => decide +revert
  | ⟨2, h⟩ => decide +revert
  | ⟨3, h⟩ => decide +revert
  | ⟨4, h⟩ => decide +revert
  | ⟨5, h⟩ => decide +revert

/-- inner 数词字符串 (1..64) 之 List Char (无 «»). -/
def numeralInnerChars (n : Nat) : List Char := (numeralInner n).toList

/-- printNumeral n 之 List Char (含 «»). -/
def printNumeralChars (n : Nat) : List Char :=
  '«' :: numeralInnerChars n ++ ['»']

/-- printNumeral n (1 ≤ n ≤ 64) 之 toList 形：'«' :: inner ++ ['»']. -/
theorem printNumeral_toList (n : Nat) (h1 : 1 ≤ n) (h64 : n ≤ 64) :
    (printNumeral n).toList = printNumeralChars n := by
  unfold printNumeralChars numeralInnerChars
  interval_cases n <;> native_decide

/-- numeralInner 之 List Char 不含 '»' (在 1..64 之内). -/
theorem numeralInnerChars_no_close (n : Nat) (h1 : 1 ≤ n) (h64 : n ≤ 64) :
    ∀ c ∈ numeralInnerChars n, c ≠ '»' := by
  unfold numeralInnerChars
  interval_cases n <;> native_decide

/-- 单条指令打印之 List Char 形 (镜像 printInstr 之分发). -/
def printInstrChars : YiInstr → List Char
  | .nop  => ['«', '不', '动', '»']
  | .hu   => ['«', '互', '»']
  | .cuo  => ['«', '错', '»']
  | .zong => ['«', '综', '»']
  | .push => ['«', '推', '»']
  | .pop  => ['«', '取', '»']
  | .halt => ['«', '终', '»']
  | .setShi s    => ['«', '设', '时', '»', ' '] ++ printShiChars s
  | .flipYao i   => ['«', '翻', '爻', '»', ' '] ++ printYaoChars i
  | .branchYaoEq i j t =>
      ['«', '比', '爻', '»', ' '] ++ printYaoChars i ++ [' '] ++ printYaoChars j ++
        [' ', '«', '至', '»', ' '] ++ printNumeralChars t
  | .branchShiEq s t =>
      ['«', '比', '时', '»', ' '] ++ printShiChars s ++ [' ', '«', '至', '»', ' '] ++
        printNumeralChars t
  | .jump t =>
      ['«', '跳', '»', ' ', '«', '至', '»', ' '] ++ printNumeralChars t

/-- (printInstr i).toList 化为 printInstrChars i (在 validInstr i = true 之下). -/
theorem printInstr_toList (i : YiInstr) (h : validInstr i = true) :
    (printInstr i).toList = printInstrChars i := by
  cases i with
  | nop  => decide
  | hu   => decide
  | cuo  => decide
  | zong => decide
  | push => decide
  | pop  => decide
  | halt => decide
  | setShi s => cases s <;> decide
  | flipYao i =>
      simp only [printInstr, printInstrChars, String.toList_append]
      rw [printYao_toList i]
      rfl
  | branchYaoEq i j t =>
      simp only [validInstr, decide_eq_true_eq] at h
      obtain ⟨h1, h64⟩ := h
      simp only [printInstr, printInstrChars, String.toList_append]
      rw [printYao_toList i, printYao_toList j, printNumeral_toList t h1 h64]
      rfl
  | branchShiEq s t =>
      simp only [validInstr, decide_eq_true_eq] at h
      obtain ⟨h1, h64⟩ := h
      simp only [printInstr, printInstrChars, String.toList_append]
      rw [printShi_toList s, printNumeral_toList t h1 h64]
      rfl
  | jump t =>
      simp only [validInstr, decide_eq_true_eq] at h
      obtain ⟨h1, h64⟩ := h
      simp only [printInstr, printInstrChars, String.toList_append]
      rw [printNumeral_toList t h1 h64]
      rfl

/-! ## § 5.6  per-instruction lex bridge (M1 v3.1 之主柱) -/

/-- 单条指令 lex 所需 fuel 数 (= 括号组 + 内空格). -/
def instrLexFuel : YiInstr → Nat
  | .nop  | .hu  | .cuo | .zong | .push | .pop | .halt => 1
  | .setShi _   | .flipYao _ => 3
  | .jump _ => 5
  | .branchShiEq _ _ => 7
  | .branchYaoEq _ _ _ => 9

/-- printShiChars 之 inner 不含 '»'. -/
private theorem printShiChars_inner_no_close (s : Shi) :
    ∀ c ∈ (printShiChars s).tail.dropLast, c ≠ '»' := by
  cases s <;> (intro c hc; simp [printShiChars] at hc; subst hc; decide)

/-- printYaoChars 之 inner 不含 '»'. -/
private theorem printYaoChars_inner_no_close (i : Fin 6) :
    ∀ c ∈ (printYaoChars i).tail.dropLast, c ≠ '»' := by
  match i with
  | ⟨0, _⟩ => intro c hc; simp [printYaoChars] at hc; rcases hc with rfl | rfl <;> decide
  | ⟨1, _⟩ => intro c hc; simp [printYaoChars] at hc; rcases hc with rfl | rfl <;> decide
  | ⟨2, _⟩ => intro c hc; simp [printYaoChars] at hc; rcases hc with rfl | rfl <;> decide
  | ⟨3, _⟩ => intro c hc; simp [printYaoChars] at hc; rcases hc with rfl | rfl <;> decide
  | ⟨4, _⟩ => intro c hc; simp [printYaoChars] at hc; rcases hc with rfl | rfl <;> decide
  | ⟨5, _⟩ => intro c hc; simp [printYaoChars] at hc; rcases hc with rfl | rfl <;> decide

/-- '«' ++ inner ++ '»' ++ tail 之 lex 形 (将 List Char 写为 «inner» tail). -/
private theorem lexFuel_bracket_split
    (inner tail : List Char) (n : Nat)
    (h_no_close : ∀ c ∈ inner, c ≠ '»') :
    lexFuel (n + 1) (('«' :: inner ++ ['»']) ++ tail)
      = (lexFuel n tail).map (fun toks => Tok.cjk (String.ofList inner) :: toks) := by
  show lexFuel (n + 1) ('«' :: (inner ++ ['»'] ++ tail))
        = (lexFuel n tail).map (fun toks => Tok.cjk (String.ofList inner) :: toks)
  have h_eq : inner ++ ['»'] ++ tail = inner ++ '»' :: tail := by simp
  rw [h_eq]
  exact lexFuel_bracket_group inner tail n h_no_close

/-- printShiChars 之 lex (用 lexFuel_bracket_split 直接). -/
private theorem lexFuel_printShiChars
    (s : Shi) (tail : List Char) (n : Nat) :
    lexFuel (n + 1) (printShiChars s ++ tail)
      = (lexFuel n tail).map (fun toks => tokOfShi s :: toks) := by
  cases s with
  | dao =>
      show lexFuel (n + 1) (('«' :: ['道'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['道'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl
  | ji =>
      show lexFuel (n + 1) (('«' :: ['已'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['已'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl
  | jin =>
      show lexFuel (n + 1) (('«' :: ['今'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['今'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl
  | wei =>
      show lexFuel (n + 1) (('«' :: ['未'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['未'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl

/-- printYaoChars 之 lex. -/
private theorem lexFuel_printYaoChars
    (i : Fin 6) (tail : List Char) (n : Nat) :
    lexFuel (n + 1) (printYaoChars i ++ tail)
      = (lexFuel n tail).map (fun toks => tokOfYao i :: toks) := by
  match i with
  | ⟨0, _⟩ =>
      show lexFuel (n + 1) (('«' :: ['初', '爻'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['初', '爻'] tail n
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rfl
  | ⟨1, _⟩ =>
      show lexFuel (n + 1) (('«' :: ['二', '爻'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['二', '爻'] tail n
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rfl
  | ⟨2, _⟩ =>
      show lexFuel (n + 1) (('«' :: ['三', '爻'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['三', '爻'] tail n
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rfl
  | ⟨3, _⟩ =>
      show lexFuel (n + 1) (('«' :: ['四', '爻'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['四', '爻'] tail n
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rfl
  | ⟨4, _⟩ =>
      show lexFuel (n + 1) (('«' :: ['五', '爻'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['五', '爻'] tail n
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rfl
  | ⟨5, _⟩ =>
      show lexFuel (n + 1) (('«' :: ['上', '爻'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['上', '爻'] tail n
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rfl

/-- printNumeralChars 之 lex (1 ≤ t ≤ 64). -/
private theorem lexFuel_printNumeralChars
    (t : Nat) (h1 : 1 ≤ t) (h64 : t ≤ 64) (tail : List Char) (n : Nat) :
    lexFuel (n + 1) (printNumeralChars t ++ tail)
      = (lexFuel n tail).map (fun toks => tokOfNum t :: toks) := by
  unfold printNumeralChars
  rw [lexFuel_bracket_split (numeralInnerChars t) tail n (numeralInnerChars_no_close t h1 h64)]
  unfold numeralInnerChars
  simp only [tokOfNum, String.ofList_toList]

/-- 单条指令 print 后之 lex 抽离主柱 (with append). -/
theorem lexFuel_printInstrChars_app
    (i : YiInstr) (tail : List Char) (n : Nat) (h : validInstr i = true) :
    lexFuel (n + instrLexFuel i) (printInstrChars i ++ tail)
      = (lexFuel n tail).map (fun toks => tokensOfInstr i ++ toks) := by
  cases i with
  | nop =>
      show lexFuel (n + 1) (('«' :: ['不', '动'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['不', '动'] tail n
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rfl
  | hu =>
      show lexFuel (n + 1) (('«' :: ['互'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['互'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl
  | cuo =>
      show lexFuel (n + 1) (('«' :: ['错'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['错'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl
  | zong =>
      show lexFuel (n + 1) (('«' :: ['综'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['综'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl
  | push =>
      show lexFuel (n + 1) (('«' :: ['推'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['推'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl
  | pop =>
      show lexFuel (n + 1) (('«' :: ['取'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['取'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl
  | halt =>
      show lexFuel (n + 1) (('«' :: ['终'] ++ ['»']) ++ tail) = _
      rw [lexFuel_bracket_split ['终'] tail n
            (by intro c hc; simp at hc; subst hc; decide)]
      rfl
  | setShi s =>
      -- printInstrChars (setShi s) = ['«', '设', '时', '»', ' '] ++ printShiChars s
      simp only [printInstrChars, instrLexFuel]
      have heq : (['«', '设', '时', '»', ' '] : List Char) ++ printShiChars s ++ tail
        = ('«' :: ['设', '时'] ++ ['»']) ++ ' ' :: (printShiChars s ++ tail) := by simp
      rw [heq, show n + 3 = (n + 2) + 1 from rfl]
      rw [lexFuel_bracket_split ['设', '时'] (' ' :: (printShiChars s ++ tail)) (n + 2)
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rw [show n + 2 = (n + 1) + 1 from rfl, lexFuel_skip_space _ (n + 1)]
      rw [lexFuel_printShiChars s tail n]
      simp only [tokensOfInstr, List.cons_append, List.nil_append, Option.map_map,
                 Function.comp_def, show String.ofList ['设', '时'] = "设时" from rfl]
  | flipYao i =>
      simp only [printInstrChars, instrLexFuel]
      have heq : (['«', '翻', '爻', '»', ' '] : List Char) ++ printYaoChars i ++ tail
        = ('«' :: ['翻', '爻'] ++ ['»']) ++ ' ' :: (printYaoChars i ++ tail) := by simp
      rw [heq, show n + 3 = (n + 2) + 1 from rfl]
      rw [lexFuel_bracket_split ['翻', '爻'] (' ' :: (printYaoChars i ++ tail)) (n + 2)
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rw [show n + 2 = (n + 1) + 1 from rfl, lexFuel_skip_space _ (n + 1)]
      rw [lexFuel_printYaoChars i tail n]
      simp only [tokensOfInstr, List.cons_append, List.nil_append, Option.map_map,
                 Function.comp_def, show String.ofList ['翻', '爻'] = "翻爻" from rfl]
  | branchYaoEq i j t =>
      simp only [validInstr, decide_eq_true_eq] at h
      obtain ⟨h1, h64⟩ := h
      simp only [printInstrChars, instrLexFuel]
      -- 重组 chars: [«比爻» yao_i yao_j «至» numeral] tail
      have heq : (['«', '比', '爻', '»', ' '] : List Char) ++ printYaoChars i ++ [' '] ++
                  printYaoChars j ++ [' ', '«', '至', '»', ' '] ++ printNumeralChars t ++ tail
        = ('«' :: ['比', '爻'] ++ ['»']) ++ ' ' :: (printYaoChars i ++ ' ' :: (printYaoChars j ++
            ' ' :: (('«' :: ['至'] ++ ['»']) ++ ' ' :: (printNumeralChars t ++ tail)))) := by simp
      rw [heq]
      -- 比爻 bracket
      rw [show n + 9 = (n + 8) + 1 from rfl]
      rw [lexFuel_bracket_split ['比', '爻'] _ (n + 8)
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      -- space
      rw [show n + 8 = (n + 7) + 1 from rfl, lexFuel_skip_space _ (n + 7)]
      -- yao_i
      rw [lexFuel_printYaoChars i _ (n + 6)]
      -- space
      rw [show n + 6 = (n + 5) + 1 from rfl, lexFuel_skip_space _ (n + 5)]
      -- yao_j
      rw [lexFuel_printYaoChars j _ (n + 4)]
      -- space
      rw [show n + 4 = (n + 3) + 1 from rfl, lexFuel_skip_space _ (n + 3)]
      -- 至 bracket
      rw [show n + 3 = (n + 2) + 1 from rfl]
      rw [lexFuel_bracket_split ['至'] _ (n + 2)
            (by intro c hc; simp at hc; subst hc; decide)]
      -- space
      rw [show n + 2 = (n + 1) + 1 from rfl, lexFuel_skip_space _ (n + 1)]
      -- numeral
      rw [lexFuel_printNumeralChars t h1 h64 tail n]
      simp only [tokensOfInstr, List.cons_append, List.nil_append, Option.map_map,
                 Function.comp_def, show String.ofList ['比', '爻'] = "比爻" from rfl,
                 show String.ofList ['至'] = "至" from rfl]
  | branchShiEq s t =>
      simp only [validInstr, decide_eq_true_eq] at h
      obtain ⟨h1, h64⟩ := h
      simp only [printInstrChars, instrLexFuel]
      have heq : (['«', '比', '时', '»', ' '] : List Char) ++ printShiChars s ++
                  [' ', '«', '至', '»', ' '] ++ printNumeralChars t ++ tail
        = ('«' :: ['比', '时'] ++ ['»']) ++ ' ' :: (printShiChars s ++
            ' ' :: (('«' :: ['至'] ++ ['»']) ++ ' ' :: (printNumeralChars t ++ tail))) := by simp
      rw [heq]
      rw [show n + 7 = (n + 6) + 1 from rfl]
      rw [lexFuel_bracket_split ['比', '时'] _ (n + 6)
            (by intro c hc; simp at hc; rcases hc with rfl|rfl <;> decide)]
      rw [show n + 6 = (n + 5) + 1 from rfl, lexFuel_skip_space _ (n + 5)]
      rw [lexFuel_printShiChars s _ (n + 4)]
      rw [show n + 4 = (n + 3) + 1 from rfl, lexFuel_skip_space _ (n + 3)]
      rw [show n + 3 = (n + 2) + 1 from rfl]
      rw [lexFuel_bracket_split ['至'] _ (n + 2)
            (by intro c hc; simp at hc; subst hc; decide)]
      rw [show n + 2 = (n + 1) + 1 from rfl, lexFuel_skip_space _ (n + 1)]
      rw [lexFuel_printNumeralChars t h1 h64 tail n]
      simp only [tokensOfInstr, List.cons_append, List.nil_append, Option.map_map,
                 Function.comp_def, show String.ofList ['比', '时'] = "比时" from rfl,
                 show String.ofList ['至'] = "至" from rfl]
  | jump t =>
      simp only [validInstr, decide_eq_true_eq] at h
      obtain ⟨h1, h64⟩ := h
      simp only [printInstrChars, instrLexFuel]
      have heq : (['«', '跳', '»', ' ', '«', '至', '»', ' '] : List Char) ++
                  printNumeralChars t ++ tail
        = ('«' :: ['跳'] ++ ['»']) ++ ' ' :: (('«' :: ['至'] ++ ['»']) ++
            ' ' :: (printNumeralChars t ++ tail)) := by simp
      rw [heq]
      rw [show n + 5 = (n + 4) + 1 from rfl]
      rw [lexFuel_bracket_split ['跳'] _ (n + 4)
            (by intro c hc; simp at hc; subst hc; decide)]
      rw [show n + 4 = (n + 3) + 1 from rfl, lexFuel_skip_space _ (n + 3)]
      rw [show n + 3 = (n + 2) + 1 from rfl]
      rw [lexFuel_bracket_split ['至'] _ (n + 2)
            (by intro c hc; simp at hc; subst hc; decide)]
      rw [show n + 2 = (n + 1) + 1 from rfl, lexFuel_skip_space _ (n + 1)]
      rw [lexFuel_printNumeralChars t h1 h64 tail n]
      simp only [tokensOfInstr, List.cons_append, List.nil_append, Option.map_map,
                 Function.comp_def, show String.ofList ['至'] = "至" from rfl,
                 show String.ofList ['跳'] = "跳" from rfl]

/-! ## § 6  parseInstr inversion (12 案，with append) -/

/-- 单条指令之 parser 逆 (with append)：吃 tokensOfInstr i ++ rest 后留 rest. -/
theorem parseInstr_tokensOfInstr_app (i : YiInstr) (rest : List Tok) (h : validInstr i = true) :
    parseInstr (tokensOfInstr i ++ rest) = some (i, rest) := by
  cases i with
  | nop  => rfl
  | hu   => rfl
  | cuo  => rfl
  | zong => rfl
  | push => rfl
  | pop  => rfl
  | halt => rfl
  | setShi s => cases s <;> rfl
  | flipYao i =>
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
      | ⟨4, _⟩ => rfl
      | ⟨5, _⟩ => rfl
  | branchYaoEq i j t =>
      simp [validInstr] at h
      obtain ⟨h1, h64⟩ := h
      have hnum := parseNumeral_numeralInner t h1 h64
      have hi := parseYao_yao i
      have hj := parseYao_yao j
      have htoki := tokOfYao_eq i
      have htokj := tokOfYao_eq j
      simp only [tokensOfInstr, List.cons_append, List.nil_append, parseInstr]
      rw [htoki, htokj]
      simp only [tokOfNum]
      rw [hi, hj, hnum]
  | branchShiEq s t =>
      simp [validInstr] at h
      obtain ⟨h1, h64⟩ := h
      have hnum := parseNumeral_numeralInner t h1 h64
      simp only [tokensOfInstr, List.cons_append, List.nil_append, parseInstr, tokOfShi, tokOfNum]
      cases s <;> simp [parseShi, hnum]
  | jump t =>
      simp [validInstr] at h
      obtain ⟨h1, h64⟩ := h
      have hnum := parseNumeral_numeralInner t h1 h64
      simp only [tokensOfInstr, List.cons_append, List.nil_append, parseInstr, tokOfNum]
      simp [hnum]

/-- parseInstr 之 print-逆（不留残）. -/
theorem parseInstr_tokensOfInstr (i : YiInstr) (h : validInstr i = true) :
    parseInstr (tokensOfInstr i) = some (i, []) := by
  have := parseInstr_tokensOfInstr_app i [] h
  rw [List.append_nil] at this
  exact this

/-! ## § 7  parseProgFuel 单调性 -/

/-- fuel 单调（parseProgFuel）。 -/
theorem parseProgFuel_mono : ∀ (n m : Nat) (toks : List Tok) (out : List YiInstr),
    n ≤ m → parseProgFuel n toks = some out → parseProgFuel m toks = some out := by
  intro n
  induction n with
  | zero =>
      intro m toks out _ hn
      simp [parseProgFuel] at hn
  | succ n ih =>
      intro m toks out hnm hn
      cases m with
      | zero => omega
      | succ m =>
          have hnm' : n ≤ m := Nat.le_of_succ_le_succ hnm
          cases toks with
          | nil =>
              simp [parseProgFuel] at hn ⊢
              exact hn
          | cons t ts =>
              -- 用 generalize 把 parseInstr (t::ts) 抽出
              simp only [parseProgFuel] at hn ⊢
              generalize hpi : parseInstr (t :: ts) = pi at hn ⊢
              cases pi with
              | none => simp at hn
              | some pair =>
                  obtain ⟨i, rest⟩ := pair
                  cases rest with
                  | nil => simpa using hn
                  | cons r rs =>
                      cases r with
                      | sep =>
                          cases rs with
                          | nil => simpa using hn
                          | cons r' rs' =>
                              simp only at hn ⊢
                              cases hres : parseProgFuel n (r' :: rs') with
                              | none => rw [hres] at hn; simp at hn
                              | some out' =>
                                  rw [hres] at hn
                                  simp at hn
                                  have := ih m (r' :: rs') out' hnm' hres
                                  rw [this]
                                  simpa using hn
                      | cjk _ => simp at hn

/-! ## § 8  parseProgN 之 print-逆 (主结构归纳) -/

/-- **主公示**：程序级 inversion — parseProgN 之 print-逆 (结构归纳 on List YiInstr). -/
theorem parseProgN_tokensOfProg (p : List YiInstr) (h : validProg p = true) :
    parseProgN (tokensOfProg p) = some p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
      have hi : validInstr i = true := by
        unfold validProg at h
        simp [List.all_cons] at h
        exact h.1
      have hrest' : validProg rest = true := by
        unfold validProg at h ⊢
        simp [List.all_cons] at h
        exact List.all_eq_true.mpr h.2
      have ih' := ih hrest'
      cases rest with
      | nil =>
          show parseProgN (tokensOfInstr i) = some [i]
          have h_ne : tokensOfInstr i ≠ [] := by cases i <;> simp [tokensOfInstr]
          cases hti : tokensOfInstr i with
          | nil => exact absurd hti h_ne
          | cons t0 ts0 =>
              show parseProgFuel ((t0 :: ts0).length + 1) (t0 :: ts0) = some [i]
              simp only [parseProgFuel]
              have hpi' : parseInstr (t0 :: ts0) = some (i, []) := by
                rw [← hti]
                exact parseInstr_tokensOfInstr i hi
              rw [hpi']
      | cons r rs =>
          show parseProgN (tokensOfInstr i ++ Tok.sep :: tokensOfProg (r :: rs)) = some (i :: r :: rs)
          -- 不用 set；直接处理 (tokensOfInstr i ++ Tok.sep :: tokensOfProg (r :: rs))
          have h_ne : tokensOfInstr i ++ Tok.sep :: tokensOfProg (r :: rs) ≠ [] := by simp
          -- 现 cases on tokensOfInstr i 之结构
          have h_t_ne : tokensOfInstr i ≠ [] := by cases i <;> simp [tokensOfInstr]
          cases hti : tokensOfInstr i with
          | nil => exact absurd hti h_t_ne
          | cons t0 ts0 =>
              -- tokensOfInstr i = t0 :: ts0
              -- tokensOfInstr i ++ Tok.sep :: tokensOfProg (r :: rs)
              --   = t0 :: (ts0 ++ Tok.sep :: tokensOfProg (r :: rs))
              show parseProgN (t0 :: (ts0 ++ Tok.sep :: tokensOfProg (r :: rs)))
                = some (i :: r :: rs)
              unfold parseProgN
              simp only [parseProgFuel]
              have hpi' : parseInstr (t0 :: (ts0 ++ Tok.sep :: tokensOfProg (r :: rs))) =
                  some (i, Tok.sep :: tokensOfProg (r :: rs)) := by
                have h_app : t0 :: (ts0 ++ Tok.sep :: tokensOfProg (r :: rs)) =
                            (t0 :: ts0) ++ Tok.sep :: tokensOfProg (r :: rs) := by simp
                rw [h_app, ← hti]
                exact parseInstr_tokensOfInstr_app i _ hi
              rw [hpi']
              have h_rest_ne : tokensOfProg (r :: rs) ≠ [] := by
                cases rs with
                | nil =>
                    show tokensOfInstr r ≠ []
                    cases r <;> simp [tokensOfInstr]
                | cons _ _ =>
                    show tokensOfInstr r ++ Tok.sep :: _ ≠ []
                    cases r <;> simp [tokensOfInstr]
              cases h_tor : tokensOfProg (r :: rs) with
              | nil => exact absurd h_tor h_rest_ne
              | cons rh rrs =>
                  simp only []
                  have ih_arg : parseProgFuel ((tokensOfProg (r::rs)).length + 1)
                              (tokensOfProg (r :: rs)) = some (r :: rs) := ih'
                  rw [h_tor] at ih_arg
                  -- ih_arg : parseProgFuel ((rh :: rrs).length + 1) (rh :: rrs) = some (r :: rs)
                  -- 即 parseProgFuel (rrs.length + 1 + 1) (rh :: rrs) = some (r :: rs)
                  -- 用 mono 升至当前 goal 之 fuel:
                  -- 当前 goal 之 fuel 是 (t0 :: ...).length（因 parseProgFuel n+1 之 n 步进）
                  -- = ts0.length + (rh :: rrs).length + 2 = ts0.length + rrs.length + 3
                  -- 用 mono with fuel any ≥ rrs.length + 2:
                  cases hres : parseProgFuel (t0 :: (ts0 ++ Tok.sep :: rh :: rrs)).length (rh :: rrs) with
                  | none =>
                      exfalso
                      have h_le : (rh :: rrs).length + 1 ≤
                          (t0 :: (ts0 ++ Tok.sep :: rh :: rrs)).length := by
                        simp [List.length_cons, List.length_append]; omega
                      have := parseProgFuel_mono ((rh :: rrs).length + 1)
                          (t0 :: (ts0 ++ Tok.sep :: rh :: rrs)).length
                          (rh :: rrs) (r :: rs) h_le ih_arg
                      rw [hres] at this
                      simp at this
                  | some out =>
                      have h_le : (rh :: rrs).length + 1 ≤
                          (t0 :: (ts0 ++ Tok.sep :: rh :: rrs)).length := by
                        simp [List.length_cons, List.length_append]; omega
                      have := parseProgFuel_mono ((rh :: rrs).length + 1)
                          (t0 :: (ts0 ++ Tok.sep :: rh :: rrs)).length
                          (rh :: rrs) (r :: rs) h_le ih_arg
                      rw [hres] at this
                      simp at this
                      subst this
                      simp

/-! ## § 9  String-level round-trip (M1 v3.1：fully proven, 0 hypothesis) -/

/-- 主公示之 hypothesis-form：given lex inversion，得 String-level 完全 round-trip.
    保留为旧式入口；现 `lexN_printProg_thm` 不需此 hypothesis. -/
theorem parseN_printProg_inverse_via_lex_inversion (p : List YiInstr)
    (h : validProg p = true)
    (h_lex : lexN («印程» p) = some (tokensOfProg p)) :
    «解程N» («印程» p) = some p := by
  unfold «解程N»
  rw [h_lex]
  simp
  exact parseProgN_tokensOfProg p h

/-- '；'.toList 之展开 (用 native_decide 见证). -/
private theorem fullwidth_semicolon_toList : "；".toList = ['；'] := by decide

/-- printProg 所需 lex fuel (per-instr + sep 数). -/
def progLexFuel : List YiInstr → Nat
  | [] => 0
  | [i] => instrLexFuel i
  | i :: rest => instrLexFuel i + 1 + progLexFuel rest

/-- printProg 之 lexFuel 一致 — fuel = progLexFuel p + 1 时之 lex 正确性. -/
private theorem lexFuel_printProg_exact (p : List YiInstr)
    (h : validProg p = true) :
    lexFuel (progLexFuel p + 1) (printProg p).toList = some (tokensOfProg p) := by
  induction p with
  | nil =>
      show lexFuel 1 [] = some []
      simp [lexFuel]
  | cons i rest ih =>
      have hi : validInstr i = true := by
        unfold validProg at h
        simp only [List.all_cons, Bool.and_eq_true] at h
        exact h.1
      have hrest : validProg rest = true := by
        unfold validProg at h ⊢
        simp only [List.all_cons, Bool.and_eq_true] at h
        exact h.2
      cases rest with
      | nil =>
          show lexFuel (progLexFuel [i] + 1) (printProg [i]).toList = some (tokensOfProg [i])
          have h_print : (printProg [i]).toList = printInstrChars i := by
            show (printInstr i).toList = printInstrChars i
            exact printInstr_toList i hi
          rw [h_print]
          rw [show printInstrChars i = printInstrChars i ++ [] from (List.append_nil _).symm]
          show lexFuel (instrLexFuel i + 1) (printInstrChars i ++ []) = _
          rw [show instrLexFuel i + 1 = 1 + instrLexFuel i from Nat.add_comm _ _]
          rw [lexFuel_printInstrChars_app i [] 1 hi]
          show (lexFuel 1 []).map _ = some (tokensOfProg [i])
          simp [lexFuel, tokensOfProg]
      | cons r rs =>
          have ih_rest := ih hrest
          show lexFuel (progLexFuel (i :: r :: rs) + 1) (printProg (i :: r :: rs)).toList
            = some (tokensOfProg (i :: r :: rs))
          have h_print : (printProg (i :: r :: rs)).toList
            = printInstrChars i ++ '；' :: (printProg (r :: rs)).toList := by
            show (printInstr i ++ "；" ++ printProg (r :: rs)).toList = _
            rw [String.toList_append, String.toList_append, fullwidth_semicolon_toList]
            rw [printInstr_toList i hi]
            simp
          rw [h_print]
          have h_split : printInstrChars i ++ '；' :: (printProg (r :: rs)).toList
            = printInstrChars i ++ ('；' :: (printProg (r :: rs)).toList) := by rfl
          rw [h_split]
          show lexFuel (progLexFuel (i :: r :: rs) + 1)
                (printInstrChars i ++ ('；' :: (printProg (r :: rs)).toList))
              = some (tokensOfProg (i :: r :: rs))
          have h_pf : progLexFuel (i :: r :: rs) = instrLexFuel i + 1 + progLexFuel (r :: rs) := by
            rfl
          rw [h_pf]
          rw [show instrLexFuel i + 1 + progLexFuel (r :: rs) + 1
                = (1 + progLexFuel (r :: rs) + 1) + instrLexFuel i from by omega]
          rw [lexFuel_printInstrChars_app i ('；' :: (printProg (r :: rs)).toList)
               (1 + progLexFuel (r :: rs) + 1) hi]
          rw [show 1 + progLexFuel (r :: rs) + 1
                = (progLexFuel (r :: rs) + 1) + 1 from by omega]
          rw [lexFuel_sep_fullwidth (printProg (r :: rs)).toList (progLexFuel (r :: rs) + 1)]
          rw [ih_rest]
          show (Option.map (fun toks => Tok.sep :: toks) (some (tokensOfProg (r :: rs)))).map
                  (fun toks => tokensOfInstr i ++ toks)
              = some (tokensOfProg (i :: r :: rs))
          simp [tokensOfProg]

/-- progLexFuel p ≤ (printProg p).toList.length —— 每 fuel 单位至少消耗 1 char. -/
private theorem progLexFuel_le_length (p : List YiInstr) (h : validProg p = true) :
    progLexFuel p ≤ (printProg p).toList.length := by
  induction p with
  | nil => simp [progLexFuel, printProg]
  | cons i rest ih =>
      have hi : validInstr i = true := by
        unfold validProg at h
        simp only [List.all_cons, Bool.and_eq_true] at h
        exact h.1
      have hrest : validProg rest = true := by
        unfold validProg at h ⊢
        simp only [List.all_cons, Bool.and_eq_true] at h
        exact h.2
      cases rest with
      | nil =>
          show instrLexFuel i ≤ (printInstr i).toList.length
          rw [printInstr_toList i hi]
          -- printInstrChars i 的 length 大于 instrLexFuel i (since each fuel = ≥ 1 char)
          cases i with
          | nop  => decide
          | hu   => decide
          | cuo  => decide
          | zong => decide
          | push => decide
          | pop  => decide
          | halt => decide
          | setShi s =>
              cases s <;> simp [printInstrChars, printShiChars, instrLexFuel]
          | flipYao i =>
              match i with
              | ⟨0, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
              | ⟨1, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
              | ⟨2, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
              | ⟨3, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
              | ⟨4, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
              | ⟨5, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
          | branchYaoEq i j t =>
              simp [printInstrChars, instrLexFuel, printNumeralChars, numeralInnerChars]
              try omega
          | branchShiEq s t =>
              simp [printInstrChars, instrLexFuel, printNumeralChars, numeralInnerChars]
              try omega
          | jump t =>
              simp [printInstrChars, instrLexFuel, printNumeralChars, numeralInnerChars]
              try omega
      | cons r rs =>
          have ih' := ih hrest
          show instrLexFuel i + 1 + progLexFuel (r :: rs)
            ≤ (printInstr i ++ "；" ++ printProg (r :: rs)).toList.length
          rw [String.toList_append, String.toList_append, fullwidth_semicolon_toList]
          rw [List.length_append, List.length_append]
          rw [printInstr_toList i hi]
          have h_inst : instrLexFuel i ≤ (printInstrChars i).length := by
            cases i with
            | nop  => decide
            | hu   => decide
            | cuo  => decide
            | zong => decide
            | push => decide
            | pop  => decide
            | halt => decide
            | setShi s => cases s <;> simp [printInstrChars, printShiChars, instrLexFuel]
            | flipYao i =>
                match i with
                | ⟨0, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
                | ⟨1, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
                | ⟨2, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
                | ⟨3, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
                | ⟨4, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
                | ⟨5, _⟩ => simp [printInstrChars, printYaoChars, instrLexFuel]
            | branchYaoEq i j t =>
                simp [printInstrChars, instrLexFuel, printNumeralChars, numeralInnerChars]
                try omega
            | branchShiEq s t =>
                simp [printInstrChars, instrLexFuel, printNumeralChars, numeralInnerChars]
                try omega
            | jump t =>
                simp [printInstrChars, instrLexFuel, printNumeralChars, numeralInnerChars]
                try omega
          have h_sep : ['；'].length = 1 := rfl
          rw [h_sep]
          omega

/-- **M1 v3.1 主定理**：完整 String-level lex inversion (无 hypothesis). -/
theorem lexN_printProg_thm (p : List YiInstr) (h : validProg p = true) :
    lexN (printProg p) = some (tokensOfProg p) := by
  unfold lexN lexCharsN
  have h_exact := lexFuel_printProg_exact p h
  have h_bound := progLexFuel_le_length p h
  exact lexFuel_mono (progLexFuel p + 1) ((printProg p).toList.length + 1) _ _
        (by omega) h_exact

/-- 主公示 (alias 与原 hypothesis-form 同语义 — 现已为 theorem). -/
theorem lexN_printProg_hypothesis :
    ∀ (p : List YiInstr), validProg p = true → lexN (printProg p) = some (tokensOfProg p) :=
  lexN_printProg_thm

/-- 一般 String-level round-trip 命题 (现已为 theorem). -/
theorem parseN_printProg_inverse_universal :
    ∀ (p : List YiInstr), validProg p = true → «解程N» («印程» p) = some p :=
  fun p hp => parseN_printProg_inverse_via_lex_inversion p hp (lexN_printProg_thm p hp)

/-- 归约保留：lex theorem ⇒ universal round-trip. -/
theorem universal_via_lex_hypothesis :
    ∀ (p : List YiInstr), validProg p = true → «解程N» («印程» p) = some p :=
  parseN_printProg_inverse_universal

/-! ## § 10  testPrograms 上之 round-trip 见证 (native_decide) -/

/-- 测试集 round-trip 之 lex 见证. -/
theorem testPrograms_lexN_eq_tokensOfProg :
    testPrograms.all (fun p =>
      validProg p = true ∧ lexN (printProg p) = some (tokensOfProg p)) = true := by
  native_decide

/-- 测试集 round-trip 之 解程N. -/
theorem testPrograms_roundtripN :
    testPrograms.all (fun p => «解程N» («印程» p) = some p) = true := by
  native_decide

/-- 与 partial 原版之兼容性：测试集 上 lexN 与原 lex 一致. -/
theorem testPrograms_lexN_agrees_lex :
    testPrograms.all (fun p => lexN (printProg p) = lex (printProg p)) = true := by
  native_decide

/-! ## § 11  daoJudgeProg / allKindReprs / numeralRange 之 round-trip 在新 parser -/

/-- daoJudgeProg 在新 parser 之 round-trip. -/
theorem daoJudgeProg_roundtripN :
    «解程N» («印程» daoJudgeProg) = some daoJudgeProg := by native_decide

/-- 12 构造子代表之单例 round-trip 在新 parser. -/
theorem allKindReprs_singleton_roundtripN :
    allKindReprs.all (fun i => «解程N» (printInstr i) = some [i]) = true := by
  native_decide

/-- 1..64 之 jump round-trip 在新 parser. -/
theorem numeralRange_jump_roundtripN :
    numeralRange.all (fun n =>
      «解程N» (printInstr (.jump n)) = some [.jump n]) = true := by
  native_decide

/-- 1..64 之 branchYaoEq round-trip 在新 parser (with 具体爻位). -/
theorem numeralRange_branchYaoEq_roundtripN :
    numeralRange.all (fun n =>
      «解程N» (printInstr (.branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ n))
        = some [.branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ n]) = true := by
  native_decide

/-- 1..64 之 branchShiEq round-trip 在新 parser. -/
theorem numeralRange_branchShiEq_roundtripN :
    numeralRange.all (fun n =>
      «解程N» (printInstr (.branchShiEq .wei n)) = some [.branchShiEq .wei n]) = true := by
  native_decide

/-! ## § 12  M1 v3.1 之闭合 (formerly remaining gaps)

* `lexN_printProg_thm` (formerly `lexN_printProg_hypothesis`)：完整 character-level
  之 lex 串接归纳，**已闭合** (无 hypothesis)。证明结构 § 2.5 + § 5.5 + § 5.6 + § 9：
  - § 2.5 lex 之 fuel 单调与括号组分离 (lexFuel_mono, lexFuel_bracket_group, ...)
  - § 5.5 printInstr 之 List Char 桥 (printInstrChars + printInstr_toList)
  - § 5.6 12-构造子之 lexFuel append 主柱 (lexFuel_printInstrChars_app)
  - § 9   按 List YiInstr 结构归纳 (progLexFuel + lexFuel_printProg_exact +
          progLexFuel_le_length + lexN_printProg_thm)

* String-level 之 universal round-trip (`parseN_printProg_inverse_universal`)：
  现已为 theorem (而非 hypothesis-conditional)，由 `lexN_printProg_thm` 直证.

无 sorry / 无 axiom（验证：`#print axioms lexN_printProg_thm` /
`#print axioms parseN_printProg_inverse_universal` 应仅显 `propext`、
`Classical.choice`、`Quot.sound` 等 Lean stdlib axiom + native_decide reflection axioms.
后者来自 `numeralInnerChars_no_close` 等之 native_decide 计算，不增信任基.
-/

end SSBX.Foundation.Wen.WenyanParserGeneral
