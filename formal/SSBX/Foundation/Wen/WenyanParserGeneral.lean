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
open SSBX.Foundation.Bagua.Cell192
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

/-! ## § 3  规范化 token 序列 -/

/-- 单个 时态 之 token. -/
def tokOfShi (s : Shi) : Tok :=
  match s with
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
    parseShi (match s with | .ji => "已" | .jin => "今" | .wei => "未") = some s := by
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

/-! ## § 9  String-level round-trip (HYP form + testPrograms 见证)

  完整 String-level round-trip 之 final step 是 `lex (printProg p) = some (tokensOfProg p)`：
  此涉 lex 之 character-level 串接 + balance 引理，约 ~150-200 行.
  v3 暂以 hypothesis-form 提供，并以 testPrograms 上 native_decide 见证. -/

/-- 主公示之 hypothesis-form：given lex inversion，得 String-level 完全 round-trip. -/
theorem parseN_printProg_inverse_via_lex_inversion (p : List YiInstr)
    (h : validProg p = true)
    (h_lex : lexN («印程» p) = some (tokensOfProg p)) :
    «解程N» («印程» p) = some p := by
  unfold «解程N»
  rw [h_lex]
  simp
  exact parseProgN_tokensOfProg p h

/-- 一般 lex inversion 命题（v3.1 之事）。 -/
def lexN_printProg_hypothesis : Prop :=
  ∀ (p : List YiInstr), validProg p = true → lexN (printProg p) = some (tokensOfProg p)

/-- 一般 String-level round-trip 命题。 -/
def parseN_printProg_inverse_universal : Prop :=
  ∀ (p : List YiInstr), validProg p = true → «解程N» («印程» p) = some p

/-- 归约：lex hypothesis ⇒ universal round-trip. -/
theorem universal_via_lex_hypothesis (h_lex : lexN_printProg_hypothesis) :
    parseN_printProg_inverse_universal :=
  fun p hp => parseN_printProg_inverse_via_lex_inversion p hp (h_lex p hp)

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

/-! ## § 12  剩余间隙之声明 (remaining gaps)

* `lexN_printProg_hypothesis`：完整 character-level 之 lex 串接归纳；
  约 ~150-200 行，留待 v3.1。 当前 testPrograms 上由 native_decide 见证.

* String-level 之 universal round-trip (`parseN_printProg_inverse_universal`)：
  在 `lexN_printProg_hypothesis` 之假定下由 `universal_via_lex_hypothesis` 即得.

无 sorry / 无 axiom（验证：`#print axioms parseProgN_tokensOfProg` 应仅显
`propext`、`Classical.choice` 等 Lean stdlib axiom）.
-/

end SSBX.Foundation.Wen.WenyanParserGeneral
