/-
# DaoJudge — 解释器 + 道判机 closed within 128 cells

A self-closed language: the alphabet, the operators, and the result space
are all the same 128-cell carrier (R7 = Hexagram × YinBit = (Z/2)⁷).

## Surface

- **字 (atom)**: a 7-character ASCII string of `o`/`x`. First 6 chars =
  hexagram yao positions (`o` = yang = 0, `x` = yin = 1, matching the
  OXNotation convention from R8). The 7th char = YinBit (`o` = 无 =
  false, `x` = 有 = true).
  - `ooooooo` = (heaven, false) = 乾·无 = origin = 道
  - `xxxxxxx` = (earth, true)  = 坤·有 = the antipode

- **句 (sentence)**: `(A B)` where A and B are programs. Reduction:
  evaluate A and B to cells, return `A ⊕ B` (R7 XOR). No other
  keywords. **The operator IS a cell** (Cayley fusion: cell-as-yuan ≡
  cell-as-yao).

A program is therefore a binary tree of cell atoms. Its value is the XOR
of all leaves with multiplicities mod 2.

## 道判机 (DaoJudge)

`isDao : Sexp → Bool` evaluates the program and returns `true` iff the
value equals origin. Since the language is just the abelian group (Z/2)⁷,
"is 道" reduces to: do all 7 bit positions have even total leaf
occurrence?

## What this demo is showing

1. The language is genuinely closed: every term in the AST is one of the
   128 cells; the only operator is application; application IS XOR.
2. Truth-as-道 is decidable in finite time (just XOR the leaves).
3. The yao/yuan duality is operationally witnessed: `(A B)` reads A as a
   value and as an operator simultaneously without distinction.
-/

import SSBX.Foundation.Lang.Sexp
import SSBX.Foundation.Lang.Names
import SSBX.Foundation.Bagua.R7
import SSBX.Foundation.Yi.Yi

namespace SSBX.Foundation.Lang.DaoJudge

open SSBX.Foundation.Yi.Yi (Yao Hexagram)
open SSBX.Foundation.Bagua.R7

/-! ## § 1  Atom parser: 7-char `o/x` string ↔ R7 -/

private def parseYao : Char → Option Yao
  | 'o' => some Yao.yang
  | 'x' => some Yao.yin
  | _   => none

private def parseBool : Char → Option Bool
  | 'o' => some false
  | 'x' => some true
  | _   => none

/-- Parse a 7-char `o/x` string to R7. Returns `none` on bad input. -/
def parseCellAtom (s : String) : Option R7 :=
  match s.toList with
  | [c1, c2, c3, c4, c5, c6, c7] => do
      let y1 ← parseYao c1
      let y2 ← parseYao c2
      let y3 ← parseYao c3
      let y4 ← parseYao c4
      let y5 ← parseYao c5
      let y6 ← parseYao c6
      let yb ← parseBool c7
      pure ((⟨y1, y2, y3, y4, y5, y6⟩ : Hexagram), yb)
  | _ => none

private def yaoChar : Yao → Char
  | .yang => 'o'
  | .yin  => 'x'

/-- Pretty-print a R7 as the canonical 7-char `o/x` atom. -/
def printCellAtom : R7 → String
  | (⟨y1, y2, y3, y4, y5, y6⟩, yb) =>
      String.ofList
        [yaoChar y1, yaoChar y2, yaoChar y3, yaoChar y4,
         yaoChar y5, yaoChar y6, if yb then 'x' else 'o']

example : parseCellAtom "ooooooo" = some R7.origin := by native_decide
example : printCellAtom R7.origin = "ooooooo" := by native_decide

/-! ## § 1.5  Chinese-name parser

A second atom form, `<卦名>·<因>`, e.g. `乾·无` / `既济·有`. Parses via
`Hexagram.fromName` and the standard {无/有} YinBit suffix. Both forms
are accepted by the unified `parseCell` below.
-/

/-- Parse a Chinese-named cell atom of the form `<卦名>·<因>`. -/
def parseChineseAtom (s : String) : Option R7 :=
  match s.splitOn "·" with
  | [hexName, yinName] =>
      match SSBX.Foundation.Yi.Yi.Hexagram.fromName hexName, yinName with
      | some h, "无" => some (h, false)
      | some h, "有" => some (h, true)
      | _, _         => none
  | _ => none

example : parseChineseAtom "乾·无" = some R7.origin := by native_decide
example : parseChineseAtom "既济·有" =
    some (SSBX.Foundation.Yi.Yi.Hexagram.complete, true) := by native_decide
example : parseChineseAtom "未济·无" =
    some (SSBX.Foundation.Yi.Yi.Hexagram.incomplete, false) := by native_decide
example : parseChineseAtom "不存在·有" = none := by native_decide

/-- Unified atom parser: try 7-char `o/x` form first, then `<卦名>·<因>`. -/
def parseCell (s : String) : Option R7 :=
  parseCellAtom s |>.orElse fun () => parseChineseAtom s

example : parseCell "ooooooo" = some R7.origin := by native_decide
example : parseCell "乾·无" = some R7.origin := by native_decide
example : parseCell "garbage" = none := by native_decide

/-! ## § 2  Evaluator: Sexp → Option R7

The grammar:
```
prog  ::=  atom-7-char-string                  -- a literal cell (o/x form)
        |  atom-of-form-<卦名>·<因>             -- a literal cell (Chinese form)
        |  (prog prog)                          -- application = Cayley XOR
```

Both atom forms coexist; you can mix them in one program. Anything else
(unknown atoms, 3-element lists, etc.) is `none`.
-/

partial def eval : Sexp → Option R7
  | .atom s         => parseCell s
  | .list [p, q]    => do
      let pc ← eval p
      let qc ← eval q
      pure (R7.xor pc qc)
  | _               => none

/-- The 道-judge: evaluate the program; is the result `origin`? -/
def isDao (s : Sexp) : Bool :=
  match eval s with
  | some c => c == R7.origin
  | none   => false

/-- Run an interpreter on a raw `String` source — full pipeline. -/
def judge (src : String) : Bool :=
  match Sexp.parse src with
  | .ok sexp => isDao sexp
  | .error _ => false

/-! ## § 3  Examples — runnable verdicts

The following `#eval` lines are the actual interpreter doing its thing.
Each prints `true` (道) or `false` (非道).
-/

-- 道本身：bare origin atom.
#eval judge "ooooooo"                                -- true

-- 自消律：A ⊕ A = 道。 (any cell, applied to itself.)
#eval judge "(xxxxxxx xxxxxxx)"                       -- true
#eval judge "(xoxoxox xoxoxox)"                       -- true

-- 非道：origin ⊕ non-origin = non-origin.
#eval judge "(ooooooo xxxxxxx)"                       -- false

-- 复合自消：(A ⊕ B) ⊕ (A ⊕ B) = 道.
#eval judge "((xoxoxox ooxxoox) (xoxoxox ooxxoox))"   -- true

-- 交换 + 自消：(A ⊕ B) ⊕ (B ⊕ A) = 道.
#eval judge "((xoxoxox ooxxoox) (ooxxoox xoxoxox))"   -- true

-- 关联 + 自消：(A ⊕ (A ⊕ B)) = B —— 非道 unless B = origin.
#eval judge "(xoxoxox (xoxoxox ooxxoox))"             -- false (= ooxxoox)

-- 但若 B = 道：(A ⊕ (A ⊕ 道)) = 道.
#eval judge "(xoxoxox (xoxoxox ooooooo))"             -- true

-- 错配：parse error → false.
#eval judge "(xxxxxxx)"                               -- false (1-elt list)
#eval judge "qwerty7"                                 -- false (bad chars)

/-! ## § 4  Theorems — the judge is sound

`isDao` agrees with the algebraic notion of "evaluates to origin". Since
both sides reduce by `native_decide` on concrete inputs, we exhibit five
representative test cases as `example` proofs.
-/

example : judge "ooooooo" = true := by native_decide

example : judge "(xxxxxxx xxxxxxx)" = true := by native_decide

example : judge "(ooooooo xxxxxxx)" = false := by native_decide

example : judge "((xoxoxox ooxxoox) (xoxoxox ooxxoox))" = true := by native_decide

example : judge "(xoxoxox (xoxoxox ooooooo))" = true := by native_decide

/-! ## § 4.25  Chinese-form judge runs

Same algebra, now via cell names. -/

-- 道 itself, named form.
#eval judge "乾·无"                                   -- true

-- A ⊕ A = 道 with named A.
#eval judge "(既济·有 既济·有)"                       -- true
#eval judge "(未济·无 未济·无)"                       -- true

-- Different named cells: non-道.
#eval judge "(乾·无 既济·有)"                         -- false

-- Mixed form: o/x and named in one program.
#eval judge "(乾·无 ooooooo)"                         -- true (same cell)
#eval judge "(xxxxxxx 坤·有)"                         -- true (xxxxxxx = 坤·有)

-- Compound: (A ⊕ B) ⊕ (B ⊕ A) = 道 with named cells.
#eval judge "((既济·有 未济·无) (未济·无 既济·有))"   -- true

example : judge "乾·无" = true := by native_decide
example : judge "(既济·有 既济·有)" = true := by native_decide
example : judge "(xxxxxxx 坤·有)" = true := by native_decide
example : judge "((既济·有 未济·无) (未济·无 既济·有))" = true := by native_decide

/-- 仁义礼智信 in Chinese-name form. Cross-references 仁/义/礼/智/信
    against the 64 周易 hexagrams reveal:
      仁 = 姤   (#44, encounter)
      义 = 同人 (#13, fellowship)
      礼 = 履   (#10, treading)
      智 = 小畜 (#9, small restraint)
      信 = 观   (#20, contemplation)
    The five 卦 are NOT the trigram-doubled "pure" ones — they emerge
    naturally from the algebraic constraint that one of them be the
    XOR-synthesis of the others. -/
example : judge "((((姤·无 同人·无) 履·无) 小畜·无) 观·无)" = true := by
  native_decide

/-! ## § 4.5  仁义礼智信是道 —— 五常归一 demonstration

Map the Five Confucian Constants (五常) onto R7 atoms via 五行:
- 仁 (benevolence, 木): single-flip at y1  = `xoooooo`
- 义 (righteousness, 金): single-flip at y2  = `oxooooo`
- 礼 (propriety,  火): single-flip at y3  = `ooxoooo`
- 智 (wisdom,    水): single-flip at y4  = `oooxooo`
- 信 (trust,     土): combined flip y1+y2+y3+y4 = `xxxxooo`
                       = 仁 ⊕ 义 ⊕ 礼 ⊕ 智  (the synthesis)

`信` emerges as the algebraic synthesis of the other four. This is forced
by the (Z/2)⁷ structure: for the five to balance to 道, one of them must
be the XOR of the rest. The doctrine names this synthetic element **土**
(earth, the centre that holds the four directions) and morally **信**
(integrity, the centre that holds the four virtues).

Verdict: 仁⊕义⊕礼⊕智⊕信 = 道. -/
example :
    judge "((((xoooooo oxooooo) ooxoooo) oooxooo) xxxxooo)" = true := by
  native_decide

/-- The 信-as-synthesis derivation: without 信, the other four leave a
residue 四端未合 = `xxxxooo`. -/
example :
    judge "(((xoooooo oxooooo) ooxoooo) oooxooo)" = false := by
  native_decide

/-! ## § 5  Soundness as a finite list of test points

The judge is decidable in finite time (just XOR the leaves). We exhibit
soundness via the test bundle below — ten representative programs whose
verdicts are computed via `native_decide`. The full theorem
"`isDao s = true ↔ eval s = some origin`" follows from `BEq R7`
agreeing with `=` (LawfulBEq is automatically derived from the structure).
We do not state it here; the test bundle suffices for demo purposes.
-/

theorem dao_judge_test_bundle :
    judge "ooooooo" = true ∧
    judge "(xxxxxxx xxxxxxx)" = true ∧
    judge "(xoxoxox xoxoxox)" = true ∧
    judge "(ooooooo xxxxxxx)" = false ∧
    judge "((xoxoxox ooxxoox) (xoxoxox ooxxoox))" = true ∧
    judge "((xoxoxox ooxxoox) (ooxxoox xoxoxox))" = true ∧
    judge "(xoxoxox (xoxoxox ooxxoox))" = false ∧
    judge "(xoxoxox (xoxoxox ooooooo))" = true ∧
    judge "(xxxxxxx)" = false ∧
    judge "qwerty7" = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals native_decide

end SSBX.Foundation.Lang.DaoJudge
