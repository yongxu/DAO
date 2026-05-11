/-
# Demo — exercising the R-hierarchy Lisp interpreter

Three runnable demos plus a fourth discussion-only section on the limits of
v1 (what a CIC-style R₁→R₂→…→R₇ self-bootstrap would need beyond what we
have today).

## Demos

1. **§1 生生不息 (perpetual generation)** — 乾·无 → 坤·有 at L7 in 7 atomic
   steps, then provably reversible. No state in (Z/2)⁷ is a terminal sink.
2. **§2 道法自然 (Dao follows Nature)** — `origin` (= 道 = (Z/2)ⁿ zero) is
   the fixed point of the empty rule list and the identity of `apply` at
   every layer. Theorems exhibited at L1 and L7.
3. **§3 R₂ ⊃ R₁ × R₁ (layer-as-product witness in the Lisp)** — pair of
   conversion rules that round-trip between `(sixiang ?a ?b)` and
   `(pair (yao ?a) (yao ?b))`. The Lisp witnesses, at the Sexp level, that
   L2 cells decompose into pairs of L1 cells. Same idiom extends to R_n =
   R_{n-1} × R_1 at every layer.
4. **§4 What v1 does *not* express** — discussion of why a true
   "R₁ defines R₂ defines R₃" CIC-style self-bootstrap requires features
   v1 does not have, with a concrete list.
-/

import SSBX.Foundation.Lang.L1_Yao
import SSBX.Foundation.Lang.L2_SiXiang
import SSBX.Foundation.Lang.L7_Cell128

namespace SSBX.Foundation.Lang.Demo

open SSBX.Foundation.Lang
open SSBX.Foundation.Yi.Yi    (Yao Hexagram)
open SSBX.Foundation.Bagua.R7

/-! ## § 1  生生不息 — 乾·无 → 坤·有 in 7 atomic flips

We start at L7's `origin` (= `(heaven, false)` = 乾·无) and walk through 7
atomic generators of (Z/2)⁷. After 7 fuel steps the cell is `(earth, true)` =
坤·有, the unique antipode. Each step uses a distinct atomic operator, so
any of the 128! such walks is a valid witness; we use the canonical one
(flip y1; y2; …; y6; then 印).

The "perpetual" part: since each atomic op is its own inverse, the same
7-rule list, run again on `坤·有`, walks back to `乾·无`. The state space
has no sink — every cell has 7 outgoing edges, all reversible.
-/

/-- R7 cell `(heaven, false)` rendered as Sexp at L7. -/
private def qianWuSexp : Sexp := L7.printCell L7.origin

/-- R7 cell `(earth, true)` rendered as Sexp at L7. -/
private def kunYouSexp : Sexp :=
  L7.printCell ((⟨.yin, .yin, .yin, .yin, .yin, .yin⟩ : Hexagram), true)

/-- The 7 atomic-flip walk rules from L7 (without the endpoint-toggle helpers
    in `L7.defaultRules`, which would create kunWu↔kunYou cycles). -/
private def shengshengRules : List Rule :=
  [L7.rule_step1, L7.rule_step2, L7.rule_step3, L7.rule_step4,
   L7.rule_step5, L7.rule_step6, L7.rule_step7_yin]

/-- 7 fuel ticks lift origin to its antipode. (the headline reachability) -/
example : (Eval.runRules shengshengRules qianWuSexp 7 == kunYouSexp) = true := by
  native_decide

/-- After the 7-step walk, the rule list reaches a true fixed point at 坤·有.
    None of the 7 step-rules match the antipode (each rule's pattern is the
    pre-state of its specific step). -/
example : Eval.reachedFixedPoint shengshengRules kunYouSexp = true := by
  native_decide

/-- Mechanically derive the 7 reverse rules by swapping pattern and replacement
    of each step. This witnesses involutivity of the Cayley action: the same
    7 generators run in reverse order undo the forward walk. -/
private def reverseRules : List Rule :=
  shengshengRules.reverse.map (fun r =>
    { pat := r.repl, repl := r.pat,
      name := r.name.map (fun n => "rev-" ++ n),
      priority := r.priority, kind := r.kind })

/-- 14 fuel ticks of the round-trip rule list `reverse ++ forward` returns
    to origin: 7 forward ticks reach 坤·有 (forward rules don't fire on
    the early states because reverse rules' patterns lie downstream), then
    7 reverse ticks return. This is 生生不息 in the strict sense —
    perpetual round-trip.

    NB: rule order matters — `reverse ++ forward` is correct. With
    `forward ++ reverse` instead, the forward `step7_yin` rule erroneously
    re-fires at the kunWu state during the reverse walk and oscillates
    kunWu↔kunYou. The fix is to give the reverse rules priority via list
    order. -/
example :
    (Eval.runRules (reverseRules ++ shengshengRules) qianWuSexp 14
      == qianWuSexp) = true := by
  native_decide

/-! ## § 2  道法自然 — origin is the identity

道 = origin = the (Z/2)ⁿ zero. "法自然" — its action is the natural
identity. Two faces of the same theorem:
- **As yao (data)**: origin is fixed by the empty rule list.
- **As yuan (operator)**: applying origin to any cell is the identity.

The latter is `LangLayer.origin_apply`, already in the typeclass.
-/

/-- 道 is fixed by ANY rule list whose patterns don't match it (e.g., the empty list). -/
example : Eval.runRules ([] : List Rule) (L7.printCell L7.origin) 100
    = L7.printCell L7.origin := by
  rfl

/-- 道 as yuan: applying origin leaves any cell unchanged (Cayley identity). -/
example (c : L1.Cell) : L1.apply L1.origin c = c := L1.origin_apply c
example (c : L7.Cell) : L7.apply L7.origin c = c := L7.origin_apply c

/-- 道 as yao: origin XOR origin = origin (idempotent under self-action). -/
example : L7.apply L7.origin L7.origin = L7.origin := L7.apply_self L7.origin

/-- All four faces of "道法自然" are one fact: at every layer,
    cayley-with-origin = identity, equivalently origin is the additive zero. -/
theorem dao_fa_zi_ran :
    (∀ c : L1.Cell, cayley L1.origin c = c) ∧
    (∀ c : L7.Cell, cayley L7.origin c = c) :=
  ⟨L1.origin_apply, L7.origin_apply⟩

/-! ## § 3  R₂ ⊃ R₁ × R₁ — layer composition witnessed in the Lisp

The doctrine says R_n = R_{n-1} × R_1 (each layer adds one bit). Outside
the language this is trivially true (Cell n+1 is by construction a pair).
**Inside** the Lisp, we can witness the iso at the Sexp level by writing
a pair of conversion rules. Running either rule on the appropriate Sexp
flips between the SiXiang form and the L1×L1 pair form.

This is the v1 equivalent of "R₁ defines R₂": the Lisp itself can convert
between the two views. (The richer "CIC-style" definition is discussed in
§4 below.)
-/

/-- Decompose: `(sixiang ?a ?b)` → `(pair (yao ?a) (yao ?b))`. -/
private def sixiangToPair : Rule :=
  Rule.named "sixiang→pair"
    (.list [.atom "sixiang", .atom "?a", .atom "?b"])
    (.list [.atom "pair",
            .list [.atom "yao", .atom "?a"],
            .list [.atom "yao", .atom "?b"]])

/-- Recompose: `(pair (yao ?a) (yao ?b))` → `(sixiang ?a ?b)`. -/
private def pairToSixiang : Rule :=
  Rule.named "pair→sixiang"
    (.list [.atom "pair",
            .list [.atom "yao", .atom "?a"],
            .list [.atom "yao", .atom "?b"]])
    (.list [.atom "sixiang", .atom "?a", .atom "?b"])

/-- Round-trip on a concrete L2 cell: 太阳 (yang yang) → pair → 太阳. -/
example :
    (Eval.runRules [sixiangToPair, pairToSixiang]
        (.list [.atom "sixiang", .atom "阳", .atom "阳"]) 2
      == (.list [.atom "sixiang", .atom "阳", .atom "阳"])) = true := by
  native_decide

/-- Decomposition fires on first step. -/
example :
    (Eval.runRules [sixiangToPair, pairToSixiang]
        (.list [.atom "sixiang", .atom "阴", .atom "阳"]) 1
      == (.list [.atom "pair",
                 .list [.atom "yao", .atom "阴"],
                 .list [.atom "yao", .atom "阳"]])) = true := by
  native_decide

/-! ## § 4  What v1 does *not* express (honest scope note)

The user's framing — "R₁ 定义 R₂ 定义 R₃ … 自指且完备, CIC 那种" — would
require:

(a) **Reflective rule lists**: rules whose replacements compute over
    matched bindings (not just substitute literally). Example: a rule
    `(bit ?b) → (toggle ?b)` where `(toggle ?b)` evaluates `?b` to its
    complement at substitution time.
(b) **Hierarchical types in the Sexp**: an Sexp constructor that says
    "this sub-tree is at layer L_n", letting the language reason about
    layer membership. Currently atoms are flat strings; layer is implicit.
(c) **Recursive type definitions**: a way to write `(deflayer L_{n+1}
    (* L_n L_1))` that produces a runtime layer description usable by
    rules. v1's `LangLayer` typeclass lives in Lean, not in Lisp.
(d) **Soundness of the bootstrap**: a theorem stating that every
    Lisp-level layer definition agrees with the corresponding Lean-level
    `LangLayer` instance. v1 has no notion of Lisp-defined layers.

Each of these is a v2 feature. The 文言 phase is the natural home for
(a)+(b); a small reflection step in `Rule.replacement` (interpreting
certain head-symbols as primitive ops) closes (a) without disturbing the
v1 semantics for non-reflective rules. (c)+(d) are deeper — the cleanest
path is to add a syntactic category for layer definitions and an
elaborator that emits the corresponding Lean-level instance + a soundness
witness.

For now, §1+§2+§3 demonstrate that the v1 interpreter computes correctly
on real R-hierarchy cells, and that the doctrine's structural claims
(perpetual generation, dao-as-identity, layer-as-product) are all
verifiable in the Lisp by running concrete programs.
-/

/-- Public summary bundle of the three demos. -/
theorem demo_summary :
    (Eval.runRules shengshengRules qianWuSexp 7 == kunYouSexp) = true ∧
    (Eval.runRules (reverseRules ++ shengshengRules) qianWuSexp 14
        == qianWuSexp) = true ∧
    (∀ c : L1.Cell, cayley L1.origin c = c) ∧
    (∀ c : L7.Cell, cayley L7.origin c = c) ∧
    (Eval.runRules [sixiangToPair, pairToSixiang]
        (.list [.atom "sixiang", .atom "阳", .atom "阳"]) 2
      == (.list [.atom "sixiang", .atom "阳", .atom "阳"])) = true := by
  refine ⟨?_, ?_, L1.origin_apply, L7.origin_apply, ?_⟩
  all_goals native_decide

end SSBX.Foundation.Lang.Demo
