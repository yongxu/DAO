/-
# 間 之 核 (Jian Kernel) — Lean 4 formalization

  Per spec 史料/真理/interval-kernel.md (archived v12; the 文/约/替 minimal computational core).

  Scope of this file (P-current; first verification pass):
    - 文 (Wen): inductive grammar, 文 ::= 字 | [文 之 文]
    - 替 (subst): capture-naive substitution
    - 约 (step): single-step root reduction implementing the 9 约 rules
    - stepAny: outermost-leftmost congruence (descend into pair sub-terms)
    - reduceN: bounded multi-step reduction
    - Verification: 4 examples from §六 (let+apply, ¬¬, ∀-instantiation, sequencing)

  Out of scope (future layers):
    - Confluence proof
    - STLC simulation theorem
    - 九字 minimality (negative results)
    - Capture-avoiding substitution with α-renaming
-/

namespace SSBX.Foundation.Jian.Jian

/-- 14 字 之 名 — operator atoms (extended from original 9: 方/已/矣 fill D4
    时序; 提/取 fill the (¬主从, 提取) sub-cell of D1 关联).

    Per spec, 之 IS the structural pair (`Wen.pair`); 之 listed here as Op
    is the marker name (rarely needed in AST since pair itself is 之).
    The other 13 operators MARK their compound forms via prefix-canonical AST.

    Dimension assignments (per 6-dim particle taxonomy):
      D1 关联 (composition):
          之 (主从)             — D1.subord, head-dependent
          而 (等位)             — D1.parallel, no head-dep
          者 (主从 ∧ 提取)       — D1.binderExtract, lifted with binder
          提 (¬主从 ∧ 提取)      — D1.liftOnly, observation/flow/proof — NEW
          取 (¬主从 ∧ 提取)      — D1.selectOnly, instance-pick — NEW
      D2 指 (reference):        即 (identity-assert) / 是 (deictic→identity)
      D3 量 (quantification):   凡 (universal)
      D4 时序 (temporality):
          方 (续, ongoing now-pointer)        — D4.progressive
          已 (止, anterior past pointer)      — D4.anterior   — NEW
          矣 (止, change-of-state perfect)    — D4.cos        — NEW
      D5 言态 (mood):           也 (declarative-final) / 令 (directive)
      D6 真值 (polarity):       非 (negation) -/
inductive Op : Type
  | zhi      -- 之 (structural pair; in AST appears only when name is referenced)
  | zhe      -- 者 (λ-abstraction binder; D1 主从+提取)
  | fei      -- 非 (negation; D6)
  | er       -- 而 (sequencing of judgments; D1 等位)
  | fan      -- 凡 (universal-judgment binder; D3)
  | ji       -- 即 (equality check; D2)
  | ye       -- 也 (judgment / closure marker; D5 declarative)
  | shi      -- 是 (reference / dereference; D2)
  | ling     -- 令 (let binding; D5 directive)
  | fang     -- 方 (D4 续: ongoing-process pointer; idempotent persistent tag)
  | yiAnter  -- 已 (D4 止: anterior pointer; idempotent persistent tag)
  | yiCos    -- 矣 (D4 止: change-of-state perfect; idempotent persistent tag)
  | ti       -- 提 (D1 提取-without-主从: observation lift; idempotent persistent)
  | qu       -- 取 (D1 提取-without-主从: instance select; idempotent persistent)
  deriving Repr, DecidableEq, BEq

/-- 6 dimensions of the particle kernel. -/
inductive Dimension : Type
  | D1  -- 关联 (composition / associating)
  | D2  -- 指 (reference / pointing)
  | D3  -- 量 (quantification / scope)
  | D4  -- 时序 (temporality / aspect)
  | D5  -- 言态 (mood / speech-act)
  | D6  -- 真值 (polarity / truth)
  deriving Repr, DecidableEq, BEq

namespace Op

/-- Each operator's home dimension. -/
def dim : Op → Dimension
  | zhi | zhe | er | ti | qu => .D1
  | ji | shi                 => .D2
  | fan                       => .D3
  | fang | yiAnter | yiCos    => .D4
  | ye | ling                 => .D5
  | fei                       => .D6

/-- All 14 atomic operators, in canonical order. -/
def allOps : List Op :=
  [zhi, zhe, fei, er, fan, ji, ye, shi, ling, fang, yiAnter, yiCos, ti, qu]

theorem allOps_length : allOps.length = 14 := rfl

/-- Operators in a given dimension. -/
def opsInDim (d : Dimension) : List Op :=
  allOps.filter (fun o => o.dim = d)

theorem D1_count : (opsInDim .D1).length = 5 := by native_decide
theorem D2_count : (opsInDim .D2).length = 2 := by native_decide
theorem D3_count : (opsInDim .D3).length = 1 := by native_decide
theorem D4_count : (opsInDim .D4).length = 3 := by native_decide
theorem D5_count : (opsInDim .D5).length = 2 := by native_decide
theorem D6_count : (opsInDim .D6).length = 1 := by native_decide

/-- The 14 = 5 + 2 + 1 + 3 + 2 + 1 sum equality. -/
theorem dim_partition_sums :
    (opsInDim .D1).length + (opsInDim .D2).length + (opsInDim .D3).length
    + (opsInDim .D4).length + (opsInDim .D5).length + (opsInDim .D6).length
    = allOps.length := by native_decide

end Op

/-- 文 (term): 文 ::= 字 | [文 之 文].
    Encoded as: atom (字 — ordinary names like 子, 由, 戊, 庚, 真, 假, 己, 他),
    op (operator atom), or pair (the 之-pair, structurally THE relation). -/
inductive Wen : Type
  | atom : String → Wen
  | op : Op → Wen
  | pair : Wen → Wen → Wen
  deriving Repr, DecidableEq

namespace Wen

/-! ## Surface-form helpers

  Each maps a surface bracket form to its canonical (prefix) AST representation. -/

/-- `[者 b body]` — λ-abstraction. -/
def Zhe (binder : String) (body : Wen) : Wen :=
  .pair (.op .zhe) (.pair (.atom binder) body)

/-- `[非 x]` — negation. -/
def Fei (x : Wen) : Wen := .pair (.op .fei) x

/-- `[x 而 y]` — sequencing (canonicalized to prefix). -/
def Er (x y : Wen) : Wen := .pair (.op .er) (.pair x y)

/-- `[凡 b body]` — universal-judgment binder. -/
def Fan (binder : String) (body : Wen) : Wen :=
  .pair (.op .fan) (.pair (.atom binder) body)

/-- `[x 即 y]` — equality check (canonicalized to prefix). -/
def Ji (x y : Wen) : Wen := .pair (.op .ji) (.pair x y)

/-- `[x 也]` — judgment / closure (canonicalized to prefix). -/
def Ye (x : Wen) : Wen := .pair (.op .ye) x

/-- `[是 x]` — reference / dereference. -/
def Shi (x : Wen) : Wen := .pair (.op .shi) x

/-- `[令 b val body]` — let binding. -/
def Ling (binder : String) (val body : Wen) : Wen :=
  .pair (.op .ling) (.pair (.atom binder) (.pair val body))

/-- `[方 X]` — ongoing-process tag (D4 续, "now-pointer").
    Idempotent: `[方 [方 X]] → [方 X]`. Persistent: doesn't strip on deref. -/
def Fang (x : Wen) : Wen := .pair (.op .fang) x

/-- `[已 X]` — anterior tag (D4 止, "before-now pointer").
    Idempotent + persistent like 方. Semantically: X has already happened. -/
def YiAnter (x : Wen) : Wen := .pair (.op .yiAnter) x

/-- `[矣 X]` — change-of-state perfect (D4 止, "X has come to be").
    Idempotent + persistent. Distinct from 已: 已 = anterior placement;
    矣 = transition into a new state. -/
def YiCos (x : Wen) : Wen := .pair (.op .yiCos) x

/-- `[提 X]` — observation lift (D1 提取-without-主从).
    Witness/quote operator: turns X from "used" to "noted". Persistent.
    "提及" / "提到": bring X to attention without binding. -/
def Ti (x : Wen) : Wen := .pair (.op .ti) x

/-- `[取 X]` — instance select (D1 提取-without-主从).
    Selection operator: pick from X. Persistent. -/
def Qu (x : Wen) : Wen := .pair (.op .qu) x

/-- Tree-size of a term (atom = 1, op = 1, pair = 1 + lsize + rsize).
    Used for well-founded recursion of subst (post α-renaming). -/
def size : Wen → Nat
  | .atom _ => 1
  | .op _ => 1
  | .pair l r => 1 + l.size + r.size

end Wen

/-- Free variables (atomic names) appearing free in t.
    Binder positions (者/凡/令) exclude their binder from body's free set. -/
def freeVars : Wen → List String
  | .atom n => [n]
  | .op _ => []
  | .pair (.op .zhe) (.pair (.atom b) body) =>
      (freeVars body).filter (· ≠ b)
  | .pair (.op .fan) (.pair (.atom b) body) =>
      (freeVars body).filter (· ≠ b)
  | .pair (.op .ling) (.pair (.atom b) (.pair v body)) =>
      freeVars v ++ (freeVars body).filter (· ≠ b)
  | .pair l r => freeVars l ++ freeVars r

/-- Generate a name not in `used`, based on `base`. -/
def freshName (used : List String) (base : String) : String :=
  let candidates := (List.range (used.length + 1)).map (fun i => base ++ "_" ++ toString i)
  match candidates.find? (fun c => !(used.contains c)) with
  | some c => c
  | none => base ++ "_overflow"  -- unreachable: candidates has length+1 names, can't all be used

/-- 易 (yì): atomic name-transformation. Maps `f : String → String` over every
    atom; rebuilds structure as-is for op and pair. Structurally recursive.

    与 capture-avoiding rename 之 区别: 易 不 respect binder shadowing — 它 改
    所有 atom (including bound ones). 用于 subst 之 α-renaming 时, b' 必 fresh,
    所以 易 与 shadow-respecting rename 之 输出 α-equivalent (Lean 视为 different
    syntactic terms but semantically same). 此 simpler form 之 size 证明 4 行. -/
def yi (f : String → String) : Wen → Wen
  | .atom n => .atom (f n)
  | .op o => .op o
  | .pair l r => .pair (yi f l) (yi f r)

/-- 易 之 量 不变: atomic transformation preserves Wen-size. -/
theorem yi_size (f : String → String) (t : Wen) :
    (yi f t).size = t.size := by
  induction t with
  | atom n => rfl
  | op o => rfl
  | pair l r ihl ihr => simp [yi, Wen.size, ihl, ihr]

/-- Single-atom rename via 易: replace `b` with `b'` everywhere. -/
def yi1 (b b' : String) : Wen → Wen :=
  yi (fun n => if n = b then b' else n)

/-- Single-atom rename preserves size — direct corollary of `yi_size`. -/
theorem yi1_size (b b' : String) (t : Wen) :
    (yi1 b b' t).size = t.size :=
  yi_size _ t

/-- Default `Wen` value for `Inhabited` instance. -/
instance : Inhabited Wen := ⟨.atom ""⟩

/-- Wen.size is always at least 1 (minimum case = atom or op). -/
theorem Wen.size_pos (t : Wen) : 1 ≤ t.size := by
  cases t <;> simp [Wen.size] <;> omega

/-- 替 (subst, capture-avoiding): t{name ↦ val}.

    Per spec § 五: when binder name conflicts with a free name in val,
    α-rename the binder to a fresh name first to prevent capture.

    Three binder forms (者/凡/令) need the α-rename check. Termination via
    well-founded recursion on `t.size`: recursive calls are on direct sub-terms
    or on `yi1 b b' body` which by `yi1_size` has the same size as body.

    α-renaming uses `yi1` (always-recurse atomic swap) rather than a
    shadow-respecting variant. Since `b'` is fresh, the two are α-equivalent;
    `yi1` admits a 4-line size proof versus 130 lines for shadow-respect. -/
def subst : Wen → String → Wen → Wen
  | .atom n, name, val => if n = name then val else .atom n
  | .op o, _, _ => .op o
  | .pair (.op .zhe) (.pair (.atom b) body), name, val =>
      if b = name then
        .pair (.op .zhe) (.pair (.atom b) body)
      else if (freeVars val).contains b then
        let b' := freshName (freeVars body ++ freeVars val ++ [name]) b
        let body' := yi1 b b' body
        .pair (.op .zhe) (.pair (.atom b') (subst body' name val))
      else
        .pair (.op .zhe) (.pair (.atom b) (subst body name val))
  | .pair (.op .fan) (.pair (.atom b) body), name, val =>
      if b = name then
        .pair (.op .fan) (.pair (.atom b) body)
      else if (freeVars val).contains b then
        let b' := freshName (freeVars body ++ freeVars val ++ [name]) b
        let body' := yi1 b b' body
        .pair (.op .fan) (.pair (.atom b') (subst body' name val))
      else
        .pair (.op .fan) (.pair (.atom b) (subst body name val))
  | .pair (.op .ling) (.pair (.atom b) (.pair v body)), name, val =>
      let v' := subst v name val
      if b = name then
        .pair (.op .ling) (.pair (.atom b) (.pair v' body))
      else if (freeVars val).contains b then
        let b' := freshName (freeVars body ++ freeVars val ++ [name]) b
        let body' := yi1 b b' body
        .pair (.op .ling) (.pair (.atom b') (.pair v' (subst body' name val)))
      else
        .pair (.op .ling) (.pair (.atom b) (.pair v' (subst body name val)))
  | .pair l r, name, val => .pair (subst l name val) (subst r name val)
termination_by t _ _ => t.size
decreasing_by
  all_goals first
    | (simp_wf; simp only [Wen.size, yi1, yi_size]; omega)
    | (simp_wf; simp only [Wen.size]; omega)

/-- 约 (step): one-step ROOT reduction. Returns `some t'` if a reduction rule
    fires at the outermost form; `none` otherwise.

    The 14 rules from §三 (rule 9 「断之约」 is the implicit fall-through;
    rules 10-14 are idempotency for the 5 persistent unary tags 方/已/矣/提/取). -/
def step : Wen → Option Wen
  -- 一、令之约: [令 b v body] → body{b↦v}
  | .pair (.op .ling) (.pair (.atom n) (.pair v body)) =>
      some (subst body n v)
  -- 二、施之约: [[者 b body] 之 arg] → body{b↦arg}
  | .pair (.pair (.op .zhe) (.pair (.atom n) body)) arg =>
      some (subst body n arg)
  -- 三、否之约: [非 [非 x]] → x
  | .pair (.op .fei) (.pair (.op .fei) inner) =>
      some inner
  -- 四、续之约: [[x 也] 而 y] → y
  | .pair (.op .er) (.pair (.pair (.op .ye) _) right) =>
      some right
  -- 五、遍之约: [[凡 b body] 之 arg] → [body{b↦arg} 也]
  | .pair (.pair (.op .fan) (.pair (.atom n) body)) arg =>
      some (.pair (.op .ye) (subst body n arg))
  -- 六、同合 / 七、同异: [x 即 y] → [真 也] (if x = y) | [假 也] (else)
  | .pair (.op .ji) (.pair l r) =>
      if l = r then some (.pair (.op .ye) (.atom "真"))
      else some (.pair (.op .ye) (.atom "假"))
  -- 八、指之约: [是 x] → x
  | .pair (.op .shi) inner => some inner
  -- 十、方之约 (idempotency): [方 [方 x]] → [方 x]
  -- (Persistence + idempotence: pointer-to-now collapses repeated nesting.)
  | .pair (.op .fang) (.pair (.op .fang) inner) =>
      some (.pair (.op .fang) inner)
  -- 十一、已之约 (idempotency): [已 [已 x]] → [已 x]
  | .pair (.op .yiAnter) (.pair (.op .yiAnter) inner) =>
      some (.pair (.op .yiAnter) inner)
  -- 十二、矣之约 (idempotency): [矣 [矣 x]] → [矣 x]
  | .pair (.op .yiCos) (.pair (.op .yiCos) inner) =>
      some (.pair (.op .yiCos) inner)
  -- 十三、提之约 (idempotency): [提 [提 x]] → [提 x]
  | .pair (.op .ti) (.pair (.op .ti) inner) =>
      some (.pair (.op .ti) inner)
  -- 十四、取之约 (idempotency): [取 [取 x]] → [取 x]
  | .pair (.op .qu) (.pair (.op .qu) inner) =>
      some (.pair (.op .qu) inner)
  -- Otherwise (incl. rule 九、断之约 — [x 也] terminal at root)
  | _ => none

/-- Outermost-leftmost congruence with **eager-args for 即** (per consult resolution
    aligned with 异名同实 doctrine: 即 fires only after both args reach normal form).

    For 即-pairs: descend into args FIRST, only fire 即 rule when both args
    are normal. For all other forms: standard outermost-leftmost. -/
def stepAny : Wen → Option Wen
  | .pair (.op .ji) (.pair l r) =>
      -- Eager-args 即: try args first, fire only when both normal
      match stepAny l with
      | some l' => some (.pair (.op .ji) (.pair l' r))
      | none =>
        match stepAny r with
        | some r' => some (.pair (.op .ji) (.pair l r'))
        | none => step (.pair (.op .ji) (.pair l r))
  | .pair l r =>
      match step (.pair l r) with
      | some t' => some t'
      | none =>
        match stepAny l with
        | some l' => some (.pair l' r)
        | none =>
          match stepAny r with
          | some r' => some (.pair l r')
          | none => none
  | t => step t

/-- Bounded reduction: at most n stepAny applications. -/
def reduceN : Nat → Wen → Wen
  | 0, t => t
  | n+1, t =>
    match stepAny t with
    | some t' => reduceN n t'
    | none => t

/-! ## § 七 性质 — verified properties

  This section accumulates verified properties from spec § 七.
  Status:
    - **Deterministic strategy** (below): proven (trivial; stepAny is a function)
    - **Eager-args 即 confluence** (counterexample test): empirically verified in Examples
    - **Confluence** (full Church-Rosser): abstract Newman's lemma proved in
      `SSBX.Foundation.Bagua.Newman`; application to Wen requires SN+LC verification
      on a typed fragment (Wen is not globally SN due to Y-combinator encoding)
    - **STLC-completeness** (者/之/令 ⊢ STLC): proved in `SSBX.Foundation.Jian.JianSTLC`
      (`simulation` theorem, axiom-free)
    - **Strong normalization** (typed fragment): requires type system first
    - **Minimality** (each-字-removal-breaks): proved in `SSBX.Foundation.Jian.JianMinimality`
-/

/-- stepAny is deterministic: same input gives same output (trivially, since it's a function).
    This is NOT global confluence — only that ONE strategy is well-defined. -/
theorem stepAny_deterministic (t u v : Wen)
    (hu : stepAny t = some u) (hv : stepAny t = some v) : u = v := by
  rw [hu] at hv
  injection hv

/-- reduceN is deterministic for the same reason. -/
theorem reduceN_deterministic (n : Nat) (t u v : Wen)
    (hu : reduceN n t = u) (hv : reduceN n t = v) : u = v := by
  rw [← hu, ← hv]

/-! ### Confluence — scaffolding

  The full Church-Rosser theorem (§ 七 "Confluent"):
  ```
    ∀ t u v, t →* u → t →* v → ∃ w, u →* w ∧ v →* w
  ```
  for the GENERAL `→` relation (any redex, any choice), not just stepAny.

  **Path to proof**:

  1. Define a relation `Step : Wen → Wen → Prop` capturing all valid single-step
     reductions (the 9 rules + congruence under pair). Constraint: 即 (rule 6/7)
     must require `isNormal` on its args (eager-args resolution from consult).

  2. Define `MultiStep := Relation.ReflTransGen Step`.

  3. **Local confluence** (Newman pre-condition):
     `∀ t u v, Step t u → Step t v → ∃ w, MultiStep u w ∧ MultiStep v w`

     Case analysis on (rule_u, rule_v):
       - Disjoint sub-terms: trivially commute.
       - Nested redexes (rule 1/2/5 ∋ rule_inside): substitution lemma needed
         (`subst_subst : subst (subst t x v) y w = ...`). Requires α-renaming
         soundness (currently `partial def`; theorem-level needs termination
         via `rename_size` lemma + well-founded recursion).
       - 即 with eager-args: by isNormal constraint, args fully reduced before
         即 fires, so 即 doesn't conflict with inner reductions.

  4. **Strong normalization** (Newman pre-condition; spec § 七 claims SN
     for typed fragment only): requires type system definition first.

  5. **Newman's lemma**: LC + SN ⟹ confluence. Standard, ~50 LoC if 3 and 4 done.

  **Scope assessment**: ~500-800 LoC across a typed system definition (200),
  substitution lemmas with α-rename termination (150), local confluence cases
  (200), SN proof (100), Newman application (50). Multi-iteration work.

  **Current turn delivers**: Steps 1-2 prerequisites — eager-args 即 (DONE),
  α-renaming subst (DONE, partial def). The Step relation, local confluence,
  SN, and Newman application are the next layer. -/

/-! ## Verification — §六 examples -/

namespace Examples

open Wen

/-- 例一: `[令 子 [者 由 由] [子 之 戊]] →* 戊` -/
def ex1 : Wen :=
  Ling "子" (Zhe "由" (.atom "由")) (.pair (.atom "子") (.atom "戊"))

theorem ex1_reduces : reduceN 5 ex1 = .atom "戊" := by native_decide

/-- 例二: `[非 [非 [真 也]]] →* [真 也]` -/
def ex2 : Wen := Fei (Fei (Ye (.atom "真")))

theorem ex2_reduces : reduceN 5 ex2 = Ye (.atom "真") := by native_decide

/-- 例三: `[[凡 子 [子 即 子]] 之 戊] →* [[真 也] 也]` -/
def ex3 : Wen := .pair (Fan "子" (Ji (.atom "子") (.atom "子"))) (.atom "戊")

theorem ex3_reduces : reduceN 5 ex3 = Ye (Ye (.atom "真")) := by native_decide

/-- 例四: `[[[戊 即 戊] 也] 而 庚] →* 庚` -/
def ex4 : Wen := Er (Ye (Ji (.atom "戊") (.atom "戊"))) (.atom "庚")

theorem ex4_reduces : reduceN 5 ex4 = .atom "庚" := by native_decide

/-- 反例 (consult resolution test): `[[非 [非 [真 也]]] 即 [真 也]]`.

    In syntactic-即 semantics this would non-confluently reduce to `[假 也]`
    if 即 fires before inner ¬¬-elimination, but to `[真 也]` if inner reduces
    first. With **eager-args 即** (per OPTION B / 异名同实): both args are
    normalized first, so the comparison is always between normal forms. Here
    LHS reduces to `[真 也]`, then `[[真 也] 即 [真 也]]` fires with equal args. -/
def counterexample : Wen :=
  Ji (Fei (Fei (Ye (.atom "真")))) (Ye (.atom "真"))

theorem counterexample_eager_reduces :
    reduceN 10 counterexample = Ye (.atom "真") := by native_decide

/-- 替之 capture-test: applying `[者 x [x 之 y]]` to `y` should NOT capture y.

    Naive subst would give `[y 之 y]` (capture!) — the y from the arg
    aliases the binder x's body's free y.
    α-renaming binder x → x_n first, then substitute: result `[y 之 y]`
    is wrong; correct is `[y 之 y]` only if the body's `y` is meant.
    Our case: body `[x 之 y]`, with `x` being binder, `y` being free.
    Substituting `x ↦ y` should give `[y 之 y]` IF y wasn't already free.
    But y IS free in body (the body's outer y). So the result is well-defined: y. -/
def captureTest : Wen :=
  .pair (Zhe "x" (.pair (.atom "x") (.atom "y"))) (.atom "y")

theorem captureTest_reduces :
    reduceN 5 captureTest = .pair (.atom "y") (.atom "y") := by native_decide

/-- A more pointed capture test: `[[者 y [者 x [x 之 y]]] 之 y]`.
    Outer arg is `y` (free in result context); inner binder is `y` then `x`.
    Substituting the outer y, naive subst would let inner y-binder capture.
    α-renaming protects: inner `y`-binder gets renamed to `y_n`, free `y`
    in outermost `[x 之 y]` survives substitution. -/
def captureTest2 : Wen :=
  .pair (Zhe "y" (Zhe "x" (.pair (.atom "x") (.atom "y")))) (.atom "y")

theorem captureTest2_reduces_correct :
    -- Should be a 者-form (irreducible since arg is just `y` — atom — but no
    -- 者-application yet at outer; inner binder `y` shadows outer arg `y`).
    -- After β: result body `[x 之 y]`{y ↦ y_outer-arg-which-is-y} = `[x 之 y]`.
    -- That's `Zhe "x" (.pair (.atom "x") (.atom "y"))` — irreducible (no 者-arg).
    reduceN 5 captureTest2 = Zhe "x" (.pair (.atom "x") (.atom "y")) := by native_decide

/-! ### 方 (D4 续-marker) — verified examples -/

/-- 方 idempotency (rule 10): `[方 [方 戊]] →* [方 戊]` (one-step). -/
def fang_idem : Wen := Fang (Fang (.atom "戊"))

theorem fang_idem_reduces : reduceN 1 fang_idem = Fang (.atom "戊") := by native_decide

/-- 方 idempotency stabilizes after collapse: `[方 戊]` is normal. -/
theorem fang_normal : reduceN 5 (Fang (.atom "戊")) = Fang (.atom "戊") := by native_decide

/-- 方 is PERSISTENT (unlike 是 which strips on rule 8): `[方 X]` doesn't unwrap.
    Compare: `[是 戊] →* 戊` (rule 8 strips); `[方 戊] →* [方 戊]` (no rule, stays). -/
theorem fang_does_not_strip : reduceN 5 (Fang (.atom "戊")) ≠ .atom "戊" := by
  native_decide

/-- 方 commutes with internal reduction: inner X may reduce, 方 wrapper persists.
    Test: `[方 [非 [非 [真 也]]]] →* [方 [真 也]]`. -/
def fang_inner : Wen := Fang (Fei (Fei (Ye (.atom "真"))))

theorem fang_inner_reduces : reduceN 5 fang_inner = Fang (Ye (.atom "真")) := by
  native_decide

/-- Triple 方: `[方 [方 [方 X]]] →* [方 X]` after enough steps (idempotency cascades). -/
def fang_triple : Wen := Fang (Fang (Fang (.atom "庚")))

theorem fang_triple_collapses :
    reduceN 5 fang_triple = Fang (.atom "庚") := by native_decide

/-! ### 已 (D4 止 anterior) — verified examples -/

theorem yiAnter_idem : reduceN 1 (YiAnter (YiAnter (.atom "戊"))) = YiAnter (.atom "戊") := by
  native_decide

theorem yiAnter_persistent : reduceN 5 (YiAnter (.atom "戊")) ≠ .atom "戊" := by native_decide

theorem yiAnter_inner_reduces :
    reduceN 5 (YiAnter (Fei (Fei (Ye (.atom "真"))))) = YiAnter (Ye (.atom "真")) := by
  native_decide

/-! ### 矣 (D4 止 change-of-state) — verified examples -/

theorem yiCos_idem : reduceN 1 (YiCos (YiCos (.atom "戊"))) = YiCos (.atom "戊") := by
  native_decide

theorem yiCos_persistent : reduceN 5 (YiCos (.atom "戊")) ≠ .atom "戊" := by native_decide

/-- Independence: 已 and 矣 are distinct (NOT mutually idempotent). -/
theorem yiAnter_yiCos_independent :
    reduceN 5 (YiAnter (YiCos (.atom "戊"))) ≠ YiAnter (.atom "戊") := by native_decide

/-! ### 提 / 取 (D1 提取-without-主从) — verified examples -/

theorem ti_idem : reduceN 1 (Ti (Ti (.atom "戊"))) = Ti (.atom "戊") := by native_decide

theorem qu_idem : reduceN 1 (Qu (Qu (.atom "戊"))) = Qu (.atom "戊") := by native_decide

theorem ti_persistent : reduceN 5 (Ti (.atom "戊")) ≠ .atom "戊" := by native_decide
theorem qu_persistent : reduceN 5 (Qu (.atom "戊")) ≠ .atom "戊" := by native_decide

/-- Inner reduction proceeds beneath both 提 and 取. -/
theorem ti_inner_reduces :
    reduceN 5 (Ti (Fei (Fei (Ye (.atom "真"))))) = Ti (Ye (.atom "真")) := by
  native_decide

theorem qu_inner_reduces :
    reduceN 5 (Qu (Fei (Fei (Ye (.atom "真"))))) = Qu (Ye (.atom "真")) := by
  native_decide

/-- 提 and 取 do NOT collapse with each other (different operations).
    `[提 [取 X]]` does not reduce to `[提 X]` or to X — they're distinct atoms. -/
theorem ti_qu_independent :
    reduceN 5 (Ti (Qu (.atom "戊"))) ≠ Ti (.atom "戊") := by native_decide

theorem qu_ti_independent :
    reduceN 5 (Qu (Ti (.atom "戊"))) ≠ Qu (.atom "戊") := by native_decide

end Examples

end SSBX.Foundation.Jian.Jian
