/-
# WenSurface.RewriteRules — wen-2.0 ⑫ 定 LHS 等 RHS

User-level equational rewrite rules over `WenDef.Tm`.

## Surface

A `定 LHS 等 RHS` chunk declares a top-level rewrite rule.  The two operands
are ordinary Wen expressions; any **free variable** appearing in LHS is
treated as a **pattern metavariable** that may match any sub-Tm at the
corresponding position.  RHS must use only the same pattern metavariables.

Example (the canonical case from spec ⑫):

    定 错 错 甲 等 甲

Reads as: "complement of complement of 甲 equals 甲" where `甲` is a
pattern metavariable.  After this declaration, every term of shape
`错 错 X` in subsequent chunks is normalised to `X`.

## v1 limitations

* **Linear patterns**: each pattern metavariable appears at most once on
  the LHS (multi-use would require an equality side condition).
* **No side conditions**: only pure structural matches.
* **Confluence**: enforced conservatively by rejecting two rules whose
  LHS head constructors agree (so at most one rule may rewrite any given
  outermost shape per constructor).  This is over-strict but safe; v2
  can use a proper critical-pair check.
* **Termination**: each `normalize` pass is fuel-bounded; we apply rules
  bottom-up to a fixpoint within fuel and stop.

## Status

0 sorry / 0 axiom.  Pure structural transform over `Tm`.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Wen.WenDef

/-! ## § 1  Rewrite-rule data -/

/-- A compiled rewrite rule.

    Pattern metavariables are encoded as **free occurrences of `Tm.var n`**
    inside `lhs`.  The list `vars` records exactly those names (in left-to-right
    LHS pre-order) so the rule is independent of α-renaming concerns in the
    surface and so we can enforce linearity statically. -/
structure RewriteRule where
  lhs  : Tm
  rhs  : Tm
  vars : List String
deriving Repr

/-- Accumulated rules, in declaration order.  Rules are applied newest-first
    in `normalize`; the confluence check at `addRule` keeps head constructors
    disjoint so order doesn't matter modulo termination. -/
abbrev RewriteEnv := List RewriteRule

/-! ## § 2  Free-var collection (used for pattern-var detection) -/

/-- Collect all `Tm.var` free-occurrence names in `t`, **in left-to-right
    pre-order**, allowing duplicates.  Binders (`abs`, `fix`) remove their
    bound name from the result; `quote` bodies are treated as opaque data
    (never a pattern context). -/
def freeVarsList : Tm → List String
  | .var n => [n]
  | .abs n _ body => (freeVarsList body).filter (fun m => m ≠ n)
  | .app f x => freeVarsList f ++ freeVarsList x
  | .catalogue1 _ a => freeVarsList a
  | .catalogue2 _ a b => freeVarsList a ++ freeVarsList b
  | .catalogue3 _ a b c => freeVarsList a ++ freeVarsList b ++ freeVarsList c
  | .quote _ => []
  | .fix n _ body => (freeVarsList body).filter (fun m => m ≠ n)
  | _ => []

private def dedupStrings : List String → List String → List String
  | acc, [] => acc.reverse
  | acc, n :: rest =>
      if acc.contains n then dedupStrings acc rest else dedupStrings (n :: acc) rest

/-- Same as `freeVarsList` but deduplicated (preserves first-occurrence order). -/
def freeVars (t : Tm) : List String :=
  dedupStrings [] (freeVarsList t)

/-! ## § 3  Linear-pattern + closed-RHS checks -/

/-- True iff every pattern var in `lhs` appears at most once. -/
def isLinearPattern (lhs : Tm) : Bool :=
  let occ := freeVarsList lhs
  let dedup := freeVars lhs
  decide (occ.length = dedup.length)

/-- True iff RHS uses only variables that appear on the LHS.
    (Extra free vars on the RHS would be unsound — they have no binding.) -/
def rhsUsesOnly (lhs rhs : Tm) : Bool :=
  let lhsVars := freeVars lhs
  (freeVars rhs).all (fun n => lhsVars.contains n)

/-! ## § 4  Head constructor tag (for confluence check) -/

/-- A coarse `head constructor` discriminator.  Two rules with the same
    head are rejected at decl time (v1 confluence policy). -/
inductive HeadTag where
  | varH
  | absH
  | appH
  | hexLitH
  | boolLitH
  | cellLitH
  | primH (idx : Nat)   -- one tag per built-in primitive, indexed
  | cat1H | cat2H | cat3H
  | quoteH
  | fixH
deriving DecidableEq, Repr

private def primIdxOf : Tm → Option Nat
  | .jia => some 0    | .yi => some 1
  | .notB => some 2   | .andB => some 3   | .orB => some 4
  | .eqHex => some 5  | .forallH => some 6
  | .uniqueH => some 7 | .exactly3H => some 8 | .majorityH => some 9
  | .cuoH => some 10  | .zongH => some 11 | .huH => some 12 | .cuoZongH => some 13
  | .flip1H => some 14 | .flip2H => some 15 | .flip3H => some 16
  | .flip4H => some 17 | .flip5H => some 18 | .flip6H => some 19
  | .pairH => some 20  | .dupH => some 21
  | .list1H => some 22 | .list2H => some 23 | .list3H => some 24 | .headH => some 25
  | .eqCell => some 26 | .cuoC => some 27 | .zongC => some 28 | .huC => some 29
  | .shiNextC => some 30 | .shiPrevC => some 31
  | .flip1C => some 32 | .flip2C => some 33 | .flip3C => some 34
  | .flip4C => some 35 | .flip5C => some 36 | .flip6C => some 37
  | _ => none

def headTag : Tm → HeadTag
  | .var _ => .varH
  | .abs _ _ _ => .absH
  | .app _ _ => .appH
  | .hexLit _ => .hexLitH
  | .boolLit _ => .boolLitH
  | .cellLit _ => .cellLitH
  | .catalogue1 _ _ => .cat1H
  | .catalogue2 _ _ _ => .cat2H
  | .catalogue3 _ _ _ _ => .cat3H
  | .quote _ => .quoteH
  | .fix _ _ _ => .fixH
  | t =>
    match primIdxOf t with
    | some i => .primH i
    | none   => .varH  -- unreachable for total Tm; defensive

/-! ## § 5  Pattern matching -/

/-- `Subst`: a finite map from pattern-var name to matched Tm. -/
abbrev Subst := List (String × Tm)

private def Subst.lookup : Subst → String → Option Tm
  | [], _ => none
  | (n, t) :: rest, name => if n = name then some t else rest.lookup name

/-- One-shot matcher.  `pat` is the LHS template; `t` is the candidate.

    Pattern-var binding: a free `.var n` in `pat` matches any `t`.  If `n` is
    already bound (linear patterns reject this at decl time, but we play it
    safe), the previously bound Tm must equal `t`.

    All other constructors must agree structurally, including binder names
    inside `abs`/`fix` (we don't α-convert; the LHS is user-authored and
    free vars are pattern slots, so binder names should not be considered
    metavariables — if a user writes `定 abs x. X 等 X` the inner `X` is the
    metavar and the binder `x` is structural).

    `pVars` is the set of names that ARE pattern vars in this LHS; vars not
    in `pVars` are treated as ordinary structural references that must match
    by name. -/
partial def matchPat (pVars : List String) : Tm → Tm → Subst → Option Subst
  | .var n, t, σ =>
      if pVars.contains n then
        match σ.lookup n with
        | some t' => if decide (t = t') then some σ else none
        | none    => some ((n, t) :: σ)
      else
        match t with
        | .var m => if n = m then some σ else none
        | _ => none
  | .abs n t1 b1, .abs m t2 b2, σ =>
      if n = m && decide (t1 = t2) then matchPat pVars b1 b2 σ else none
  | .app f1 x1, .app f2 x2, σ =>
      match matchPat pVars f1 f2 σ with
      | some σ' => matchPat pVars x1 x2 σ'
      | none    => none
  | .hexLit h1, .hexLit h2, σ => if decide (h1 = h2) then some σ else none
  | .boolLit b1, .boolLit b2, σ => if b1 = b2 then some σ else none
  | .cellLit c1, .cellLit c2, σ => if decide (c1 = c2) then some σ else none
  | .catalogue1 id1 a1, .catalogue1 id2 a2, σ =>
      if decide (id1 = id2) then matchPat pVars a1 a2 σ else none
  | .catalogue2 id1 a1 b1, .catalogue2 id2 a2 b2, σ =>
      if decide (id1 = id2) then
        match matchPat pVars a1 a2 σ with
        | some σ' => matchPat pVars b1 b2 σ'
        | none    => none
      else none
  | .catalogue3 id1 a1 b1 c1, .catalogue3 id2 a2 b2 c2, σ =>
      if decide (id1 = id2) then
        match matchPat pVars a1 a2 σ with
        | some σ1 =>
            match matchPat pVars b1 b2 σ1 with
            | some σ2 => matchPat pVars c1 c2 σ2
            | none    => none
        | none => none
      else none
  | .quote b1, .quote b2, σ => if decide (b1 = b2) then some σ else none
  | .fix n1 t1 b1, .fix n2 t2 b2, σ =>
      if n1 = n2 && decide (t1 = t2) then matchPat pVars b1 b2 σ else none
  | p, t, σ =>
      -- Primitive leaves match iff identical.
      if decide (p = t) then some σ else none

/-! ## § 6  RHS instantiation (template substitution) -/

/-- Apply a substitution to a template Tm.  Pattern-var names in `pVars`
    that are bound by `σ` are replaced; binders shadow as usual. -/
def instantiate (pVars : List String) (σ : Subst) : Tm → Tm
  | .var n =>
      if pVars.contains n then
        match σ.lookup n with
        | some t => t
        | none   => .var n
      else .var n
  | .abs n t body =>
      -- Binders shadow pattern names: if n is a pattern var, drop it
      -- from the scope during body instantiation.
      let pVars' := pVars.filter (· ≠ n)
      .abs n t (instantiate pVars' σ body)
  | .app f x => .app (instantiate pVars σ f) (instantiate pVars σ x)
  | .catalogue1 id a => .catalogue1 id (instantiate pVars σ a)
  | .catalogue2 id a b => .catalogue2 id (instantiate pVars σ a) (instantiate pVars σ b)
  | .catalogue3 id a b c =>
      .catalogue3 id (instantiate pVars σ a) (instantiate pVars σ b) (instantiate pVars σ c)
  | .quote b => .quote b
  | .fix n t body =>
      let pVars' := pVars.filter (· ≠ n)
      .fix n t (instantiate pVars' σ body)
  | t => t  -- literals + primitives

/-! ## § 7  Single-step rule application -/

/-- Try every rule in `env` against `t` at the **root**; return the first
    rewritten Tm, or `none` if no rule fires. -/
def tryRulesRoot (env : RewriteEnv) (t : Tm) : Option Tm :=
  env.findSome? fun r =>
    match matchPat r.vars r.lhs t [] with
    | some σ => some (instantiate r.vars σ r.rhs)
    | none   => none

/-- Bottom-up single-pass rewrite: rewrite children first, then try root.

    Fuel-bounded; if a rule fires we **restart** the bottom-up walk with
    decremented fuel to handle cascading rewrites (e.g. `错 错 错 错 X` →
    `错 错 X` → `X` takes 2 passes). -/
partial def normalizeAux (env : RewriteEnv) : Nat → Tm → Tm
  | 0, t => t
  | n+1, t =>
    let t' := rewriteBottomUp t
    match tryRulesRoot env t' with
    | some t'' => normalizeAux env n t''
    | none     => t'
where
  rewriteBottomUp : Tm → Tm
    | .abs nm ty body =>
        let body' := rewriteBottomUp body
        let cand := Tm.abs nm ty body'
        match tryRulesRoot env cand with
        | some t' => t'
        | none    => cand
    | .app f x =>
        let f' := rewriteBottomUp f
        let x' := rewriteBottomUp x
        let cand := Tm.app f' x'
        match tryRulesRoot env cand with
        | some t' => t'
        | none    => cand
    | .catalogue1 id a =>
        let a' := rewriteBottomUp a
        let cand := Tm.catalogue1 id a'
        match tryRulesRoot env cand with
        | some t' => t'
        | none    => cand
    | .catalogue2 id a b =>
        let a' := rewriteBottomUp a
        let b' := rewriteBottomUp b
        let cand := Tm.catalogue2 id a' b'
        match tryRulesRoot env cand with
        | some t' => t'
        | none    => cand
    | .catalogue3 id a b c =>
        let a' := rewriteBottomUp a
        let b' := rewriteBottomUp b
        let c' := rewriteBottomUp c
        let cand := Tm.catalogue3 id a' b' c'
        match tryRulesRoot env cand with
        | some t' => t'
        | none    => cand
    | .fix nm ty body =>
        let body' := rewriteBottomUp body
        let cand := Tm.fix nm ty body'
        match tryRulesRoot env cand with
        | some t' => t'
        | none    => cand
    | t => t  -- leaves (var / hexLit / boolLit / cellLit / primitives / quote)

/-- Public entry: apply `env`'s rules to `t` with a default fuel budget. -/
def normalize (env : RewriteEnv) (t : Tm) : Tm :=
  normalizeAux env 64 t

/-! ## § 8  Rule construction + confluence check -/

/-- Errors specific to rewrite-rule declarations (wen-2.0 ⑫).

    These wrap into `DefErr` via `ProgramErrWithDefs` at the call site in
    `EndToEnd.lean`.
-/
inductive RewriteErr where
  | emptyLhs
  | emptyRhs
  | nonLinearLhs       (vars : List String)
  | rhsExtraVars       (extra : List String)
  | overlapWithExisting (newHead existingHead : HeadTag)
  | lhsIsBareVar       -- LHS is a single pattern var — would rewrite EVERYTHING
deriving Repr

/-- Validate a candidate rule and (if valid) extend the env.

    Checks:
    1. LHS must not be a bare pattern variable (would match every Tm and
       trivially diverge).
    2. LHS must be linear in its pattern vars.
    3. RHS must use only vars declared on the LHS.
    4. The new rule's head tag must not collide with any existing rule
       (v1 confluence: disjoint heads).

    Returns the extended env on success, or the offending `RewriteErr`. -/
def addRule (env : RewriteEnv) (lhs rhs : Tm)
    : Except RewriteErr RewriteEnv :=
  let pVars := freeVars lhs
  -- (1) bare-var guard.
  match lhs with
  | .var _ => .error .lhsIsBareVar
  | _ =>
    -- (2) linearity.
    if !isLinearPattern lhs then
      .error (.nonLinearLhs pVars)
    else
      -- (3) RHS uses only declared vars.
      let rhsVars := freeVars rhs
      let extra := rhsVars.filter (fun n => !pVars.contains n)
      if !extra.isEmpty then
        .error (.rhsExtraVars extra)
      else
        -- (4) head-tag disjointness with existing rules.
        let newHead := headTag lhs
        match env.find? (fun r => decide (headTag r.lhs = newHead)) with
        | some r => .error (.overlapWithExisting newHead (headTag r.lhs))
        | none   =>
            let rule : RewriteRule := { lhs := lhs, rhs := rhs, vars := pVars }
            .ok (env ++ [rule])

/-! ## § 9  Sanity examples -/

/-- Free-var collection: binders shadow correctly. -/
example : freeVars (.abs "x" .hex (.var "x")) = [] := by native_decide

example : freeVars (.app (.var "f") (.var "x")) = ["f", "x"] := by native_decide

example :
    freeVars (.catalogue1 .Z_5 (.catalogue1 .Z_5 (.var "甲"))) = ["甲"] := by
  native_decide

/-- Linearity: a var appearing twice on LHS is non-linear. -/
example :
    isLinearPattern (.app (.var "x") (.var "x")) = false := by native_decide

example :
    isLinearPattern (.app (.var "x") (.var "y")) = true := by native_decide

/-- Head tags discriminate constructors. -/
example : headTag (.catalogue1 .Z_5 .yi) = .cat1H := by native_decide
example : headTag (.app .notB (.boolLit true)) = .appH := by native_decide
example : headTag .yi = .primH 1 := by native_decide

/-- Single-rule normalize: `错 错 X` → `X`. -/
example :
    let rule : RewriteRule :=
      { lhs := .catalogue1 .Z_5 (.catalogue1 .Z_5 (.var "甲"))
      , rhs := .var "甲"
      , vars := ["甲"] }
    normalize [rule]
        (.catalogue1 .Z_5 (.catalogue1 .Z_5 (.hexLit SSBX.Foundation.Yi.Yi.«乾»)))
      = .hexLit SSBX.Foundation.Yi.Yi.«乾» := by native_decide

/-- Cascade: `错 错 错 错 X` → `X` via two rule firings. -/
example :
    let rule : RewriteRule :=
      { lhs := .catalogue1 .Z_5 (.catalogue1 .Z_5 (.var "甲"))
      , rhs := .var "甲"
      , vars := ["甲"] }
    normalize [rule]
        (.catalogue1 .Z_5 (.catalogue1 .Z_5
          (.catalogue1 .Z_5 (.catalogue1 .Z_5
            (.hexLit SSBX.Foundation.Yi.Yi.«乾»)))))
      = .hexLit SSBX.Foundation.Yi.Yi.«乾» := by native_decide

/-- A rule that doesn't fire is a no-op. -/
example :
    let rule : RewriteRule :=
      { lhs := .catalogue1 .Z_5 (.catalogue1 .Z_5 (.var "甲"))
      , rhs := .var "甲"
      , vars := ["甲"] }
    normalize [rule] (.app .notB (.boolLit true))
      = .app .notB (.boolLit true) := by native_decide

/-- addRule: simple successful add. -/
example :
    let lhs := Tm.catalogue1 .Z_5 (.catalogue1 .Z_5 (.var "甲"))
    let rhs := Tm.var "甲"
    (addRule [] lhs rhs).toOption.map List.length = some 1 := by native_decide

/-- addRule: bare-var LHS rejected. -/
example :
    addRule [] (Tm.var "x") (Tm.var "x")
      = .error .lhsIsBareVar := by native_decide

/-- addRule: non-linear LHS rejected. -/
example :
    addRule [] (Tm.app (.var "x") (.var "x")) (.var "x")
      = .error (.nonLinearLhs ["x"]) := by native_decide

/-- addRule: extra RHS vars rejected. -/
example :
    (match addRule [] (Tm.catalogue1 .Z_5 (.var "x")) (.var "y") with
     | .error (.rhsExtraVars ["y"]) => true
     | _ => false) = true := by native_decide

/-- addRule: head-tag overlap rejected. -/
example :
    let lhs1 := Tm.catalogue1 .Z_5 (.catalogue1 .Z_5 (.var "x"))
    let lhs2 := Tm.catalogue1 .Z_6 (.catalogue1 .Z_6 (.var "y"))
    (match
       (do
         let env1 ← addRule [] lhs1 (.var "x")
         addRule env1 lhs2 (.var "y")) with
     | .error (.overlapWithExisting .cat1H .cat1H) => true
     | _ => false) = true := by native_decide

/-- addRule: disjoint heads OK. -/
example :
    let lhs1 := Tm.catalogue1 .Z_5 (.catalogue1 .Z_5 (.var "x"))
    let lhs2 := Tm.app .notB (.app .notB (.var "y"))
    ((do
        let env1 ← addRule [] lhs1 (.var "x")
        addRule env1 lhs2 (.var "y"))).toOption.map List.length = some 2 := by
  native_decide

end SSBX.Foundation.Wen.WenSurface
