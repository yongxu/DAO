/-
# WenSurface.TypeInfer — Hindley-Milner type inference for Wen 2.0 ①

Replaces the ad-hoc 5-candidate domain-type trial used by the elaborator
for `者 NAME body` (lambda binders) with constraint-based unification over
`Ty` extended with metavariables.

## Design

* `MTy`: `Ty` extended with `.mvar Nat` (type metavariables).
* `Subst`: total `Nat → Option MTy` represented as `List (Nat × MTy)`.
* `unify` with occurs-check; substitution composition is folded in via
  `Subst.lookup` recursing under `apply`.
* `infer : InferCtx → Tm → InferM MTy` walks the `Tm`, generating fresh
  metavars only for binder domains whose annotation is `.mvar _` (which is
  what the elaborator emits when it does not yet know the domain).
* `zonk` finalises `MTy → Ty`, defaulting unsolved vars to `.hex` so the
  resulting `Tm` typechecks with the kernel `WenDef.typeCheck`.

## Scope

The inference here is **monomorphic** Hindley-Milner over the finite Wen
type system (no generalisation; no type-schemes; no row types).  This is
sufficient because every Wen `Tm` constant has a closed monotype and the
only unknowns are binder-domain annotations.

## Status

0 sorry / 0 axiom / total.  All combinators are structurally recursive
with explicit fuel where unification's substitution depth needs bounding.
-/
import SSBX.Foundation.Wen.WenDef
import SSBX.Text.OperatorSignatures

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Wen.WenDef
open SSBX.Text.OperatorSignatures

/-! ## § 1  Meta types -/

/-- Wen type extended with unification metavariables. -/
inductive MTy : Type
  | mvar (id : Nat)
  | hex
  | bool
  | cell
  | catalogue (kind : SignatureKind)
  | prod (fst snd : MTy)
  | list (elem : MTy)
  | arr (dom cod : MTy)
  | quoted
  /-- wen-2.0 ④ user inductive nominal type (mirrors `Ty.user`). -/
  | user (name : String)
  /-- wen-2.0 ⑦: predicate-extension set type, mirrors `Ty.set`. -/
  | set (elem : MTy)
deriving DecidableEq, Repr

/-- Lift a closed `Ty` into `MTy` (no metavariables introduced). -/
def MTy.ofTy : Ty → MTy
  | .hex => .hex
  | .bool => .bool
  | .cell => .cell
  | .catalogue k => .catalogue k
  | .prod a b => .prod (MTy.ofTy a) (MTy.ofTy b)
  | .list a => .list (MTy.ofTy a)
  | .arr a b => .arr (MTy.ofTy a) (MTy.ofTy b)
  | .quoted => .quoted
  | .user n => .user n
  | .set a => .set (MTy.ofTy a)

/-- Total substitution: list of `(id, MTy)` pairs.  Lookup is first-match. -/
abbrev Subst := List (Nat × MTy)

def Subst.empty : Subst := []

def Subst.lookup : Subst → Nat → Option MTy
  | [], _ => none
  | (i, t) :: rest, j => if i = j then some t else Subst.lookup rest j

/-- Apply a substitution structurally; fuel-bounded to keep totality.
    `fuel = nat-depth-of-chain`; in practice 64 suffices (we never build
    chains longer than the number of mvars). -/
def MTy.apply : Nat → Subst → MTy → MTy
  | 0,    _, t => t
  | _+1,  _, .hex => .hex
  | _+1,  _, .bool => .bool
  | _+1,  _, .cell => .cell
  | _+1,  _, .quoted => .quoted
  | _+1,  _, .catalogue k => .catalogue k
  | _+1,  _, .user n => .user n
  | n+1,  s, .prod a b => .prod (MTy.apply n s a) (MTy.apply n s b)
  | n+1,  s, .list a => .list (MTy.apply n s a)
  | n+1,  s, .arr a b => .arr (MTy.apply n s a) (MTy.apply n s b)
  | n+1,  s, .set a => .set (MTy.apply n s a)
  | n+1,  s, .mvar i =>
      match s.lookup i with
      | some t => MTy.apply n s t
      | none => .mvar i

/-- Default fuel for substitution chains: 64 is more than enough for the
    finite Wen surface (binder nest depth ≤ small constant). -/
def applyFuel : Nat := 64

def MTy.applyS (s : Subst) (t : MTy) : MTy := MTy.apply applyFuel s t

/-! ## § 2  Occurs check -/

def MTy.occurs (i : Nat) : MTy → Bool
  | .mvar j => decide (i = j)
  | .hex | .bool | .cell | .quoted | .catalogue _ | .user _ => false
  | .prod a b => MTy.occurs i a || MTy.occurs i b
  | .list a => MTy.occurs i a
  | .arr a b => MTy.occurs i a || MTy.occurs i b
  | .set a => MTy.occurs i a

/-! ## § 3  Unification -/

inductive UnifyErr where
  | mismatch (a b : MTy)
  | occursCheck (i : Nat) (t : MTy)
deriving DecidableEq, Repr

/-- Bind metavar `i ↦ t` after occurs-check, returning extended substitution. -/
def bindVar (s : Subst) (i : Nat) (t : MTy) : Except UnifyErr Subst :=
  match t with
  | .mvar j => if i = j then .ok s else .ok ((i, .mvar j) :: s)
  | _ =>
      if MTy.occurs i t then .error (.occursCheck i t)
      else .ok ((i, t) :: s)

/-- Robinson unification with fuel.  The fuel bound is structural: we
    consume one unit per recursive call, which is bounded by the structural
    sum of the two MTys after applying `s`. -/
def unify : Nat → Subst → MTy → MTy → Except UnifyErr Subst
  | 0, _, _, _ => .error (.mismatch .hex .hex)  -- fuel exhausted (unreachable in practice)
  | n+1, s, a, b =>
      let a' := MTy.applyS s a
      let b' := MTy.applyS s b
      match a', b' with
      | .mvar i, .mvar j => if i = j then .ok s else bindVar s i (.mvar j)
      | .mvar i, t => bindVar s i t
      | t, .mvar i => bindVar s i t
      | .hex, .hex => .ok s
      | .bool, .bool => .ok s
      | .cell, .cell => .ok s
      | .quoted, .quoted => .ok s
      | .catalogue k1, .catalogue k2 =>
          if k1 = k2 then .ok s else .error (.mismatch a' b')
      -- wen-2.0 ④ user types unify iff their names match exactly.
      -- `.mvar ↔ .user` is handled by the mvar cases above.
      | .user n1, .user n2 =>
          if n1 = n2 then .ok s else .error (.mismatch a' b')
      | .prod x1 y1, .prod x2 y2 =>
          match unify n s x1 x2 with
          | .error e => .error e
          | .ok s' => unify n s' y1 y2
      | .list x1, .list x2 => unify n s x1 x2
      | .arr x1 y1, .arr x2 y2 =>
          match unify n s x1 x2 with
          | .error e => .error e
          | .ok s' => unify n s' y1 y2
      | .set x1, .set x2 => unify n s x1 x2
      | _, _ => .error (.mismatch a' b')

def unifyFuel : Nat := 256

def unifyTop (s : Subst) (a b : MTy) : Except UnifyErr Subst :=
  unify unifyFuel s a b

/-! ## § 4  Inference state + monad-ish helpers -/

structure InferState where
  next  : Nat
  subst : Subst
deriving Repr

def InferState.empty : InferState := { next := 0, subst := Subst.empty }

/-- Fresh metavariable; returns `(MTy.mvar fresh, state')`. -/
def freshMVar (st : InferState) : MTy × InferState :=
  (.mvar st.next, { st with next := st.next + 1 })

inductive InferErr where
  | unknownVar (name : String)
  | unifyFail (e : UnifyErr)
deriving Repr

abbrev MCtx := List (String × MTy)

def MCtx.lookup : MCtx → String → Option MTy
  | [], _ => none
  | (n, t) :: rest, name => if n = name then some t else MCtx.lookup rest name

/-! ## § 5  Built-in monotypes -/

/-- Closed monotype for every `Tm` constant.  Mirrors `WenDef.typeCheck`
    but in `MTy`.  Constants never introduce metavariables. -/
def builtinType : Tm → Option MTy
  | .jia       => some (.arr .hex (.arr .hex .hex))
  | .yi        => some .hex
  | .notB      => some (.arr .bool .bool)
  | .andB      => some (.arr .bool (.arr .bool .bool))
  | .orB       => some (.arr .bool (.arr .bool .bool))
  | .eqHex     => some (.arr .hex (.arr .hex .bool))
  | .forallH   => some (.arr (.arr .hex .bool) .bool)
  | .uniqueH   => some (.arr (.arr .hex .bool) .bool)
  | .exactly3H => some (.arr (.arr .hex .bool) .bool)
  | .majorityH => some (.arr (.arr .hex .bool) .bool)
  | .cuoH | .zongH | .huH | .cuoZongH
  | .flip1H | .flip2H | .flip3H | .flip4H | .flip5H | .flip6H =>
      some (.arr .hex .hex)
  | .pairH     => some (.arr .hex (.arr .hex (.prod .hex .hex)))
  | .dupH      => some (.arr .hex (.prod .hex .hex))
  | .list1H    => some (.arr .hex (.list .hex))
  | .list2H    => some (.arr .hex (.arr .hex (.list .hex)))
  | .list3H    => some (.arr .hex (.arr .hex (.arr .hex (.list .hex))))
  | .headH     => some (.arr (.list .hex) .hex)
  | .eqCell    => some (.arr .cell (.arr .cell .bool))
  | .cuoC | .zongC | .huC | .shiNextC | .shiPrevC
  | .flip1C | .flip2C | .flip3C | .flip4C | .flip5C | .flip6C =>
      some (.arr .cell .cell)
  | _ => none

/-! ## § 6  Catalogue argument type expectation in MTy land -/

def catalogueExpectedArgMTy (kind : SignatureKind) (pos : Nat) : MTy :=
  MTy.ofTy (catalogueExpectedArgTy kind pos)

/-! ## § 7  Inference -/

/-- Unify the given two MTys in the state's substitution; returns updated state. -/
def InferState.unify (st : InferState) (a b : MTy) : Except InferErr InferState :=
  match unifyTop st.subst a b with
  | .ok s' => .ok { st with subst := s' }
  | .error e => .error (.unifyFail e)

/-- Bidirectional infer: returns the term's MTy and the updated state.
    Fuel is the structural depth of the Tm; `4 * sizeOf Tm + 16` suffices in
    practice (each Tm constructor adds at most one recursive call). -/
def infer : Nat → MCtx → Tm → InferState →
    Except InferErr (MTy × InferState)
  | 0,    _,   _, _ => .error (.unknownVar "<fuel>")
  | _+1,  ctx, .var n, st =>
      match MCtx.lookup ctx n with
      | some t => .ok (t, st)
      | none => .error (.unknownVar n)
  | n+1,  ctx, .abs name dom body, st =>
      -- wen-2.0 ④: when the elaborator's prior guess is a user-inductive
      -- nominal type (`.user`), preserve it as-is — HM has no way to
      -- *infer* a user-type binder (no constraints from primitive ops
      -- could narrow `α` to `.user "X"`), so we honour the annotation.
      -- For all other binder annotations (`.hex`, `.bool`, ...), HM
      -- ignores the prior guess and uses a fresh metavar α, letting
      -- `body`'s usage constrain it via app/catalogue unifications.
      match dom with
      | .user _ =>
          match infer n ((name, MTy.ofTy dom) :: ctx) body st with
          | .error e => .error e
          | .ok (tb, st2) => .ok (.arr (MTy.ofTy dom) tb, st2)
      | _ =>
          let (alpha, st1) := freshMVar st
          match infer n ((name, alpha) :: ctx) body st1 with
          | .error e => .error e
          | .ok (tb, st2) => .ok (.arr alpha tb, st2)
  | n+1,  ctx, .app f x, st =>
      match infer n ctx f st with
      | .error e => .error e
      | .ok (tf, st1) =>
          match infer n ctx x st1 with
          | .error e => .error e
          | .ok (tx, st2) =>
              let (beta, st3) := freshMVar st2
              match st3.unify tf (.arr tx beta) with
              | .error e => .error e
              | .ok st4 => .ok (beta, st4)
  | _+1,  _, .hexLit _,  st => .ok (.hex, st)
  | _+1,  _, .boolLit _, st => .ok (.bool, st)
  | _+1,  _, .cellLit _, st => .ok (.cell, st)
  | n+1,  ctx, .catalogue1 id a, st =>
      let sig := fullSignatureFor id
      match infer n ctx a st with
      | .error e => .error e
      | .ok (ta, st1) =>
          match st1.unify ta (catalogueExpectedArgMTy sig.kind 0) with
          | .error e =>
              -- wen-2.0 ⑥: textAct's last positional arg may be `.quoted`.
              if sig.kind = .textAct && sig.arity = 1 then
                match st1.unify ta .quoted with
                | .ok st2 => .ok (.catalogue sig.kind, st2)
                | .error _ => .error e
              else .error e
          | .ok st2 => .ok (.catalogue sig.kind, st2)
  | n+1,  ctx, .catalogue2 id a b, st =>
      let sig := fullSignatureFor id
      match infer n ctx a st with
      | .error e => .error e
      | .ok (ta, st1) =>
          match st1.unify ta (catalogueExpectedArgMTy sig.kind 0) with
          | .error e => .error e
          | .ok st2 =>
              match infer n ctx b st2 with
              | .error e => .error e
              | .ok (tb, st3) =>
                  let expected1 := catalogueExpectedArgMTy sig.kind 1
                  match st3.unify tb expected1 with
                  | .ok st4 => .ok (.catalogue sig.kind, st4)
                  | .error e =>
                      if sig.kind = .textAct && sig.arity = 2 then
                        match st3.unify tb .quoted with
                        | .ok st4 => .ok (.catalogue sig.kind, st4)
                        | .error _ => .error e
                      else .error e
  | n+1,  ctx, .catalogue3 id a b c, st =>
      let sig := fullSignatureFor id
      match infer n ctx a st with
      | .error e => .error e
      | .ok (ta, st1) =>
          match st1.unify ta (catalogueExpectedArgMTy sig.kind 0) with
          | .error e => .error e
          | .ok st2 =>
              match infer n ctx b st2 with
              | .error e => .error e
              | .ok (tb, st3) =>
                  match st3.unify tb (catalogueExpectedArgMTy sig.kind 1) with
                  | .error e => .error e
                  | .ok st4 =>
                      match infer n ctx c st4 with
                      | .error e => .error e
                      | .ok (tc, st5) =>
                          let expected2 := catalogueExpectedArgMTy sig.kind 2
                          match st5.unify tc expected2 with
                          | .ok st6 => .ok (.catalogue sig.kind, st6)
                          | .error e =>
                              if sig.kind = .textAct && sig.arity = 3 then
                                match st5.unify tc .quoted with
                                | .ok st6 => .ok (.catalogue sig.kind, st6)
                                | .error _ => .error e
                              else .error e
  | _+1,  _, .quote _, st => .ok (.quoted, st)
  -- wen-2.0 ④ user-ctor: typechecks to `.user typeName` (table validity is
  -- enforced upstream in the surface elaborator).
  | _+1,  _, .userCtor tn _, st => .ok (.user tn, st)
  -- wen-2.0 ⑦: setOf pred — infer pred, unify with `α → Bool`, result `set α`.
  | n+1,  ctx, .setOf pred, st =>
      match infer n ctx pred st with
      | .error e => .error e
      | .ok (tp, st1) =>
          let (alpha, st2) := freshMVar st1
          match st2.unify tp (.arr alpha .bool) with
          | .error e => .error e
          | .ok st3 => .ok (.set alpha, st3)
  -- wen-2.0 ⑦: memberOf x s — s : set α, x : α, result Bool.
  | n+1,  ctx, .memberOf x s, st =>
      match infer n ctx s st with
      | .error e => .error e
      | .ok (ts, st1) =>
          let (alpha, st2) := freshMVar st1
          match st2.unify ts (.set alpha) with
          | .error e => .error e
          | .ok st3 =>
              match infer n ctx x st3 with
              | .error e => .error e
              | .ok (tx, st4) =>
                  match st4.unify tx alpha with
                  | .error e => .error e
                  | .ok st5 => .ok (.bool, st5)
  | _+1,  _, t, st =>
      match builtinType t with
      | some ty => .ok (ty, st)
      | none => .error (.unknownVar "<unsupported>")

/-! ## § 8  Zonking — collapse MTy → Ty, defaulting unsolved vars -/

/-- Default for unsolved metavariables.  `Hex` is the canonical Wen
    universe element. -/
def defaultTy : Ty := .hex

/-- Zonk: walk MTy structurally, looking up each mvar in `s`.  Unsolved
    vars become `defaultTy`.  Fuel-bounded for totality. -/
def zonk : Nat → Subst → MTy → Ty
  | 0,    _, _ => defaultTy
  | _+1,  _, .hex => .hex
  | _+1,  _, .bool => .bool
  | _+1,  _, .cell => .cell
  | _+1,  _, .quoted => .quoted
  | _+1,  _, .catalogue k => .catalogue k
  | _+1,  _, .user n => .user n
  | n+1,  s, .prod a b => .prod (zonk n s a) (zonk n s b)
  | n+1,  s, .list a => .list (zonk n s a)
  | n+1,  s, .arr a b => .arr (zonk n s a) (zonk n s b)
  | n+1,  s, .set a => .set (zonk n s a)
  | n+1,  s, .mvar i =>
      match s.lookup i with
      | some t => zonk n s t
      | none => defaultTy

def zonkFuel : Nat := 64

def zonkTop (s : Subst) (t : MTy) : Ty := zonk zonkFuel s t

/-! ## § 9  Rewrite Tm — fill in binder domain annotations from substitution -/

/-- Walk the `Tm`, replacing every `.abs name dom body` with `.abs name dom'
    body'` where `dom'` is computed by zonking the metavariable assigned to
    that binder during inference.  We rebuild from scratch using a parallel
    walk; metavariables are introduced left-to-right matching `infer`. -/
def reannotate : Nat → MCtx → Subst → InferState → Tm → Tm × InferState
  | 0,    _, _, st, t => (t, st)
  | _+1,  _, _, st, .var n => (.var n, st)
  | n+1,  ctx, s, st, .abs name dom body =>
      -- wen-2.0 ④: preserve `.user` annotations (mirrors `infer`).
      match dom with
      | .user _ =>
          let (body', st1) := reannotate n ((name, MTy.ofTy dom) :: ctx) s st body
          (.abs name dom body', st1)
      | _ =>
          let (alpha, st1) := freshMVar st
          let dom' := zonkTop s alpha
          let (body', st2) := reannotate n ((name, alpha) :: ctx) s st1 body
          (.abs name dom' body', st2)
  | n+1,  ctx, s, st, .app f x =>
      let (f', st1) := reannotate n ctx s st f
      let (x', st2) := reannotate n ctx s st1 x
      (.app f' x', st2)
  | n+1,  ctx, s, st, .catalogue1 id a =>
      let (a', st1) := reannotate n ctx s st a
      (.catalogue1 id a', st1)
  | n+1,  ctx, s, st, .catalogue2 id a b =>
      let (a', st1) := reannotate n ctx s st a
      let (b', st2) := reannotate n ctx s st1 b
      (.catalogue2 id a' b', st2)
  | n+1,  ctx, s, st, .catalogue3 id a b c =>
      let (a', st1) := reannotate n ctx s st a
      let (b', st2) := reannotate n ctx s st1 b
      let (c', st3) := reannotate n ctx s st2 c
      (.catalogue3 id a' b' c', st3)
  | _+1,  _, _, st, .quote body =>
      -- Quote bodies are opaque to inference; preserve as-is.
      (.quote body, st)
  -- wen-2.0 ⑦: setOf / memberOf — recurse structurally.
  | n+1,  ctx, s, st, .setOf pred =>
      let (pred', st1) := reannotate n ctx s st pred
      (.setOf pred', st1)
  | n+1,  ctx, s, st, .memberOf x set =>
      let (x', st1) := reannotate n ctx s st x
      let (set', st2) := reannotate n ctx s st1 set
      (.memberOf x' set', st2)
  | _+1,  _, _, st, t => (t, st)

/-! ## § 10  Top-level: infer + reannotate -/

/-- Re-elaborate binder domains in `tm` using HM inference.  If inference
    fails, returns the original `tm` unchanged (the caller's typecheck will
    then surface the original error).  If inference succeeds, returns a
    `Tm` whose `.abs` annotations are zonked from the substitution. -/
def inferAndReannotate (tm : Tm) : Tm :=
  let initState := InferState.empty
  let fuel := 1024
  match infer fuel [] tm initState with
  | .error _ => tm
  | .ok (_, st) =>
      let (tm', _) := reannotate fuel [] st.subst InferState.empty tm
      tm'

/-- Run HM on `.abs name placeholderDom body` and return only the
    HM-inferred domain `Ty` for `name`.  Useful when the caller wants to
    drive a single elaboration pass with a known-good domain and let the
    kernel `typeCheck` derive the codomain naturally — this preserves
    legacy back-compat for cases where HM's principal codomain (default
    `.hex`) differs from the legacy candidate-trial's chosen codomain.

    Returns `none` if HM inference itself fails. -/
def inferBinderDomain (ctxTys : List (String × Ty)) (name : String) (body : Tm) : Option Ty :=
  let initState := InferState.empty
  let fuel := 1024
  -- Lift the caller's `Ctx` into `MCtx` with no metavars (caller's
  -- previously chosen binder domains are taken as ground truth).
  let mctx : MCtx := ctxTys.map (fun ⟨n, ty⟩ => (n, MTy.ofTy ty))
  let candidate : Tm := .abs name .hex body
  match infer fuel mctx candidate initState with
  | .error _ => none
  | .ok (resTy, st) =>
      -- `resTy = .arr α β` where α is the binder's fresh mvar; zonk α.
      match resTy with
      | .arr α _ => some (zonkTop st.subst α)
      | _ => none

/-- The legacy candidate domain list, kept here for back-compat
    defaulting.  HM produces a valid principal-type instance, but for
    cases where multiple principal-type instances exist (e.g. higher-
    order `者 甲 甲 之 真`, where both `(Bool→Hex)→Hex` and
    `(Bool→Bool)→Bool` are valid), we prefer the legacy choice so
    existing test fixtures continue to match.

    Order matches `binderDomainCandidates` in `WenSurface.Syntax`. -/
def legacyBinderDomainCandidates : List Ty :=
  [ .hex
  , .bool
  , .arr .hex .hex
  , .arr .hex .bool
  , .arr .bool .bool
  , .arr .bool .hex ]

/-- Check that HM's inferred domain for `name` in `body`, when used as
    the binder's `dom`, is consistent (HM admits this assignment). -/
def hmAdmitsDomain (ctxTys : List (String × Ty)) (name : String) (dom : Ty) (body : Tm) : Bool :=
  let initState := InferState.empty
  let fuel := 1024
  let mctx : MCtx := (name, MTy.ofTy dom) :: ctxTys.map (fun ⟨n, ty⟩ => (n, MTy.ofTy ty))
  match infer fuel mctx body initState with
  | .ok _ => true
  | .error _ => false

/-- Pick the first legacy candidate domain that HM accepts.  This is the
    Wen 2.0 ① replacement for the elaborator's hand-rolled 6-candidate
    trial: we still iterate the legacy list, but **HM is the predicate**
    (rather than re-running the elaborator + typecheck for each guess).

    Returns `none` if no candidate is HM-admissible. -/
def pickBinderDomain (ctxTys : List (String × Ty)) (name : String) (body : Tm) : Option Ty :=
  legacyBinderDomainCandidates.find? (fun dom => hmAdmitsDomain ctxTys name dom body)

/-! ## § 11  Sanity examples -/

/-- Unify two equal hex types — no substitution change. -/
example : (unifyTop [] .hex .hex).toOption = some [] := by native_decide

/-- Mvar 0 unifies with .bool, producing `[(0, .bool)]`. -/
example : (unifyTop [] (.mvar 0) .bool).toOption = some [(0, .bool)] := by
  native_decide

/-- Occurs check fires for `α ~ α → β`. -/
example :
    (match unifyTop [] (.mvar 0) (.arr (.mvar 0) .hex) with
     | .error (.occursCheck 0 _) => true
     | _ => false) = true := by native_decide

/-- Zonk a fully solved chain. -/
example : zonkTop [(0, .bool)] (.mvar 0) = .bool := by native_decide

/-- Zonk an unsolved var defaults to .hex. -/
example : zonkTop [] (.mvar 99) = .hex := by native_decide

/-- HM infers `λx. x` at `Hex → Hex` (default for unsolved binder). -/
example :
    typeCheck [] (inferAndReannotate (.abs "x" .hex (.var "x")))
      = some (.arr .hex .hex) := by native_decide

/-- HM infers `λx. notB x` at `Bool → Bool`, regardless of prior guess. -/
example :
    typeCheck [] (inferAndReannotate (.abs "x" .hex (.app .notB (.var "x"))))
      = some (.arr .bool .bool) := by native_decide

/-- HM infers `λx. jia x x` at `Hex → Hex`. -/
example :
    typeCheck [] (inferAndReannotate
        (.abs "x" .bool (.app (.app .jia (.var "x")) (.var "x"))))
      = some (.arr .hex .hex) := by native_decide

/-- HM infers higher-order `λf. f 一` at `(Hex → α) → α`, where unsolved α
    defaults to Hex.  Resulting kernel type is `(Hex → Hex) → Hex`. -/
example :
    typeCheck [] (inferAndReannotate
        (.abs "f" .hex (.app (.var "f") .yi)))
      = some (.arr (.arr .hex .hex) .hex) := by native_decide

/-! ### wen-2.0 ④ HM unification on user types -/

/-- Same-name `.user` types unify. -/
example : (unifyTop [] (.user "五行") (.user "五行")).toOption = some [] := by
  native_decide

/-- Different-name `.user` types fail to unify. -/
example :
    (match unifyTop [] (.user "五行") (.user "真假") with
     | .error (.mismatch _ _) => true
     | _ => false) = true := by native_decide

/-- `.mvar` unifies with `.user`. -/
example :
    (unifyTop [] (.mvar 0) (.user "X")).toOption
      = some [(0, .user "X")] := by native_decide

/-- `.user "X"` does not unify with `.hex` (nominal types are disjoint
    from primitive types). -/
example :
    (match unifyTop [] (.user "X") .hex with
     | .error _ => true
     | _ => false) = true := by native_decide

/-- HM infers `λx. x` where `x : .user "X"` body returns `x`.  The binder
    must be annotated by the elaborator (HM defaults unsolved mvars to
    `.hex`); we test that ground-truth `.user` annotations round-trip. -/
example :
    typeCheck [] (inferAndReannotate (.abs "x" (.user "五行") (.var "x")))
      = some (.arr (.user "五行") (.user "五行")) := by native_decide

end SSBX.Foundation.Wen.WenSurface
