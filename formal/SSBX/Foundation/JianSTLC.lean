/-
# 間 之 核 — STLC simulation (Task #52 complete; axiom discharged)

  Per spec § 七 "STLC-complete": 者/之 (with optional 令) suffice to encode STLC.
  We work with the more general untyped λ-calculus (Lam) since type-erasure is sound.

  Scope of this file:
    - `Lam` inductive: var/abs/app, `Lam.size`, `Lam.yi`/`Lam.yi1` (atomic rename)
    - `Lam.subst`: capture-avoiding substitution (real def, well-founded on size)
    - `Lam.Beta`: one-step β-reduction relation
    - `enc : Lam → Wen`: structural encoding (var → atom, abs → 者, app → 之-pair)
    - `enc_freeVars`, `enc_yi`, `enc_yi1`, `subst_preserves_enc`: bridge lemmas
    - `simulation`: general STLC simulation theorem (no axioms — all lemmas proved)
    - Verified examples (native_decide): identity, K-combinator, S-K-K reduction

  ## 易 (yì) instead of `rename`

  Atomic name-transformation `yi : (String → String) → Lam → Lam` is fully
  structurally recursive — no shadow respect. For α-renaming inside `subst`,
  the target `b'` is fresh, so `yi` and any shadow-respecting variant produce
  α-equivalent results (Lean treats them as syntactically distinct, but
  semantically they're the same).

  Win: `yi_size` is a 4-line proof; the prior `rename_size` for shadow-
  respecting rename was 130 lines of pattern dispatch.
-/

import SSBX.Foundation.Jian

namespace SSBX.Foundation.JianSTLC

open SSBX.Foundation.Jian
open SSBX.Foundation.Jian.Wen

/-- λ-calculus syntax (untyped; STLC is the typed restriction).
    Three constructors: variable, abstraction, application. -/
inductive Lam : Type
  | var : String → Lam
  | abs : String → Lam → Lam
  | app : Lam → Lam → Lam
  deriving Repr, DecidableEq

namespace Lam

/-- Free variables of a λ-term. -/
def freeVars : Lam → List String
  | .var n => [n]
  | .abs b body => (freeVars body).filter (· ≠ b)
  | .app f x => freeVars f ++ freeVars x

/-- Generate a fresh name not in `used`. -/
def freshName (used : List String) (base : String) : String :=
  let candidates := (List.range (used.length + 1)).map (fun i => base ++ "_" ++ toString i)
  match candidates.find? (fun c => !(used.contains c)) with
  | some c => c
  | none => base ++ "_overflow"

/-- 易 (yì): atomic name-transformation on Lam. Lam analog of `Wen.yi`. -/
def yi (f : String → String) : Lam → Lam
  | .var n => .var (f n)
  | .abs x body => .abs (f x) (yi f body)
  | .app f' x => .app (yi f f') (yi f x)

instance : Inhabited Lam := ⟨.var ""⟩

/-- Tree-size on Lam (parallel to Wen.size). -/
def size : Lam → Nat
  | .var _ => 1
  | .abs _ body => 1 + body.size
  | .app f x => 1 + f.size + x.size

/-- 易 之 量 不变: atomic transformation preserves Lam-size. 4-line proof. -/
theorem yi_size (f : String → String) (t : Lam) :
    (yi f t).size = t.size := by
  induction t with
  | var n => rfl
  | abs x body ih => simp [yi, Lam.size, ih]
  | app f' x ih_f ih_x => simp [yi, Lam.size, ih_f, ih_x]

/-- Single-atom rename via 易. -/
def yi1 (b b' : String) : Lam → Lam :=
  yi (fun n => if n = b then b' else n)

theorem yi1_size (b b' : String) (t : Lam) :
    (yi1 b b' t).size = t.size :=
  yi_size _ t

/-- Capture-avoiding substitution. Parallels Wen.subst (mirrored α-renaming).
    Termination via well-founded recursion on `t.size`. -/
def subst : Lam → String → Lam → Lam
  | .var n, name, val => if n = name then val else .var n
  | .abs b body, name, val =>
      if b = name then .abs b body
      else if (freeVars val).contains b then
        let b' := freshName (freeVars body ++ freeVars val ++ [name]) b
        let body' := yi1 b b' body
        .abs b' (subst body' name val)
      else
        .abs b (subst body name val)
  | .app f x, name, val => .app (subst f name val) (subst x name val)
termination_by t _ _ => t.size
decreasing_by
  all_goals first
    | (simp_wf; simp only [Lam.size, Lam.yi1, Lam.yi_size]; omega)
    | (simp_wf; simp only [Lam.size]; omega)

/-- One-step β-reduction relation (allows reduction at any redex). -/
inductive Beta : Lam → Lam → Prop
  | beta (b : String) (body arg : Lam) :
      Beta (.app (.abs b body) arg) (Lam.subst body b arg)
  | congAppL (f f' x : Lam) : Beta f f' → Beta (.app f x) (.app f' x)
  | congAppR (f x x' : Lam) : Beta x x' → Beta (.app f x) (.app f x')
  | congAbs (b : String) (body body' : Lam) :
      Beta body body' → Beta (.abs b body) (.abs b body')

end Lam

/-- Structural encoding: λ-calc → Wen.
    var → atom (name);  abs → 者-form;  app → 之-pair. -/
def enc : Lam → Wen
  | .var n => .atom n
  | .abs b body => Zhe b (enc body)
  | .app f x => .pair (enc f) (enc x)

/-! ## § 七 STLC-completeness — verified examples -/

namespace Examples

/-- Identity combinator: `I = λx.x`. -/
def lamI : Lam := .abs "x" (.var "x")

/-- `I y` should reduce to `y`. -/
def lamI_y : Lam := .app lamI (.var "y")
def lamY : Lam := .var "y"

theorem encI_y_reduces_to_encY :
    reduceN 5 (enc lamI_y) = enc lamY := by native_decide

/-- K-combinator: `K = λx.λy.x`. -/
def lamK : Lam := .abs "x" (.abs "y" (.var "x"))

/-- `K a b` should reduce to `a`. -/
def lamK_a_b : Lam := .app (.app lamK (.var "a")) (.var "b")
def lamA : Lam := .var "a"

theorem encK_a_b_reduces_to_encA :
    reduceN 10 (enc lamK_a_b) = enc lamA := by native_decide

/-- KI ≡ K applied to I: `K I y = (λx.λy.x) I y → λy.I y → I`.
    Wait, more carefully: `K I = (λx.λy.x) I → λy.I`, and `(K I) y = (λy.I) y → I`. -/
def lamKI : Lam := .app lamK lamI
def lamKI_y : Lam := .app lamKI (.var "y")

theorem encKI_y_reduces_to_encI :
    reduceN 10 (enc lamKI_y) = enc lamI := by native_decide

/-- S-combinator: `S = λx.λy.λz. x z (y z)` — let's verify a partial application.
    S K K is the identity (`SKK x = K x (K x) = x`). Verify on a specific x. -/
def lamS : Lam :=
  .abs "x" (.abs "y" (.abs "z"
    (.app (.app (.var "x") (.var "z")) (.app (.var "y") (.var "z")))))

def lamSKK_z : Lam :=
  .app (.app (.app lamS lamK) lamK) (.var "z")

def lamZ : Lam := .var "z"

theorem encSKK_z_reduces_to_encZ :
    reduceN 30 (enc lamSKK_z) = enc lamZ := by native_decide

end Examples

/-! ## General simulation theorem

  Proof strategy: define a non-deterministic `Step` relation (allowing any redex,
  any choice), use its reflexive-transitive closure `Step.star`. Prove that
  λ-calculus β-reduction induces `Step.star` on encoded terms.

  The proof requires one substitution-preservation lemma which is currently an
  AXIOM — discharge requires theorem-level Wen.subst (replacing partial def via
  rename_size + sizeOf termination, tracked as Task #52). -/

/-- A single Step (any redex, restricted to rule 2 since STLC encoding only triggers β).
    We don't include all 9 rules here — only what STLC simulation needs. -/
inductive Step : Wen → Wen → Prop
  /-- Rule 2 (施之约): β-reduction via 者. Uses Jian.subst (capture-avoiding). -/
  | rule2 (b : String) (body arg : Wen) :
      Step (.pair (.pair (.op .zhe) (.pair (.atom b) body)) arg)
            (SSBX.Foundation.Jian.subst body b arg)
  /-- Congruence: reduce inside left of pair. -/
  | congPairL {l l' : Wen} (r : Wen) : Step l l' → Step (.pair l r) (.pair l' r)
  /-- Congruence: reduce inside right of pair. -/
  | congPairR (l : Wen) {r r' : Wen} : Step r r' → Step (.pair l r) (.pair l r')

/-- Reflexive-transitive closure: `t →* u`. Defined inline (no Mathlib dep). -/
inductive Step.star : Wen → Wen → Prop where
  | refl : Step.star t t
  | tail : Step.star a b → Step b c → Step.star a c

namespace Step.star

/-- Single-step → reflexive-transitive closure. -/
theorem single {a b : Wen} (h : Step a b) : Step.star a b :=
  .tail .refl h

/-- Transitivity of Step.star. -/
theorem trans {a b c : Wen} (h1 : Step.star a b) (h2 : Step.star b c) :
    Step.star a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact .tail ih hstep

/-- Lift Step* through the LEFT of a pair. -/
theorem congPairL {l l' : Wen} (h : Step.star l l') (r : Wen) :
    Step.star (.pair l r) (.pair l' r) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    exact .tail ih (Step.congPairL r hstep)

/-- Lift Step* through the RIGHT of a pair. -/
theorem congPairR (l : Wen) {r r' : Wen} (h : Step.star r r') :
    Step.star (.pair l r) (.pair l r') := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    exact .tail ih (Step.congPairR l hstep)

/-- Lift Step* through both sides of a pair. -/
theorem congPair {l l' r r' : Wen}
    (hl : Step.star l l') (hr : Step.star r r') :
    Step.star (.pair l r) (.pair l' r') :=
  Step.star.trans (congPairL hl r) (congPairR l' hr)

end Step.star

/-! ## Bridge lemmas: Lam ↔ Wen (free vars / rename / freshName commute with enc) -/

/-- Helper: `freeVars` of an enc-pair always falls through to the catch-all
    branch (since `enc f` is never a bare op-atom). Need to case-split on `f`
    to expose `enc f`'s shape for Lean's pattern matcher. -/
private theorem freeVars_enc_pair (f x : Lam) :
    SSBX.Foundation.Jian.freeVars (Wen.pair (enc f) (enc x))
      = SSBX.Foundation.Jian.freeVars (enc f)
        ++ SSBX.Foundation.Jian.freeVars (enc x) := by
  cases f <;> rfl

/-- Encoding preserves free-variable lists. -/
theorem enc_freeVars (t : Lam) :
    SSBX.Foundation.Jian.freeVars (enc t) = Lam.freeVars t := by
  induction t with
  | var n => rfl
  | abs b body ih =>
      show (SSBX.Foundation.Jian.freeVars (enc body)).filter (· ≠ b)
            = (Lam.freeVars body).filter (· ≠ b)
      rw [ih]
  | app f x ih_f ih_x =>
      show SSBX.Foundation.Jian.freeVars (Wen.pair (enc f) (enc x))
            = Lam.freeVars f ++ Lam.freeVars x
      rw [freeVars_enc_pair, ih_f, ih_x]

/-- `freshName` definitions in Jian and Lam are identical algorithms over the
    same input type — so produce equal results. -/
theorem freshName_eq (used : List String) (base : String) :
    SSBX.Foundation.Jian.freshName used base = Lam.freshName used base := rfl

/-- Encoding commutes with 易 (atomic transformation). 7-line proof — much
    shorter than the old shadow-respecting `enc_rename` which needed
    `rename_enc_pair` and `rename_enc_zhe` helpers. -/
theorem enc_yi (f : String → String) (t : Lam) :
    SSBX.Foundation.Jian.yi f (enc t) = enc (Lam.yi f t) := by
  induction t with
  | var n => rfl
  | abs x body ih =>
      show Wen.pair (.op .zhe) (.pair (.atom (f x))
              (SSBX.Foundation.Jian.yi f (enc body)))
            = Wen.pair (.op .zhe) (.pair (.atom (f x)) (enc (Lam.yi f body)))
      rw [ih]
  | app f' x ih_f ih_x =>
      show Wen.pair (SSBX.Foundation.Jian.yi f (enc f'))
                    (SSBX.Foundation.Jian.yi f (enc x))
            = Wen.pair (enc (Lam.yi f f')) (enc (Lam.yi f x))
      rw [ih_f, ih_x]

/-- Specialized for single-atom rename (yi1). -/
theorem enc_yi1 (b b' : String) (t : Lam) :
    SSBX.Foundation.Jian.yi1 b b' (enc t) = enc (Lam.yi1 b b' t) :=
  enc_yi _ t

/-! ## Discharging the axiom -/

/-- Helper: `subst` of an enc-pair falls through to the catch-all branch.
    `subst` is well-founded, so unfolding requires `simp` with equation lemmas
    rather than `rfl`. -/
private theorem subst_enc_pair (f x : Lam) (name : String) (val : Wen) :
    SSBX.Foundation.Jian.subst (Wen.pair (enc f) (enc x)) name val
      = Wen.pair (SSBX.Foundation.Jian.subst (enc f) name val)
                 (SSBX.Foundation.Jian.subst (enc x) name val) := by
  cases f <;> simp only [enc, Wen.Zhe, SSBX.Foundation.Jian.subst]

/-- Encoding commutes with substitution (Task #52 axiom now proved). -/
theorem subst_preserves_enc : ∀ (body : Lam) (name : String) (val : Lam),
    enc (Lam.subst body name val)
      = SSBX.Foundation.Jian.subst (enc body) name (enc val)
  | .var n, name, val => by
      simp only [enc, Lam.subst, SSBX.Foundation.Jian.subst]
      by_cases h : n = name
      · simp [h]
      · simp [h, enc]
  | .abs b body, name, val => by
      simp only [Lam.subst, SSBX.Foundation.Jian.subst, enc, Wen.Zhe,
                 enc_freeVars]
      by_cases h_shadow : b = name
      · simp [h_shadow, enc, Wen.Zhe]
      · rw [if_neg h_shadow, if_neg h_shadow]
        by_cases h_capture : (Lam.freeVars val).contains b = true
        · -- α-rename branch
          rw [if_pos h_capture, if_pos h_capture]
          rw [show Lam.freshName (Lam.freeVars body ++ Lam.freeVars val ++ [name]) b
                  = SSBX.Foundation.Jian.freshName
                      (Lam.freeVars body ++ Lam.freeVars val ++ [name]) b from rfl]
          simp only [enc, Wen.Zhe]
          rw [subst_preserves_enc
                (Lam.yi1 b
                  (SSBX.Foundation.Jian.freshName
                    (Lam.freeVars body ++ Lam.freeVars val ++ [name]) b)
                  body)
                name val,
              enc_yi1 b _ body]
        · -- non-shadowing, non-capture branch
          rw [if_neg h_capture, if_neg h_capture]
          simp only [enc, Wen.Zhe]
          rw [subst_preserves_enc body name val]
  | .app f x, name, val => by
      simp only [Lam.subst, enc]
      rw [subst_enc_pair, subst_preserves_enc f name val,
          subst_preserves_enc x name val]
termination_by t _ _ => t.size
decreasing_by
  all_goals first
    | (simp_wf; simp only [Lam.size, Lam.yi1, Lam.yi_size]; omega)
    | (simp_wf; simp only [Lam.size]; omega)

/-- **General STLC simulation theorem** (modulo `subst_preserves_enc` axiom).

    For any one-step β-reduction in λ-calc, the encoded terms are related by
    the multi-step Wen relation. -/
theorem simulation : ∀ {t u : Lam}, Lam.Beta t u → Step.star (enc t) (enc u) := by
  intro t u h
  induction h with
  | beta b body arg =>
    show Step.star (enc (.app (.abs b body) arg)) (enc (Lam.subst body b arg))
    rw [subst_preserves_enc]
    show Step.star (.pair (Wen.Zhe b (enc body)) (enc arg))
                   (SSBX.Foundation.Jian.subst (enc body) b (enc arg))
    exact Step.star.single (Step.rule2 b (enc body) (enc arg))
  | congAppL f f' x _h_step ih =>
    show Step.star (enc (.app f x)) (enc (.app f' x))
    exact Step.star.congPairL ih (enc x)
  | congAppR f x x' _h_step ih =>
    show Step.star (enc (.app f x)) (enc (.app f x'))
    exact Step.star.congPairR (enc f) ih
  | congAbs b body body' _h_step ih =>
    show Step.star (enc (.abs b body)) (enc (.abs b body'))
    -- enc (.abs b body) = Zhe b (enc body) = .pair (.op .zhe) (.pair (.atom b) (enc body))
    show Step.star (.pair (.op .zhe) (.pair (.atom b) (enc body)))
                   (.pair (.op .zhe) (.pair (.atom b) (enc body')))
    apply Step.star.congPairR
    apply Step.star.congPairR
    exact ih

end SSBX.Foundation.JianSTLC
