/-
# Wen.Layered.Derivability -- generic finite derivability checker

The checker is intentionally carrier-neutral: it works for any Boolean
evaluator on `Rn`, and `linearEval q` is the canonical linear-query instance.
-/

import SSBX.Foundation.Wen.Layered.Finite

namespace SSBX.Foundation.Wen.Layered

namespace BitSpace

/-- A generator list preserves an evaluator when every listed translation
preserves it at every root. -/
def invariantOnGenerators {n : Nat} (gens : List (BitSpace n))
    (eval : BitSpace n → Bool) : Prop :=
  ∀ x g : BitSpace n, g ∈ gens → eval (xor x g) = eval x

/-- Boolean finite check for one generator. -/
noncomputable def invariantOnGenerator? {n : Nat} (eval : BitSpace n → Bool)
    (g : BitSpace n) : Bool :=
  (Finset.univ : Finset (BitSpace n)).toList.all fun x =>
    decide (eval (xor x g) = eval x)

/-- Boolean finite check for a generator list. -/
noncomputable def generatorsInvariant? {n : Nat} (gens : List (BitSpace n))
    (eval : BitSpace n → Bool) : Bool :=
  gens.all fun g => invariantOnGenerator? eval g

theorem invariantOnGenerator?_eq_true_iff {n : Nat}
    (eval : BitSpace n → Bool) (g : BitSpace n) :
    invariantOnGenerator? eval g = true
      ↔ ∀ x : BitSpace n, eval (xor x g) = eval x := by
  classical
  unfold invariantOnGenerator?
  constructor
  · intro h x
    have hx :
        decide (eval (xor x g) = eval x) = true := by
      apply List.all_eq_true.mp h
      simp
    exact decide_eq_true_iff.mp hx
  · intro h
    apply List.all_eq_true.mpr
    intro x _
    exact decide_eq_true_iff.mpr (h x)

theorem generatorsInvariant?_eq_true_iff {n : Nat}
    (gens : List (BitSpace n)) (eval : BitSpace n → Bool) :
    generatorsInvariant? gens eval = true
      ↔ invariantOnGenerators gens eval := by
  classical
  unfold generatorsInvariant? invariantOnGenerators
  constructor
  · intro h x g hg
    have hgtrue :
        invariantOnGenerator? eval g = true := by
      exact List.all_eq_true.mp h g hg
    exact (invariantOnGenerator?_eq_true_iff eval g).mp hgtrue x
  · intro h
    apply List.all_eq_true.mpr
    intro g hg
    exact (invariantOnGenerator?_eq_true_iff eval g).mpr (fun x => h x g hg)

theorem invariant_foldXor_of_generators {n : Nat}
    {gens chosen : List (BitSpace n)} {eval : BitSpace n → Bool}
    (hgens : invariantOnGenerators gens eval)
    (hchosen : ∀ g : BitSpace n, g ∈ chosen → g ∈ gens) :
    ∀ x : BitSpace n, eval (xor x (foldXor chosen)) = eval x := by
  induction chosen with
  | nil =>
      intro x
      simp [foldXor]
  | cons g rest ih =>
      intro x
      have hg : g ∈ gens := hchosen g (by simp)
      have hrest : ∀ y : BitSpace n, y ∈ rest → y ∈ gens := by
        intro y hy
        exact hchosen y (by simp [hy])
      have hperm :
        xor x (xor g (foldXor rest)) =
            xor (xor x (foldXor rest)) g := by
        funext i
        dsimp [xor]
        cases x i <;> cases g i <;> cases (foldXor rest) i <;> decide
      calc
        eval (xor x (foldXor (g :: rest)))
            = eval (xor x (xor g (foldXor rest))) := rfl
        _ = eval (xor (xor x (foldXor rest)) g) := by rw [hperm]
        _ = eval (xor x (foldXor rest)) := hgens (xor x (foldXor rest)) g hg
        _ = eval x := ih hrest x

theorem isInvariant_spanList_of_generators {n : Nat}
    {gens : List (BitSpace n)} {eval : BitSpace n → Bool}
    (hgens : invariantOnGenerators gens eval) :
    isInvariant (spanList gens) eval := by
  intro x g hg
  rcases hg with ⟨chosen, hchosen, hfold⟩
  rw [← hfold]
  exact invariant_foldXor_of_generators hgens hchosen x

theorem invariantOnGenerators_of_isInvariant_spanList {n : Nat}
    {gens : List (BitSpace n)} {eval : BitSpace n → Bool}
    (hinv : isInvariant (spanList gens) eval) :
    invariantOnGenerators gens eval := by
  intro x g hg
  exact hinv x g (mem_spanList_of_mem_generators hg)

theorem isInvariant_spanList_iff_generators {n : Nat}
    (gens : List (BitSpace n)) (eval : BitSpace n → Bool) :
    isInvariant (spanList gens) eval ↔ invariantOnGenerators gens eval :=
  ⟨invariantOnGenerators_of_isInvariant_spanList,
   isInvariant_spanList_of_generators⟩

/-- Generic derivability checker for a finite generated translation subgroup.
It returns the root evaluation exactly when the evaluator is invariant under
all listed generators. -/
noncomputable def derivable? {n : Nat} (gens : List (BitSpace n))
    (eval : BitSpace n → Bool) (root : BitSpace n) : Option Bool :=
  if generatorsInvariant? gens eval then
    some (eval root)
  else
    none

theorem derivable?_some_iff {n : Nat}
    (gens : List (BitSpace n)) (eval : BitSpace n → Bool)
    (root : BitSpace n) :
    derivable? gens eval root = some (eval root)
      ↔ isInvariant (spanList gens) eval := by
  classical
  by_cases h : generatorsInvariant? gens eval = true
  · constructor
    · intro _
      exact isInvariant_spanList_of_generators
        ((generatorsInvariant?_eq_true_iff gens eval).mp h)
    · intro _
      simp [derivable?, h]
  · have hfalse : generatorsInvariant? gens eval = false := by
      cases hgi : generatorsInvariant? gens eval
      · rfl
      · exact False.elim (h hgi)
    constructor
    · intro hsome
      exfalso
      simp [derivable?, hfalse] at hsome
    · intro hinv
      have hprop := (isInvariant_spanList_iff_generators gens eval).mp hinv
      have htrue := (generatorsInvariant?_eq_true_iff gens eval).mpr hprop
      exact False.elim (h htrue)

theorem derivable?_sound {n : Nat}
    {gens : List (BitSpace n)} {eval : BitSpace n → Bool}
    {root : BitSpace n} {value : Bool}
    (h : derivable? gens eval root = some value) :
    value = eval root ∧ isInvariant (spanList gens) eval := by
  classical
  unfold derivable? at h
  by_cases hcheck : generatorsInvariant? gens eval = true
  · simp [hcheck] at h
    subst value
    exact ⟨rfl,
      isInvariant_spanList_of_generators
        ((generatorsInvariant?_eq_true_iff gens eval).mp hcheck)⟩
  · have hfalse : generatorsInvariant? gens eval = false := by
      cases hgi : generatorsInvariant? gens eval
      · rfl
      · exact False.elim (hcheck hgi)
    simp [hfalse] at h

/-- Linear masks annihilate a generated subgroup when their canonical linear
query is invariant under that subgroup.  This is deliberately phrased through
`isInvariant`; a later Mathlib linear-algebra refinement can prove an
orthogonal-complement characterization underneath the same public name. -/
def annihilatesMask {n : Nat} (gens : List (BitSpace n)) (q : BitSpace n) : Prop :=
  isInvariant (spanList gens) (linearEval q)

noncomputable def derivableLinear? {n : Nat} (gens : List (BitSpace n))
    (q root : BitSpace n) : Option Bool :=
  derivable? gens (linearEval q) root

theorem derivableLinear?_some_iff {n : Nat}
    (gens : List (BitSpace n)) (q root : BitSpace n) :
    derivableLinear? gens q root = some (linearEval q root)
      ↔ annihilatesMask gens q :=
  derivable?_some_iff gens (linearEval q) root

theorem derivability_summary (n : Nat) :
    (∀ (gens : List (BitSpace n)) (eval : BitSpace n → Bool),
      generatorsInvariant? (n := n) gens eval = true
        ↔ invariantOnGenerators gens eval)
    ∧ (∀ (gens : List (BitSpace n)) (eval : BitSpace n → Bool),
      isInvariant (spanList gens) eval ↔ invariantOnGenerators gens eval)
    ∧ (∀ (gens : List (BitSpace n)) (q root : BitSpace n),
      derivableLinear? (n := n) gens q root = some (linearEval q root)
        ↔ annihilatesMask gens q) :=
  ⟨generatorsInvariant?_eq_true_iff,
   isInvariant_spanList_iff_generators,
   derivableLinear?_some_iff⟩

end BitSpace

end SSBX.Foundation.Wen.Layered
