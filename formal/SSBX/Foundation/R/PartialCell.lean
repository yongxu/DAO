/-
# Foundation.R.PartialCell — partial cells / face lattice of `R N`

A `PartialCell N` is a function `Fin N → Option Bool`: at each position
either `none` (unspecified) or `some b` (pinned to `b`).

This is the **face lattice of the N-cube**.  A `PartialCell N` with `k`
specified positions selects a face of dimension `N − k`, containing
`2^(N − k)` full `R N` vectors (the cells whose values agree with the
spec at every specified position).

## R-tower as codim filtration ("栈降格为 codim")

The squaring tower `R 2 / R 4 / R 8` collapses into a single substrate
once we view R_k characters as partial cells of a common ceiling:

* R₈ 字 = `|support| = 8`  (an 8-cube vertex,  0-face)
* R₄ 字 = `|support| = 4`  (a 4-face)
* R₂ 字 = `|support| = 2`  (a 6-face)
* R₀ 字 / 道 = `|support| = 0`  (the whole N-cube, `dao`)

Heterogeneous mixing in language (R₈ + R₄ + R₂ in one string) becomes
the **single** operation `merge : PartialCell N → PartialCell N → Option`,
yielding `none` exactly when two characters disagree on some shared
specified position (= 不通 / ungrammatical).

This realises the partial-cell view that unifies (甲) lift-to-ceiling
and (乙) 元/爻 application into one merge operation differentiated only
by mask geometry:

* **并列** (parallel, lateral): disjoint supports
* **修饰** (modifier-head, vertical): one support ⊆ the other
* **不通** (conflict): overlapping supports with disagreeing values

`dao` is the unique merge identity; merging is idempotent and
commutative (when defined).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.R

/-- `PartialCell N` — partial bit-assignment of `N` positions.
    `none` = unspecified; `some b` = pinned to `b`. -/
def PartialCell (N : ℕ) : Type := Fin N → Option Bool

namespace PartialCell

variable {N : ℕ}

/-- 道 — the empty partial assignment.  Selects the entire N-cube;
    identity for `merge`. -/
def dao : PartialCell N := fun _ => none

/-- The set of specified positions. -/
def support (c : PartialCell N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => (c i).isSome = true)

/-- Lift a full `R N` to a `PartialCell N` (all positions specified). -/
def ofFull (v : R N) : PartialCell N := fun i => some (v i)

/-- Two partial cells are **compatible** iff they agree at every shared
    specified position. -/
def compatible (a b : PartialCell N) : Prop :=
  ∀ i, a i = none ∨ b i = none ∨ a i = b i

instance instDecidableCompatible (a b : PartialCell N) :
    Decidable (compatible a b) :=
  Fintype.decidableForallFintype

/-- Pointwise merge function (first specified value wins). -/
def mergeFn (a b : PartialCell N) : PartialCell N :=
  fun i => match a i with | some x => some x | none => b i

/-- **Merge** — partial commutative monoid operation with identity `dao`.
    Returns `some _` iff `compatible a b`; otherwise `none` (= 不通). -/
def merge (a b : PartialCell N) : Option (PartialCell N) :=
  if compatible a b then some (mergeFn a b) else none

/-! ## § Monoid identities -/

theorem compatible_dao_left (c : PartialCell N) : compatible dao c := by
  intro _; exact Or.inl rfl

theorem compatible_dao_right (c : PartialCell N) : compatible c dao := by
  intro _; exact Or.inr (Or.inl rfl)

theorem compatible_self (c : PartialCell N) : compatible c c := by
  intro _; exact Or.inr (Or.inr rfl)

@[simp] theorem mergeFn_dao_left (c : PartialCell N) :
    mergeFn dao c = c := by
  funext _; rfl

@[simp] theorem mergeFn_dao_right (c : PartialCell N) :
    mergeFn c dao = c := by
  funext i
  unfold mergeFn dao
  cases c i <;> rfl

@[simp] theorem mergeFn_self (c : PartialCell N) :
    mergeFn c c = c := by
  funext i
  unfold mergeFn
  cases c i <;> rfl

@[simp] theorem dao_merge (c : PartialCell N) :
    merge dao c = some c := by
  unfold merge
  rw [if_pos (compatible_dao_left c), mergeFn_dao_left]

@[simp] theorem merge_dao (c : PartialCell N) :
    merge c dao = some c := by
  unfold merge
  rw [if_pos (compatible_dao_right c), mergeFn_dao_right]

theorem merge_self (c : PartialCell N) :
    merge c c = some c := by
  unfold merge
  rw [if_pos (compatible_self c), mergeFn_self]

/-! ## § R-tower correspondence

A full `R N` vector embeds as a `PartialCell N` with full support; a
`PartialCell N` whose support has size `N` recovers a unique full
vector.  This is the canonical印/投 pair at the partial-cell level. -/

@[simp] theorem ofFull_apply (v : R N) (i : Fin N) :
    ofFull v i = some (v i) := rfl

theorem support_ofFull (v : R N) :
    support (ofFull v) = Finset.univ := by
  unfold support ofFull
  apply Finset.filter_true_of_mem
  intro i _; rfl

@[simp] theorem support_dao : support (dao : PartialCell N) = ∅ := by
  unfold support dao
  ext i
  simp

/-! ## § Phase B — commutativity, associativity, restriction, full extraction -/

/-! ### B.1 Compatibility is symmetric -/

theorem compatible_comm (a b : PartialCell N) :
    compatible a b ↔ compatible b a := by
  refine ⟨fun h i => ?_, fun h i => ?_⟩
  · rcases h i with hi | hi | hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inl hi
    · exact Or.inr (Or.inr hi.symm)
  · rcases h i with hi | hi | hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inl hi
    · exact Or.inr (Or.inr hi.symm)

theorem compatible_symm {a b : PartialCell N} (h : compatible a b) :
    compatible b a := (compatible_comm a b).mp h

/-! ### B.2 `mergeFn` commutativity under compatibility -/

theorem mergeFn_comm {a b : PartialCell N} (h : compatible a b) :
    mergeFn a b = mergeFn b a := by
  funext i
  unfold mergeFn
  rcases h i with hi | hi | hi
  · rw [hi]; cases b i <;> rfl
  · rw [hi]; cases a i <;> rfl
  · rw [hi]

/-! ### B.3 `merge` is unconditionally commutative -/

theorem merge_comm (a b : PartialCell N) : merge a b = merge b a := by
  unfold merge
  by_cases h : compatible a b
  · rw [if_pos h, if_pos (compatible_symm h), mergeFn_comm h]
  · rw [if_neg h, if_neg (fun h' => h (compatible_symm h'))]

/-! ### B.4 `mergeFn` is unconditionally associative (pointwise "first specified wins") -/

theorem mergeFn_assoc (a b c : PartialCell N) :
    mergeFn (mergeFn a b) c = mergeFn a (mergeFn b c) := by
  funext i
  unfold mergeFn
  cases a i <;> cases b i <;> cases c i <;> rfl

/-! ### B.5 Restriction (codim-controlled projection) -/

/-- Restrict a partial cell to a sub-mask: positions outside `s` become unspecified.
    This is the codim-increasing direction of the partial-cell lattice. -/
def restrict (s : Finset (Fin N)) (c : PartialCell N) : PartialCell N :=
  fun i => if i ∈ s then c i else none

@[simp] theorem restrict_dao (s : Finset (Fin N)) :
    restrict s (dao : PartialCell N) = dao := by
  funext i
  unfold restrict dao
  split <;> rfl

@[simp] theorem restrict_univ (c : PartialCell N) :
    restrict Finset.univ c = c := by
  funext i
  unfold restrict
  rw [if_pos (Finset.mem_univ i)]

@[simp] theorem restrict_empty (c : PartialCell N) :
    restrict ∅ c = dao := by
  funext i
  unfold restrict dao
  simp

/-! ### B.6 Full extraction `toFull?` -/

/-- Try to extract a full `R N` vector.  Returns `some v` iff every
    position is specified (`support c = univ`), `none` otherwise. -/
def toFull? (c : PartialCell N) : Option (R N) :=
  if h : ∀ i, (c i).isSome = true then
    some (fun i => (c i).get (h i))
  else none

@[simp] theorem toFull?_ofFull (v : R N) :
    toFull? (ofFull v) = some v := by
  unfold toFull? ofFull
  split_ifs with h
  · rfl
  · exact absurd (fun _ => rfl) h

/-! ## § Phase D — full monoid laws + List fold + support algebra -/

/-! ### D.1 Compatibility transports through `mergeFn` -/

theorem compatible_mergeFn_left (a b c : PartialCell N)
    (hac : compatible a c) (hbc : compatible b c) :
    compatible (mergeFn a b) c := by
  intro i
  show (mergeFn a b) i = none ∨ c i = none ∨ (mergeFn a b) i = c i
  unfold mergeFn
  cases ha : a i with
  | none => exact hbc i
  | some x =>
    have hi := hac i
    rw [ha] at hi
    rcases hi with hi | hi | hi
    · cases hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)

theorem compatible_mergeFn_right (a b c : PartialCell N)
    (hab : compatible a b) (hac : compatible a c) :
    compatible a (mergeFn b c) :=
  compatible_symm (compatible_mergeFn_left b c a (compatible_symm hab) (compatible_symm hac))

/-! ### D.2 Full `merge` associativity (under pairwise compatibility) -/

theorem merge_assoc (a b c : PartialCell N)
    (hab : compatible a b) (hac : compatible a c) (hbc : compatible b c) :
    merge a b >>= (fun ab => merge ab c) =
    merge b c >>= (fun bc => merge a bc) := by
  have hAB : merge a b = some (mergeFn a b) := by unfold merge; rw [if_pos hab]
  have hBC : merge b c = some (mergeFn b c) := by unfold merge; rw [if_pos hbc]
  rw [hAB, hBC]
  show merge (mergeFn a b) c = merge a (mergeFn b c)
  have hABc : compatible (mergeFn a b) c :=
    compatible_mergeFn_left a b c hac hbc
  have haBC : compatible a (mergeFn b c) :=
    compatible_mergeFn_right a b c hab hac
  have h1 : merge (mergeFn a b) c = some (mergeFn (mergeFn a b) c) := by
    unfold merge; rw [if_pos hABc]
  have h2 : merge a (mergeFn b c) = some (mergeFn a (mergeFn b c)) := by
    unfold merge; rw [if_pos haBC]
  rw [h1, h2]
  congr 1
  exact mergeFn_assoc a b c

/-! ### D.3 List fold `mergeAll` -/

/-- Right-fold of `merge` over a list of partial cells.
    Empty list folds to `dao`.  Result is `none` iff the chain fails
    compatibility somewhere. -/
def mergeAll : List (PartialCell N) → Option (PartialCell N)
  | [] => some dao
  | c :: rest => mergeAll rest >>= merge c

@[simp] theorem mergeAll_nil :
    mergeAll ([] : List (PartialCell N)) = some dao := rfl

@[simp] theorem mergeAll_cons (c : PartialCell N) (rest : List (PartialCell N)) :
    mergeAll (c :: rest) = mergeAll rest >>= merge c := rfl

theorem mergeAll_singleton (c : PartialCell N) : mergeAll [c] = some c := by
  show mergeAll [] >>= merge c = some c
  rw [mergeAll_nil]
  show merge c dao = some c
  exact merge_dao c

/-! ### D.4 Support algebra (codim filtration) -/

theorem support_mergeFn (a b : PartialCell N) :
    support (mergeFn a b) = support a ∪ support b := by
  ext i
  unfold support mergeFn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  cases a i <;> cases b i <;> simp

theorem support_restrict (s : Finset (Fin N)) (c : PartialCell N) :
    support (restrict s c) = s ∩ support c := by
  ext i
  unfold support restrict
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i ∈ s
  · simp [hi]
  · simp [hi]

end PartialCell

end SSBX.Foundation.R
