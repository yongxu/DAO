/-
# Foundation.Representation.OXPattern — Strategy E: o/x bit-string locator

The **most concrete** locator strategy in the representation-closure
suite: directly parse an o/x bit pattern of arbitrary length to an
R-tower element.

Convention (per `Foundation/R/Basic.lean`):

* `o` = `false` (yang, ⚊)
* `x` = `true`  (yin,  ⚋)

For a string `s` consisting of 'o' and 'x' characters (other characters
are treated as 'o' in the lenient parser):

* `level(s) = s.length`
* `cell(s)  = (fun i => s.toList[i] == 'x') : R s.length`

This is the inverse of bit-pattern enumeration: every o/x string of
length N gives a unique element of R N, and every R N element renders
back to a unique o/x string.

Examples:

* `"o"`        ↦ R 1, oo
* `"x"`        ↦ R 1, xx
* `"oo"`       ↦ R 2, oo
* `"xo"`       ↦ R 2, xo  (V₄ Shi `ji`)
* `"ox"`       ↦ R 2, ox  (V₄ Shi `wei`)
* `"xx"`       ↦ R 2, xx
* `"xox"`      ↦ R 3 (一 of the 8 trigrams)
* `"oxoxox"`   ↦ R 6 (一 of the 64 hexagrams)
* `"ooxoxox"`  ↦ R 7 (no traditional name, sits in the strict tower)
* `"xxxxxxxx"` ↦ R 8, the all-yin byte

The integration with `Concept`'s `cell` field (Strategy A's placeholder)
is deferred — Strategy E stands alone for now; downstream work can
refine `Concept.atom`'s cell witness using `fromOX` once the lexical
anchor pass (Strategy C / 汉字) is also on the table.

## Doctrinal anchor

* `wen-substrate.md` v1.4 §Representation.
* `Foundation/R/Basic.lean` for the o/x convention (`o = false = yang`,
  `x = true = yin`).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Representation

open SSBX.Foundation.R

/-! ## § 1 Character ↔ Bool conversion (o/x convention) -/

namespace OXChar

/-- Strict character-to-Bool: `'o' ↦ false`, `'x' ↦ true`,
    other characters ↦ `none`. -/
def toBool? : Char → Option Bool
  | 'o' => some false
  | 'x' => some true
  | _   => none

/-- Lenient character-to-Bool: `'x' ↦ true`, anything else ↦ `false`. -/
def toBool : Char → Bool
  | 'x' => true
  | _   => false

@[simp] theorem toBool_o : toBool 'o' = false := rfl
@[simp] theorem toBool_x : toBool 'x' = true  := rfl

end OXChar

namespace OXBool

/-- Render a `Bool` as the o/x character: `false ↦ 'o'`, `true ↦ 'x'`. -/
def toChar : Bool → Char
  | false => 'o'
  | true  => 'x'

@[simp] theorem toChar_false : toChar false = 'o' := rfl
@[simp] theorem toChar_true  : toChar true  = 'x' := rfl

/-- Round-trip: rendering then parsing recovers the original Bool. -/
@[simp] theorem toBool_toChar (b : Bool) : OXChar.toBool (toChar b) = b := by
  cases b <;> rfl

end OXBool

/-! ## § 2 The list-level locators -/

/-- List-level lenient parse: a list of characters becomes an R-tower
    element of size = list length, with each position determined by the
    character (`'x' ↦ true`, otherwise `false`). -/
def fromOXList (chars : List Char) : R chars.length :=
  fun i => OXChar.toBool (chars.get i)

/-- List-level rendering: produce a list of characters from an R-tower
    element, using the o/x convention.  Length-indexed via `List.ofFn`. -/
def renderOXList (N : ℕ) (r : R N) : List Char :=
  List.ofFn (fun i : Fin N => OXBool.toChar (r i))

@[simp] theorem renderOXList_length (N : ℕ) (r : R N) :
    (renderOXList N r).length = N := by
  simp [renderOXList]

@[simp] theorem renderOXList_get (N : ℕ) (r : R N) (i : Fin N) :
    (renderOXList N r).get (i.cast (renderOXList_length N r).symm)
      = OXBool.toChar (r i) := by
  simp [renderOXList]

/-! ## § 3 The string-level locators -/

/-- **The o/x bit-string locator.**  Given a string of arbitrary length,
    return the R-tower element of size = string length, with characters
    parsed under the lenient o/x convention.

    The size is paired with the cell via Σ — together they form the
    full R-tower coordinate `(N, x ∈ R N)`. -/
def fromOX (s : String) : Σ N, R N :=
  ⟨s.toList.length, fromOXList s.toList⟩

/-- Render an R-tower element of any level as an o/x string of length
    equal to the level. -/
def renderOX {N : ℕ} (r : R N) : String :=
  String.ofList (renderOXList N r)

/-! ## § 4 Specific lookups against the canonical R 2 constants -/

/-- `"oo"` has length 2 (sits at R 2). -/
@[simp] theorem fromOX_oo_fst : (fromOX "oo").fst = 2 := rfl
/-- `"oo"` parses to `R 2`'s `oo` (= V₄ identity / 道 in Atlas naming). -/
@[simp] theorem fromOX_oo_snd : (fromOX "oo").snd = R.oo := by
  funext i; fin_cases i <;> rfl

/-- `"xo"` has length 2. -/
@[simp] theorem fromOX_xo_fst : (fromOX "xo").fst = 2 := rfl
/-- `"xo"` parses to `R 2`'s `xo` (= V₄ P-flip / 已 in Atlas naming). -/
@[simp] theorem fromOX_xo_snd : (fromOX "xo").snd = R.xo := by
  funext i; fin_cases i <;> rfl

/-- `"ox"` has length 2. -/
@[simp] theorem fromOX_ox_fst : (fromOX "ox").fst = 2 := rfl
/-- `"ox"` parses to `R 2`'s `ox` (= V₄ T-flip / 未 in Atlas naming). -/
@[simp] theorem fromOX_ox_snd : (fromOX "ox").snd = R.ox := by
  funext i; fin_cases i <;> rfl

/-- `"xx"` has length 2. -/
@[simp] theorem fromOX_xx_fst : (fromOX "xx").fst = 2 := rfl
/-- `"xx"` parses to `R 2`'s `xx` (= V₄ PT / 今 in Atlas naming). -/
@[simp] theorem fromOX_xx_snd : (fromOX "xx").snd = R.xx := by
  funext i; fin_cases i <;> rfl

/-! ## § 5 Length sanity-checks across the squaring tower -/

example : (fromOX "o").fst = 1 := rfl
example : (fromOX "ox").fst = 2 := rfl
example : (fromOX "oxox").fst = 4 := rfl
example : (fromOX "oxoxoxox").fst = 8 := rfl

/-- The user's running example: an arbitrary-length o/x pattern. -/
example : (fromOX "ooxoxox").fst = 7 := rfl

/-- All-yin byte sits at R 8 ceiling. -/
example : (fromOX "xxxxxxxx").snd = (fun _ => true : R 8) := by
  funext i; fin_cases i <;> rfl

/-- All-yang byte at R 8 (= R 8 zero = V₄ identity lifted). -/
example : (fromOX "oooooooo").snd = (fun _ => false : R 8) := by
  funext i; fin_cases i <;> rfl

/-! ## § 6 Round-trip identities -/

/-- Per-character identity: on the o/x alphabet, `toChar ∘ toBool` is
    the identity.  This is the key lemma threading through the
    `renderOX ∘ fromOX` round-trip. -/
theorem OXChar.toChar_toBool_of_valid (c : Char) (h : c = 'o' ∨ c = 'x') :
    OXBool.toChar (OXChar.toBool c) = c := by
  rcases h with h | h <;> (rw [h]; rfl)

/-- **List-level right inverse**: `fromOXList ∘ renderOXList = id` on every
    R N element, pointwise (after the length cast). -/
theorem fromOXList_renderOXList {N : ℕ} (r : R N) (i : Fin N) :
    fromOXList (renderOXList N r) (i.cast (renderOXList_length N r).symm) = r i := by
  -- Unfold to: OXChar.toBool ((renderOXList N r).get (i.cast _)) = r i.
  show OXChar.toBool ((renderOXList N r).get (i.cast _)) = r i
  rw [renderOXList_get]
  -- Goal: OXChar.toBool (OXBool.toChar (r i)) = r i
  exact OXBool.toBool_toChar (r i)

/-- **List-level left inverse**: `renderOXList ∘ fromOXList = id` on
    character lists whose every element is 'o' or 'x'. -/
theorem renderOXList_fromOXList (chars : List Char)
    (h : ∀ c ∈ chars, c = 'o' ∨ c = 'x') :
    renderOXList chars.length (fromOXList chars) = chars := by
  apply List.ext_get
  · simp [renderOXList]
  · intro i hi₁ _hi₂
    -- LHS: (renderOXList _ (fromOXList chars)).get ⟨i, hi₁⟩
    --     = OXBool.toChar (fromOXList chars (⟨i, _⟩.cast _))
    --     = OXBool.toChar (OXChar.toBool (chars.get ⟨i, _⟩))
    -- RHS: chars.get ⟨i, _⟩
    -- The toChar ∘ toBool collapses by validity of chars.get.
    simp only [renderOXList, List.get_ofFn, fromOXList]
    apply OXChar.toChar_toBool_of_valid
    exact h _ (List.get_mem chars _)

/-- **String-level left inverse**: rendering the parsed form recovers
    the original string, provided the input contained only 'o' and 'x'
    characters.

    Non-o/x characters are mapped to 'o' by the lenient parser, so the
    validity hypothesis is necessary for this direction.

    Proof: the list-level round-trip `renderOXList_fromOXList` gives the
    underlying `List Char` equality; `String.ofList_toList` lifts it to
    the string level. -/
theorem renderOX_fromOX_of_valid (s : String)
    (h : ∀ c ∈ s.toList, c = 'o' ∨ c = 'x') :
    renderOX (fromOX s).snd = s := by
  show String.ofList (renderOXList _ (fromOXList s.toList)) = s
  rw [renderOXList_fromOXList s.toList h]
  exact String.ofList_toList

/-- The length of `(renderOX r).toList` equals N, since `renderOX r` is
    `String.ofList (renderOXList N r)` and `(String.ofList L).toList = L`. -/
@[simp] theorem renderOX_toList_length {N : ℕ} (r : R N) :
    (renderOX r).toList.length = N := by
  show (String.ofList (renderOXList N r)).toList.length = N
  rw [String.toList_ofList]
  exact renderOXList_length N r

/-- The string-level inverse of `String.ofList_toList`, specialised to our
    `renderOX`: the rendered string's `toList` is exactly the rendered list. -/
@[simp] theorem renderOX_toList {N : ℕ} (r : R N) :
    (renderOX r).toList = renderOXList N r :=
  String.toList_ofList

/-- **String-level right inverse** (level half): parsing the rendering of
    an R N element gives back an R-tower coordinate at level exactly N. -/
@[simp] theorem fromOX_renderOX_fst {N : ℕ} (r : R N) :
    (fromOX (renderOX r)).fst = N := by
  show (renderOX r).toList.length = N
  exact renderOX_toList_length r

/-- Auxiliary: `fromOXList` is functorial in list equality (via HEq, since
    the result type depends on the list's length). -/
theorem fromOXList_heq_of_eq {l₁ l₂ : List Char} (h : l₁ = l₂) :
    HEq (fromOXList l₁) (fromOXList l₂) := by
  subst h; rfl

/-- **String-level right inverse** (cell half, HEq form): the cell function
    extracted by parsing the rendered string agrees with the original `r`,
    up to the length-preserving HEq across the dependent function type. -/
theorem fromOX_renderOX_snd_heq {N : ℕ} (r : R N) :
    HEq (fromOX (renderOX r)).snd r := by
  -- Chain: (fromOX (renderOX r)).snd ≍ fromOXList (renderOXList N r) ≍ r.
  have h1 : HEq (fromOX (renderOX r)).snd (fromOXList (renderOXList N r)) :=
    fromOXList_heq_of_eq (renderOX_toList r)
  have h2 : HEq (fromOXList (renderOXList N r)) r := by
    -- Unfold R as Fin _ → Bool to let `Fin.heq_fun_iff` unify.
    change HEq (fromOXList (renderOXList N r) : Fin (renderOXList N r).length → Bool)
               (r : Fin N → Bool)
    apply (Fin.heq_fun_iff (renderOXList_length N r)).mpr
    intro i
    -- i : Fin (renderOXList N r).length
    -- Goal: fromOXList (renderOXList N r) i = r ⟨i.val, _⟩
    show OXChar.toBool ((renderOXList N r).get i) = r _
    simp only [renderOXList, List.get_ofFn]
    -- Goal: OXChar.toBool (OXBool.toChar (r (Fin.cast _ i))) = r ⟨i.val, _⟩
    rw [OXBool.toBool_toChar]
    -- Both sides are `r` applied at indices with the same `.val`; Fin.cast preserves val.
    rfl
  exact HEq.trans h1 h2

/-- **String-level right inverse** (Sigma form): rendering then parsing
    recovers the exact (level, cell) pair.  This is the master `R N → String → R N`
    round-trip identity. -/
theorem fromOX_renderOX_eq {N : ℕ} (r : R N) :
    fromOX (renderOX r) = (⟨N, r⟩ : Σ M, R M) := by
  apply Sigma.mk.inj_iff.mpr
  exact ⟨fromOX_renderOX_fst r, fromOX_renderOX_snd_heq r⟩

/-! ## § 7 Concrete round-trip examples (sanity checks) -/

example : renderOX (fromOX "ooxoxox").snd = "ooxoxox" := by native_decide
example : renderOX (fromOX "xxxxxxxx").snd = "xxxxxxxx" := by native_decide
example : renderOX (fromOX "oooooooo").snd = "oooooooo" := by native_decide
example : renderOX (fromOX "xo").snd = "xo" := by native_decide
example : renderOX (fromOX "ox").snd = "ox" := by native_decide

example : (fromOX (renderOX R.oo)).snd = R.oo := by
  funext i; fin_cases i <;> rfl

example : (fromOX (renderOX R.xo)).snd = R.xo := by
  funext i; fin_cases i <;> rfl

example : (fromOX (renderOX R.ox)).snd = R.ox := by
  funext i; fin_cases i <;> rfl

example : (fromOX (renderOX R.xx)).snd = R.xx := by
  funext i; fin_cases i <;> rfl

end SSBX.Foundation.Representation
