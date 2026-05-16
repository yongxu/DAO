/-
# Foundation.Representation.Lexicon — Strategy C: lexical anchor → R-tower coordinate

Strategy C completes the locator suite: given a 字 / 词 (Chinese key, or any
string label), look up its preferred o/x bit pattern in a school-specific
table; then hand off to Strategy E (`OXPattern.fromOX`) to compute the
R-tower coordinate.

## Architecture

This module is the **interface / plumbing** layer for Strategy C.  It defines:

* `LexicalAnchor : Type` — abstract type for "string-key → R-tower coord"
  partial mappings.
* `loadFromString : String → LexicalAnchor` — parser for the `.lex` text
  format, where each line is `<key> <ox-string>` (comments via `#`).
* `compose / merge / agreesAt` — operations for stacking and comparing
  multiple anchors.
* `wenSubstrate : LexicalAnchor` — the canonical anchor adapted from
  `Foundation.Lang.Lexicon` (8 tables, ~120 entries covering yao /
  sixiang / trigram / ben / zheng / hexagram / 五常 / 五伦).

## Multi-school pluralism

A `LexicalAnchor` is **just a function** `String → Option (Σ N, R N)`.
Different schools provide different `LexicalAnchor` instances; they can
be composed (`compose : LexicalAnchor → LexicalAnchor → LexicalAnchor`)
or compared for cross-school agreement on coordinates
(`agreesAt : LexicalAnchor → LexicalAnchor → String → String → Bool`).

Pluralism is **data-layer**, not type-layer: a new school = a new
`LexicalAnchor` term, not a new inductive case.  See
`Representation/Lexicon/Examples.lean` for demonstrations across 6+
schools (wen-substrate / yijing / confucian / daoist / buddhist /
military).

## File format

A `.lex` file is a sequence of lines:

```
# Comments start with #; blank lines OK

# Each entry: <key> <ox-string>
道       # R₀ — empty ox encodes the origin singleton
阴 o      # R₁
阳 x      # R₁
道2 oo    # R₂ (rename to avoid R₀/R₂ key collision)
已 ox    # R₂
今 xo    # R₂
未 xx    # R₂
```

Within one file, keys must be unique.  Across files (different schools),
the same key may map to different coordinates — composition resolves
by right-bias (later mapping wins).

## Convention (inherited from OXPattern)

* `o` = `false` (yang ⚊)
* `x` = `true`  (yin ⚋)
* string length = R-tower level

## Doctrinal anchor

* `wen-substrate.md` v1.4 §Representation.
* `Foundation/Lang/Lexicon.lean` — the canonical 8-table data source.
* `Foundation/Representation/OXPattern.lean` — Strategy E (bit-string parser).
-/

import SSBX.Foundation.Representation.OXPattern
import SSBX.Foundation.Lang.Lexicon

namespace SSBX.Foundation.Representation

open SSBX.Foundation.R

/-! ## § 1 Core type -/

/-- A **lexical anchor**: maps a string key (typically a 字 or 词) to
    an R-tower coordinate (level + cell), partial function.

    The function signature is intentionally abstract so that an anchor
    can be:
    * built from a static list (`ofEntries`),
    * loaded from a `.lex` text file (`loadFromString`),
    * adapted from an existing lexicon (`fromLangLexicon`),
    * or composed from any of the above. -/
abbrev LexicalAnchor := String → Option (Σ N, R N)

namespace LexicalAnchor

/-! ## § 2 The empty anchor and ofEntries builder -/

/-- The empty anchor — maps every key to `none`. -/
def empty : LexicalAnchor := fun _ => none

/-- A single mapping entry: `(key, ox-string)`. -/
abbrev Entry := String × String

/-- Build a `LexicalAnchor` from a list of entries.  When multiple
    entries share a key, the **last** one wins (right-bias).

    Implementation: traverse the list in reverse and return the first
    match — equivalent to "later entries shadow earlier ones". -/
def ofEntries (entries : List Entry) : LexicalAnchor := fun key =>
  match entries.reverse.find? (·.1 == key) with
  | some (_, ox) => some (fromOX ox)
  | none         => none

/-- Look up a key.  Use direct function application `m key` interchangeably;
    this alias is for readability when the anchor name is long. -/
def lookup (m : LexicalAnchor) (key : String) : Option (Σ N, R N) := m key

@[simp] theorem empty_lookup (key : String) : lookup empty key = none := rfl

/-! ## § 3 File-format parsing -/

namespace Parser

/-- A line is a comment if its trimmed form starts with `#`. -/
def isComment (line : String) : Bool :=
  line.trim.startsWith "#"

/-- A line is blank if its trimmed form is empty. -/
def isBlank (line : String) : Bool :=
  line.trim.isEmpty

/-- A string is a valid ox-pattern if every character is `o` or `x`.
    The empty string (R₀ origin) is valid. -/
def isValidOX (s : String) : Bool :=
  s.toList.all fun c => c == 'o' || c == 'x'

/-- Split a line on whitespace (spaces / tabs) and drop empty tokens. -/
def tokens (line : String) : List String :=
  line.trim.splitOn " " |>.foldl
    (fun acc part =>
      acc ++ (part.splitOn "\t" |>.filter (¬·.isEmpty)))
    []

/-- Parse one line `<key> <ox-string>` into `Entry`.

    Returns `none` for:
    * comment lines (start with `#`),
    * blank lines,
    * lines with > 2 tokens (malformed; silently skipped),
    * lines whose ox-token contains characters other than `o`/`x`.

    A line with a single token `k` is interpreted as `(k, "")` —
    a R₀ anchor. -/
def parseLine (line : String) : Option Entry :=
  if isComment line || isBlank line then none
  else
    match tokens line with
    | [k]      => some (k, "")
    | [k, ox]  => if isValidOX ox then some (k, ox) else none
    | _        => none

end Parser

/-- Parse a whole file content into a list of entries (silently dropping
    comment lines, blank lines, and malformed lines). -/
def parseLines (content : String) : List Entry :=
  content.splitOn "\n" |>.filterMap Parser.parseLine

/-- **Top-level loader**: parse a `.lex` file content into a `LexicalAnchor`. -/
def loadFromString (content : String) : LexicalAnchor :=
  ofEntries (parseLines content)

/-! ## § 4 Composition / merging -/

/-- Right-biased compose: `m₂` shadows `m₁` on overlapping keys.

    Reads as "default mapping `m₁`, with school-specific override `m₂`". -/
def compose (m₁ m₂ : LexicalAnchor) : LexicalAnchor := fun key =>
  match m₂ key with
  | some r => some r
  | none   => m₁ key

@[simp] theorem compose_left_empty (m : LexicalAnchor) :
    compose empty m = m := by
  funext key
  unfold compose empty
  cases m key <;> rfl

@[simp] theorem compose_right_empty (m : LexicalAnchor) :
    compose m empty = m := by
  funext key
  unfold compose empty
  rfl

/-! ## § 5 Cross-school agreement -/

/-- Two anchors **agree at** a (key₁, key₂) pair iff they map to the
    same R-tower coordinate: same level **and** same rendered o/x string.

    Rendered o/x is used (rather than `HEq` on the cell) because o/x
    strings are decidable-equal across different `R N` types. -/
def agreesAt (m₁ m₂ : LexicalAnchor) (k₁ k₂ : String) : Bool :=
  match m₁ k₁, m₂ k₂ with
  | some r₁, some r₂ =>
      r₁.1 == r₂.1 && renderOX r₁.2 == renderOX r₂.2
  | _, _ => false

/-- An anchor is **self-consistent** at a key if it agrees with itself.
    Trivially true for keys it maps. -/
theorem agreesAt_refl (m : LexicalAnchor) (key : String)
    (h : (m key).isSome) :
    agreesAt m m key key = true := by
  unfold agreesAt
  cases hm : m key with
  | none      =>
      rw [hm] at h
      simp at h
  | some r    => simp

/-! ## § 6 Bridge to `Foundation.Lang.Lexicon` -/

/-- Adapter: build a `LexicalAnchor` from the canonical 8-table
    `Lang.Lexicon`.  This is the **canonical wen-substrate anchor**.

    Note: when a Chinese form appears in multiple tables (e.g., 乾 as
    both R₃ trigram and R₆ hexagram), `byChinese` returns the **first**
    match in `allEntries` (trigram before hexagram).  Multi-level
    lookup requires going through `Lang.Lexicon.byChinese` directly
    with a level filter. -/
def fromLangLexicon : LexicalAnchor := fun key =>
  match SSBX.Foundation.Lang.Lexicon.Lookup.bitsOf key with
  | some (_, ox) => some (fromOX ox)
  | none         => none

/-- The canonical wen-substrate anchor. -/
def wenSubstrate : LexicalAnchor := fromLangLexicon

/-! ## § 7 Sanity / unit tests

  We use direct function application `m key` rather than `m.lookup key`,
  since `LexicalAnchor` is an `abbrev` (transparent) and dot notation
  on it would mis-resolve to `String.lookup`. -/

example : loadFromString "道2 oo\n已 ox" "已" = some (fromOX "ox") := by
  native_decide

example : loadFromString "道2 oo\n已 ox" "未知" = none := by
  native_decide

/-- Comment lines are skipped. -/
example : loadFromString "# this is a comment\n阴 o" "阴"
            = some (fromOX "o") := by
  native_decide

/-- Right-biased compose: later entries override earlier. -/
example :
    compose (ofEntries [("仁", "oo")]) (ofEntries [("仁", "xx")]) "仁"
      = some (fromOX "xx") := by
  native_decide

/-- The canonical wen-substrate anchor resolves 乾 (R₃ trigram). -/
example : (wenSubstrate "乾").map Sigma.fst = some 3 := by
  native_decide

/-- The canonical wen-substrate anchor resolves 仁 (R₇ Confucian wuchang). -/
example : (wenSubstrate "仁").map Sigma.fst = some 7 := by
  native_decide

/-- The canonical wen-substrate anchor resolves 未济 (R₆ hexagram). -/
example : (wenSubstrate "未济").map Sigma.fst = some 6 := by
  native_decide

end LexicalAnchor

end SSBX.Foundation.Representation
