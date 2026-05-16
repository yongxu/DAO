/-
# `SSBX.Foundation.Wen.Embeddings.FOL` — first-order / propositional logic embedded into `R N`

**Phase 3 Stream C4 (GUT roadmap G3 case 4) — T2 universality case study #4.**

Per `docs-next/10_formal_形式/gut-roadmap.md` Phase 3 Stream C4: an external
formal system (here: a small propositional logic) is embedded into the
R-Family carrier `R N := Fin N → Bool` via a Gödel-style bit-pattern
serialisation.  The point of the case study is **not** to do logic in
`R N` — it is to *witness* that classical syntactic systems factor
through the R-Family carrier, i.e., that the R-Family genuinely
articulates them.

## The embedded fragment

We embed **propositional logic with atoms indexed by `ℕ`** (a finite
signature is a special case obtained by restricting the atom index
range; the embedding does not depend on the atom alphabet being finite,
only on each individual formula being finite).  The language:

```
PL ::= atom n             -- atom indexed by natural number n
     | ¬ φ                -- negation
     | φ ∧ ψ              -- conjunction
     | φ ∨ ψ              -- disjunction
     | φ → ψ              -- implication
```

That is **5 constructors**, fitting in a **3-bit tag**.  Each AST node
emits a 3-bit prefix tag followed by the encoding of its (0, 1, or 2)
children.  Atom-index payload is a unary-encoded `ℕ` (`n` `true`s then
one terminating `false`).

| Tag      | Constructor  | Payload after tag                              |
|----------|--------------|------------------------------------------------|
| `000`    | `atom n`     | `n` repetitions of `true`, then one `false`    |
| `001`    | `not φ`      | encoding of `φ`                                |
| `010`    | `and φ ψ`    | encoding of `φ`, then encoding of `ψ`          |
| `011`    | `or  φ ψ`    | encoding of `φ`, then encoding of `ψ`          |
| `100`    | `imp φ ψ`    | encoding of `φ`, then encoding of `ψ`          |

Tags `101, 110, 111` are *unused* in this minimal version — they are
the natural extension points for first-order quantifiers (`∀ x. φ`,
`∃ x. φ`) and atomic relations.  See the **§6 First-order extension
sketch** below.

## Round-trip ("decode ∘ encode = some") — faithfulness

We prove `encode_decode_roundtrip : ∀ φ, decodeOpt (encode φ) = some φ`.
This is the categorical-level statement that **the embedding is
faithful**: distinct formulae have distinct bit-string encodings, and
every encoded formula is recoverable.

## Compositionality

By construction, `encode` is **structurally recursive**:

* `encode (¬ φ)         = [false, false, true] ++ encode φ`
* `encode (φ ∧ ψ)       = [false, true, false] ++ encode φ ++ encode ψ`
* `encode (φ ∨ ψ)       = [false, true, true] ++ encode φ ++ encode ψ`
* `encode (φ → ψ)       = [true, false, false] ++ encode φ ++ encode ψ`

i.e., the encoding of a compound formula is a *function* of the
encodings of its sub-formulae.  This is the categorical
compositionality property.

## The `R N` bridge

`R N = Fin N → Bool` is a *fixed-length* bit-vector type; the encoding
above produces a variable-length `List Bool`.  We bridge via:

* `toR (bs : List Bool) (N : ℕ) : R N` — pad with `false` (right) or
  truncate to length `N`.
* `encodeR (φ) (N : ℕ) : R N := toR (encode φ) N` — the canonical
  embedding into a fixed-length R-Family cell.
* `decodeR (v : R N) : Option PL.Formula` — converts back to a
  `List Bool` and parses.

For `N` chosen ≥ `encode φ`.length (i.e., the formula fits in `N`
bits), `decodeR (encodeR φ N) = some φ`.

## Case-study witness (§5)

The formula `(¬ p ∨ q)` (where `p = atom 0`, `q = atom 1`) encodes to
a specific bit string; we evaluate it and check round-trip via
`#eval`-friendly decision.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` Phase 3 Stream C4 (this file).
* `wen-substrate.md` v1.4 §3.7 (operation monism — formulae as
  bit-patterns is the canonical operation-content collapse).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Wen.Embeddings.FOL

open SSBX.Foundation.R

/-! ## § 1 The embedded fragment — propositional logic AST

The AST has five constructors:

* `atom n` — atom indexed by `n : ℕ`
* `not`, `and`, `or`, `imp` — the four standard connectives

A *first-order* extension (quantifiers + atomic relations over a
finite signature) is sketched in §6; we restrict to PL here because
the embedding pattern is identical and PL gives the clearest
witness. -/

/-- Propositional formula AST. -/
inductive Formula : Type where
  | atom : Nat → Formula
  | not  : Formula → Formula
  | and  : Formula → Formula → Formula
  | or   : Formula → Formula → Formula
  | imp  : Formula → Formula → Formula
deriving DecidableEq, Repr

namespace Formula

/-- Convenience notation in the local namespace. -/
@[reducible] def p (n : Nat) : Formula := .atom n

end Formula

/-! ## § 2 Encoding `Formula → List Bool`

Per the table in the file docstring:

* tag `000` → `atom`
* tag `001` → `not`
* tag `010` → `and`
* tag `011` → `or`
* tag `100` → `imp`

Atoms additionally carry a unary-encoded `ℕ`: `n` `true`s, then a
terminating `false`. -/

/-- Encode a natural number as `n` `true`s followed by a single `false`
    terminator.  This is the simplest self-delimiting `ℕ` encoding.  -/
def encodeNat : Nat → List Bool
  | 0     => [false]
  | n + 1 => true :: encodeNat n

/-- The encoder for `Formula`. -/
def encode : Formula → List Bool
  | .atom n      => [false, false, false] ++ encodeNat n
  | .not  φ      => [false, false, true]  ++ encode φ
  | .and  φ ψ    => [false, true,  false] ++ encode φ ++ encode ψ
  | .or   φ ψ    => [false, true,  true]  ++ encode φ ++ encode ψ
  | .imp  φ ψ    => [true,  false, false] ++ encode φ ++ encode ψ

/-! ## § 3 Decoding `List Bool → Option (Formula × List Bool)`

We decode in the standard "parser-combinator returning remainder"
style: `decodeAux` takes a bit-stream and returns `(parsed formula,
remaining bits)` if the prefix is well-formed.  `decodeOpt` then
requires the remaining-bits to be `[]` for full consumption.

Fuel is needed because Lean's structural-recursion checker does not
automatically see that the recursive calls on the remainder are
well-founded (the list shrinks but in a way the checker does not
trivially observe without `WellFoundedRecursion` on `List.length`).
We pass an explicit fuel parameter ≥ the formula depth. -/

/-- Decode a unary-encoded `ℕ` from a bit-stream.  Returns
    `(n, remainder)` on success, `none` on stream exhaustion. -/
def decodeNat : List Bool → Option (Nat × List Bool)
  | []            => none
  | false :: rest => some (0, rest)
  | true  :: rest =>
      match decodeNat rest with
      | none           => none
      | some (n, rest') => some (n + 1, rest')

/-- Decode a `Formula` from a bit-stream using `fuel` recursion budget.
    Returns `(parsed formula, remaining bits)` on success. -/
def decodeAux : Nat → List Bool → Option (Formula × List Bool)
  | 0,        _    => none
  | _ + 1,    []   => none
  | fuel + 1, b₁ :: b₂ :: b₃ :: rest =>
      match b₁, b₂, b₃ with
      | false, false, false =>           -- atom
          match decodeNat rest with
          | none           => none
          | some (n, rest') => some (.atom n, rest')
      | false, false, true =>            -- not
          match decodeAux fuel rest with
          | none           => none
          | some (φ, rest') => some (.not φ, rest')
      | false, true, false =>            -- and
          match decodeAux fuel rest with
          | none           => none
          | some (φ, rest') =>
              match decodeAux fuel rest' with
              | none            => none
              | some (ψ, rest'') => some (.and φ ψ, rest'')
      | false, true, true =>             -- or
          match decodeAux fuel rest with
          | none           => none
          | some (φ, rest') =>
              match decodeAux fuel rest' with
              | none            => none
              | some (ψ, rest'') => some (.or φ ψ, rest'')
      | true, false, false =>            -- imp
          match decodeAux fuel rest with
          | none           => none
          | some (φ, rest') =>
              match decodeAux fuel rest' with
              | none            => none
              | some (ψ, rest'') => some (.imp φ ψ, rest'')
      | _, _, _ => none                  -- unused tags (101/110/111)
  | _ + 1, _ => none                     -- shorter than 3 bits

/-- Tree depth — used to compute a safe fuel bound. -/
def Formula.depth : Formula → Nat
  | .atom _    => 1
  | .not  φ    => φ.depth + 1
  | .and  φ ψ  => max φ.depth ψ.depth + 1
  | .or   φ ψ  => max φ.depth ψ.depth + 1
  | .imp  φ ψ  => max φ.depth ψ.depth + 1

/-- Decode a complete bit-stream: must consume *all* bits.  The fuel
    bound `bs.length + 1` is safe because every decode step consumes
    ≥ 3 bits (so depth ≤ length / 3 < length + 1). -/
def decodeOpt (bs : List Bool) : Option Formula :=
  match decodeAux (bs.length + 1) bs with
  | some (φ, []) => some φ
  | _            => none

/-! ## § 4 Round-trip / faithfulness

The key correctness statement: every encoded formula decodes back to
itself.  We prove this in two stages:

* `decodeNat_encodeNat` — unary `ℕ` round-trips with `[]` remainder.
* `decodeAux_encode_append` — for any sufficient fuel and any suffix
  `tail`, `decodeAux fuel (encode φ ++ tail) = some (φ, tail)`.
* `encode_decode_roundtrip` — corollary, using `tail = []`. -/

theorem decodeNat_encodeNat (n : Nat) :
    decodeNat (encodeNat n) = some (n, []) := by
  induction n with
  | zero       => rfl
  | succ n ih  =>
      show decodeNat (true :: encodeNat n) = some (n + 1, [])
      simp [decodeNat, ih]

theorem decodeNat_encodeNat_append (n : Nat) (tail : List Bool) :
    decodeNat (encodeNat n ++ tail) = some (n, tail) := by
  induction n with
  | zero       =>
      show decodeNat (false :: tail) = some (0, tail)
      rfl
  | succ n ih  =>
      show decodeNat (true :: (encodeNat n ++ tail)) = some (n + 1, tail)
      simp [decodeNat, ih]

/-- Sufficient-fuel round-trip with a residual `tail`.  The key
    induction lemma: with at least `φ.depth` units of fuel we can
    parse `encode φ ++ tail` and return `(φ, tail)`. -/
theorem decodeAux_encode_append
    (φ : Formula) (tail : List Bool) (fuel : Nat) (hfuel : φ.depth ≤ fuel) :
    decodeAux fuel (encode φ ++ tail) = some (φ, tail) := by
  induction φ generalizing tail fuel with
  | atom n =>
      cases fuel with
      | zero =>
          exfalso
          have : (Formula.atom n).depth = 1 := rfl
          omega
      | succ f =>
          show decodeAux (f + 1)
              ([false, false, false] ++ encodeNat n ++ tail) = _
          simp [decodeAux]
          have : decodeNat (encodeNat n ++ tail) = some (n, tail) :=
            decodeNat_encodeNat_append n tail
          rw [this]
  | not φ ih =>
      cases fuel with
      | zero =>
          exfalso
          have : (Formula.not φ).depth = φ.depth + 1 := rfl
          omega
      | succ f =>
          have hf : φ.depth ≤ f := by
            have : (Formula.not φ).depth = φ.depth + 1 := rfl
            omega
          show decodeAux (f + 1)
              ([false, false, true] ++ encode φ ++ tail) = _
          have step : decodeAux f (encode φ ++ tail) = some (φ, tail) :=
            ih tail f hf
          simp [decodeAux, step]
  | and φ ψ ihφ ihψ =>
      cases fuel with
      | zero =>
          exfalso
          have : (Formula.and φ ψ).depth = max φ.depth ψ.depth + 1 := rfl
          omega
      | succ f =>
          have hfφ : φ.depth ≤ f := by
            have h₁ : (Formula.and φ ψ).depth = max φ.depth ψ.depth + 1 :=
              rfl
            have h₂ : φ.depth ≤ max φ.depth ψ.depth := le_max_left _ _
            omega
          have hfψ : ψ.depth ≤ f := by
            have h₁ : (Formula.and φ ψ).depth = max φ.depth ψ.depth + 1 :=
              rfl
            have h₂ : ψ.depth ≤ max φ.depth ψ.depth := le_max_right _ _
            omega
          show decodeAux (f + 1)
              ([false, true, false] ++ encode φ ++ encode ψ ++ tail) = _
          have stepφ : decodeAux f (encode φ ++ (encode ψ ++ tail))
              = some (φ, encode ψ ++ tail) :=
            ihφ (encode ψ ++ tail) f hfφ
          have stepψ : decodeAux f (encode ψ ++ tail) = some (ψ, tail) :=
            ihψ tail f hfψ
          simp [decodeAux, List.append_assoc, stepφ, stepψ]
  | or φ ψ ihφ ihψ =>
      cases fuel with
      | zero =>
          exfalso
          have : (Formula.or φ ψ).depth = max φ.depth ψ.depth + 1 := rfl
          omega
      | succ f =>
          have hfφ : φ.depth ≤ f := by
            have h₁ : (Formula.or φ ψ).depth = max φ.depth ψ.depth + 1 :=
              rfl
            have h₂ : φ.depth ≤ max φ.depth ψ.depth := le_max_left _ _
            omega
          have hfψ : ψ.depth ≤ f := by
            have h₁ : (Formula.or φ ψ).depth = max φ.depth ψ.depth + 1 :=
              rfl
            have h₂ : ψ.depth ≤ max φ.depth ψ.depth := le_max_right _ _
            omega
          show decodeAux (f + 1)
              ([false, true, true] ++ encode φ ++ encode ψ ++ tail) = _
          have stepφ : decodeAux f (encode φ ++ (encode ψ ++ tail))
              = some (φ, encode ψ ++ tail) :=
            ihφ (encode ψ ++ tail) f hfφ
          have stepψ : decodeAux f (encode ψ ++ tail) = some (ψ, tail) :=
            ihψ tail f hfψ
          simp [decodeAux, List.append_assoc, stepφ, stepψ]
  | imp φ ψ ihφ ihψ =>
      cases fuel with
      | zero =>
          exfalso
          have : (Formula.imp φ ψ).depth = max φ.depth ψ.depth + 1 := rfl
          omega
      | succ f =>
          have hfφ : φ.depth ≤ f := by
            have h₁ : (Formula.imp φ ψ).depth = max φ.depth ψ.depth + 1 :=
              rfl
            have h₂ : φ.depth ≤ max φ.depth ψ.depth := le_max_left _ _
            omega
          have hfψ : ψ.depth ≤ f := by
            have h₁ : (Formula.imp φ ψ).depth = max φ.depth ψ.depth + 1 :=
              rfl
            have h₂ : ψ.depth ≤ max φ.depth ψ.depth := le_max_right _ _
            omega
          show decodeAux (f + 1)
              ([true, false, false] ++ encode φ ++ encode ψ ++ tail) = _
          have stepφ : decodeAux f (encode φ ++ (encode ψ ++ tail))
              = some (φ, encode ψ ++ tail) :=
            ihφ (encode ψ ++ tail) f hfφ
          have stepψ : decodeAux f (encode ψ ++ tail) = some (ψ, tail) :=
            ihψ tail f hfψ
          simp [decodeAux, List.append_assoc, stepφ, stepψ]

/-- Tree depth is bounded by encoded length — used to discharge the
    fuel side-condition in `encode_decode_roundtrip`.  -/
theorem depth_le_encode_length (φ : Formula) : φ.depth ≤ (encode φ).length + 1 := by
  induction φ with
  | atom n =>
      show 1 ≤ (encode (.atom n)).length + 1
      omega
  | not φ ih =>
      have hd : (Formula.not φ).depth = φ.depth + 1 := rfl
      have hlen : (encode (.not φ)).length = (encode φ).length + 3 := by
        simp [encode]
      omega
  | and φ ψ ihφ ihψ =>
      have hd : (Formula.and φ ψ).depth = max φ.depth ψ.depth + 1 := rfl
      have hlen :
          (encode (.and φ ψ)).length
            = (encode φ).length + (encode ψ).length + 3 := by
        simp [encode]
      have hmax : max φ.depth ψ.depth ≤ φ.depth + ψ.depth := by
        rcases le_total φ.depth ψ.depth with h | h
        · rw [max_eq_right h]; omega
        · rw [max_eq_left h]; omega
      omega
  | or φ ψ ihφ ihψ =>
      have hd : (Formula.or φ ψ).depth = max φ.depth ψ.depth + 1 := rfl
      have hlen :
          (encode (.or φ ψ)).length
            = (encode φ).length + (encode ψ).length + 3 := by
        simp [encode]
      have hmax : max φ.depth ψ.depth ≤ φ.depth + ψ.depth := by
        rcases le_total φ.depth ψ.depth with h | h
        · rw [max_eq_right h]; omega
        · rw [max_eq_left h]; omega
      omega
  | imp φ ψ ihφ ihψ =>
      have hd : (Formula.imp φ ψ).depth = max φ.depth ψ.depth + 1 := rfl
      have hlen :
          (encode (.imp φ ψ)).length
            = (encode φ).length + (encode ψ).length + 3 := by
        simp [encode]
      have hmax : max φ.depth ψ.depth ≤ φ.depth + ψ.depth := by
        rcases le_total φ.depth ψ.depth with h | h
        · rw [max_eq_right h]; omega
        · rw [max_eq_left h]; omega
      omega

/-- **Faithfulness.**  `decodeOpt ∘ encode = some`: every formula
    round-trips through its bit-string encoding. -/
theorem encode_decode_roundtrip (φ : Formula) :
    decodeOpt (encode φ) = some φ := by
  unfold decodeOpt
  have hfuel : φ.depth ≤ (encode φ).length + 1 :=
    depth_le_encode_length φ
  have hcons : decodeAux ((encode φ).length + 1) (encode φ ++ []) =
      some (φ, []) :=
    decodeAux_encode_append φ [] _ hfuel
  rw [List.append_nil] at hcons
  rw [hcons]

/-! ## § 5 The `R N` bridge

`encode` produces a variable-length `List Bool`.  The R-Family carrier
`R N := Fin N → Bool` is fixed-length, so we provide pad-or-truncate
helpers.  Round-trip via `R N` holds when `N` is at least the encoded
length (no truncation). -/

/-- `toR bs N` : convert a `List Bool` to a `R N` cell.  Out-of-range
    indices get `false`; in-range indices use `bs.getElem?`. -/
def toR (bs : List Bool) (N : ℕ) : R N :=
  fun i => (bs[i.val]?).getD false

/-- `fromR v` : convert a `R N` cell back to a `List Bool` of length
    exactly `N`.  This is the right inverse of `toR` when `bs.length
    = N`. -/
def fromR {N : ℕ} (v : R N) : List Bool :=
  (List.finRange N).map (fun i => v i)

@[simp] theorem fromR_length {N : ℕ} (v : R N) : (fromR v).length = N := by
  simp [fromR]

/-- Canonical `Formula → R N` embedding.  Caller is responsible for
    choosing `N ≥ (encode φ).length`. -/
def encodeR (φ : Formula) (N : ℕ) : R N := toR (encode φ) N

/-- Decode by reading off the `N` bits of `v` (with trailing `false`s
    treated as the post-formula slack) and stripping the trailing
    `false`-run that is *not* part of any formula's encoding. -/
def decodeR {N : ℕ} (v : R N) : Option Formula :=
  -- Try to decode an *initial* segment: use `decodeAux` directly with
  -- length+1 fuel, and accept any well-formed prefix whose remainder
  -- is all `false`s (the padding we added in `toR`).
  match decodeAux ((fromR v).length + 1) (fromR v) with
  | some (φ, rest) =>
      if rest.all (· = false) then some φ else none
  | none => none

/-- Helper: `toR (encode φ) N` for `N ≥ (encode φ).length` yields a
    bit-stream whose `fromR` returns `encode φ` padded by `false`s. -/
theorem fromR_toR_padded
    (bs : List Bool) (N : ℕ) (hN : bs.length ≤ N) :
    fromR (toR bs N) = bs ++ List.replicate (N - bs.length) false := by
  apply List.ext_getElem
  · simp [fromR_length, hN]
  · intro i hi₁ hi₂
    simp only [fromR, toR, List.getElem_map, List.getElem_finRange]
    by_cases h : i < bs.length
    · have h₁ : bs[i]? = some bs[i] := List.getElem?_eq_getElem h
      rw [List.getElem_append_left h]
      simp [h₁]
    · have hge : bs.length ≤ i := Nat.le_of_not_lt h
      have h₁ : bs[i]? = none := List.getElem?_eq_none hge
      rw [List.getElem_append_right hge]
      simp [h₁, List.getElem_replicate]

/-- Decoding `decodeAux` ignores trailing `false`-runs that follow a
    fully-consumed formula:  `decodeAux fuel (encode φ ++ pad) = some (φ, pad)`
    where `pad` is any list (in particular, the padding `replicate k false`). -/
theorem decodeAux_encode_pad
    (φ : Formula) (pad : List Bool) (fuel : Nat) (hfuel : φ.depth ≤ fuel) :
    decodeAux fuel (encode φ ++ pad) = some (φ, pad) :=
  decodeAux_encode_append φ pad fuel hfuel

/-- All-`false` lists pass the all-`false` predicate. -/
theorem all_false_replicate (k : ℕ) :
    (List.replicate k false).all (· = false) = true := by
  induction k with
  | zero => rfl
  | succ k _ => simp [List.replicate, List.all_cons]

/-- **R-Family round-trip.**  When `N ≥ (encode φ).length`, the
    R-Family embedding faithfully round-trips. -/
theorem encodeR_decodeR_roundtrip
    (φ : Formula) (N : ℕ) (hN : (encode φ).length ≤ N) :
    decodeR (encodeR φ N) = some φ := by
  have hbs : fromR (toR (encode φ) N)
      = encode φ ++ List.replicate (N - (encode φ).length) false :=
    fromR_toR_padded (encode φ) N hN
  have hfuel :
      φ.depth ≤
        (encode φ ++ List.replicate (N - (encode φ).length) false).length + 1 := by
    have hb : φ.depth ≤ (encode φ).length + 1 := depth_le_encode_length φ
    have hl : (encode φ).length ≤
        (encode φ ++ List.replicate (N - (encode φ).length) false).length := by
      simp
    omega
  have hcons :
      decodeAux
        ((encode φ ++ List.replicate (N - (encode φ).length) false).length + 1)
        (encode φ ++ List.replicate (N - (encode φ).length) false)
        = some (φ, List.replicate (N - (encode φ).length) false) :=
    decodeAux_encode_pad φ
      (List.replicate (N - (encode φ).length) false) _ hfuel
  show (match decodeAux ((fromR (toR (encode φ) N)).length + 1)
        (fromR (toR (encode φ) N)) with
      | some (φ, rest) =>
          if rest.all (· = false) = true then some φ else none
      | none => none) = some φ
  rw [hbs, hcons]
  -- The remaining goal is `(if (List.replicate k false).all (· = false) then
  -- some φ else none) = some φ`; simp's decision procedure normalises the
  -- all-false check away.  `all_false_replicate` is the underlying lemma but
  -- not directly needed in the closing simp.
  simp

/-! ## § 6 Case study — `¬ p ∨ q` and the encoding evaluation

We concretely evaluate the embedding on the formula `(¬ p ∨ q)` where
`p = atom 0`, `q = atom 1`.  This is the §5 deliverable per the
roadmap. -/

/-- The case-study formula: `¬ p ∨ q` with `p = atom 0`, `q = atom 1`. -/
def caseStudy : Formula :=
  .or (.not (.atom 0)) (.atom 1)

/-- The case-study formula `(¬ p ∨ q)` has the documented bit-string
    encoding.  Manually:

    `encode (or (not (atom 0)) (atom 1))`
      = `[F, T, T]` (or-tag)
        ++ `encode (not (atom 0))`
        ++ `encode (atom 1)`
      = `[F, T, T]`
        ++ `[F, F, T]` (not-tag)
          ++ `encode (atom 0)`
        ++ `[F, F, F]` (atom-tag)
          ++ `[F]` (encodeNat 0)
      = `[F, T, T]`
        ++ `[F, F, T]`
          ++ `[F, F, F]`
            ++ `[F]`
        ++ `[F, F, F]`
          ++ `[T, F]`
      = `[F, T, T, F, F, T, F, F, F, F, F, F, F, T, F]`  (15 bits) -/
example : encode caseStudy =
    [false, true,  true,
     false, false, true,
     false, false, false, false,
     false, false, false,
     true,  false] := by
  rfl

/-- Round-trip on the case-study formula. -/
example : decodeOpt (encode caseStudy) = some caseStudy :=
  encode_decode_roundtrip caseStudy

/-- Round-trip via `R N` with `N = 16` (one extra bit of slack). -/
example : decodeR (encodeR caseStudy 16) = some caseStudy :=
  encodeR_decodeR_roundtrip caseStudy 16 (by decide)

/-! ## § 7 First-order extension sketch (informal)

The PL embedding above uses tags `000, 001, 010, 011, 100`.  Tags
`101, 110, 111` are free for a first-order extension over a *finite*
relation signature `rel = Fin r` and variable space `var = Fin v`:

* Add `inductive Term : Type | var : Fin v → Term | const : Fin c → Term`
  with a 1-bit tag (`var` vs `const`) plus a unary-encoded `Fin n` index.
* Replace `atom : Nat → Formula` with `atom : Fin r → List Term → Formula`
  (a `r`-relation applied to a list of terms).  Length of term-list
  is determined by signature arity (a function of `r`, not free).
* Add `forall, exists : Fin v → Formula → Formula` under tags `101, 110`.

The round-trip lemma generalises mechanically: each new constructor
contributes one inductive case in `decodeAux_encode_append`, with
exactly the same shape as the existing `not` / `and` cases.  This file
chooses **PL** as the minimal witness; the first-order generalisation
is a straightforward continuation, not a new theoretical step.  Per
the roadmap, this is sufficient evidence that the **propositional /
first-order syntactic layer** factors through the R-Family carrier.

-/

end SSBX.Foundation.Wen.Embeddings.FOL
