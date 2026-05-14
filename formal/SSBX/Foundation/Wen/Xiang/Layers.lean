/-
# Wen.SquaringTower.Layers — five interface layer aliases

The five interface tower layers of `wen-algebra` v0.2 §3.1, exposed as
plain `abbrev`s on top of the `X n` family.  Each is the `n`-fold image
direct product at its proper arity:

| Lean alias             | n | 文        | English             | |·|  |
|------------------------|---|-----------|---------------------|------|
| `Origin`               | 0 | 太极      | Origin              |    1 |
| `Image1`               | 1 | 象 / 四象 | Image / Four Images |    4 |
| `PairedImage`          | 2 | 对象      | Paired Image        |   16 |
| `Hexagram`             | 3 | 卦        | Hexagram            |   64 |
| `TemporalHexagram`     | 4 | 时卦      | Temporal Hexagram   |  256 |

`abbrev` keeps these definitionally equal to the corresponding `X n`,
so all instance resolution and proofs work transparently across both
names.  Per v0.2 §3.1, layers `n ≥ 5` are **IR-internal only** and
deliberately not aliased here.

Cardinality theorems are recorded at the bottom; they are
`Fintype.card`-statements proved by `decide`.
-/

import SSBX.Foundation.Wen.SquaringTower.X
import Mathlib.Data.Fintype.Pi

namespace SSBX.Foundation.Wen.SquaringTower

/-! ## § 1 The five interface aliases -/

/-- **太极 / Origin** — `X 0`.  The trivial layer with one element
    (the empty tuple).  `wen-algebra` v0.2 §3.1, §4.3. -/
abbrev Origin : Type := X 0

/-- **象 / 四象 / Image / Four Images** — `X 1`.  The atomic layer
    isomorphic to `Image` itself; four V₄ elements.
    `wen-algebra` v0.2 §3.1, §4.3. -/
abbrev Image1 : Type := X 1

/-- **对象 / Paired Image** — `X 2`.  Sixteen elements, two image
    coordinates.  `wen-algebra` v0.2 §3.1, §4.3. -/
abbrev PairedImage : Type := X 2

/-- **卦 / 六十四卦 / Hexagram** — `X 3`.  Sixty-four elements,
    three image coordinates (= six F₂-bits, = six 爻).  Per v0.2 §4.4
    this is the natural algebraic basis of the classical 64-hexagram
    tradition. -/
abbrev Hexagram : Type := X 3

/-- **时卦 / Temporal Hexagram** — `X 4`.  256 elements, four image
    coordinates: per v0.2 §4.4 the first three are the `Hexagram` factor
    and the fourth is the `Time-Image` factor (`{Atemporal, Not-Yet,
    Already, Composite-Now}`). -/
abbrev TemporalHexagram : Type := X 4

/-! ## § 2 Layer cardinalities

Per `wen-algebra` v0.2 §4.3, |X n| = 4ⁿ.  Proofs go via Mathlib's
`Fintype.card_fun` and `Fintype.card_fin`, plus the atomic
`Image_card = 4`. -/

/-- |Image| = 4 (V₄ has four elements). -/
theorem Image_card : Fintype.card Image = 4 := by decide

theorem Origin_card : Fintype.card Origin = 1 := by decide

theorem Image1_card : Fintype.card Image1 = 4 := by decide

theorem PairedImage_card : Fintype.card PairedImage = 16 := by decide

theorem Hexagram_card : Fintype.card Hexagram = 64 := by native_decide

theorem TemporalHexagram_card : Fintype.card TemporalHexagram = 256 := by native_decide

/-- All five layer cardinalities packaged as one summary lemma. -/
theorem layer_cardinalities :
    Fintype.card Origin = 1
    ∧ Fintype.card Image1 = 4
    ∧ Fintype.card PairedImage = 16
    ∧ Fintype.card Hexagram = 64
    ∧ Fintype.card TemporalHexagram = 256 :=
  ⟨Origin_card, Image1_card, PairedImage_card, Hexagram_card,
   TemporalHexagram_card⟩

/-! ## § 3 The unique `Origin` element -/

namespace Origin

/-- 太极 — the unique element of `Origin = X 0`.  This is the empty
    tuple of `Image` atoms; in v0.2 §0.2 it is the trivial 道. -/
def taiji : Origin := fun i => i.elim0

theorem unique (a b : Origin) : a = b := by
  funext i
  exact i.elim0

end Origin

end SSBX.Foundation.Wen.SquaringTower
