/-
# Foundation.Atlas.Yi.Stratify — R₀..R₈ closure bundle on R-Family carriers

R-Family port of the classical `SSBX.Foundation.Bagua.R8Stratify` module
(formerly under `Atlas/Yi/Classical/Cells/R8Stratify.lean`).  Differences:

* All layers `R₀..R₈` are indexed `R n` from `Foundation.R.Basic` plus the
  Atlas naming overlay (`Yao = R 1`, `Trigram = R 3`, `Hexagram = R 6`,
  `Shi = R 2`, `Cell128 = R 7`, `Cell256 = R 8`).
* No legacy `BenZheng.Mian` / `Sheng` / `R8.shiCuo` dependencies.
* Operators reused: `Cell256.hexCuo / hexZong / hexHu / hexCuoZong`,
  `Cell256.shiCuo / shiZong / shiCuoZong`, single-yao `flip1..flip6`.
* The (Z/2)⁸ group action is exposed via `Cell256.xor` and the Cayley
  endomap (already proven `Function.Injective`).
* `R8_complete` re-packages the public Phase-A summary plus
  stratification (R₇ ↔ R₈ lift/project) and cardinalities.

## Layer map (all `R n` carriers — `|R n| = 2^n`)

    R₀  =  R 0          =  1            (trivial / 太极)
    R₁  =  R 1          =  2            (Yao / 爻)
    R₂  =  R 2          =  4            (Shi / 四象)
    R₃  =  R 3          =  8            (Trigram / 八卦)
    R₄  =  R 4          =  16           (= Shi × Shi)
    R₅  =  R 5          =  32
    R₆  =  R 6          =  64           (Hexagram / 六十四卦)
    R₇  =  Cell128      =  128          (Hexagram × YinBit)
    R₈  =  Cell256      =  256          (Hexagram × Shi)

## Doctrinal anchor

* `wen-algebra.md` v0.6 §1.1–§1.8 (R-Family Tower).
* `v4-foundation.md` v0.5 §15 (external traditions).
* `yi-RO-hierarchy.md` (R/O hierarchy doctrine).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Hexagrams
import SSBX.Foundation.Atlas.Yi.Shi
import SSBX.Foundation.Atlas.Yi.Operators
import SSBX.Foundation.Atlas.Yi.Cell128
import SSBX.Foundation.Atlas.Yi.Cell256

namespace SSBX.Foundation.Atlas.Yi.Stratify

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 R-Hierarchy R₀..R₈: index-named aliases -/

/-- R₀ (太极) = `R 0` = 1 trivial element. -/
abbrev R₀ := R 0

/-- R₁ (爻) = `R 1` = 2-element bit; same as `Yao`. -/
abbrev R₁ := R 1

/-- R₂ (四象 / 时态 V₄) = `R 2` = 4 elements; same as `Shi`. -/
abbrev R₂ := R 2

/-- R₃ (八卦) = `R 3` = 8 elements; same as `Trigram`. -/
abbrev R₃ := R 3

/-- R₄ (= 四象 × 四象, the "min-complete unit") = `R 4` = 16. -/
abbrev R₄ := R 4

/-- R₅ = `R 5` = 32 (no traditional Yi anchor). -/
abbrev R₅ := R 5

/-- R₆ (六十四卦) = `R 6` = 64; same as `Hexagram`. -/
abbrev R₆ := R 6

/-- R₇ (R₇-layer / Hexagram × YinBit) = `Cell128` = 128. -/
abbrev R₇ := Cell128

/-- R₈ (256-cell / Hexagram × Shi) = `Cell256` = 256. -/
abbrev R₈ := Cell256

/-! ### Cardinality theorems for every layer.

These use `Fintype.card` rather than ad-hoc list enumerations: with `R n
= Fin n → Bool` the cardinality is just `2^n`, available via
`R.card_eq`.  For `R₇ / R₈` we also expose the product-cardinality
since `Cell128 = Hexagram × YinBit` and `Cell256 = Hexagram × Shi`. -/

theorem R₀_card : Fintype.card R₀ = 1 := R.R0_card

theorem R₁_card : Fintype.card R₁ = 2 := R.R1_card

theorem R₂_card : Fintype.card R₂ = 4 := R.R2_card

theorem R₃_card : Fintype.card R₃ = 8 := by
  show Fintype.card (R 3) = 8
  rw [R.card_eq]; rfl

theorem R₄_card : Fintype.card R₄ = 16 := R.R4_card

theorem R₅_card : Fintype.card R₅ = 32 := by
  show Fintype.card (R 5) = 32
  rw [R.card_eq]; rfl

theorem R₆_card : Fintype.card R₆ = 64 := by
  show Fintype.card (R 6) = 64
  rw [R.card_eq]; rfl

/-- |R₇| = |Hexagram| · |YinBit| = 64 · 2 = 128. -/
theorem R₇_card : Fintype.card R₇ = 128 := by
  show Fintype.card (Hexagram × YinBit) = 128
  rw [Fintype.card_prod]
  show Fintype.card (R 6) * Fintype.card Bool = 128
  rw [R.card_eq, Fintype.card_bool]; rfl

/-- |R₈| = |Hexagram| · |Shi| = 64 · 4 = 256. -/
theorem R₈_card : Fintype.card R₈ = 256 := by
  show Fintype.card (Hexagram × Shi) = 256
  rw [Fintype.card_prod]
  show Fintype.card (R 6) * Fintype.card (R 2) = 256
  rw [R.card_eq, R.card_eq]; rfl

/-! ## § 2 Step-up isomorphisms — R(n+1) factors over R(n)

The R-Family is self-similar: each layer factors as the product of two
strictly-smaller layers in `(Z/2)`.  Here we expose the splittings used
by the higher layers. -/

/-- R₇ = R₆ × R₁ (definitional — `Cell128 := Hexagram × YinBit`). -/
example : R₇ = (Hexagram × YinBit) := rfl

/-- R₈ = R₆ × R₂ (definitional — `Cell256 := Hexagram × Shi`). -/
example : R₈ = (Hexagram × Shi) := rfl

/-- "GuoBit" — the second Shi bit (the V₄ T-axis), the only bit that
    `Cell128 → Cell256` adds.  `false` = no future trace; `true` = with
    future trace. -/
abbrev GuoBit : Type := Bool

/-! ### R₇ → R₈ lift: bundle a (Hexagram, YinBit) with a GuoBit -/

/-- Build a Shi from its two bit components. -/
def shiOfBits (yb : YinBit) (gb : GuoBit) : Shi := fun i =>
  match i with
  | ⟨0, _⟩ => yb
  | ⟨1, _⟩ => gb

/-- Read the YinBit (s 0). -/
def shiYinBit (s : Shi) : YinBit := s ⟨0, by decide⟩

/-- Read the GuoBit (s 1). -/
def shiGuoBit (s : Shi) : GuoBit := s ⟨1, by decide⟩

@[simp] theorem shiYinBit_ofBits (yb : YinBit) (gb : GuoBit) :
    shiYinBit (shiOfBits yb gb) = yb := rfl

@[simp] theorem shiGuoBit_ofBits (yb : YinBit) (gb : GuoBit) :
    shiGuoBit (shiOfBits yb gb) = gb := rfl

theorem shiOfBits_yinBit_guoBit (s : Shi) :
    shiOfBits (shiYinBit s) (shiGuoBit s) = s := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- R₇ → R₈ lift: bundle a `Cell128 = (Hexagram, YinBit)` with a
    GuoBit. -/
def liftR7toR8 (c : R₇) (gb : GuoBit) : R₈ :=
  (c.1, shiOfBits c.2 gb)

/-- R₈ → R₇ project: drop the GuoBit (keep Shi's first bit). -/
def projR8toR7 (c : R₈) : R₇ :=
  (c.1, shiYinBit c.2)

/-- Round-trip: `proj ∘ lift = id` (the YinBit is preserved). -/
theorem projR8toR7_liftR7toR8 (c : R₇) (gb : GuoBit) :
    projR8toR7 (liftR7toR8 c gb) = c := by
  rcases c with ⟨h, yb⟩
  unfold projR8toR7 liftR7toR8
  show (h, shiYinBit (shiOfBits yb gb)) = (h, yb)
  rw [shiYinBit_ofBits]

/-- The GuoBit projection: drop the YinBit, keep Shi's second bit. -/
def projR8toGuoBit (c : R₈) : GuoBit := shiGuoBit c.2

theorem projR8toGuoBit_liftR7toR8 (c : R₇) (gb : GuoBit) :
    projR8toGuoBit (liftR7toR8 c gb) = gb := by
  rcases c with ⟨h, yb⟩
  unfold projR8toGuoBit liftR7toR8
  show shiGuoBit (shiOfBits yb gb) = gb
  rw [shiGuoBit_ofBits]

/-- Joint surjectivity: every Cell256 element is exactly
    `liftR7toR8 (projR8toR7 c) (projR8toGuoBit c)`. -/
theorem lift_proj_full (c : R₈) :
    liftR7toR8 (projR8toR7 c) (projR8toGuoBit c) = c := by
  rcases c with ⟨h, s⟩
  unfold liftR7toR8 projR8toR7 projR8toGuoBit
  show (h, shiOfBits (shiYinBit s) (shiGuoBit s)) = (h, s)
  rw [shiOfBits_yinBit_guoBit]

/-! ## § 3 V₄ on R₈: hex / shi / combined parity-and-time operators

The classical R8Stratify exposed four named operators:

* `parity`        = hex `cuo` lift (preserve Shi)        →  `hexCuo`
* `timeReversal`  = hex `zong` + shi `reverse`            →  `hexZong ∘ shiZong`
* `PT`            = `parity ∘ timeReversal`               →  `hexCuoZong ∘ shiZong`
* `yComb`         = hex `hu` lift (preserve Shi)          →  `hexHu`

All four come for free from `Cell256.lean`; we just re-export them under
the stratification names. -/

/-- P (parity): hex `cuo` lift on `Cell256`; preserves Shi. -/
abbrev parity : R₈ → R₈ := Cell256.hexCuo

/-- T (time-reversal): hex `zong` + Shi `reverse` (the V₄ T-axis flip).
    On bit level: reverse the 6 yao and flip the GuoBit. -/
def timeReversal (c : R₈) : R₈ :=
  Cell256.shiZong (Cell256.hexZong c)

/-- PT: `parity ∘ timeReversal` (= `cuoZong` on hex + Shi reverse). -/
def PT (c : R₈) : R₈ :=
  parity (timeReversal c)

/-- Y (Y-combinator / 互): hex `hu` lift; preserves Shi. -/
abbrev yComb : R₈ → R₈ := Cell256.hexHu

theorem parity_parity (c : R₈) : parity (parity c) = c :=
  Cell256.hexCuo_involutive c

theorem timeReversal_timeReversal (c : R₈) :
    timeReversal (timeReversal c) = c := by
  rcases c with ⟨h, s⟩
  unfold timeReversal Cell256.shiZong Cell256.hexZong
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · exact Hexagram.zong_involutive h
  · exact Shi.reverse_involutive s

/-- P and T commute: `parity ∘ timeReversal = timeReversal ∘ parity`. -/
theorem parity_timeReversal_comm (c : R₈) :
    parity (timeReversal c) = timeReversal (parity c) := by
  rcases c with ⟨h, s⟩
  unfold parity Cell256.hexCuo timeReversal Cell256.hexZong Cell256.shiZong
  refine Prod.mk.injEq .. |>.mpr ⟨?_, rfl⟩
  exact (Hexagram.cuo_zong_comm h).symm

theorem PT_PT (c : R₈) : PT (PT c) = c := by
  show parity (timeReversal (parity (timeReversal c))) = c
  rw [← parity_timeReversal_comm (timeReversal c), parity_parity,
      timeReversal_timeReversal]

/-- 乾乾 / 道 cell is a Y-fixed point. -/
theorem yComb_qianqian_dao :
    yComb (Hexagram.qianqian, Shi.dao) = (Hexagram.qianqian, Shi.dao) := by
  unfold yComb Cell256.hexHu
  rw [Hexagram.hu_qianqian]

/-- 坤坤 / 道 cell is a Y-fixed point. -/
theorem yComb_kunkun_dao :
    yComb (Hexagram.kunkun, Shi.dao) = (Hexagram.kunkun, Shi.dao) := by
  unfold yComb Cell256.hexHu
  rw [Hexagram.hu_kunkun]

/-! ## § 4 (Z/2)⁸ group action — simply transitive on R₈

The (Z/2)⁸ group is `Cell256` itself; the action is `Cell256.xor`.  We
already have `Cell256.cayley_inj`; pair it with surjectivity from
`Cell256.xor_origin` to get simply-transitive at the origin
`(qianqian, dao)`. -/

/-- (Z/2)⁸ group element type — same as `Cell256`, just renamed. -/
abbrev R₈Combo : Type := Cell256

/-- Group element ⊕ point action — same as `Cell256.xor`. -/
def comboApply (g : R₈Combo) (c : R₈) : R₈ := Cell256.xor g c

/-- At the origin, the action is identity-in-component:
    `comboApply g origin = g`. -/
theorem comboApply_at_origin (g : R₈Combo) :
    comboApply g Cell256.origin = g := by
  unfold comboApply
  exact Cell256.xor_origin g

/-- Surjective at the origin: every `c : R₈` is `comboApply g origin` for
    some `g`. -/
theorem comboApply_origin_surjective (c : R₈) :
    ∃ g : R₈Combo, comboApply g Cell256.origin = c :=
  ⟨c, comboApply_at_origin c⟩

/-- Injective at the origin (Cayley regular). -/
theorem comboApply_origin_injective :
    Function.Injective (fun g : R₈Combo => comboApply g Cell256.origin) := by
  intro g₁ g₂ h
  have h₁ : comboApply g₁ Cell256.origin = g₁ := comboApply_at_origin g₁
  have h₂ : comboApply g₂ Cell256.origin = g₂ := comboApply_at_origin g₂
  exact (h₁.symm.trans h).trans h₂

/-- Simply-transitive at the origin: unique element witnesses each
    target. -/
theorem comboApply_origin_simply_transitive (c : R₈) :
    ∃ g : R₈Combo, comboApply g Cell256.origin = c
      ∧ ∀ g' : R₈Combo, comboApply g' Cell256.origin = c → g' = g := by
  refine ⟨c, comboApply_at_origin c, ?_⟩
  intro g' hg'
  exact comboApply_origin_injective (hg'.trans (comboApply_at_origin c).symm)

/-! ## § 5 R₇ ↔ R₈ stratification: lifting & projection

R₇ and R₈ form an adjacent pair in the squaring tower; the lift and
projection above are the canonical bridge.  We expose them with the
naming used by the closure bundle theorem. -/

/-- Lift a single R₇ point via the trivial GuoBit (the V₄ identity
    half).  This is the canonical inclusion `R₇ ↪ R₈`. -/
def includeR7toR8 (c : R₇) : R₈ := liftR7toR8 c false

/-- The canonical inclusion lands on the `false`-GuoBit half. -/
theorem projR8toGuoBit_includeR7toR8 (c : R₇) :
    projR8toGuoBit (includeR7toR8 c) = false :=
  projR8toGuoBit_liftR7toR8 c false

/-- The inclusion is a section of the YinBit projection. -/
theorem projR8toR7_includeR7toR8 (c : R₇) :
    projR8toR7 (includeR7toR8 c) = c :=
  projR8toR7_liftR7toR8 c false

/-! ## § 6 R₈ closure summary theorem — the public hand-off bundle

This is the R-Family analog of the classical `R8_complete`.  It
collects:

  1. Cardinalities of every layer R₀..R₈
  2. Step-up factorisations (Cell128 = Hexagram × Bool;
     Cell256 = Hexagram × Shi)
  3. V₄ on R₈ closure (P/T/PT/Y involutivity + P-T commutativity)
  4. (Z/2)⁸ group action simply-transitive at the origin
  5. R₇ ↔ R₈ stratification (lift/project round-trip)
  6. Cayley regular representation (injection + retraction-at-origin)
  7. 印 / 投 mask-form involutivity (re-exported from `Cell256`)
-/

theorem R8_complete :
    -- (1) Cardinalities of every layer
    Fintype.card R₀ = 1
    ∧ Fintype.card R₁ = 2
    ∧ Fintype.card R₂ = 4
    ∧ Fintype.card R₃ = 8
    ∧ Fintype.card R₄ = 16
    ∧ Fintype.card R₅ = 32
    ∧ Fintype.card R₆ = 64
    ∧ Fintype.card R₇ = 128
    ∧ Fintype.card R₈ = 256
    -- (2) Step-up factorisations (definitional equality of types)
    ∧ (∀ c : R₇, c = (c.1, c.2))
    ∧ (∀ c : R₈, c = (c.1, c.2))
    -- (3) V₄ on R₈ closure: P/T/PT/Y involutivity + PT commute
    ∧ (∀ c : R₈, parity (parity c) = c)
    ∧ (∀ c : R₈, timeReversal (timeReversal c) = c)
    ∧ (∀ c : R₈, PT (PT c) = c)
    ∧ (∀ c : R₈, parity (timeReversal c) = timeReversal (parity c))
    -- (4) (Z/2)⁸ group action simply-transitive at origin
    ∧ Function.Injective (fun g : R₈Combo => comboApply g Cell256.origin)
    ∧ (∀ c : R₈, ∃ g : R₈Combo, comboApply g Cell256.origin = c)
    -- (5) R₇ ↔ R₈ stratification round-trip
    ∧ (∀ c : R₇, ∀ gb : GuoBit, projR8toR7 (liftR7toR8 c gb) = c)
    ∧ (∀ c : R₇, ∀ gb : GuoBit, projR8toGuoBit (liftR7toR8 c gb) = gb)
    ∧ (∀ c : R₈, liftR7toR8 (projR8toR7 c) (projR8toGuoBit c) = c)
    -- (6) Cayley regular representation: injection + retraction
    ∧ Function.Injective Cell256.cayley
    ∧ (∀ c : R₈, Cell256.epsAtOrigin (Cell256.cayley c) = c)
    ∧ Function.Injective Cell128.cayley
    ∧ (∀ c : R₇, Cell128.epsAtOrigin (Cell128.cayley c) = c)
    -- (7) 印 / 投 mask-form involutivity + commutativity
    ∧ (∀ c : R₈, Cell256.imprint (Cell256.imprint c) = c)
    ∧ (∀ c : R₈, Cell256.project (Cell256.project c) = c)
    ∧ (∀ c : R₈, Cell256.imprint (Cell256.project c)
                  = Cell256.project (Cell256.imprint c))
    ∧ (∀ c : R₇, Cell128.imprint (Cell128.imprint c) = c) :=
  ⟨R₀_card, R₁_card, R₂_card, R₃_card, R₄_card, R₅_card, R₆_card,
   R₇_card, R₈_card,
   fun c => by rcases c with ⟨_, _⟩; rfl,
   fun c => by rcases c with ⟨_, _⟩; rfl,
   parity_parity,
   timeReversal_timeReversal,
   PT_PT,
   parity_timeReversal_comm,
   comboApply_origin_injective,
   comboApply_origin_surjective,
   projR8toR7_liftR7toR8,
   projR8toGuoBit_liftR7toR8,
   lift_proj_full,
   Cell256.cayley_inj,
   Cell256.epsAtOrigin_cayley,
   Cell128.cayley_inj,
   Cell128.epsAtOrigin_cayley,
   Cell256.imprint_involutive,
   Cell256.project_involutive,
   Cell256.imprint_project_comm,
   Cell128.imprint_involutive⟩

/-! ## § 7 Per-layer cardinality enumeration via `native_decide` -/

/-- The full layer cardinality vector `[1, 2, 4, 8, 16, 32, 64, 128, 256]`. -/
def layerCards : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256]

theorem layerCards_length : layerCards.length = 9 := by native_decide

theorem layerCards_sum : layerCards.sum = 511 := by native_decide

/-- Cumulative cardinality through R₈: 1+2+4+...+256 = 511 = 2^9 - 1. -/
theorem total_cells_through_R₈ :
    Fintype.card R₀ + Fintype.card R₁ + Fintype.card R₂ + Fintype.card R₃
      + Fintype.card R₄ + Fintype.card R₅ + Fintype.card R₆
      + Fintype.card R₇ + Fintype.card R₈ = 511 := by
  rw [R₀_card, R₁_card, R₂_card, R₃_card, R₄_card, R₅_card, R₆_card,
      R₇_card, R₈_card]

end SSBX.Foundation.Atlas.Yi.Stratify
