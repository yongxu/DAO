/-
# V₄ Tensor — R₈ ≅ V₄⁴

This module is the first Mathlib-facing bridge for the R8 carrier.
Foundation files keep Mathlib imports out; here we bind the already-proved
R8 XOR laws to `Fintype` and `AddCommGroup` instances, then expose the
four Klein-four axes of R₈.
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import SSBX.Foundation.Bagua.R8
import SSBX.Foundation.Hierarchy.LiftProject
import SSBX.Foundation.Notation.OXNotation

namespace SSBX.Foundation.Squaring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R8

namespace V4Tensor

/-! ## Local Mathlib instances for existing carriers -/

instance instFintypeYao : Fintype Yao where
  elems := [Yao.yang, Yao.yin].toFinset
  complete := by
    intro y
    cases y <;> simp

instance instAddYao : Add Yao := ⟨R8.yaoXor⟩
instance instZeroYao : Zero Yao := ⟨Yao.yang⟩
instance instNegYao : Neg Yao := ⟨id⟩
instance instSubYao : Sub Yao := ⟨R8.yaoXor⟩

@[simp] theorem yao_add_eq_xor (a b : Yao) : a + b = R8.yaoXor a b := rfl

instance instAddCommGroupYao : AddCommGroup Yao where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  zero_add := by
    intro a
    cases a <;> rfl
  add_zero := by
    intro a
    cases a <;> rfl
  neg_add_cancel := by
    intro a
    cases a <;> rfl
  add_comm := by
    intro a b
    cases a <;> cases b <;> rfl

instance instFintypeHexagram : Fintype Hexagram where
  elems := Hexagram.allHex.toFinset
  complete := fun h => List.mem_toFinset.mpr (hexagram_mem_allHex h)

instance instFintypeR8 : Fintype R8 where
  elems := R8.all.toFinset
  complete := fun c => List.mem_toFinset.mpr (R8.mem_all c)

instance instAddCommGroupR8 : AddCommGroup R8 where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := R8.xor_assoc
  zero_add := R8.origin_xor
  add_zero := R8.xor_origin
  neg_add_cancel := by
    intro c
    simpa [R8.neg_def] using R8.xor_self c
  add_comm := R8.xor_comm

/-! ## Generic V₄ carrier and the third-axis alias -/

/-- Generic Klein-four carrier represented as two Yao bits. -/
abbrev V4 : Type := Yao × Yao

/-- Third V₄ axis from `(y₅,y₆)`. The doctrine-level name remains open. -/
abbrev OuterMian : Type := V4

def boolToYao : Bool → Yao
  | false => Yao.yang
  | true => Yao.yin

def yaoToBool : Yao → Bool
  | Yao.yang => false
  | Yao.yin => true

@[simp] theorem boolToYao_yaoToBool (y : Yao) : boolToYao (yaoToBool y) = y := by
  cases y <;> rfl

@[simp] theorem yaoToBool_boolToYao (b : Bool) : yaoToBool (boolToYao b) = b := by
  cases b <;> rfl

@[simp] theorem boolToYao_xor (a b : Bool) :
    boolToYao (Bool.xor a b) = boolToYao a + boolToYao b := by
  cases a <;> cases b <;> rfl

def shiToV4 (s : Shi) : V4 :=
  (boolToYao (Shi.toYinGuo s).1, boolToYao (Shi.toYinGuo s).2)

def v4ToShi (v : V4) : Shi :=
  Shi.ofYinGuo (yaoToBool v.1, yaoToBool v.2)

@[simp] theorem v4ToShi_shiToV4 (s : Shi) : v4ToShi (shiToV4 s) = s := by
  rcases s with ⟨yin, guo⟩
  cases yin <;> cases guo <;> rfl

@[simp] theorem shiToV4_v4ToShi (v : V4) : shiToV4 (v4ToShi v) = v := by
  rcases v with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-! ## Main equivalence: R8 ≃+ V₄⁴ -/

def toV4Quad (c : R8) : V4 × V4 × V4 × V4 :=
  ((c.1.y1, c.1.y2), (c.1.y3, c.1.y4), (c.1.y5, c.1.y6), shiToV4 c.2)

def ofV4Quad : V4 × V4 × V4 × V4 → R8
  | ((y1, y2), (y3, y4), (y5, y6), shi) =>
      (⟨y1, y2, y3, y4, y5, y6⟩, v4ToShi shi)

theorem to_of (q : V4 × V4 × V4 × V4) : toV4Quad (ofV4Quad q) = q := by
  rcases q with ⟨⟨y1, y2⟩, ⟨y3, y4⟩, ⟨y5, y6⟩, ⟨s1, s2⟩⟩
  cases s1 <;> cases s2 <;> rfl

theorem of_to (c : R8) : ofV4Quad (toV4Quad c) = c := by
  rcases c with ⟨h, s⟩
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  rcases s with ⟨yin, guo⟩
  cases yin <;> cases guo <;> rfl

/-! ## R8 as temporal-state-indexed R6 slices -/

/-- R₈ is four temporal-state-indexed R₆/Hexagram slices.

The underlying carrier is definitionally `Hexagram × Shi`; this equivalence
puts the V₄ temporal-state coordinate first so the four fibers are explicit. -/
def r8_eq_temporal_state_indexed_r6 : R8 ≃ Shi × Hexagram where
  toFun := fun c => (c.2, c.1)
  invFun := fun p => (p.2, p.1)
  left_inv := by
    intro c
    rcases c with ⟨h, s⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨s, h⟩
    rfl

/-- The temporal state is exactly a trace bit and a projection bit. -/
def temporalStateEquivTraceProjection : Shi ≃ Bool × Bool where
  toFun := Shi.toYinGuo
  invFun := Shi.ofYinGuo
  left_inv := Shi.ofYinGuo_toYinGuo
  right_inv := Shi.toYinGuo_ofYinGuo

/-- R₈ exposes the R₆/Hexagram coordinate plus trace and projection bits. -/
def r8_eq_r6_times_trace_projection : R8 ≃ Hexagram × Bool × Bool where
  toFun := fun c => (c.1, temporalStateEquivTraceProjection c.2)
  invFun := fun p => (p.1, temporalStateEquivTraceProjection.symm p.2)
  left_inv := by
    intro c
    rcases c with ⟨h, s⟩
    rcases s with ⟨trace, projection⟩
    cases trace <;> cases projection <;> rfl
  right_inv := by
    intro p
    rcases p with ⟨h, ⟨trace, projection⟩⟩
    cases trace <;> cases projection <;> rfl

/-- A fixed temporal-state fiber is just the Hexagram/R₆ coordinate. -/
def temporalStateFiberEquiv (s : Shi) : {c : R8 // c.2 = s} ≃ Hexagram where
  toFun := fun c => c.1.1
  invFun := fun h => ⟨(h, s), rfl⟩
  left_inv := by
    intro c
    rcases c with ⟨⟨h, t⟩, ht⟩
    cases ht
    rfl
  right_inv := by
    intro h
    rfl

theorem hexagram_card_eq_64 : Fintype.card Hexagram = 64 := by
  native_decide

/-- Each temporal-state slice of R₈ contains 64 cells. -/
theorem r8_temporal_state_fiber_card_eq_64 (s : Shi) :
    Fintype.card {c : R8 // c.2 = s} = 64 := by
  rw [Fintype.card_congr (temporalStateFiberEquiv s), hexagram_card_eq_64]

/-- Roadmap §3.1 phrasing: the V₄ partition has four 64-cell fibers. -/
theorem r8_v4_partition (s : Shi) :
    Fintype.card {c : R8 // c.2 = s} = 64 :=
  r8_temporal_state_fiber_card_eq_64 s

/-- Summary anchor: R₈ has a Hexagram coordinate and two temporal-coordinate bits. -/
theorem r8_temporal_coordinate_summary :
    Nonempty (R8 ≃ Hexagram × Bool × Bool)
    ∧ (∀ s : Shi, temporalStateEquivTraceProjection.symm
        (temporalStateEquivTraceProjection s) = s)
    ∧ (∀ s : Shi, Fintype.card {c : R8 // c.2 = s} = 64) :=
  ⟨⟨r8_eq_r6_times_trace_projection⟩,
   temporalStateEquivTraceProjection.left_inv,
   r8_temporal_state_fiber_card_eq_64⟩

/-! ## Way origin and cell-as-operator anchors -/

/-- Way is the canonical R₈ origin: heaven hexagram at the temporal-state origin. -/
theorem way_at_origin : R8.origin = (Hexagram.heaven, Shi.dao) := rfl

/-- The operator represented by a cell: act on a state by XOR with that cell. -/
def cellOperator (c : R8) : R8 → R8 := fun s => R8.xor s c

@[simp] theorem cell_operator_apply (c s : R8) :
    cellOperator c s = R8.xor s c := rfl

/-- In an abelian R₈, the right-translation operator is the Cayley translation. -/
theorem cell_operator_eq_cayley (c : R8) :
    cellOperator c = R8.cayley c := by
  funext s
  simp [cellOperator, R8.cayley, R8.xor_comm]

/-- Cells inject into operators by their action on the origin. -/
theorem cell_is_operator : Function.Injective cellOperator := by
  intro c1 c2 h
  have heq := congrFun h R8.origin
  simpa [cellOperator, R8.origin_xor] using heq

/-- Way/origin is the no-op operator. -/
theorem way_noop_operator : cellOperator R8.origin = id := by
  funext s
  simp [cellOperator]

/-! ## R-O fusion: cells as their own XOR operators -/

/-- The represented XOR-operator space: exactly those endomaps that are
    translation by some R₈ cell. -/
abbrev XorOperator : Type := { f : R8 → R8 // ∃ c : R8, f = cellOperator c }

/-- A cell viewed as the operator it already is. -/
def asXorOperator (c : R8) : XorOperator :=
  ⟨cellOperator c, ⟨c, rfl⟩⟩

/-- Recover a represented XOR operator by evaluating it at Way/origin. -/
def evalXorOperatorAtOrigin (F : XorOperator) : R8 := F.1 R8.origin

@[simp] theorem eval_asXorOperator (c : R8) :
    evalXorOperatorAtOrigin (asXorOperator c) = c := by
  simp [evalXorOperatorAtOrigin, asXorOperator, cellOperator]

@[simp] theorem as_evalXorOperatorAtOrigin (F : XorOperator) :
    asXorOperator (evalXorOperatorAtOrigin F) = F := by
  rcases F with ⟨f, ⟨c, rfl⟩⟩
  simp [asXorOperator, evalXorOperatorAtOrigin, cellOperator]

/-- R₈ is equivalent to its own represented XOR-operator space. -/
def r8_equiv_xor_operator : R8 ≃ XorOperator where
  toFun := asXorOperator
  invFun := evalXorOperatorAtOrigin
  left_inv := eval_asXorOperator
  right_inv := as_evalXorOperatorAtOrigin

/-- Composition internal to the represented XOR-operator space. -/
def xorOperatorComp (F G : XorOperator) : XorOperator :=
  asXorOperator
    (R8.xor (evalXorOperatorAtOrigin F) (evalXorOperatorAtOrigin G))

/-- The represented-operator composition recovers the XOR of representatives
    by evaluating at Way/origin. -/
theorem xorOperatorComp_eval (F G : XorOperator) :
    evalXorOperatorAtOrigin (xorOperatorComp F G) =
      R8.xor (evalXorOperatorAtOrigin F) (evalXorOperatorAtOrigin G) := by
  simp [xorOperatorComp]

/-- Operator composition is the same computation as XOR of the representing
    cells.  This is the formal "self-representation" mechanism. -/
theorem cell_operator_comp (a b : R8) :
    cellOperator (R8.xor a b) = cellOperator a ∘ cellOperator b := by
  funext s
  simp [cellOperator, Function.comp_apply, R8.xor_assoc, R8.xor_comm a b]

/-- Internal represented-operator composition agrees with ordinary function
    composition. -/
theorem xorOperatorComp_coe (F G : XorOperator) :
    (xorOperatorComp F G).1 = F.1 ∘ G.1 := by
  rcases F with ⟨f, ⟨a, rfl⟩⟩
  rcases G with ⟨g, ⟨b, rfl⟩⟩
  simpa [xorOperatorComp, evalXorOperatorAtOrigin, asXorOperator] using
    cell_operator_comp a b

/-- The equivalence `R8 ≃ XorOperator` preserves the same computation:
    composing represented operators is represented by XOR of their cells. -/
theorem r8_equiv_xor_operator_map_xor (a b : R8) :
    (r8_equiv_xor_operator (R8.xor a b)).1 =
      (r8_equiv_xor_operator a).1 ∘ (r8_equiv_xor_operator b).1 :=
  cell_operator_comp a b

/-- Pointwise form of represented-operator composition. -/
theorem cell_operator_comp_apply (a b s : R8) :
    cellOperator a (cellOperator b s) = cellOperator (R8.xor a b) s := by
  have h := congrFun (cell_operator_comp a b) s
  simpa [Function.comp_apply] using h.symm

/-- Every represented cell-operator is self-inverse. -/
theorem cell_operator_self_inverse (c : R8) :
    cellOperator c ∘ cellOperator c = id := by
  funext s
  simp [cellOperator, Function.comp_apply, R8.xor_assoc, R8.xor_self]

/-! ## Negation and OX mask readings -/

/-- Yao negation is XOR with the nonzero R₁ bit. -/
theorem yao_neg_eq_xor_yin (y : Yao) :
    y.neg = R8.yaoXor y Yao.yin := by
  cases y <;> rfl

/-- In the `(Z/2)^8` group, additive inverse is self; this is distinct from
    full OX bit-complement below. -/
theorem r8_additive_neg_is_self (c : R8) :
    -c = c :=
  R8.neg_def c

/-- Hexagram complement is XOR with the all-yin hexagram mask. -/
theorem hex_complement_eq_xor_earth (h : Hexagram) :
    h.complement = R8.hexXor h Hexagram.earth := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;>
    cases y4 <;> cases y5 <;> cases y6 <;> rfl

/-- R₈ hexagram-level complement is XOR with `xxxxxxoo`. -/
theorem r8_hexCuo_eq_xor_earth_mask (c : R8) :
    R8.hexCuo c = R8.xor c (Hexagram.earth, Shi.dao) := by
  rcases c with ⟨h, s⟩
  simp [R8.hexCuo, R8.xor, hex_complement_eq_xor_earth]

/-- Full 8-bit negation mask: six hexagram bits plus both temporal bits. -/
def fullNegMask : R8 := (Hexagram.earth, Shi.jin)

/-- Full 8-bit negation as XOR with `xxxxxxxx`. -/
def fullNegOperator (c : R8) : R8 := R8.xor c fullNegMask

/-- Full OX negation is the cell-operator represented by the full mask. -/
theorem fullNegOperator_eq_cellOperator_fullNegMask :
    fullNegOperator = cellOperator fullNegMask := by
  funext c
  simp [fullNegOperator, cellOperator]

theorem fullNegOperator_involutive (c : R8) :
    fullNegOperator (fullNegOperator c) = c := by
  unfold fullNegOperator
  rw [R8.xor_assoc, R8.xor_self, R8.xor_origin]

/-- Full negation decomposes into hexagram complement and temporal PT flip. -/
theorem fullNegOperator_eq_hexCuo_shiCuoZong (c : R8) :
    fullNegOperator c = R8.shiCuoZong (R8.hexCuo c) := by
  rcases c with ⟨h, s⟩
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  rcases s with ⟨yin, guo⟩
  cases y1 <;> cases y2 <;> cases y3 <;>
    cases y4 <;> cases y5 <;> cases y6 <;>
    cases yin <;> cases guo <;> rfl

theorem ox_origin_eq_origin : OX["oooooooo"] = (R8.origin : R8) := rfl
theorem ox_imprint_mask_eq : OX["ooooooxo"] = R8.imprint_mask := rfl
theorem ox_project_mask_eq : OX["ooooooox"] = R8.project_mask := rfl
theorem ox_temporal_pt_mask_eq :
    OX["ooooooxx"] = R8.xor R8.imprint_mask R8.project_mask := rfl
theorem ox_hex_neg_mask_eq :
    OX["xxxxxxoo"] = (Hexagram.earth, Shi.dao) := rfl
theorem ox_full_neg_mask_eq :
    OX["xxxxxxxx"] = fullNegMask := rfl

/-- The full OX negation mask is the XOR of hexagram complement and
    temporal PT masks. -/
theorem ox_full_neg_mask_decomposes :
    OX["xxxxxxxx"] = R8.xor OX["xxxxxxoo"] OX["ooooooxx"] := rfl

/-- The full OX negation operator is the represented operator for
    `OX["xxxxxxxx"]`. -/
theorem fullNegOperator_eq_ox_full_neg_operator :
    fullNegOperator = cellOperator OX["xxxxxxxx"] := by
  rw [ox_full_neg_mask_eq]
  exact fullNegOperator_eq_cellOperator_fullNegMask

/-- The OX full-negation operator is self-inverse. -/
theorem ox_full_neg_operator_involutive :
    cellOperator OX["xxxxxxxx"] ∘ cellOperator OX["xxxxxxxx"] = id := by
  rw [ox_full_neg_mask_eq]
  exact cell_operator_self_inverse fullNegMask

/-- Full OX negation decomposes as hexagram complement followed by temporal
    PT flip; commutativity makes the order immaterial for represented XOR
    operators. -/
theorem ox_full_neg_operator_decomposes :
    cellOperator OX["xxxxxxxx"] =
      cellOperator OX["xxxxxxoo"] ∘ cellOperator OX["ooooooxx"] := by
  rw [ox_full_neg_mask_decomposes, cell_operator_comp]

/-! ## Mask characters: finite Boolean self-duality skeleton -/

/-- `o/x` coordinate as a Boolean bit: yang/o is false; yin/x is true. -/
def yaoBit : Yao → Bool
  | Yao.yang => false
  | Yao.yin => true

/-- Boolean dot product over the eight R₈ coordinates. -/
def r8Dot (mask state : R8) : Bool :=
  Bool.xor (mask.2.2 && state.2.2) <|
  Bool.xor (mask.2.1 && state.2.1) <|
  Bool.xor (yaoBit mask.1.y6 && yaoBit state.1.y6) <|
  Bool.xor (yaoBit mask.1.y5 && yaoBit state.1.y5) <|
  Bool.xor (yaoBit mask.1.y4 && yaoBit state.1.y4) <|
  Bool.xor (yaoBit mask.1.y3 && yaoBit state.1.y3) <|
  Bool.xor (yaoBit mask.1.y2 && yaoBit state.1.y2)
    (yaoBit mask.1.y1 && yaoBit state.1.y1)

theorem r8Dot_comm : ∀ a b : R8, r8Dot a b = r8Dot b a := by
  native_decide

/-- The Boolean character represented by a mask.  `true` is the nontrivial
    sign bit; in ±1 notation it corresponds to `-1`. -/
def maskCharacter (mask : R8) : R8 → Bool := fun state => r8Dot mask state

/-- Mask characters are homomorphisms from R₈ XOR to Bool XOR. -/
theorem maskCharacter_xor :
    ∀ mask a b : R8,
      maskCharacter mask (R8.xor a b) =
        Bool.xor (maskCharacter mask a) (maskCharacter mask b) := by
  native_decide

/-- Mask characters also compute XOR in the mask coordinate. -/
theorem maskCharacter_xor_mask (m n s : R8) :
    maskCharacter (R8.xor m n) s =
      Bool.xor (maskCharacter m s) (maskCharacter n s) := by
  calc
    maskCharacter (R8.xor m n) s = maskCharacter s (R8.xor m n) := by
      exact r8Dot_comm (R8.xor m n) s
    _ = Bool.xor (maskCharacter s m) (maskCharacter s n) :=
      maskCharacter_xor s m n
    _ = Bool.xor (maskCharacter m s) (maskCharacter n s) := by
      rw [show maskCharacter s m = maskCharacter m s from r8Dot_comm s m,
        show maskCharacter s n = maskCharacter n s from r8Dot_comm s n]

/-- Different masks give different Boolean characters. -/
theorem maskCharacter_injective : Function.Injective maskCharacter := by
  native_decide

/-- The represented Boolean character space, i.e. the image of R₈ masks under
    `maskCharacter`.  This is the finite Pontryagin-style self-dual carrier
    used here; it avoids pretending that analytic `U(1)` has been built. -/
abbrev MaskCharacterImage : Type :=
  { χ : R8 → Bool // ∃ mask : R8, χ = maskCharacter mask }

noncomputable def r8_equiv_mask_character_image : R8 ≃ MaskCharacterImage where
  toFun := fun mask => ⟨maskCharacter mask, ⟨mask, rfl⟩⟩
  invFun := fun χ => Classical.choose χ.2
  left_inv := by
    intro mask
    have hspec :
        maskCharacter mask =
          maskCharacter (Classical.choose
            (show ∃ m : R8, maskCharacter mask = maskCharacter m from ⟨mask, rfl⟩)) :=
      Classical.choose_spec
        (show ∃ m : R8, maskCharacter mask = maskCharacter m from ⟨mask, rfl⟩)
    exact (maskCharacter_injective hspec).symm
  right_inv := by
    intro χ
    apply Subtype.ext
    exact (Classical.choose_spec χ.2).symm

theorem r8_operator_character_duality_summary :
    Nonempty (R8 ≃ XorOperator)
    ∧ (∀ F G : XorOperator, (xorOperatorComp F G).1 = F.1 ∘ G.1)
    ∧ (∀ a b : R8,
        cellOperator (R8.xor a b) = cellOperator a ∘ cellOperator b)
    ∧ (∀ a b : R8,
        (r8_equiv_xor_operator (R8.xor a b)).1 =
          (r8_equiv_xor_operator a).1 ∘ (r8_equiv_xor_operator b).1)
    ∧ (∀ c : R8, cellOperator c ∘ cellOperator c = id)
    ∧ Nonempty (R8 ≃ MaskCharacterImage)
    ∧ (∀ mask a b : R8,
        maskCharacter mask (R8.xor a b) =
          Bool.xor (maskCharacter mask a) (maskCharacter mask b)) :=
  ⟨⟨r8_equiv_xor_operator⟩,
   xorOperatorComp_coe,
   cell_operator_comp,
   r8_equiv_xor_operator_map_xor,
   cell_operator_self_inverse,
   ⟨r8_equiv_mask_character_image⟩,
   maskCharacter_xor⟩

theorem r8_character_duality_computation_summary :
    (∀ mask a b : R8,
      maskCharacter mask (R8.xor a b) =
        Bool.xor (maskCharacter mask a) (maskCharacter mask b))
    ∧ (∀ m n s : R8,
      maskCharacter (R8.xor m n) s =
        Bool.xor (maskCharacter m s) (maskCharacter n s))
    ∧ Function.Injective maskCharacter :=
  ⟨maskCharacter_xor, maskCharacter_xor_mask, maskCharacter_injective⟩

theorem r8_negation_ox_operator_summary :
    (∀ c : R8, -c = c)
    ∧ fullNegOperator = cellOperator OX["xxxxxxxx"]
    ∧ cellOperator OX["xxxxxxxx"] ∘ cellOperator OX["xxxxxxxx"] = id
    ∧ OX["xxxxxxxx"] = R8.xor OX["xxxxxxoo"] OX["ooooooxx"]
    ∧ cellOperator OX["xxxxxxxx"] =
        cellOperator OX["xxxxxxoo"] ∘ cellOperator OX["ooooooxx"] :=
  ⟨r8_additive_neg_is_self,
   fullNegOperator_eq_ox_full_neg_operator,
   ox_full_neg_operator_involutive,
   ox_full_neg_mask_decomposes,
   ox_full_neg_operator_decomposes⟩

def iso : R8 ≃+ (V4 × V4 × V4 × V4) where
  toFun := toV4Quad
  invFun := ofV4Quad
  left_inv := of_to
  right_inv := to_of
  map_add' := by
    intro a b
    rcases a with ⟨ha, sa⟩
    rcases b with ⟨hb, sb⟩
    rcases ha with ⟨a1, a2, a3, a4, a5, a6⟩
    rcases hb with ⟨b1, b2, b3, b4, b5, b6⟩
    rcases sa with ⟨ay, ag⟩
    rcases sb with ⟨byin, bg⟩
    simp [toV4Quad, R8.add_def, R8.xor, R8.hexXor,
      R8.shiXor, Shi.toYinGuo, Shi.ofYinGuo, shiToV4]

theorem origin_toV4Quad :
    toV4Quad R8.origin =
      ((Yao.yang, Yao.yang), (Yao.yang, Yao.yang),
       (Yao.yang, Yao.yang), (Yao.yang, Yao.yang)) := rfl

theorem way_origin_operator_summary :
    R8.origin = (Hexagram.heaven, Shi.dao)
    ∧ cellOperator R8.origin = id
    ∧ toV4Quad R8.origin =
      ((Yao.yang, Yao.yang), (Yao.yang, Yao.yang),
       (Yao.yang, Yao.yang), (Yao.yang, Yao.yang)) :=
  ⟨way_at_origin, way_noop_operator, origin_toV4Quad⟩

theorem v4_tensor_summary :
    (∀ c : R8, ofV4Quad (toV4Quad c) = c)
    ∧ (∀ q : V4 × V4 × V4 × V4, toV4Quad (ofV4Quad q) = q)
    ∧ toV4Quad R8.origin =
      ((Yao.yang, Yao.yang), (Yao.yang, Yao.yang),
       (Yao.yang, Yao.yang), (Yao.yang, Yao.yang)) :=
  ⟨of_to, to_of, origin_toV4Quad⟩

end V4Tensor

end SSBX.Foundation.Squaring
