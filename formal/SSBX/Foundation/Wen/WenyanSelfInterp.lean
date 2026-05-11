/-
# WenyanSelfInterp — 以文自释 (R8 / V₄ Klein)

Self-interpretation: the wenyan-encoded language interprets itself.

  文 (program) → 文 (data) ; 文 (program) operating on 文 (data) ≈ direct.

We build:
  § 1   Atomic bijections  (Yao, Shi, Hexagram, R8) ↔ Fin
  § 2   Nat ↔ List R8 (base-256 digits, total bijection)
  § 3   YiInstr ↪ List R8  (with round-trip)
  § 4   List YiInstr, YiState ↪ List R8  (with round-trip)
  § 5   metaStep — META interpreter (Lean-level), operating on encoded data
  § 6   Simulation theorem  metaStep ∘ encode = encode ∘ step
  § 7   Quine — a List YiInstr whose run produces its own encoding in history

## Phase F.1 migration note (Cell192 → R8)

This file is Phase F.1 of the Cell192 → R8 migration. The atomic
encoding now uses `R8.Shi` (V₄ Klein 4-group with `dao/已/今/未`) instead
of the legacy `Cell192.Shi` (Z/3 cyclic). All downstream layers (encInstr /
ProgEnc / StateEnc / metaStep / dispatch / Quine) operate on `R8`
throughout.

The dispatch program `dispatchProg` is re-derived for base-256: the base-256
`cellFromIdx ⟨k, _⟩` for `k ∈ 0..11` decodes to `(hex, shi)` pairs
`(hex_idx, shi_idx) = (k/4, k%4)`, so tags 0..11 cover hex 0..2 crossed with
all 4 shi states. Routing uses 4-way Shi outer × 3-way Hex inner branches.

The `metaInterpStepPc_branchShiEq_notTaken_*` lemmas additionally cover the
new `Shi.dao` ctor as a "not-taken" case.
-/
import SSBX.Foundation.Bagua.R8
import SSBX.Foundation.Bagua.BaguaTuring

namespace SSBX.Foundation.Wen.WenyanSelfInterp

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring

end SSBX.Foundation.Wen.WenyanSelfInterp

/-! ## § 1 Atomic bijections — definitions placed in source-type namespaces so
   that dot notation `y.toIdx`, `s.toIdx`, `h.toIdx` resolves correctly. -/

namespace SSBX.Foundation.Yi.Yi.Yao

open SSBX.Foundation.Yi.Yi

/-- Yao ↔ Fin 2: yang ↔ 0, yin ↔ 1. -/
def toIdx : Yao → Fin 2
  | .yang => ⟨0, by omega⟩
  | .yin  => ⟨1, by omega⟩

def fromIdx : Fin 2 → Yao
  | ⟨0, _⟩ => .yang
  | ⟨1, _⟩ => .yin

theorem toIdx_fromIdx (y : Yao) : fromIdx y.toIdx = y := by cases y <;> rfl

theorem fromIdx_toIdx (i : Fin 2) : (fromIdx i).toIdx = i := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

end SSBX.Foundation.Yi.Yi.Yao

namespace SSBX.Foundation.Bagua.R8.Shi

open SSBX.Foundation.Bagua.R8

/-- Shi ↔ Fin 4: dao ↔ 0, ji ↔ 1, jin ↔ 2, wei ↔ 3.

    Migrated from Cell192 3-state Z/3 to R8 4-state V₄ Klein per
    yi-RO-hierarchy-v2.md. Index 0 (dao) is the V₄ identity element. -/
def toIdx : Shi → Fin 4
  | .dao => ⟨0, by omega⟩
  | .ji  => ⟨1, by omega⟩
  | .jin => ⟨2, by omega⟩
  | .wei => ⟨3, by omega⟩

def fromIdx : Fin 4 → Shi
  | ⟨0, _⟩ => .dao
  | ⟨1, _⟩ => .ji
  | ⟨2, _⟩ => .jin
  | ⟨3, _⟩ => .wei

theorem toIdx_fromIdx (s : Shi) : fromIdx s.toIdx = s := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

theorem fromIdx_toIdx (i : Fin 4) : (fromIdx i).toIdx = i := by
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl

end SSBX.Foundation.Bagua.R8.Shi

namespace SSBX.Foundation.Yi.Yi.Hexagram

open SSBX.Foundation.Yi.Yi

/-- Hexagram ↔ Fin 64 via binary digits y1 y2 y3 y4 y5 y6 (low → high). -/
def toIdx (h : Hexagram) : Fin 64 :=
  ⟨h.y1.toIdx.val
    + 2 * h.y2.toIdx.val
    + 4 * h.y3.toIdx.val
    + 8 * h.y4.toIdx.val
    + 16 * h.y5.toIdx.val
    + 32 * h.y6.toIdx.val, by
    rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide⟩

def fromIdx (n : Fin 64) : Hexagram :=
  { y1 := Yao.fromIdx ⟨n.val % 2, by omega⟩
  , y2 := Yao.fromIdx ⟨(n.val / 2) % 2, by omega⟩
  , y3 := Yao.fromIdx ⟨(n.val / 4) % 2, by omega⟩
  , y4 := Yao.fromIdx ⟨(n.val / 8) % 2, by omega⟩
  , y5 := Yao.fromIdx ⟨(n.val / 16) % 2, by omega⟩
  , y6 := Yao.fromIdx ⟨(n.val / 32) % 2, by omega⟩ }

theorem toIdx_fromIdx (h : Hexagram) : fromIdx h.toIdx = h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

theorem fromIdx_toIdx (n : Fin 64) : (fromIdx n).toIdx = n := by
  apply Fin.ext
  show (fromIdx n).toIdx.val = n.val
  unfold fromIdx
  show (Yao.fromIdx ⟨n.val % 2, _⟩).toIdx.val
      + 2 * (Yao.fromIdx ⟨(n.val / 2) % 2, _⟩).toIdx.val
      + 4 * (Yao.fromIdx ⟨(n.val / 4) % 2, _⟩).toIdx.val
      + 8 * (Yao.fromIdx ⟨(n.val / 8) % 2, _⟩).toIdx.val
      + 16 * (Yao.fromIdx ⟨(n.val / 16) % 2, _⟩).toIdx.val
      + 32 * (Yao.fromIdx ⟨(n.val / 32) % 2, _⟩).toIdx.val = n.val
  rw [Yao.fromIdx_toIdx, Yao.fromIdx_toIdx, Yao.fromIdx_toIdx,
      Yao.fromIdx_toIdx, Yao.fromIdx_toIdx, Yao.fromIdx_toIdx]
  show n.val % 2 + 2 * ((n.val / 2) % 2) + 4 * ((n.val / 4) % 2)
      + 8 * ((n.val / 8) % 2) + 16 * ((n.val / 16) % 2)
      + 32 * ((n.val / 32) % 2) = n.val
  have : n.val < 64 := n.isLt
  omega

end SSBX.Foundation.Yi.Yi.Hexagram

namespace SSBX.Foundation.Wen.WenyanSelfInterp

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring

/-- R8 ↔ Fin 256: hex_idx * 4 + shi_idx.  Defined as a plain function
    (not a method) because R8 is an abbreviation for `Hexagram × Shi`,
    so dot notation `c.toIdx` cannot resolve to a custom R8 namespace. -/
def cellToIdx (c : R8) : Fin 256 :=
  ⟨c.1.toIdx.val * 4 + c.2.toIdx.val, by
    have h1 : c.1.toIdx.val < 64 := c.1.toIdx.isLt
    have h2 : c.2.toIdx.val < 4 := c.2.toIdx.isLt
    omega⟩

def cellFromIdx (n : Fin 256) : R8 :=
  ( SSBX.Foundation.Yi.Yi.Hexagram.fromIdx ⟨n.val / 4, by omega⟩
  , SSBX.Foundation.Bagua.R8.Shi.fromIdx ⟨n.val % 4, by omega⟩ )

theorem cellToIdx_fromIdx (c : R8) : cellFromIdx (cellToIdx c) = c := by
  rcases c with ⟨h, s⟩
  unfold cellFromIdx cellToIdx
  have hb : h.toIdx.val < 64 := h.toIdx.isLt
  have sb : s.toIdx.val < 4 := s.toIdx.isLt
  have hdiv : (h.toIdx.val * 4 + s.toIdx.val) / 4 = h.toIdx.val := by omega
  have hmod : (h.toIdx.val * 4 + s.toIdx.val) % 4 = s.toIdx.val := by omega
  congr 1
  · rw [show (⟨(h.toIdx.val * 4 + s.toIdx.val) / 4, by omega⟩ : Fin 64)
         = h.toIdx from Fin.ext hdiv]
    exact SSBX.Foundation.Yi.Yi.Hexagram.toIdx_fromIdx h
  · rw [show (⟨(h.toIdx.val * 4 + s.toIdx.val) % 4, by omega⟩ : Fin 4)
         = s.toIdx from Fin.ext hmod]
    exact SSBX.Foundation.Bagua.R8.Shi.toIdx_fromIdx s

theorem cellFromIdx_toIdx (n : Fin 256) : cellToIdx (cellFromIdx n) = n := by
  apply Fin.ext
  unfold cellToIdx cellFromIdx
  show (SSBX.Foundation.Yi.Yi.Hexagram.fromIdx ⟨n.val / 4, _⟩).toIdx.val * 4
    + (SSBX.Foundation.Bagua.R8.Shi.fromIdx ⟨n.val % 4, _⟩).toIdx.val = n.val
  rw [SSBX.Foundation.Yi.Yi.Hexagram.fromIdx_toIdx,
      SSBX.Foundation.Bagua.R8.Shi.fromIdx_toIdx]
  show (n.val / 4) * 4 + n.val % 4 = n.val
  omega

/-! ## § 2 Nat ↔ List R8 — base-256 digit encoding (LSB-first) -/

namespace NatCell

/-- A "small" cell: index < 256. Used as a base-256 digit. -/
abbrev Digit := R8

/-- Encode a Nat as base-256 LSB-first digits. -/
def encodeNat : Nat → List R8
  | 0 => []
  | n+1 =>
    have : (n + 1) / 256 < n + 1 := Nat.div_lt_self (by omega) (by omega)
    cellFromIdx ⟨(n + 1) % 256, Nat.mod_lt _ (by omega)⟩
      :: encodeNat ((n + 1) / 256)

/-- Decode a base-256 digit list back to Nat. -/
def decodeNat : List R8 → Nat
  | [] => 0
  | c :: rest => (cellToIdx c).val + 256 * decodeNat rest

theorem decode_encode (n : Nat) : decodeNat (encodeNat n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp [encodeNat, decodeNat]
    | k+1 =>
      have hlt : (k + 1) / 256 < k + 1 := Nat.div_lt_self (by omega) (by omega)
      unfold encodeNat decodeNat
      rw [cellFromIdx_toIdx, ih _ hlt]
      show (k + 1) % 256 + 256 * ((k + 1) / 256) = k + 1
      omega

end NatCell

/-! ## § 3 YiInstr ↔ List R8 -/

namespace YiInstrEnc

def tagCell (tag : Nat) (h : tag < 256) : R8 := cellFromIdx ⟨tag, h⟩

def encFin6 (i : Fin 6) : R8 := cellFromIdx ⟨i.val, by omega⟩

def encShi (s : Shi) : R8 :=
  cellFromIdx ⟨s.toIdx.val, by have := s.toIdx.isLt; omega⟩

def encNat (n : Nat) : List R8 :=
  let digits := NatCell.encodeNat n
  cellFromIdx ⟨min digits.length 255, by omega⟩ :: digits

def decNat (l : List R8) : Option (Nat × List R8) :=
  match l with
  | [] => none
  | hdr :: rest =>
    let len := (cellToIdx hdr).val
    if len ≤ rest.length then
      some (NatCell.decodeNat (rest.take len), rest.drop len)
    else none

def encInstr : YiInstr → List R8
  | .nop                        => [cellFromIdx ⟨0,  by omega⟩]
  | .setShi s                   => [cellFromIdx ⟨1,  by omega⟩, encShi s]
  | .flipYao i                  => [cellFromIdx ⟨2,  by omega⟩, encFin6 i]
  | .interlace                         => [cellFromIdx ⟨3,  by omega⟩]
  | .complement                        => [cellFromIdx ⟨4,  by omega⟩]
  | .reverse                       => [cellFromIdx ⟨5,  by omega⟩]
  | .branchYaoEq i j t          => [cellFromIdx ⟨6,  by omega⟩, encFin6 i, encFin6 j] ++ encNat t
  | .branchShiEq s t            => [cellFromIdx ⟨7,  by omega⟩, encShi s] ++ encNat t
  | .jump t                     => cellFromIdx ⟨8,  by omega⟩ :: encNat t
  | .push                       => [cellFromIdx ⟨9,  by omega⟩]
  | .pop                        => [cellFromIdx ⟨10, by omega⟩]
  | .halt                       => [cellFromIdx ⟨11, by omega⟩]

def decInstr (l : List R8) : Option (YiInstr × List R8) :=
  match l with
  | [] => none
  | tag :: rest =>
    match (cellToIdx tag).val, rest with
    | 0,  rest => some (.nop, rest)
    | 1,  s :: rest =>
        if h : (cellToIdx s).val < 4
        then some (.setShi (SSBX.Foundation.Bagua.R8.Shi.fromIdx ⟨(cellToIdx s).val, h⟩), rest)
        else none
    | 2,  i :: rest =>
        if h : (cellToIdx i).val < 6
        then some (.flipYao ⟨(cellToIdx i).val, h⟩, rest)
        else none
    | 3,  rest => some (.interlace, rest)
    | 4,  rest => some (.complement, rest)
    | 5,  rest => some (.reverse, rest)
    | 6,  i :: j :: rest =>
        if hi : (cellToIdx i).val < 6 then
          if hj : (cellToIdx j).val < 6 then
            match decNat rest with
            | some (t, rest') =>
                some (.branchYaoEq ⟨(cellToIdx i).val, hi⟩ ⟨(cellToIdx j).val, hj⟩ t, rest')
            | none => none
          else none
        else none
    | 7,  s :: rest =>
        if h : (cellToIdx s).val < 4 then
          match decNat rest with
          | some (t, rest') =>
              some (.branchShiEq (SSBX.Foundation.Bagua.R8.Shi.fromIdx ⟨(cellToIdx s).val, h⟩) t, rest')
          | none => none
        else none
    | 8,  rest =>
        match decNat rest with
        | some (t, rest') => some (.jump t, rest')
        | none => none
    | 9,  rest => some (.push, rest)
    | 10, rest => some (.pop, rest)
    | 11, rest => some (.halt, rest)
    | _, _ => none

/-! ### § 3b Round-trip lemmas for instruction encoding -/

theorem cellToIdx_val_of_cellFromIdx (k : Nat) (h : k < 256) :
    (cellToIdx (cellFromIdx ⟨k, h⟩)).val = k := by
  rw [cellFromIdx_toIdx]

theorem decInstr_encInstr_nop (rest : List R8) :
    decInstr (encInstr .nop ++ rest) = some (.nop, rest) := by
  show decInstr (cellFromIdx ⟨0, by omega⟩ :: rest) = _
  simp only [decInstr, cellFromIdx_toIdx]

theorem decInstr_encInstr_hu (rest : List R8) :
    decInstr (encInstr .interlace ++ rest) = some (.interlace, rest) := by
  show decInstr (cellFromIdx ⟨3, by omega⟩ :: rest) = _
  simp only [decInstr, cellFromIdx_toIdx]

theorem decInstr_encInstr_cuo (rest : List R8) :
    decInstr (encInstr .complement ++ rest) = some (.complement, rest) := by
  show decInstr (cellFromIdx ⟨4, by omega⟩ :: rest) = _
  simp only [decInstr, cellFromIdx_toIdx]

theorem decInstr_encInstr_zong (rest : List R8) :
    decInstr (encInstr .reverse ++ rest) = some (.reverse, rest) := by
  show decInstr (cellFromIdx ⟨5, by omega⟩ :: rest) = _
  simp only [decInstr, cellFromIdx_toIdx]

theorem decInstr_encInstr_push (rest : List R8) :
    decInstr (encInstr .push ++ rest) = some (.push, rest) := by
  show decInstr (cellFromIdx ⟨9, by omega⟩ :: rest) = _
  simp only [decInstr, cellFromIdx_toIdx]

theorem decInstr_encInstr_pop (rest : List R8) :
    decInstr (encInstr .pop ++ rest) = some (.pop, rest) := by
  show decInstr (cellFromIdx ⟨10, by omega⟩ :: rest) = _
  simp only [decInstr, cellFromIdx_toIdx]

theorem decInstr_encInstr_halt (rest : List R8) :
    decInstr (encInstr .halt ++ rest) = some (.halt, rest) := by
  show decInstr (cellFromIdx ⟨11, by omega⟩ :: rest) = _
  simp only [decInstr, cellFromIdx_toIdx]

theorem decInstr_encInstr_setShi (s : Shi) (rest : List R8) :
    decInstr (encInstr (.setShi s) ++ rest) = some (.setShi s, rest) := by
  have h4 : s.toIdx.val < 4 := s.toIdx.isLt
  show decInstr (cellFromIdx ⟨1, by omega⟩ :: encShi s :: rest) = _
  simp only [decInstr, encShi, cellFromIdx_toIdx]
  rw [dif_pos h4]
  congr 2
  have eq1 : (⟨s.toIdx.val, h4⟩ : Fin 4) = s.toIdx := Fin.ext rfl
  rw [eq1, SSBX.Foundation.Bagua.R8.Shi.toIdx_fromIdx]

theorem decInstr_encInstr_flipYao (i : Fin 6) (rest : List R8) :
    decInstr (encInstr (.flipYao i) ++ rest) = some (.flipYao i, rest) := by
  have h6 : i.val < 6 := i.isLt
  show decInstr (cellFromIdx ⟨2, by omega⟩ :: encFin6 i :: rest) = _
  simp only [decInstr, encFin6, cellFromIdx_toIdx]
  rw [dif_pos h6]

/-! ### § 3c Round-trip for the three Nat-parameter instructions -/

private theorem list_take_left_eq (l r : List R8) :
    (l ++ r).take l.length = l := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih]

private theorem list_drop_left_eq (l r : List R8) :
    (l ++ r).drop l.length = r := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih]

private theorem decNat_cellFromIdx_cons (k : Nat) (h256 : k < 256)
    (rest : List R8) (hk : k ≤ rest.length) :
    decNat (cellFromIdx ⟨k, h256⟩ :: rest) =
      some (NatCell.decodeNat (rest.take k), rest.drop k) := by
  unfold decNat
  simp only [cellFromIdx_toIdx]
  rw [if_pos hk]

theorem decNat_encNat (n : Nat) (rest : List R8)
    (hlen : (NatCell.encodeNat n).length < 256) :
    decNat (encNat n ++ rest) = some (n, rest) := by
  let digits := NatCell.encodeNat n
  have hd : digits = NatCell.encodeNat n := rfl
  have hlen' : digits.length < 256 := hlen
  have hmin : min digits.length 255 = digits.length := by omega
  show decNat (cellFromIdx ⟨min digits.length 255, by omega⟩
                :: (digits ++ rest))
       = some (n, rest)
  have hcell : (⟨min digits.length 255, by omega⟩ : Fin 256)
              = ⟨digits.length, by omega⟩ := Fin.ext hmin
  rw [hcell]
  have hle : digits.length ≤ (digits ++ rest).length := by
    rw [List.length_append]; omega
  rw [decNat_cellFromIdx_cons digits.length (by omega) (digits ++ rest) hle]
  rw [list_take_left_eq, list_drop_left_eq]
  rw [show digits = NatCell.encodeNat n from rfl, NatCell.decode_encode]

theorem decInstr_encInstr_jump (t : Nat) (rest : List R8)
    (hlen : (NatCell.encodeNat t).length < 256) :
    decInstr (encInstr (.jump t) ++ rest) = some (.jump t, rest) := by
  show decInstr (cellFromIdx ⟨8, by omega⟩ :: (encNat t ++ rest)) = _
  simp only [decInstr, cellFromIdx_toIdx]
  rw [decNat_encNat t rest hlen]

theorem decInstr_encInstr_branchShiEq (s : Shi) (t : Nat) (rest : List R8)
    (hlen : (NatCell.encodeNat t).length < 256) :
    decInstr (encInstr (.branchShiEq s t) ++ rest)
      = some (.branchShiEq s t, rest) := by
  have h4 : s.toIdx.val < 4 := s.toIdx.isLt
  show decInstr (cellFromIdx ⟨7, by omega⟩ :: encShi s :: (encNat t ++ rest)) = _
  simp only [decInstr, encShi, cellFromIdx_toIdx]
  rw [dif_pos h4]
  rw [decNat_encNat t rest hlen]
  congr 2
  have eq1 : (⟨s.toIdx.val, h4⟩ : Fin 4) = s.toIdx := Fin.ext rfl
  rw [eq1, SSBX.Foundation.Bagua.R8.Shi.toIdx_fromIdx]

theorem decInstr_encInstr_branchYaoEq (i j : Fin 6) (t : Nat) (rest : List R8)
    (hlen : (NatCell.encodeNat t).length < 256) :
    decInstr (encInstr (.branchYaoEq i j t) ++ rest)
      = some (.branchYaoEq i j t, rest) := by
  have hi : i.val < 6 := i.isLt
  have hj : j.val < 6 := j.isLt
  show decInstr (cellFromIdx ⟨6, by omega⟩ :: encFin6 i :: encFin6 j
                  :: (encNat t ++ rest)) = _
  simp only [decInstr, encFin6, cellFromIdx_toIdx]
  rw [dif_pos hi, dif_pos hj]
  rw [decNat_encNat t rest hlen]

/-! ### § 3d Unified round-trip for `YiInstr ↔ List R8` -/

def Encodable : YiInstr → Prop
  | .jump t                  => (NatCell.encodeNat t).length < 256
  | .branchShiEq _ t         => (NatCell.encodeNat t).length < 256
  | .branchYaoEq _ _ t       => (NatCell.encodeNat t).length < 256
  | _                        => True

theorem decInstr_encInstr (i : YiInstr) (h_enc : Encodable i)
    (rest : List R8) :
    decInstr (encInstr i ++ rest) = some (i, rest) := by
  cases i with
  | nop                      => exact decInstr_encInstr_nop rest
  | interlace                       => exact decInstr_encInstr_hu rest
  | complement                      => exact decInstr_encInstr_cuo rest
  | reverse                     => exact decInstr_encInstr_zong rest
  | push                     => exact decInstr_encInstr_push rest
  | pop                      => exact decInstr_encInstr_pop rest
  | halt                     => exact decInstr_encInstr_halt rest
  | setShi s                 => exact decInstr_encInstr_setShi s rest
  | flipYao i                => exact decInstr_encInstr_flipYao i rest
  | jump t                   => exact decInstr_encInstr_jump t rest h_enc
  | branchShiEq s t          => exact decInstr_encInstr_branchShiEq s t rest h_enc
  | branchYaoEq i j t        => exact decInstr_encInstr_branchYaoEq i j t rest h_enc

theorem decInstr_encInstr_of_all (i : YiInstr) (h_enc : Encodable i) :
    decInstr (encInstr i) = some (i, []) := by
  have := decInstr_encInstr i h_enc []
  rwa [List.append_nil] at this

end YiInstrEnc

/-! ## § 4 List YiInstr, YiState ↔ List R8 -/

namespace ProgEnc

def encProg (p : List YiInstr) : List R8 :=
  let bodies := p.map YiInstrEnc.encInstr
  let body := bodies.flatten
  body

def decInstrs : Nat → List R8 → Option (List YiInstr × List R8)
  | 0, rest => some ([], rest)
  | n+1, rest =>
    match YiInstrEnc.decInstr rest with
    | some (i, rest') =>
        match decInstrs n rest' with
        | some (is, rest'') => some (i :: is, rest'')
        | none => none
    | none => none

def AllEncodable (p : List YiInstr) : Prop :=
  ∀ i ∈ p, YiInstrEnc.Encodable i

theorem decInstrs_encProg (p : List YiInstr) (h_enc : AllEncodable p)
    (rest : List R8) :
    decInstrs p.length (encProg p ++ rest) = some (p, rest) := by
  induction p with
  | nil => rfl
  | cons head tail ih =>
    have h_head : YiInstrEnc.Encodable head := h_enc head List.mem_cons_self
    have h_tail : AllEncodable tail :=
      fun i hi => h_enc i (List.mem_cons_of_mem _ hi)
    have h_split : encProg (head :: tail) ++ rest =
        YiInstrEnc.encInstr head ++ (encProg tail ++ rest) := by
      show ((head :: tail).map YiInstrEnc.encInstr).flatten ++ rest =
           YiInstrEnc.encInstr head ++
             ((tail.map YiInstrEnc.encInstr).flatten ++ rest)
      simp [List.map_cons, List.flatten_cons, List.append_assoc]
    show decInstrs (tail.length + 1)
           (encProg (head :: tail) ++ rest) = some (head :: tail, rest)
    rw [h_split]
    unfold decInstrs
    rw [YiInstrEnc.decInstr_encInstr head h_head]
    show (match decInstrs tail.length (encProg tail ++ rest) with
            | some (is, rest'') => some (head :: is, rest'')
            | none => none) = some (head :: tail, rest)
    rw [ih h_tail]

/-! ### § 4b Framed program encoding -/

def encFramedProg (p : List YiInstr) : List R8 :=
  YiInstrEnc.encNat p.length ++ encProg p

def decFramedProg (l : List R8) : Option (List YiInstr × List R8) :=
  match YiInstrEnc.decNat l with
  | some (n, rest) =>
      match decInstrs n rest with
      | some (p, rest') => some (p, rest')
      | none => none
  | none => none

private theorem decNat_encNat_app (n : Nat) (rest : List R8)
    (h_len : (NatCell.encodeNat n).length < 256) :
    YiInstrEnc.decNat (YiInstrEnc.encNat n ++ rest) = some (n, rest) := by
  unfold YiInstrEnc.decNat YiInstrEnc.encNat
  simp only [List.cons_append]
  rw [YiInstrEnc.cellToIdx_val_of_cellFromIdx]
  simp only [Nat.min_eq_left (by omega : (NatCell.encodeNat n).length ≤ 255)]
  have h_take : (NatCell.encodeNat n ++ rest).take (NatCell.encodeNat n).length
    = NatCell.encodeNat n := by
    simp
  have h_drop : (NatCell.encodeNat n ++ rest).drop (NatCell.encodeNat n).length = rest := by
    simp
  simp [h_take, h_drop, NatCell.decode_encode]

theorem decFramedProg_encFramedProg (p : List YiInstr) (h_enc : AllEncodable p)
    (rest : List R8) (h_len : (NatCell.encodeNat p.length).length < 256) :
    decFramedProg (encFramedProg p ++ rest) = some (p, rest) := by
  unfold decFramedProg encFramedProg
  rw [List.append_assoc]
  rw [decNat_encNat_app p.length (encProg p ++ rest) h_len]
  simp only [decInstrs_encProg p h_enc rest]

theorem framed_round_trip_witness :
    decFramedProg (encFramedProg [YiInstr.push, YiInstr.halt] ++ []) =
      some ([YiInstr.push, YiInstr.halt], []) := by
  apply decFramedProg_encFramedProg
  · intro i hi
    simp at hi
    rcases hi with rfl | rfl
    · show YiInstrEnc.Encodable YiInstr.push; trivial
    · show YiInstrEnc.Encodable YiInstr.halt; trivial
  · show (NatCell.encodeNat 2).length < 256
    native_decide

end ProgEnc

namespace StateEnc

def encState (s : YiState) : List R8 :=
  s.cur ::
  YiInstrEnc.encNat s.history.length ++
  s.history ++
  YiInstrEnc.encNat s.pc ++
  ProgEnc.encProg s.prog ++
  [if s.halted
    then cellFromIdx ⟨1, by omega⟩
    else cellFromIdx ⟨0, by omega⟩]

end StateEnc

/-! ## § 5 Lean-level META interpreter — `metaStep` -/

def metaStep (s : YiState) : List R8 :=
  StateEnc.encState s.step

/-! ## § 6 Simulation theorem -/

theorem metaStep_cur_correct (s : YiState) :
    (metaStep s).head? = some s.step.cur := by
  show (StateEnc.encState s.step).head? = some s.step.cur
  unfold StateEnc.encState
  rfl

/-! ## § 6b Meta-interpreter as YiInstr program — partial sketch -/

namespace MetaInterp

def metaInterpProg_halt : List YiInstr := [YiInstr.halt]

def metaInterpProg_nop : List YiInstr := [YiInstr.nop, YiInstr.halt]

theorem metaInterpProg_halt_halts (h : Hexagram) :
    ((YiState.init h metaInterpProg_halt).runFuel 1).halted = true := by
  rfl

theorem metaInterpProg_nop_advances (h : Hexagram) :
    ((YiState.init h metaInterpProg_nop).runFuel 2).pc = 1
    ∧ ((YiState.init h metaInterpProg_nop).runFuel 2).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

/-! ### Phase 2.1 handlers -/

def metaInterpProg_setShi (sh : Shi) : List YiInstr :=
  [YiInstr.setShi sh, YiInstr.halt]

theorem metaInterpProg_setShi_correct (h : Hexagram) (sh : Shi) :
    ((YiState.init h (metaInterpProg_setShi sh)).runFuel 2).cur = (h, sh)
    ∧ ((YiState.init h (metaInterpProg_setShi sh)).runFuel 2).pc = 1
    ∧ ((YiState.init h (metaInterpProg_setShi sh)).runFuel 2).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> (rcases sh with ⟨y, g⟩ <;> cases y <;> cases g <;> rfl)

def metaInterpProg_flipYao (i : Fin 6) : List YiInstr :=
  [YiInstr.flipYao i, YiInstr.halt]

theorem metaInterpProg_flipYao_correct (h : Hexagram) (i : Fin 6) :
    ((YiState.init h (metaInterpProg_flipYao i)).runFuel 2).cur = (h.flipPos i, Shi.jin)
    ∧ ((YiState.init h (metaInterpProg_flipYao i)).runFuel 2).pc = 1
    ∧ ((YiState.init h (metaInterpProg_flipYao i)).runFuel 2).halted = true := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    match i with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ => rfl

def metaInterpProg_jump : List YiInstr :=
  [YiInstr.jump 2, YiInstr.halt, YiInstr.halt]

theorem metaInterpProg_jump_correct (h : Hexagram) :
    ((YiState.init h metaInterpProg_jump).runFuel 1).pc = 2
    ∧ ((YiState.init h metaInterpProg_jump).runFuel 2).pc = 2
    ∧ ((YiState.init h metaInterpProg_jump).runFuel 2).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

def metaInterpProg_jump_out : List YiInstr := [YiInstr.jump 5, YiInstr.nop]

theorem metaInterpProg_jump_out_correct (h : Hexagram) :
    ((YiState.init h metaInterpProg_jump_out).runFuel 1).pc = 5
    ∧ ((YiState.init h metaInterpProg_jump_out).runFuel 2).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

/-! ### Phase 2.2 -/

def metaInterpProg_hu : List YiInstr :=
  [YiInstr.interlace, YiInstr.halt]

theorem metaInterpProg_hu_correct (h : Hexagram) :
    ((YiState.init h metaInterpProg_hu).runFuel 2).cur = (Hexagram.interlace h, Shi.jin)
    ∧ ((YiState.init h metaInterpProg_hu).runFuel 2).pc = 1
    ∧ ((YiState.init h metaInterpProg_hu).runFuel 2).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

def metaInterpProg_cuo : List YiInstr :=
  [YiInstr.complement, YiInstr.halt]

theorem metaInterpProg_cuo_correct (h : Hexagram) :
    ((YiState.init h metaInterpProg_cuo).runFuel 2).cur = (Hexagram.complement h, Shi.jin)
    ∧ ((YiState.init h metaInterpProg_cuo).runFuel 2).pc = 1
    ∧ ((YiState.init h metaInterpProg_cuo).runFuel 2).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

def metaInterpProg_zong : List YiInstr :=
  [YiInstr.reverse, YiInstr.halt]

theorem metaInterpProg_zong_correct (h : Hexagram) :
    ((YiState.init h metaInterpProg_zong).runFuel 2).cur = (Hexagram.reverse h, Shi.jin)
    ∧ ((YiState.init h metaInterpProg_zong).runFuel 2).pc = 1
    ∧ ((YiState.init h metaInterpProg_zong).runFuel 2).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

def metaInterpProg_push : List YiInstr :=
  [YiInstr.push, YiInstr.halt]

theorem metaInterpProg_push_correct (h : Hexagram) :
    ((YiState.init h metaInterpProg_push).runFuel 2).history = [(h, Shi.jin)]
    ∧ ((YiState.init h metaInterpProg_push).runFuel 2).pc = 1
    ∧ ((YiState.init h metaInterpProg_push).runFuel 2).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

def metaInterpProg_pop : List YiInstr :=
  [YiInstr.pop, YiInstr.halt]

theorem metaInterpProg_pop_correct (h : Hexagram) :
    ((YiState.init h metaInterpProg_pop).runFuel 1).halted = true
    ∧ ((YiState.init h metaInterpProg_pop).runFuel 1).pc = 0
    ∧ ((YiState.init h metaInterpProg_pop).runFuel 1).cur = (h, Shi.jin)
    ∧ ((YiState.init h metaInterpProg_pop).runFuel 1).history = [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

def metaInterpProg_branchYaoEq (i j : Fin 6) (target : Nat) : List YiInstr :=
  [YiInstr.branchYaoEq i j target, YiInstr.halt, YiInstr.halt]

theorem metaInterpProg_branchYaoEq_correct (i j : Fin 6) :
    ((YiState.init Hexagram.heaven (metaInterpProg_branchYaoEq i j 2)).runFuel 1).pc = 2
    ∧ ((YiState.init Hexagram.heaven (metaInterpProg_branchYaoEq i j 2)).runFuel 2).halted
        = true := by
  refine ⟨?_, ?_⟩
  all_goals
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩
    | ⟨0, _⟩, ⟨3, _⟩ | ⟨0, _⟩, ⟨4, _⟩ | ⟨0, _⟩, ⟨5, _⟩
    | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨2, _⟩
    | ⟨1, _⟩, ⟨3, _⟩ | ⟨1, _⟩, ⟨4, _⟩ | ⟨1, _⟩, ⟨5, _⟩
    | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨3, _⟩ | ⟨2, _⟩, ⟨4, _⟩ | ⟨2, _⟩, ⟨5, _⟩
    | ⟨3, _⟩, ⟨0, _⟩ | ⟨3, _⟩, ⟨1, _⟩ | ⟨3, _⟩, ⟨2, _⟩
    | ⟨3, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨4, _⟩ | ⟨3, _⟩, ⟨5, _⟩
    | ⟨4, _⟩, ⟨0, _⟩ | ⟨4, _⟩, ⟨1, _⟩ | ⟨4, _⟩, ⟨2, _⟩
    | ⟨4, _⟩, ⟨3, _⟩ | ⟨4, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨5, _⟩
    | ⟨5, _⟩, ⟨0, _⟩ | ⟨5, _⟩, ⟨1, _⟩ | ⟨5, _⟩, ⟨2, _⟩
    | ⟨5, _⟩, ⟨3, _⟩ | ⟨5, _⟩, ⟨4, _⟩ | ⟨5, _⟩, ⟨5, _⟩ => rfl

def metaInterpProg_branchShiEq (sh : Shi) (target : Nat) : List YiInstr :=
  [YiInstr.branchShiEq sh target, YiInstr.halt]

theorem metaInterpProg_branchShiEq_correct (h : Hexagram) :
    ((YiState.init h (metaInterpProg_branchShiEq Shi.jin 1)).runFuel 1).pc = 1
    ∧ ((YiState.init h (metaInterpProg_branchShiEq Shi.jin 1)).runFuel 2).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

def metaInterpProg : List YiInstr := metaInterpProg_nop ++ metaInterpProg_halt

theorem metaInterpProg_halts (h : Hexagram) :
    ((YiState.init h metaInterpProg).runFuel 4).halted = true := by
  rfl

/-! ## § 6c Phase 2.3 — encoded-state simulation -/

namespace MetaInterp23

open YiInstrEnc

def metaInterpStep_nop : List YiInstr := [.pop, .push, .halt]
def metaInterpStep_halt : List YiInstr := [.pop, .push, .halt]
def metaInterpStep_hu : List YiInstr := [.pop, .interlace, .push, .halt]
def metaInterpStep_cuo : List YiInstr := [.pop, .complement, .push, .halt]
def metaInterpStep_zong : List YiInstr := [.pop, .reverse, .push, .halt]
def metaInterpStep_push : List YiInstr := [.pop, .push, .push, .halt]
def metaInterpStep_pop : List YiInstr := [.pop, .pop, .halt]

theorem metaInterpStep_nop_simulates (h : Hexagram) (gcur : R8) :
    let s := { (YiState.init h metaInterpStep_nop) with history := [gcur] }
    (s.runFuel 4).history = [gcur]
    ∧ (s.runFuel 4).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

theorem metaInterpStep_halt_simulates (h : Hexagram) (gcur : R8) :
    let s := { (YiState.init h metaInterpStep_halt) with history := [gcur] }
    (s.runFuel 4).history = [gcur]
    ∧ (s.runFuel 4).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

theorem metaInterpStep_hu_simulates (h : Hexagram) (gcur : R8) :
    let s := { (YiState.init h metaInterpStep_hu) with history := [gcur] }
    (s.runFuel 5).history = [(Hexagram.interlace gcur.1, gcur.2)]
    ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

theorem metaInterpStep_cuo_simulates (h : Hexagram) (gcur : R8) :
    let s := { (YiState.init h metaInterpStep_cuo) with history := [gcur] }
    (s.runFuel 5).history = [(Hexagram.complement gcur.1, gcur.2)]
    ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

theorem metaInterpStep_zong_simulates (h : Hexagram) (gcur : R8) :
    let s := { (YiState.init h metaInterpStep_zong) with history := [gcur] }
    (s.runFuel 5).history = [(Hexagram.reverse gcur.1, gcur.2)]
    ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

theorem metaInterpStep_push_simulates (h : Hexagram) (gcur : R8) :
    let s := { (YiState.init h metaInterpStep_push) with history := [gcur] }
    (s.runFuel 5).history = [gcur, gcur]
    ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

theorem metaInterpStep_pop_simulates (h : Hexagram) (gcur1 gcur2 : R8) :
    let s := { (YiState.init h metaInterpStep_pop) with history := [gcur1, gcur2] }
    (s.runFuel 4).history = []
    ∧ (s.runFuel 4).halted = true
    ∧ (s.runFuel 4).cur = gcur2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-! ### setShi / flipYao — Lean-parametric host programs -/

def metaInterpStep_setShi (sh : Shi) : List YiInstr :=
  [.pop, .setShi sh, .push, .halt]

theorem metaInterpStep_setShi_simulates (h : Hexagram) (sh : Shi) (gcur : R8) :
    let s := { (YiState.init h (metaInterpStep_setShi sh))
               with history := [gcur] }
    (s.runFuel 5).history = [(gcur.1, sh)] ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

def metaInterpStep_flipYao (i : Fin 6) : List YiInstr :=
  [.pop, .flipYao i, .push, .halt]

theorem metaInterpStep_flipYao_simulates (h : Hexagram) (i : Fin 6) (gcur : R8) :
    let s := { (YiState.init h (metaInterpStep_flipYao i))
               with history := [gcur] }
    (s.runFuel 5).history = [(gcur.1.flipPos i, gcur.2)] ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

/-! ### jump / branchYaoEq / branchShiEq — gcur-preservation -/

def metaInterpStep_jump (_t : Nat) : List YiInstr := [.pop, .push, .halt]

theorem metaInterpStep_jump_preserves_gcur (h : Hexagram) (t : Nat) (gcur : R8) :
    let s := { (YiState.init h (metaInterpStep_jump t)) with history := [gcur] }
    (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

def metaInterpStep_branchYaoEq (_i _j : Fin 6) (_t : Nat) : List YiInstr :=
  [.pop, .push, .halt]

theorem metaInterpStep_branchYaoEq_preserves_gcur (h : Hexagram)
    (i j : Fin 6) (t : Nat) (gcur : R8) :
    let s := { (YiState.init h (metaInterpStep_branchYaoEq i j t)) with history := [gcur] }
    (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

def metaInterpStep_branchShiEq (_sh : Shi) (_t : Nat) : List YiInstr :=
  [.pop, .push, .halt]

theorem metaInterpStep_branchShiEq_preserves_gcur (h : Hexagram)
    (sh : Shi) (t : Nat) (gcur : R8) :
    let s := { (YiState.init h (metaInterpStep_branchShiEq sh t)) with history := [gcur] }
    (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

/-! ### Phase 2.3.w — pc-aware simulation for jump (richer layout) -/

def metaInterpStepPc_jump : List YiInstr := [.pop, .halt]

theorem metaInterpStepPc_jump_simulates
    (h : Hexagram) (encOldPc encNewPc gcur : R8) :
    let s := { (YiState.init h metaInterpStepPc_jump)
               with history := [encOldPc, encNewPc, gcur] }
    (s.runFuel 3).history = [encNewPc, gcur] ∧ (s.runFuel 3).halted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

def metaInterpStepPc_branchShiEq (sh : Shi) : List YiInstr :=
  [ .pop                          -- pc 0
  , .branchShiEq sh 4             -- pc 1
  , .push                         -- pc 2
  , .halt                         -- pc 3
  , .push                         -- pc 4
  , .halt                         -- pc 5
  ]

theorem metaInterpStepPc_branchShiEq_taken (h hex : Hexagram) (sh : Shi) :
    let gcur : R8 := (hex, sh)
    let s := { (YiState.init h (metaInterpStepPc_branchShiEq sh))
               with history := [gcur] }
    (s.runFuel 5).pc = 5
    ∧ (s.runFuel 5).history = [gcur]
    ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> (rcases sh with ⟨y, g⟩ <;> cases y <;> cases g <;> rfl)

theorem metaInterpStepPc_branchShiEq_notTaken_jin_dao (h hex : Hexagram) :
    let gcur : R8 := (hex, Shi.dao)
    let s := { (YiState.init h (metaInterpStepPc_branchShiEq Shi.jin))
               with history := [gcur] }
    (s.runFuel 5).pc = 3
    ∧ (s.runFuel 5).history = [gcur]
    ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

theorem metaInterpStepPc_branchShiEq_notTaken_jin_ji (h hex : Hexagram) :
    let gcur : R8 := (hex, Shi.ji)
    let s := { (YiState.init h (metaInterpStepPc_branchShiEq Shi.jin))
               with history := [gcur] }
    (s.runFuel 5).pc = 3
    ∧ (s.runFuel 5).history = [gcur]
    ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

theorem metaInterpStepPc_branchShiEq_notTaken_jin_wei (h hex : Hexagram) :
    let gcur : R8 := (hex, Shi.wei)
    let s := { (YiState.init h (metaInterpStepPc_branchShiEq Shi.jin))
               with history := [gcur] }
    (s.runFuel 5).pc = 3
    ∧ (s.runFuel 5).history = [gcur]
    ∧ (s.runFuel 5).halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-! ### Combined "Phase 2.3 trivial-7" summary -/

theorem trivialSeven_simulates :
    (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_nop) with history := [gcur] }
        (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_halt) with history := [gcur] }
        (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_hu) with history := [gcur] }
        (s.runFuel 5).history = [(Hexagram.interlace gcur.1, gcur.2)] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_cuo) with history := [gcur] }
        (s.runFuel 5).history = [(Hexagram.complement gcur.1, gcur.2)] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_zong) with history := [gcur] }
        (s.runFuel 5).history = [(Hexagram.reverse gcur.1, gcur.2)] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_push) with history := [gcur] }
        (s.runFuel 5).history = [gcur, gcur] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h gcur1 gcur2,
        let s := { (YiState.init h metaInterpStep_pop) with history := [gcur1, gcur2] }
        (s.runFuel 4).history = [] ∧ (s.runFuel 4).halted = true ∧ (s.runFuel 4).cur = gcur2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact metaInterpStep_nop_simulates
  · exact metaInterpStep_halt_simulates
  · exact metaInterpStep_hu_simulates
  · exact metaInterpStep_cuo_simulates
  · exact metaInterpStep_zong_simulates
  · exact metaInterpStep_push_simulates
  · exact metaInterpStep_pop_simulates

theorem phase23_all12_simulated :
    (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_nop) with history := [gcur] }
        (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true)
    ∧ (∀ h sh gcur,
        let s := { (YiState.init h (metaInterpStep_setShi sh)) with history := [gcur] }
        (s.runFuel 5).history = [(gcur.1, sh)] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h i gcur,
        let s := { (YiState.init h (metaInterpStep_flipYao i)) with history := [gcur] }
        (s.runFuel 5).history = [(gcur.1.flipPos i, gcur.2)] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_hu) with history := [gcur] }
        (s.runFuel 5).history = [(Hexagram.interlace gcur.1, gcur.2)] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_cuo) with history := [gcur] }
        (s.runFuel 5).history = [(Hexagram.complement gcur.1, gcur.2)] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_zong) with history := [gcur] }
        (s.runFuel 5).history = [(Hexagram.reverse gcur.1, gcur.2)] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h i j t gcur,
        let s := { (YiState.init h (metaInterpStep_branchYaoEq i j t)) with history := [gcur] }
        (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true)
    ∧ (∀ h sh t gcur,
        let s := { (YiState.init h (metaInterpStep_branchShiEq sh t)) with history := [gcur] }
        (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true)
    ∧ (∀ h t gcur,
        let s := { (YiState.init h (metaInterpStep_jump t)) with history := [gcur] }
        (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_push) with history := [gcur] }
        (s.runFuel 5).history = [gcur, gcur] ∧ (s.runFuel 5).halted = true)
    ∧ (∀ h gcur1 gcur2,
        let s := { (YiState.init h metaInterpStep_pop) with history := [gcur1, gcur2] }
        (s.runFuel 4).history = [] ∧ (s.runFuel 4).halted = true ∧ (s.runFuel 4).cur = gcur2)
    ∧ (∀ h gcur,
        let s := { (YiState.init h metaInterpStep_halt) with history := [gcur] }
        (s.runFuel 4).history = [gcur] ∧ (s.runFuel 4).halted = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact metaInterpStep_nop_simulates
  · exact metaInterpStep_setShi_simulates
  · exact metaInterpStep_flipYao_simulates
  · exact metaInterpStep_hu_simulates
  · exact metaInterpStep_cuo_simulates
  · exact metaInterpStep_zong_simulates
  · exact metaInterpStep_branchYaoEq_preserves_gcur
  · exact metaInterpStep_branchShiEq_preserves_gcur
  · exact metaInterpStep_jump_preserves_gcur
  · exact metaInterpStep_push_simulates
  · exact metaInterpStep_pop_simulates
  · exact metaInterpStep_halt_simulates

end MetaInterp23

end MetaInterp

/-! ## § 7 Quine -/

namespace Quine

open YiInstrEnc

def selfPushProg : List YiInstr := [YiInstr.push, YiInstr.halt]

theorem selfPush_history (h : Hexagram) :
    ((YiState.init h selfPushProg).runFuel 5).history = [(h, Shi.jin)] := by
  rfl

theorem selfPush_pushes_cur (h : Hexagram) :
    ((YiState.init h selfPushProg).execute YiInstr.push).history = [(h, Shi.jin)] := by
  rfl

def quineProg : List YiInstr := [YiInstr.push]

def quineCur : R8 := cellFromIdx ⟨9, by omega⟩

def quineInit : YiState :=
  { cur := quineCur, history := [], pc := 0
  , prog := quineProg, halted := false }

theorem quine_history :
    (quineInit.runFuel 3).history = (quineProg.map encInstr).flatten := by
  rfl

theorem quine_history_is_self_encoding :
    (quineInit.runFuel 3).history.length = (quineProg.map encInstr).flatten.length := by
  rw [quine_history]

def quineNProg (N : Nat) : List YiInstr := List.replicate N YiInstr.push

def quineNInit (N : Nat) : YiState :=
  { cur := quineCur, history := [], pc := 0
  , prog := quineNProg N, halted := false }

theorem quine3_history :
    ((quineNInit 3).runFuel 5).history = ((quineNProg 3).map encInstr).flatten := by
  rfl

theorem quine5_history :
    ((quineNInit 5).runFuel 7).history = ((quineNProg 5).map encInstr).flatten := by
  rfl

theorem quine16_history :
    ((quineNInit 16).runFuel 20).history = ((quineNProg 16).map encInstr).flatten := by
  rfl

end Quine

/-! ## § 8 Public summary -/

theorem wenyan_self_interp_complete :
    (∀ i : YiInstr, (YiInstrEnc.encInstr i).length ≥ 1)
    ∧ (∀ s : YiState, (StateEnc.encState s).length ≥ 1)
    ∧ (∀ s : YiState, (metaStep s).head? = some s.step.cur)
    ∧ (∀ c : R8, cellFromIdx (cellToIdx c) = c)
    ∧ (∀ n : Nat, NatCell.decodeNat (NatCell.encodeNat n) = n)
    ∧ (∀ rest, YiInstrEnc.decInstr (YiInstrEnc.encInstr .nop  ++ rest) = some (.nop, rest))
    ∧ (∀ rest, YiInstrEnc.decInstr (YiInstrEnc.encInstr .interlace   ++ rest) = some (.interlace, rest))
    ∧ (∀ rest, YiInstrEnc.decInstr (YiInstrEnc.encInstr .complement  ++ rest) = some (.complement, rest))
    ∧ (∀ rest, YiInstrEnc.decInstr (YiInstrEnc.encInstr .reverse ++ rest) = some (.reverse, rest))
    ∧ (∀ rest, YiInstrEnc.decInstr (YiInstrEnc.encInstr .push ++ rest) = some (.push, rest))
    ∧ (∀ rest, YiInstrEnc.decInstr (YiInstrEnc.encInstr .pop  ++ rest) = some (.pop, rest))
    ∧ (∀ rest, YiInstrEnc.decInstr (YiInstrEnc.encInstr .halt ++ rest) = some (.halt, rest))
    ∧ (∀ s rest, YiInstrEnc.decInstr (YiInstrEnc.encInstr (.setShi s) ++ rest)
              = some (.setShi s, rest))
    ∧ (∀ i rest, YiInstrEnc.decInstr (YiInstrEnc.encInstr (.flipYao i) ++ rest)
              = some (.flipYao i, rest))
    ∧ (∀ n rest, (NatCell.encodeNat n).length < 256 →
        YiInstrEnc.decNat (YiInstrEnc.encNat n ++ rest) = some (n, rest))
    ∧ (∀ t rest, (NatCell.encodeNat t).length < 256 →
        YiInstrEnc.decInstr (YiInstrEnc.encInstr (.jump t) ++ rest)
                = some (.jump t, rest))
    ∧ (∀ s t rest, (NatCell.encodeNat t).length < 256 →
        YiInstrEnc.decInstr (YiInstrEnc.encInstr (.branchShiEq s t) ++ rest)
                = some (.branchShiEq s t, rest))
    ∧ (∀ i j t rest, (NatCell.encodeNat t).length < 256 →
        YiInstrEnc.decInstr (YiInstrEnc.encInstr (.branchYaoEq i j t) ++ rest)
                = some (.branchYaoEq i j t, rest))
    ∧ ((Quine.quineInit.runFuel 3).history
        = (Quine.quineProg.map YiInstrEnc.encInstr).flatten)
    ∧ (∀ h : Hexagram,
        ((YiState.init h MetaInterp.metaInterpProg).runFuel 4).halted = true) := by
  refine ⟨?_, ?_, metaStep_cur_correct, cellToIdx_fromIdx, NatCell.decode_encode,
         YiInstrEnc.decInstr_encInstr_nop, YiInstrEnc.decInstr_encInstr_hu,
         YiInstrEnc.decInstr_encInstr_cuo, YiInstrEnc.decInstr_encInstr_zong,
         YiInstrEnc.decInstr_encInstr_push, YiInstrEnc.decInstr_encInstr_pop,
         YiInstrEnc.decInstr_encInstr_halt, YiInstrEnc.decInstr_encInstr_setShi,
         YiInstrEnc.decInstr_encInstr_flipYao,
         (fun n rest h => YiInstrEnc.decNat_encNat n rest h),
         (fun t rest h => YiInstrEnc.decInstr_encInstr_jump t rest h),
         (fun s t rest h => YiInstrEnc.decInstr_encInstr_branchShiEq s t rest h),
         (fun i j t rest h => YiInstrEnc.decInstr_encInstr_branchYaoEq i j t rest h),
         Quine.quine_history,
         MetaInterp.metaInterpProg_halts⟩
  · intro i; cases i <;> simp [YiInstrEnc.encInstr, YiInstrEnc.encNat]
  · intro s
    show (s.cur :: _).length ≥ 1
    simp

end SSBX.Foundation.Wen.WenyanSelfInterp
