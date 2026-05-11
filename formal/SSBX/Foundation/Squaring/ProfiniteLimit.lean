/-
# Profinite limit of the squaring tower

This module keeps the M5 construction compile-oriented:

* `L n` is the finite `2^n` block carrier, implemented as iterated products.
* `pi n : L (n+1) -> L n` is first-half projection.
* `L_inf` is the coherent prefix carrier for the inverse system.
* `fromStream` and `toStream` are the concrete Stream' bridge, with both round
  trips proved and packaged as an additive equivalence.
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import SSBX.Foundation.Squaring.StreamCarrier

namespace SSBX.Foundation.Squaring

open SSBX.Foundation.Bagua.Cell256
open CategoryTheory

namespace ProfiniteLimit

/-- The finite squaring tower: `L n` is a block of length `2^n`. -/
def L : Nat -> Type
  | 0 => Cell256
  | n + 1 => L n × L n

instance instAddCommGroupL (n : Nat) : AddCommGroup (L n) := by
  induction n with
  | zero =>
      change AddCommGroup Cell256
      infer_instance
  | succ n ih =>
      change AddCommGroup (L n × L n)
      letI := ih
      infer_instance

noncomputable instance instFintypeL (n : Nat) : Fintype (L n) := by
  induction n with
  | zero =>
      change Fintype Cell256
      infer_instance
  | succ n ih =>
      change Fintype (L n × L n)
      letI := ih
      infer_instance

/-- First-half projection in the inverse system. -/
def pi (n : Nat) : L (n + 1) -> L n := Prod.fst

@[simp] theorem pi_apply (n : Nat) (x : L (n + 1)) : pi n x = x.1 := rfl

@[simp] theorem pi_map_add (n : Nat) (x y : L (n + 1)) :
    pi n (x + y) = pi n x + pi n y := rfl

/-- Coherent prefixes for the first-half projection tower. -/
structure L_inf where
  toBlock : (n : Nat) -> L n
  coh : ∀ n, pi n (toBlock (n + 1)) = toBlock n

namespace L_inf

@[ext] theorem ext {x y : L_inf} (h : ∀ n, x.toBlock n = y.toBlock n) : x = y := by
  cases x with
  | mk xb xc =>
      cases y with
      | mk yb yc =>
          have hfun : xb = yb := funext h
          subst hfun
          rfl

instance : Zero L_inf where
  zero :=
    { toBlock := fun _ => 0
      coh := by
        intro n
        rfl }

instance : Add L_inf where
  add x y :=
    { toBlock := fun n => x.toBlock n + y.toBlock n
      coh := by
        intro n
        rw [← x.coh n, ← y.coh n]
        exact (pi_map_add n (x.toBlock (n + 1)) (y.toBlock (n + 1))).symm }

instance : Neg L_inf where
  neg x :=
    { toBlock := fun n => -x.toBlock n
      coh := by
        intro n
        rw [← x.coh n]
        rfl }

instance : Sub L_inf where
  sub x y := x + -y

instance : AddCommGroup L_inf where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro a b c
    ext n
    exact add_assoc _ _ _
  zero_add := by
    intro a
    ext n
    exact zero_add _
  add_zero := by
    intro a
    ext n
    exact add_zero _
  neg_add_cancel := by
    intro a
    ext n
    exact neg_add_cancel _
  add_comm := by
    intro a b
    ext n
    exact add_comm _ _

end L_inf

instance instAddCommGroupTrajCell : AddCommGroup StreamCarrier.TrajCell := by
  change AddCommGroup (Nat -> Cell256)
  infer_instance

/-- Read a natural-number coordinate from a finite block.

Out-of-range indices are still assigned a value by recursively falling into the
right branch.  The correctness lemma below is only stated for `k < 2^n`.
-/
def blockGetNat : (n : Nat) -> L n -> Nat -> Cell256
  | 0, b, _ => b
  | n + 1, b, k =>
      if k < 2 ^ n then
        blockGetNat n b.1 k
      else
        blockGetNat n b.2 (k - 2 ^ n)

/-- First `2^n` cells of a stream, packed into the recursive block carrier. -/
def blockTake : (n : Nat) -> StreamCarrier.TrajCell -> L n
  | 0, s => s.head
  | n + 1, s => (blockTake n s, blockTake n (s.drop (2 ^ n)))

@[simp] theorem pi_blockTake (n : Nat) (s : StreamCarrier.TrajCell) :
    pi n (blockTake (n + 1) s) = blockTake n s := rfl

theorem blockGetNat_blockTake :
    ∀ (n : Nat) (s : StreamCarrier.TrajCell) {k : Nat},
      k < 2 ^ n -> blockGetNat n (blockTake n s) k = s.get k
  | 0, _s, k, hk => by
      have hk0 : k = 0 := by omega
      subst k
      rfl
  | n + 1, s, k, hk => by
      by_cases hleft : k < 2 ^ n
      · simpa [blockGetNat, blockTake, hleft] using
          blockGetNat_blockTake n s hleft
      · have hle : 2 ^ n ≤ k := Nat.le_of_not_gt hleft
        have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
          rw [pow_succ]
          omega
        have hright : k - 2 ^ n < 2 ^ n := by omega
        have hadd : 2 ^ n + (k - 2 ^ n) = k := Nat.add_sub_of_le hle
        have hrec := blockGetNat_blockTake n (s.drop (2 ^ n)) hright
        simpa [blockGetNat, blockTake, hleft, Stream'.get_drop, hadd] using hrec

theorem index_lt_level (k : Nat) : k < 2 ^ (k + 1) := by
  exact lt_of_lt_of_le Nat.lt_two_pow_self
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ k))

/-- A stream determines coherent finite prefixes. -/
def fromStream (s : StreamCarrier.TrajCell) : L_inf where
  toBlock := fun n => blockTake n s
  coh := by
    intro n
    rfl

/-- Read the `k`-th cell from a sufficiently large coherent prefix. -/
def toStream (x : L_inf) : StreamCarrier.TrajCell :=
  fun k => blockGetNat (k + 1) (x.toBlock (k + 1)) k

theorem toStream_fromStream (s : StreamCarrier.TrajCell) :
    toStream (fromStream s) = s := by
  apply Stream'.ext
  intro k
  exact blockGetNat_blockTake (k + 1) s (index_lt_level k)

theorem blockGetNat_pi (n : Nat) (b : L (n + 1)) {k : Nat} (hk : k < 2 ^ n) :
    blockGetNat n (pi n b) k = blockGetNat (n + 1) b k := by
  simp [pi, blockGetNat, hk]

theorem blockGetNat_coherent_le (x : L_inf) (m d k : Nat) (hk : k < 2 ^ m) :
    blockGetNat m (x.toBlock m) k =
      blockGetNat (m + d) (x.toBlock (m + d)) k := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hkmd : k < 2 ^ (m + d) := by
        exact lt_of_lt_of_le hk
          (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right m d))
      have hstep :
          blockGetNat (m + d) (x.toBlock (m + d)) k =
            blockGetNat ((m + d) + 1) (x.toBlock ((m + d) + 1)) k := by
        rw [← x.coh (m + d)]
        exact blockGetNat_pi (m + d) (x.toBlock ((m + d) + 1)) hkmd
      calc
        blockGetNat m (x.toBlock m) k =
            blockGetNat (m + d) (x.toBlock (m + d)) k := ih
        _ = blockGetNat ((m + d) + 1) (x.toBlock ((m + d) + 1)) k := hstep
        _ = blockGetNat (m + (d + 1)) (x.toBlock (m + (d + 1))) k := by
          have hidx : (m + d) + 1 = m + (d + 1) := by omega
          rw [hidx]

theorem blockGetNat_ext :
    ∀ (n : Nat) (a b : L n),
      (∀ k, k < 2 ^ n -> blockGetNat n a k = blockGetNat n b k) -> a = b
  | 0, a, b, h => by
      have h0 := h 0 (by norm_num)
      simpa [blockGetNat] using h0
  | n + 1, a, b, h => by
      rcases a with ⟨al, ar⟩
      rcases b with ⟨bl, br⟩
      congr
      · apply blockGetNat_ext n
        intro k hk
        have hlt : k < 2 ^ (n + 1) := by
          have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
            rw [pow_succ]
            omega
          omega
        have hp := h k hlt
        simpa [blockGetNat, hk] using hp
      · apply blockGetNat_ext n
        intro k hk
        have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
          rw [pow_succ]
          omega
        have hlt : 2 ^ n + k < 2 ^ (n + 1) := by omega
        have hnot : ¬ 2 ^ n + k < 2 ^ n := by omega
        have hsub : 2 ^ n + k - 2 ^ n = k := by omega
        have hp := h (2 ^ n + k) hlt
        simpa [blockGetNat, hnot, hsub] using hp

theorem toStream_get_eq_blockGetNat (x : L_inf) (n k : Nat) (hk : k < 2 ^ n) :
    (toStream x).get k = blockGetNat n (x.toBlock n) k := by
  dsimp [toStream, Stream'.get]
  rcases le_total n (k + 1) with hle | hle
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd]
    exact (blockGetNat_coherent_le x n d k hk).symm
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd]
    exact blockGetNat_coherent_le x (k + 1) d k (index_lt_level k)

theorem blockTake_toStream (x : L_inf) (n : Nat) :
    blockTake n (toStream x) = x.toBlock n := by
  apply blockGetNat_ext n
  intro k hk
  rw [blockGetNat_blockTake n (toStream x) hk]
  exact toStream_get_eq_blockGetNat x n k hk

theorem fromStream_toStream (x : L_inf) : fromStream (toStream x) = x := by
  ext n
  exact blockTake_toStream x n

theorem blockGetNat_add :
    ∀ (n : Nat) (a b : L n) (k : Nat),
      blockGetNat n (a + b) k = blockGetNat n a k + blockGetNat n b k
  | 0, _a, _b, _k => rfl
  | n + 1, a, b, k => by
      by_cases h : k < 2 ^ n
      · simpa [blockGetNat, h] using blockGetNat_add n a.1 b.1 k
      · simpa [blockGetNat, h] using blockGetNat_add n a.2 b.2 (k - 2 ^ n)

/-- The coherent-prefix carrier is additively equivalent to cell streams. -/
def isoStream : L_inf ≃+ StreamCarrier.TrajCell where
  toFun := toStream
  invFun := fromStream
  left_inv := fromStream_toStream
  right_inv := toStream_fromStream
  map_add' := by
    intro x y
    apply Stream'.ext
    intro k
    exact blockGetNat_add (k + 1) (x.toBlock (k + 1)) (y.toBlock (k + 1)) k

/-- Tail transported back through the proved `fromStream` direction. -/
def tailLimit (x : L_inf) : L_inf :=
  fromStream (toStream x).tail

/-- Coalgebra structure transported from the stream head/tail coalgebra. -/
def coalg (x : L_inf) : Cell256 × L_inf :=
  ((toStream x).head, tailLimit x)

theorem coalg_toStream_step (x : L_inf) :
    StreamCarrier.step (toStream x) = ((coalg x).1, toStream (coalg x).2) := by
  simp [coalg, tailLimit, StreamCarrier.step, toStream_fromStream]

def coalgebraMorphism {X : Type} (ξ : X -> Cell256 × X) : X -> L_inf :=
  fun x => fromStream (StreamCarrier.unfold ξ x)

theorem coalgebraMorphism_step {X : Type} (ξ : X -> Cell256 × X) (x : X) :
    coalg (coalgebraMorphism ξ x) =
      ((ξ x).1, coalgebraMorphism ξ (ξ x).2) := by
  simp [coalgebraMorphism, coalg, tailLimit, StreamCarrier.unfold_head,
    StreamCarrier.unfold_tail, toStream_fromStream]

theorem coalgebraMorphism_unique {X : Type} (ξ : X -> Cell256 × X) (g : X -> L_inf)
    (h : ∀ x, coalg (g x) = ((ξ x).1, g (ξ x).2)) :
    g = coalgebraMorphism ξ := by
  have hstep : ∀ x,
      StreamCarrier.step (toStream (g x)) =
        ((ξ x).1, toStream (g (ξ x).2)) := by
    intro x
    calc
      StreamCarrier.step (toStream (g x)) =
          ((coalg (g x)).1, toStream (coalg (g x)).2) := coalg_toStream_step (g x)
      _ = ((ξ x).1, toStream (g (ξ x).2)) := by rw [h x]
  funext x
  have hstream : toStream (g x) = StreamCarrier.unfold ξ x := by
    apply Stream'.ext
    intro n
    induction n generalizing x with
    | zero =>
        have hh := congrArg Prod.fst (hstep x)
        simpa [StreamCarrier.step, StreamCarrier.unfold_head] using hh
    | succ n ih =>
        have ht := congrArg Prod.snd (hstep x)
        calc
          Stream'.get (toStream (g x)) (n + 1) =
              Stream'.get (toStream (g x)).tail n := by
            rw [Stream'.get_succ]
          _ = Stream'.get (toStream (g (ξ x).2)) n := by
            simpa [StreamCarrier.step] using congrArg (fun s => Stream'.get s n) ht
          _ = Stream'.get (StreamCarrier.unfold ξ (ξ x).2) n := ih (ξ x).2
          _ = Stream'.get (StreamCarrier.unfold ξ x).tail n := by
            rw [StreamCarrier.unfold_tail]
          _ = Stream'.get (StreamCarrier.unfold ξ x) (n + 1) := by
            rw [Stream'.get_succ]
  calc
    g x = fromStream (toStream (g x)) := (fromStream_toStream (g x)).symm
    _ = fromStream (StreamCarrier.unfold ξ x) := by rw [hstream]
    _ = coalgebraMorphism ξ x := rfl

theorem L_inf_isFinalCoalgebra_concrete {X : Type} (ξ : X -> Cell256 × X) :
    ∃! g : X -> L_inf, ∀ x, coalg (g x) = ((ξ x).1, g (ξ x).2) := by
  refine ⟨coalgebraMorphism ξ, coalgebraMorphism_step ξ, ?_⟩
  intro g hg
  exact coalgebraMorphism_unique ξ g hg

/-- The concrete polynomial functor `F X = Cell256 × X` on `Type`. -/
def funcF : Type ⥤ Type where
  obj X := Cell256 × X
  map {X Y} f := TypeCat.ofHom (fun p : Cell256 × X => (p.1, f p.2))

/-- `L_inf` as a Mathlib endofunctor coalgebra. -/
def L_inf_coalgebra : CategoryTheory.Endofunctor.Coalgebra funcF where
  V := L_inf
  str := TypeCat.ofHom coalg

def terminalMorphismOf (A : CategoryTheory.Endofunctor.Coalgebra funcF) :
    A ⟶ L_inf_coalgebra where
  f := TypeCat.ofHom (coalgebraMorphism A.str)
  h := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (coalgebraMorphism_step A.str x).symm

theorem terminalMorphismOf_unique (A : CategoryTheory.Endofunctor.Coalgebra funcF)
    (m : A ⟶ L_inf_coalgebra) : m = terminalMorphismOf A := by
  apply CategoryTheory.Endofunctor.Coalgebra.ext
  apply ConcreteCategory.hom_ext
  intro x
  have hfun : (fun x => m.f x) = coalgebraMorphism A.str := by
    apply coalgebraMorphism_unique A.str
    intro x
    have hm := congrArg (fun f => f x) m.h
    simpa [funcF, L_inf_coalgebra] using hm.symm
  exact congrFun hfun x

noncomputable def L_inf_isFinalCoalgebra :
    CategoryTheory.Limits.IsTerminal L_inf_coalgebra :=
  CategoryTheory.Limits.IsTerminal.ofUniqueHom terminalMorphismOf terminalMorphismOf_unique

theorem profinite_limit_summary :
    (∀ n, Nonempty (AddCommGroup (L n)))
    ∧ (∀ n (x y : L (n + 1)), pi n (x + y) = pi n x + pi n y)
    ∧ Function.LeftInverse fromStream toStream
    ∧ (∀ s : StreamCarrier.TrajCell, toStream (fromStream s) = s)
    ∧ (∀ (X : Type) (ξ : X -> Cell256 × X),
        ∃! g : X -> L_inf, ∀ x, coalg (g x) = ((ξ x).1, g (ξ x).2))
    ∧ Nonempty (CategoryTheory.Limits.IsTerminal L_inf_coalgebra)
    ∧ (∀ x : L_inf,
        StreamCarrier.step (toStream x) = ((coalg x).1, toStream (coalg x).2)) :=
  ⟨fun n => ⟨instAddCommGroupL n⟩,
   pi_map_add,
   fromStream_toStream,
   toStream_fromStream,
   (fun X ξ => L_inf_isFinalCoalgebra_concrete (X := X) ξ),
   ⟨L_inf_isFinalCoalgebra⟩,
   coalg_toStream_step⟩

end ProfiniteLimit

end SSBX.Foundation.Squaring
