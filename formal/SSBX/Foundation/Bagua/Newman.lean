/-
# Newman's Lemma — abstract confluence theorem (Task #50)

  ⊢ Strongly Normalizing + Locally Confluent → Confluent

  Standard proof: well-founded induction on the SN order, peeling first
  steps from both diverging paths, joining via local confluence, and
  chaining IH applications.

  ## Application to Wen

  This file proves Newman's lemma in full generality (any type α, any relation
  R). Applying it to the Wen `Step` relation requires:

  1. **Strong normalization**: Wen kernel is **not** SN globally (Y-combinator
     encoding loops). To apply Newman, restrict to:
     - Lam-encoded terms typable in STLC (where β-reduction is SN by Tait).
     - Or: a fragment without recursion-enabling structure.

  2. **Local confluence**: needs critical-pair analysis on Wen's 14 reduction
     rules. Tractable but mechanical (~30+ critical pair checks).

  We provide the abstract theorem here. The application to a typed Wen
  fragment is a follow-up; the abstract Newman is the keystone.
-/

namespace SSBX.Foundation.Bagua.Newman

universe u
variable {α : Type u}

/-! ## § 1 Reflexive-transitive closure (R*) -/

/-- Reflexive-transitive closure (snoc-form: refl + extension on the right). -/
inductive RTC (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : RTC R a a
  | tail {a b c : α} : RTC R a b → R b c → RTC R a c

namespace RTC

variable {R : α → α → Prop}

theorem single {a b : α} (h : R a b) : RTC R a b := .tail (.refl a) h

theorem trans {a b c : α} (h1 : RTC R a b) (h2 : RTC R b c) : RTC R a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact .tail ih hstep

/-- Cons-form characterization: every R* path is either trivial or starts
    with a single R-step followed by another R* path. -/
theorem cons_form (t u : α) :
    RTC R t u ↔ t = u ∨ ∃ t', R t t' ∧ RTC R t' u := by
  constructor
  · intro h
    induction h with
    | refl => left; rfl
    | tail h_prev h_step ih =>
      rename_i b c
      cases ih with
      | inl heq =>
        right
        refine ⟨c, ?_, .refl c⟩
        rw [heq]; exact h_step
      | inr hex =>
        obtain ⟨t', hr, hrest⟩ := hex
        right
        exact ⟨t', hr, .tail hrest h_step⟩
  · intro h
    cases h with
    | inl heq =>
        rw [heq]; exact .refl u
    | inr hex =>
        obtain ⟨t', hr, hrest⟩ := hex
        exact .trans (.single hr) hrest

end RTC

/-! ## § 2 The three properties -/

/-- Local confluence (weak Church-Rosser): every 1-step fork joins. -/
def LocallyConfluent (R : α → α → Prop) : Prop :=
  ∀ t u v, R t u → R t v → ∃ w, RTC R u w ∧ RTC R v w

/-- Strong normalization: no infinite descent (= reverse R is well-founded).
    `wf` here means: ∀ t, every chain of R-steps from t terminates. -/
def StronglyNormalizing (R : α → α → Prop) : Prop :=
  WellFounded (fun u t => R t u)

/-- Confluence (Church-Rosser): every multi-step fork joins. -/
def Confluent (R : α → α → Prop) : Prop :=
  ∀ t u v, RTC R t u → RTC R t v → ∃ w, RTC R u w ∧ RTC R v w

/-! ## § 3 Newman's lemma — main proof -/

theorem newman (R : α → α → Prop)
    (sn : StronglyNormalizing R) (lc : LocallyConfluent R) :
    Confluent R := by
  intro t
  -- Well-founded induction on t using SN
  induction t using sn.induction with
  | _ t ih =>
    intro u v interlace hv
    -- Decompose interlace via cons-form: either t = u or t → u' → ... → u
    rw [RTC.cons_form] at interlace
    cases interlace with
    | inl heq_u =>
        -- t = u; common descendant is v
        subst heq_u
        exact ⟨v, hv, .refl v⟩
    | inr hex_u =>
        obtain ⟨u', h_t_u', h_u'_u⟩ := hex_u
        -- Decompose hv similarly
        rw [RTC.cons_form] at hv
        cases hv with
        | inl heq_v =>
            subst heq_v
            -- t = v; common descendant is u
            exact ⟨u, .refl u,
                   RTC.trans (.single h_t_u') h_u'_u⟩
        | inr hex_v =>
            obtain ⟨v', h_t_v', h_v'_v⟩ := hex_v
            -- Local confluence on the divergent first steps
            obtain ⟨z, h_u'_z, h_v'_z⟩ := lc t u' v' h_t_u' h_t_v'
            -- IH on u' (smaller than t since R t u'):
            obtain ⟨wa, h_u_wa, h_z_wa⟩ := ih u' h_t_u' u z h_u'_u h_u'_z
            -- IH on v':
            obtain ⟨wb, h_v_wb, h_z_wb⟩ := ih v' h_t_v' v z h_v'_v h_v'_z
            -- IH on z (smaller than t since t →¹ u' →* z):
            -- Need to show R t z' for some z' →* z, which we have via u'.
            -- Actually we need to call IH on something STRICTLY less than t.
            -- u' is strictly less (R t u'). We use IH on u' applied to wa, wb.
            -- Wait — we need ih on z, but `ih` requires R t z directly (one step).
            -- The signature: `ih : ∀ y, R t y → ...`. We have R t u'.
            -- For z: we don't have R t z directly. But u' →* z, so z is reachable
            -- from u' (which is reachable from t in 1 step).
            -- Hmm — sn.induction provides IH for direct R-successors only.
            -- That's not strong enough. We need IH for ALL R-descendants.
            -- Resolution: WellFounded.induction GIVES IH for any y with R t y.
            -- But we want it transitively.
            -- Trick: nest the induction. IH on u' (a direct successor of t) gives
            -- a Confluent-like property. We've already used it. To handle z,
            -- we'd want IH on z, which is indirectly reachable.
            -- Instead, observe: we can call ih u' (with R t u') and treat u' as
            -- the new "root". The Confluent-property for u' says: u' →* a, u' →* b
            -- implies common w. We have u' →* wa (via h_u_wa? no that's u→*wa).
            -- Hmm, need to re-check the IH application.
            --
            -- Let me redo: ih u' h_t_u' has type:
            --   ∀ u v, RTC R u' u → RTC R u' v → ∃ w, RTC R u w ∧ RTC R v w
            -- That IS Confluent-from-u'. So:
            --   - Apply to (u, z): get common wa with u →* wa, z →* wa. ✓
            --   - Apply to (wa, wb): need RTC R u' wa AND RTC R u' wb. We have:
            --     RTC R u' wa via z (u' →* z →* wa, but we got h_z_wa : RTC R z wa).
            --     RTC R u' wb via v' branch. Hmm complicated.
            --
            -- Simpler: apply IH on u' THREE TIMES.
            --   1. Get wa from u →* something, z →* something. (u' →* u, u' →* z)
            --   2. Use wa as the join.
            -- Then for the v side, apply IH on v' similarly.
            -- Then to merge wa with wb, we need IH on something that has both
            -- as descendants. Both wa and wb are reachable from z (via h_z_wa
            -- and h_z_wb). So apply IH on z... but we only have IH on direct
            -- successors of t.
            --
            -- The classical proof uses transitive IH. WellFounded.induction's
            -- `ih` actually gives IH on ANY y with the well-founded relation
            -- holding from t — which here is "R t y", but for the proof we
            -- want IH for any y reachable from t in any number of steps.
            -- That stronger IH can be obtained by combining the well-founded
            -- with transitivity (the transitive closure of a well-founded
            -- relation is well-founded if the relation is well-founded? No,
            -- it's NOT in general for transitive closures).
            --
            -- Actually, R is well-founded ⟹ R⁺ (transitive closure) is well-founded.
            -- So we can re-induct on R⁺. But this requires extra setup.
            --
            -- Simpler resolution: apply ih on u' to (u, wb). We need RTC R u' u
            -- (we have h_u'_u) and RTC R u' wb. wb is reached from v' via:
            --   v' →* z (h_v'_z) →* wb (h_z_wb).
            -- For RTC R u' wb: u' →* z →* wb? u' →* z via h_u'_z. z →* wb via h_z_wb.
            -- So RTC R u' wb = trans h_u'_z h_z_wb. ✓
            -- Apply ih u' h_t_u' u wb (h_u'_u) (RTC.trans h_u'_z h_z_wb):
            --   ∃ w, RTC R u w ∧ RTC R wb w
            -- Then use ⟨w, h_u_w, RTC.trans h_v_wb h_wb_w⟩
            --
            -- Wait we need to also have RTC R u' wb via this path. Yes ✓.
            obtain ⟨w, h_u_w, h_wb_w⟩ :=
              ih u' h_t_u' u wb h_u'_u (RTC.trans h_u'_z h_z_wb)
            exact ⟨w, h_u_w, RTC.trans h_v_wb h_wb_w⟩

/-! ## § 4 Newman's lemma corollary -/

/-- Phrasing as: "weakly Church-Rosser + SN ⟹ Church-Rosser". -/
theorem newman_alt (R : α → α → Prop)
    (sn : StronglyNormalizing R) (lc : LocallyConfluent R)
    (t u v : α) (interlace : RTC R t u) (hv : RTC R t v) :
    ∃ w, RTC R u w ∧ RTC R v w :=
  newman R sn lc t u v interlace hv

end SSBX.Foundation.Bagua.Newman
