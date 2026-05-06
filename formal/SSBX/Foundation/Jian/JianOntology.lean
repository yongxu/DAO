/-
Jian ontology layer.

This module records the revised Tier-1 ontology:

  三本: 物 / 動 / 間
  三显: 位 / 場 / 際
  三征: 幾 / 勢 / 機
  闸口: 開 / 閉
  合成: 網 / 體 / 流

The Lean roster keeps simplified canonical atoms where they already exist.
Traditional forms are handled at the glyph layer so orthography does not split
one ontology node into duplicate formal atoms.
-/
import SSBX.Core
import SSBX.Text.Completeness

namespace SSBX.Foundation.Jian.JianOntology

open SSBX.Core.GammaProcess
open SSBX.Roster
open SSBX.Text.Glyph

def rootSurface : OnticRoot -> String
  | .wu => "物"
  | .dong => "動"
  | .jian => "間"

def manifestationSurface : Manifestation -> String
  | .wei => "位"
  | .chang => "場"
  | .ji => "際"

def dynamicSurface : DynamicMark -> String
  | .ji => "幾"
  | .shi => "勢"
  | .jiMoment => "機"

def gateSurface : Gate -> String
  | .open => "開"
  | .closed => "閉"

def compositeSurface : CompositeForm -> String
  | .network => "網"
  | .body => "體"
  | .flow => "流"

theorem wei_is_wu_jian_with_dong_bracketed :
    Manifestation.visibleRoots .wei = [.wu, .jian] ∧
      Manifestation.bracketedRoot .wei = .dong :=
  ⟨rfl, rfl⟩

theorem chang_is_dong_wu_with_jian_bracketed :
    Manifestation.visibleRoots .chang = [.dong, .wu] ∧
      Manifestation.bracketedRoot .chang = .jian :=
  ⟨rfl, rfl⟩

theorem ji_is_jian_dong_with_wu_bracketed :
    Manifestation.visibleRoots .ji = [.jian, .dong] ∧
      Manifestation.bracketedRoot .ji = .wu :=
  ⟨rfl, rfl⟩

theorem every_manifestation_brackets_absent_root (m : Manifestation) :
    Manifestation.bracketedRoot m ∉ Manifestation.visibleRoots m :=
  Manifestation.bracketed_root_not_visible m

theorem wei_has_no_persistent_static_split :
    DynamicMark.staticFaceOf .wei = .noPersistentSplit ∧
      DynamicMark.ofManifestation .wei = .ji :=
  ⟨rfl, rfl⟩

theorem shi_is_ji_along_continuous_medium :
    dynamicSurface .shi = "勢" ∧
      DynamicMark.expansionMode .shi = "ji extended through a continuous medium" :=
  ⟨rfl, rfl⟩

theorem jiMoment_is_ji_along_topological_routing :
    dynamicSurface .jiMoment = "機" ∧
      DynamicMark.expansionMode .jiMoment = "ji gathered through topological routing" :=
  ⟨rfl, rfl⟩

theorem gate_results :
    Gate.result .ji .open = .life ∧
      Gate.result .ji .closed = .extinction ∧
      Gate.result .shi .open = .formation ∧
      Gate.result .shi .closed = .reversal ∧
      Gate.result .jiMoment .open = .turning ∧
      Gate.result .jiMoment .closed = .keeping :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gate_is_only_open_or_closed (g : Gate) :
    g = .open ∨ g = .closed :=
  Gate.gate_binary g

def mutuallyManifest : Manifestation -> Manifestation -> Prop
  | .wei, .ji => True
  | .ji, .wei => True
  | _, _ => False

theorem wei_ji_mutually_manifest :
    mutuallyManifest .wei .ji ∧ mutuallyManifest .ji .wei :=
  ⟨trivial, trivial⟩

theorem mutually_manifest_symmetric {a b : Manifestation} :
    mutuallyManifest a b -> mutuallyManifest b a := by
  cases a <;> cases b <;> simp [mutuallyManifest]

def Composes (a b : Manifestation) (c : CompositeForm) : Prop :=
  CompositeForm.parts c = (a, b) ∨ CompositeForm.parts c = (b, a)

theorem composition_table :
    Composes .wei .ji .network ∧
      Composes .wei .chang .body ∧
      Composes .chang .ji .flow :=
  ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

def Drives (d : DynamicMark) (m : Manifestation) : Prop :=
  DynamicMark.ofManifestation m = d

theorem dynamic_drive_table :
    Drives .ji .wei ∧ Drives .shi .chang ∧ Drives .jiMoment .ji :=
  ⟨rfl, rfl, rfl⟩

theorem feedback_table :
    CompositeForm.feedbackTarget .network = .wei ∧
      CompositeForm.feedbackTarget .body = .chang ∧
      CompositeForm.feedbackTarget .flow = .ji :=
  ⟨rfl, rfl, rfl⟩

structure Assembly where
  composite : CompositeForm
  left : Manifestation
  right : Manifestation
  arrangement : Nat
  parts_match : Composes left right composite

def networkAssembly (arrangement : Nat) : Assembly :=
  { composite := .network
    left := .wei
    right := .ji
    arrangement := arrangement
    parts_match := Or.inl rfl }

/--
Composition is not a reversible collapse back to bare atoms: the same visible
parts can support different arrangements.
-/
theorem network_composition_arrangement_not_unique :
    ∃ a b : Assembly,
      a.composite = .network ∧
        b.composite = .network ∧
        a.left = b.left ∧
        a.right = b.right ∧
        a.arrangement ≠ b.arrangement := by
  refine ⟨networkAssembly 0, networkAssembly 1, rfl, rfl, rfl, rfl, ?_⟩
  decide

structure SelfReferenceWitness where
  relation_structure : OnticRoot
  enacted_process : OnticRoot
  field_manifestation : Manifestation
  produced_position : Manifestation
  connecting_interface : Manifestation
  resulting_network : CompositeForm

def selfReferenceWitness : SelfReferenceWitness :=
  { relation_structure := .jian
    enacted_process := .dong
    field_manifestation := .chang
    produced_position := .wei
    connecting_interface := .ji
    resulting_network := .network }

theorem ontology_is_instance_of_its_own_shape :
    selfReferenceWitness.relation_structure = .jian ∧
      selfReferenceWitness.enacted_process = .dong ∧
      selfReferenceWitness.field_manifestation = .chang ∧
      selfReferenceWitness.produced_position = .wei ∧
      selfReferenceWitness.connecting_interface = .ji ∧
      selfReferenceWitness.resulting_network = .network :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

inductive Tier1Role where
  | root
  | manifestation
  | dynamic
  | gate
  | composite
  deriving DecidableEq, Repr

inductive Tier1Term where
  | «物» | «動» | «間»
  | «位» | «場» | «際»
  | «幾» | «勢» | «機»
  | «開» | «閉»
  | «網» | «體» | «流»
  deriving DecidableEq, Repr

def Tier1Term.role : Tier1Term -> Tier1Role
  | .«物» | .«動» | .«間» => .root
  | .«位» | .«場» | .«際» => .manifestation
  | .«幾» | .«勢» | .«機» => .dynamic
  | .«開» | .«閉» => .gate
  | .«網» | .«體» | .«流» => .composite

def Tier1Term.surface : Tier1Term -> String
  | .«物» => "物" | .«動» => "動" | .«間» => "間"
  | .«位» => "位" | .«場» => "場" | .«際» => "際"
  | .«幾» => "幾" | .«勢» => "勢" | .«機» => "機"
  | .«開» => "開" | .«閉» => "閉"
  | .«網» => "網" | .«體» => "體" | .«流» => "流"

def Tier1Term.sense (t : Tier1Term) : GlyphSense :=
  senseOfGlyph t.surface

def Tier1Term.canonicalAtom? : Tier1Term -> Option AtomName
  | .«物» => some .«物»
  | .«動» => some .«动»
  | .«間» => some .«间»
  | .«位» => some .«位»
  | .«場» => some .«场»
  | .«際» => none
  | .«幾» => some .«几»
  | .«勢» => some .«势»
  | .«機» => some .«机»
  | .«開» => some .«开»
  | .«閉» => some .«闭»
  | .«網» => none
  | .«體» => none
  | .«流» => some .«流»

def allTier1Terms : List Tier1Term :=
  [.«物», .«動», .«間», .«位», .«場», .«際», .«幾», .«勢», .«機»,
   .«開», .«閉», .«網», .«體», .«流»]

theorem tier1_complete (t : Tier1Term) : t ∈ allTier1Terms := by
  cases t <;> decide

theorem tier1_count : allTier1Terms.length = 14 :=
  rfl

theorem tier1_glyphs_registered (t : Tier1Term) :
    RegisteredSense t.sense := by
  cases t <;> native_decide

theorem tier1_canonical_atoms_registered {t : Tier1Term} {a : AtomName}
    (_h : t.canonicalAtom? = some a) :
    (A a) ∈ allSymbols := by
  exact allSymbols_complete (A a)

def glyphOnlyTier1Terms : List Tier1Term :=
  [.«際», .«網», .«體»]

theorem glyph_only_terms_have_no_canonical_atom {t : Tier1Term} :
    t ∈ glyphOnlyTier1Terms -> t.canonicalAtom? = none := by
  cases t <;> decide

end SSBX.Foundation.Jian.JianOntology
