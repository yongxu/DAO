/-
`理` as the full code-level proof system.

Here `IsLi` does not mean the local glyph `理`; it means the expression has
passed the formal system: registered atoms, single-root discipline, numbered
sense syntax, construction to the theory node, and ledger/model-grounded truth.
-/
import SSBX.Foundation.Core.Monism
import SSBX.Foundation.Core.MonadRoot
import SSBX.Model.Adequacy
import SSBX.Text.SenseSyntax

namespace SSBX.Foundation.Core.Li

open SSBX.Roster
open SSBX.Truth
open SSBX.Truth.Absolute
open SSBX.Model.Adequacy
open SSBX.Foundation.Core.Monism
open SSBX.Foundation.Core.MonadRoot
open SSBX.Text.Glyph
open SSBX.Text.SenseSyntax

structure RootExpression where
  surface : String
  atoms : List AtomName
  forms : List GlyphSense
  target : Symbol
  construction_chain : List ConstructionId
  deriving Repr

def rootToSsbxAtoms : List AtomName :=
  [.«一», .«元», .«生», .«场», .«场», .«有», .«间», .«间», .«成»,
   .«元», .«元», .«显», .«机», .«机», .«开», .«受», .«审», .«审»,
   .«成», .«真», .«真», .«成», .«道», .«道», .«行», .«护», .«共»,
   .«开», .«故», .«生», .«生», .«不», .«息»]

def rootToSsbxConstructionChain : List ConstructionId :=
  [.gammaFieldRoot, .jianRoot, .aspectTriad, .yuanTriad, .systemDynamics,
   .openCloseCore, .auditCore, .valueCore, .actionCore, .truthCore,
   .ssbxTheory]

def rootToSsbxExpression : RootExpression :=
  { surface := "一元生场，场有间，间成元，元显机，机开受审，审成真，真成道，道行护共开，故生生不息。"
    atoms := rootToSsbxAtoms
    forms := shengshengBuxiForms
    target := G .«生生不息»
    construction_chain := rootToSsbxConstructionChain }

def codeUniversalProvePrinciple : UniversalProvePrinciple where
  proves := fun id => id ∈ allConstructionIds
  proves_root := construction_ledger_complete .gammaFieldRoot
  proves_step := fun id _ => construction_ledger_complete id

theorem root_expression_atoms_registered {a : AtomName}
    (_h : a ∈ rootToSsbxExpression.atoms) :
    (A a) ∈ allSymbols :=
  allSymbols_complete (A a)

theorem root_expression_atoms_rooted {a : AtomName}
    (_h : a ∈ rootToSsbxExpression.atoms) :
    Reachable «一元» (MonadNode.atom a) :=
  all_atoms_reachable_from_root a

theorem root_expression_target_rooted :
    Reachable «一元» «生生不息论» :=
  ssbx_reachable_from_root

theorem root_expression_constructs_ssbx :
    ContentConstructsSSBX codeUniversalProvePrinciple :=
  ssbx_constructed_from_content codeUniversalProvePrinciple

theorem root_expression_target_consistent :
    rootToSsbxExpression.target = G .«生生不息» :=
  rfl

theorem root_expression_sense_syntax_valid :
    ValidSenseSyntax rootToSsbxExpression.forms :=
  shengsheng_buxi_sense_syntax_valid

structure LiCertificate (e : RootExpression) where
  atoms_registered : ∀ a, a ∈ e.atoms -> (A a) ∈ allSymbols
  atoms_rooted : ∀ a, a ∈ e.atoms -> Reachable «一元» (MonadNode.atom a)
  target_is_shengsheng_buxi : e.target = G .«生生不息»
  target_rooted : Reachable «一元» «生生不息论»
  roots_exact :
    rootsOfGenerated .«生生不息» = [A .«生», A .«生», A .«不», A .«息»]
  sense_formula_exact :
    senseFormulaOfGenerated .«生生不息» = "生2 生3 不1 息1"
  sense_syntax_valid : ValidSenseSyntax e.forms
  sheng_polysemy :
    RegisteredSense «生1» ∧ RegisteredSense «生2» ∧ RegisteredSense «生3» ∧
      «生1» ≠ «生2» ∧ «生2» ≠ «生3»
  constructs_theory : ContentConstructsSSBX codeUniversalProvePrinciple
  absolute_truth : AbsoluteTruth SSBXTheory

def IsLi (e : RootExpression) : Prop :=
  Nonempty (LiCertificate e)

def liCertificateFromTruth (H : AbsoluteTruth SSBXTheory) :
    LiCertificate rootToSsbxExpression :=
  { atoms_registered := by
      intro a h
      exact root_expression_atoms_registered h
    atoms_rooted := by
      intro a h
      exact root_expression_atoms_rooted h
    target_is_shengsheng_buxi := root_expression_target_consistent
    target_rooted := root_expression_target_rooted
    roots_exact := shengsheng_buxi_roots_exact
    sense_formula_exact := shengsheng_buxi_sense_formula_exact
    sense_syntax_valid := root_expression_sense_syntax_valid
    sheng_polysemy := sheng_polysemy_available
    constructs_theory := root_expression_constructs_ssbx
    absolute_truth := H }

theorem shengsheng_buxi_is_li_from_ledger (L : SSBXAxiomLedger) :
    IsLi rootToSsbxExpression :=
  ⟨liCertificateFromTruth (truth_depends_on_ledger L)⟩

theorem shengsheng_buxi_is_li_from_model
    (A : AdequateModel) (L : SSBXAxiomLedger) (S : ModelSupportsLedger A L) :
    IsLi rootToSsbxExpression :=
  ⟨liCertificateFromTruth (adequate_model_implies_ledger_truth A L S)⟩

end SSBX.Foundation.Core.Li
