module

import Silmaril.ProofFormats.ACL2.TrueListp.Defs
import Silmaril.Logic.ACL2.Consequence.Thms
import Silmaril.Logic.ACL2.OrdinalAdmission.Thms
import Silmaril.Logic.ACL2.Recursive.Institution.Thms
import Silmaril.Logic.ACL2.Standard.Objects.CdrSize

namespace Silmaril.ProofFormats.ACL2.TrueListp.Tests

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Standard TranslatedSource

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def fixtureText : String := include_str "../../../../corpus/acl2/true-listp/acl2-8.7.sexp"

theorem parsed : (read fixtureText).isSome = true := by decide

def source : Export := (read fixtureText).get parsed

theorem checks : (lower source).isSome = true := by decide

def lowered : Lowered source := (lower source).get checks
def block := lowered.block
def self : block.members.Symbol 1 := ⟨functionName, by decide⟩

example : source.definition.formals = [⟨"ACL2", "X"⟩] := by decide
example : source.equality.formals = [⟨"ACL2", "X"⟩, ⟨"ACL2", "Y"⟩] := by decide

theorem sourceLowered :
    Translated.Recursive.lowerBody block.members lowered.checked = some (block.body self) :=
  lowered.lowered

def certificate : Recursive.Certificate := .ite (.cdr 0) .base

def blockCertificate : Recursive.BlockCertificate block := fun _ => certificate

theorem accepted : blockCertificate.Accepted block lowered.measureArgument := by
  intro k f
  have hk : 1 = k := source.memberArity f
  subst k
  rfl

def oldModel : Model Signature.empty := ⟨objectPrimitives, fun f => nomatch f.property⟩

def measure : OrdinalAdmission.Measure block oldModel :=
  fun state => .natural (objectCdrSize.rank lowered.measureArgument state)

theorem terminates : OrdinalAdmission.Terminates block oldModel measure where
  valid _ := rfl
  decreases state :=
    (blockCertificate.terminates objectCdrSize lowered.measureArgument accepted state).mono
      fun next lt => by
        change (compare (objectCdrSize.rank lowered.measureArgument next)
          (objectCdrSize.rank lowered.measureArgument state) == .lt) = true
        exact beq_iff_eq.mpr (Nat.compare_eq_lt.mpr lt)

theorem namesFresh : block.TheoremNamesFresh World.initial := fun _ => rfl

def world : World := block.extendWorld World.initial namesFresh
def extension : World.initial.Extension world := block.worldExtension World.initial namesFresh

theorem models : world.Models terminates.model :=
  block.modelBy_models (fresh := namesFresh) terminates.wellFounded terminates.decreases
    (World.valid_bare _ _ fun _ ⟨_, _, _, body, _⟩ => nomatch body)

theorem reduct : (inst.I.map block.inclusion).mod.obj terminates.model = oldModel :=
  terminates.model_reduct

theorem equationMem : block.equation self ∈ world.presentation.equations :=
  block.equation_mem (P := World.initial.presentation) self

theorem derives : world.presentation.Derives ∅ (block.equation self) :=
  .hyp (Or.inl equationMem)

example : Consequence.presentationEntails world.presentation [] (block.equation self) :=
  Consequence.presentationSound world.presentation [] _ (.hyp (Or.inl equationMem))

def presented : (presentedInst.I.obj world.presentation).Mod :=
  ⟨terminates.model, fun _ hp => hp terminates.model fun q hq => models q (Or.inl hq)⟩

example : ((presentedInst.I.map extension.presentation).mod.obj presented).obj = oldModel :=
  reduct

example : (forgetDefinitions.η.app world.presentation).mod.obj presented = terminates.model := rfl

/-- Interpret the names used by the checked source. EQ runs its separately exported
logical body. The self-call reads the interpretation established by admission. -/
def sourceCalls : Translated.Interpretation source.signature :=
  fun {n} f args =>
    if unary : n = 1 then
      let x := args ((0 : Fin 1).cast unary.symm)
      if f.val = Translated.Recursive.conspName then Object.ofBool x.consp
      else if f.val = Translated.Recursive.cdrName then x.cdr
      else if f.val = functionName then
        terminates.model.interpret (block.symbol self) (fun i => args (i.cast unary.symm))
      else Object.nil
    else if binary : n = 2 ∧ f.val = Translated.Recursive.eqName then
      let empty : Translated.Interpretation Signature.empty := fun f => nomatch f.property
      lowered.equality.eval (scope := source.equality.formals) empty
        (fun i => args (i.cast binary.1.symm))
    else Object.nil

def sourceEval (env : Fin 1 → Object) : Object :=
  lowered.checked.eval (scope := source.definition.formals) sourceCalls env

theorem correspondence (env : Fin 1 → Object) :
    sourceEval env = ((block.body self).toTerm block).eval terminates.model env := by
  refine congrArg (fun args : Fin 1 → Object =>
    if Object.ofBool (env 0).consp = Object.nil then (env 0).equal Object.nil
    else terminates.model.interpret (block.symbol self) args) ?_
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

/-- The admitted function satisfies the checked translated source equation for all inputs. -/
theorem sourceEquation (env : Fin 1 → Object) :
    terminates.model.interpret (block.symbol self) env = sourceEval env :=
  ((Sentence.holds_eq terminates.model _ _).1 (terminates.equation_holds self) env).trans
    (correspondence env).symm

def accepts (observation : Export) : Bool :=
  ((lower observation).map fun result =>
    certificate.check result.measureArgument result.measured [] result.body).getD false

def actual (term : Translated.Raw) : Translated.RawArgs := .cons term .nil
def x : Translated.Raw := .var ⟨"ACL2", "X"⟩

def editBranch (edit : Translated.Raw → Name → Translated.RawArgs →
    Translated.Raw → Translated.Raw) : Export :=
  match source.definition.body with
  | .ite test (.call name args) no =>
      {source with definition := {source.definition with body := edit test name args no}}
  | _ => source

def noCdr : Export :=
  editBranch fun test name _ no => .ite test (.call name (actual x)) no

-- Removing CDR still gives a typed body. The certificate checks the actual recursive argument.
example : (lower noCdr).isSome = true := by decide
example : accepts noCdr = false := by decide
example : accepts (editBranch fun _ name args no =>
    .ite (.call Translated.Recursive.cdrName (actual x)) (.call name args) no) = false := by decide
example : accepts {source with measure := .call countName (actual (.var ⟨"OTHER", "X"⟩))} =
    false := by decide
example : accepts {source with relation := ⟨"ACL2", "O<="⟩} = false := by decide
example : accepts {source with definition := {source.definition with arity := 2}} =
    false := by decide
example : accepts (editBranch fun test name _ no =>
    .ite test (.call name (actual (.call Translated.Recursive.cdrName
      (actual (.var ⟨"OTHER", "X"⟩))))) no) = false := by decide
example : accepts (editBranch fun test name args no =>
    .ite test (.call {name with package := "OTHER"} args) no) = false := by decide
example : accepts (editBranch fun test name _ no => .ite test (.call name .nil) no) =
    false := by decide
def damagedEquality : Declaration :=
  {source.equality with body := .call Translated.Primitive.equal.name (.cons x (actual x))}

example : accepts {source with equality := damagedEquality} = false := by decide
example : readName (.atom (.symbol "X")) = none := by decide

#print axioms checks
#print axioms sourceLowered
#print axioms accepted
#print axioms terminates
#print axioms models
#print axioms reduct
#print axioms derives
#print axioms correspondence
#print axioms sourceEquation

end Silmaril.ProofFormats.ACL2.TrueListp.Tests
