module

import Silmaril.ProofFormats.ACL2.BinaryAppend.Defs
import Silmaril.Logic.ACL2.Consequence.Thms
import Silmaril.Logic.ACL2.OrdinalAdmission.Thms
import Silmaril.Logic.ACL2.Recursive.Institution.Thms
import Silmaril.Logic.ACL2.Standard.Objects.CdrSize
import Mathlib.Data.Fin.VecNotation

namespace Silmaril.ProofFormats.ACL2.BinaryAppend.Tests

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Standard TranslatedSource
open Silmaril.Logic.ACL2.Translated.Recursive (endpName conspName carName cdrName)

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def fixtureText : String := include_str "../../../../corpus/acl2/binary-append/acl2-8.7.sexp"
theorem parsed : (read fixtureText).isSome = true := by decide
def source : Export := (read fixtureText).get parsed

theorem checks : (lower source).isSome = true := by decide
def lowered : Lowered source := (lower source).get checks
def block := source.definition.block lowered.body
def self : block.members.Symbol 2 := ⟨functionName, by decide⟩

theorem sourceLowered :
    Translated.Recursive.lowerBody block.members lowered.checked = some (block.body self) :=
  lowered.lowered

def certificate : Recursive.Certificate := .ite (.apply [.base, .cdr 0]) .base
def blockCertificate : Recursive.BlockCertificate block := fun _ => certificate
def argument : Recursive.MeasureArgument block.members := source.definition.measureArgument lowered.measured

theorem accepted : blockCertificate.Accepted block argument := by
  intro k f
  have hk : 2 = k := source.definition.memberArity f
  subst k
  rfl

def oldModel : Model Signature.empty := ⟨objectPrimitives, fun f => nomatch f.property⟩

def measure : OrdinalAdmission.Measure block oldModel :=
  fun state => .natural (objectCdrSize.rank argument state)

theorem terminates : OrdinalAdmission.Terminates block oldModel measure where
  valid _ := rfl
  decreases state :=
    (blockCertificate.terminates objectCdrSize argument accepted state).mono fun next lt => by
      change (compare (objectCdrSize.rank argument next) (objectCdrSize.rank argument state) ==
        .lt) = true
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

def presented : (presentedInst.I.obj world.presentation).Mod :=
  ⟨terminates.model, fun _ hp => hp terminates.model fun q hq => models q (Or.inl hq)⟩

example : ((presentedInst.I.map extension.presentation).mod.obj presented).obj = oldModel :=
  reduct

def bindUnary (name : Name) (run : Object → Object)
    (rest : Translated.Interpretation source.signature) :
    Translated.Interpretation source.signature :=
  fun {n} f args =>
    if h : n = 1 ∧ f.val = name then run (args ((0 : Fin 1).cast h.1.symm))
    else rest f args

def primitiveCalls : Translated.Interpretation source.signature :=
  bindUnary conspName (fun x => Object.ofBool x.consp)
    (bindUnary carName Object.car (bindUnary cdrName Object.cdr fun _ _ => Object.nil))

def notValue (x : Object) : Object :=
  lowered.not.eval primitiveCalls (fun _ => x)

def atomValue (x : Object) : Object :=
  lowered.atom.eval (bindUnary notName notValue primitiveCalls) (fun _ => x)

def endpValue (x : Object) : Object :=
  lowered.endp.eval (bindUnary atomName atomValue primitiveCalls) (fun _ => x)

/-- The complement law follows from the three checked helper bodies in the fixture. -/
theorem endpEquation (x : Object) : endpValue x = Object.ofBool (!x.consp) := by
  change (if Object.ofBool x.consp = Object.nil then Object.truth else Object.nil) = _
  cases x.consp <;> rfl

def sourceCalls : Translated.Interpretation source.signature :=
  bindUnary endpName endpValue fun {n} f args =>
    if h : n = 2 ∧ f.val = functionName then
      terminates.model.interpret (block.symbol self) (fun i => args (i.cast h.1.symm))
    else primitiveCalls f args

def sourceEval (env : Fin 2 → Object) : Object :=
  lowered.checked.eval (scope := source.definition.formals) sourceCalls env

theorem correspondence (env : Fin 2 → Object) :
    sourceEval env = ((block.body self).toTerm block).eval terminates.model env := by
  change (if endpValue (env 0) = Object.nil then
      (env 0).car.cons (terminates.model.interpret (block.symbol self) _)
    else env 1) =
    (if Object.ofBool (env 0).consp = Object.nil then env 1
    else (env 0).car.cons (terminates.model.interpret (block.symbol self) _))
  rw (config := { transparency := .default }) [endpEquation]
  cases (env 0).consp with
  | false => rfl
  | true =>
    change (env 0).car.cons (terminates.model.interpret (block.symbol self) _) =
      (env 0).car.cons (terminates.model.interpret (block.symbol self) _)
    refine congrArg (fun args : Fin 2 → Object =>
      (env 0).car.cons (terminates.model.interpret (block.symbol self) args)) ?_
    exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)

/-- The admitted function satisfies the exported body for both branches and every input. -/
theorem sourceEquation (env : Fin 2 → Object) :
    terminates.model.interpret (block.symbol self) env = sourceEval env :=
  ((Sentence.holds_eq terminates.model _ _).1 (terminates.equation_holds self) env).trans
    (correspondence env).symm

def nilArgs : Fin 2 → Term block.signature 1 := ![.nil, .var 0]
def nilStatement : Sentence block.signature :=
  .eq (.app (block.symbol self) nilArgs) (.var 0)

def consBranch : Term block.signature 1 :=
  match ((block.body self).toTerm block).subst nilArgs with
  | .ite _ yes _ => yes
  | _ => .nil

-- The theorem book needs a derivation in the existing calculus, even though the model has
-- already been constructed. Substitution, congruence, and the two primitive rules suffice.
theorem nilProof : world.Provable nilStatement := by
  have defining : world.Provable (block.equation self) := .hyp (Or.inl equationMem)
  have unfoldAtNil : world.Provable
      (.eq (.app (block.symbol self) nilArgs) (.ite (.consp .nil) consBranch (.var 0))) :=
    .subst nilArgs defining
  have step := Derives.congr (Γ := world.theory)
    (.ite (.var (0 : Fin 3)) (.var 1) (.var 2))
    ![.consp .nil, consBranch, .var 0] ![.nil, consBranch, .var 0]
    (Fin.forall_fin_succ.2 ⟨.conspNil, Fin.forall_fin_two.2 ⟨.refl _, .refl _⟩⟩)
  exact .trans unfoldAtNil (.trans step (.ifNil _ _))

def theoremName : Name := ⟨"ACL2", "SILMARIL-BINARY-APPEND-OF-NIL"⟩
def bookOutput : World := world.addTheorem theoremName ⟨rfl, rfl⟩ nilStatement nilProof
def theoremBook : Book world bookOutput :=
  .cons (.defthm ⟨rfl, rfl⟩ nilStatement nilProof) (.nil _)

example : World.initial.Extension bookOutput := extension.comp theoremBook.extension

theorem consumer : bookOutput.presentation.Derives ∅ nilStatement := by
  have prior : world.Checked := Recursive.Block.extendWorld_checked
    (W := World.initial) (B := block) (fresh := namesFresh) (World.checked_bare Signature.empty)
  exact (theoremBook.checked prior).pi_derives
    (.hyp (Or.inr ⟨theoremName, rfl⟩))

def accepts (candidate : Export) : Bool :=
  ((lower candidate).map fun result =>
    certificate.check (candidate.definition.measureArgument result.measured)
      result.measured [] result.body).getD false

def wrongMeasure : Export :=
  {source with measure := .call countName (.cons (.var ⟨"ACL2", "Y"⟩) .nil)}

example : (lower wrongMeasure).isSome = true := by decide
example : accepts wrongMeasure = false := by decide

def wrongEndp : Declaration := {source.endp with body := .var ⟨"ACL2", "X"⟩}
example : (lower {source with endp := wrongEndp}).isNone = true := by decide

def wrongCallArity : Export :=
  match source.definition.body with
  | .ite test yes (.call cons (.cons head (.cons (.call recur (.cons cdr _)) .nil))) =>
    let shortCall := Translated.Raw.call recur (.cons cdr .nil)
    {source with definition := {source.definition with
      body := .ite test yes (.call cons (.cons head (.cons shortCall .nil)))}}
  | _ => source

example : (lower wrongCallArity).isNone = true := by decide

#print axioms sourceLowered
#print axioms accepted
#print axioms endpEquation
#print axioms sourceEquation
#print axioms models
#print axioms reduct
#print axioms nilProof
#print axioms consumer

end Silmaril.ProofFormats.ACL2.BinaryAppend.Tests
