module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.VecAgree.Fam

/-!
# The three families and `exp` in `simEnv20X`, and their corrected forms

Kernel lookups (`rfl`) of the declarations `simEnv20X B` finds at `vunop_`, `vbinop_`, `vrelop_`
and `exp`, and the shapes of the original and corrected family declarations: each original has
two instances, the second (float) one with the nullary cases `nullCases (fNames f)`, and
`VecFix.fixFamily` prepends `floatInst "F32"` and `floatInst "F64"` with those cases.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.VecFix (floatInst vunopFix20 vbinopFix20 vrelopFix20)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d119 Original.d120 Original.d122)

/-- The parameters and instances of a type declaration. -/
def typDecl : Def → TypDef
  | .typD _ ps is => (ps, is)
  | _ => ([], [])

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_vunopX : (simEnv20X B).findTyp? "vunop_" = some (typDecl Original.d119) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_vbinopX : (simEnv20X B).findTyp? "vbinop_" = some (typDecl Original.d120) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_vrelopX : (simEnv20X B).findTyp? "vrelop_" = some (typDecl Original.d122) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_expX :
    (simEnv20X B).findTyp? "exp" = some ([], [.instD [] [] (.aliasT (.numT .intT))]) := rfl

/-- The shape of a family declaration and of its correction. -/
def FamForm (d d' : Def) (f : String) : Prop :=
  ∃ ps ji bs pats, typDecl d = (ps, [ji, .instD bs pats (.variantT (nullCases (fNames f)))]) ∧
    typDecl d' = (ps, [floatInst "F32" (nullCases (fNames f)),
      floatInst "F64" (nullCases (fNames f)), ji, .instD bs pats (.variantT (nullCases (fNames f)))])

theorem famForm_vunop : FamForm Original.d119 vunopFix20 "vunop_" := ⟨_, _, _, _, rfl, rfl⟩

theorem famForm_vbinop : FamForm Original.d120 vbinopFix20 "vbinop_" := ⟨_, _, _, _, rfl, rfl⟩

theorem famForm_vrelop : FamForm Original.d122 vrelopFix20 "vrelop_" := ⟨_, _, _, _, rfl, rfl⟩

theorem vunopFix20_eq :
    vunopFix20 = .typD "vunop_" (typDecl vunopFix20).1 (typDecl vunopFix20).2 := rfl

theorem vbinopFix20_eq :
    vbinopFix20 = .typD "vbinop_" (typDecl vbinopFix20).1 (typDecl vbinopFix20).2 := rfl

theorem vrelopFix20_eq :
    vrelopFix20 = .typD "vrelop_" (typDecl vrelopFix20).1 (typDecl vrelopFix20).2 := rfl

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
