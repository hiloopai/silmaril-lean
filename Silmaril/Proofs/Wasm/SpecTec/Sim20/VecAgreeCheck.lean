module

public import Silmaril.Wasm.SpecTec.Sim20.VecAgree.Defs

/-!
# Where the 2.0 type table mentions the operator families (kernel check)

`tableOkB m`: every type definition of `m` has the shapes `VecAgree.InstsOk` asks for, as a
Boolean check:

* every alias, record-field and variant-case type names no family directly (`ffTB`), except a
  variant case `opOf f` whose payload is exactly `payT f` (`payF?`);
* every variant case has no quantifier, or the single quantifier `exp : exp` (`qsOkB`; it is
  `fNmag`'s `SUBNORM`).

**`tableOkB_fixedX20`** (`decide +kernel`): the type table of `fixedX20` passes.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (tyEvB)

/-- `ffT`, as a check. -/
def ffTB (t : Typ) : Bool := (evTyp t).all (tyEvB fams)

/-- The family whose payload `t` is, if it is one. -/
def payF? : Typ → Option String
  | .tupT [.mk "shape" (.varT "shape" []), .mk "_" (.varT f [.expA (.varE "shape")])] => some f
  | _ => none

/-- No quantifier, or `exp : exp`. -/
def qsOkB : List Param → Bool
  | [] => true
  | [.expP _ (.varT "exp" [])] => true
  | _ => false

/-- A variant case. -/
def caseOkB : TypCase → Bool
  | .mk op t qs _ =>
    (ffTB t || match payF? t with
      | some f => fams.contains f && op == opOf f
      | none => false) && qsOkB qs

/-- A type definition's body. -/
def dOkB : DefTyp → Bool
  | .aliasT t => ffTB t
  | .structT fs => fs.all fun | .mk _ t _ _ => ffTB t
  | .variantT cs => cs.all caseOkB

/-- A type's instances. -/
def instsOkB (is : List Inst) : Bool := is.all fun | .instD _ _ dt => dOkB dt

/-- Every type of a table. -/
def tableOkB (m : Map TypDef) : Bool := m.all fun p => instsOkB p.2.2

set_option maxHeartbeats 8000000 in
/-- **The type table of `fixedX20` mentions the families only as their payloads** (kernel). -/
theorem tableOkB_fixedX20 : tableOkB (typsOfDefs fixedX20) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
