module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Script.Defs

/-!
# Round 8, REH route 2: derivations go to the erased side without a swap set

Round 7's `Round7.EraseDer.dderivesB_fwd` moves a `Round6.Reading.DDerivesB` derivation of a
checked relation (`EraseAll.grE`: every relation `Step` reaches except `Step` and `Step_read`)
across export erasure, but only for derivations whose rule instances bind their quantifiers in a
swap set (`DDerivesBQ (AllIn Q)`), and with `TypFwd Q`, both of which need `QInj`. This topic
states the transfer for every derivation.

* `iterRels`: every iterated premise of a rule of a `grE` relation iterates over a list (`^*`).
  In the fixed script there are eight such premises, in five rules of the typing relations
  (`Resulttype_ok`, `Comptype_ok/struct`, `Subtype_ok2`, `Comptype_sub/struct`,
  `Resulttype_sub`); the kernel checks the shape (`Round8.NxDer.iterRels_fixed`).
* `DerFwdN B O₁ O'`: every `DDerivesB` derivation of a `grE` relation, read with `otherwise` through
  `O₁`, gives one of the erased value from the erased arguments, read through `O'`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7

/-- An iterated premise iterates over a list, at every depth. -/
def listIter : Prem → Bool
  | .iterPr pr (.mk .list _) => listIter pr
  | .iterPr _ _ => false
  | _ => true

/-- **Every iterated premise of a rule of a `grE` relation iterates over a list.** -/
def iterRels (m : Map RelDef) : Bool :=
  m.all fun p => !EraseAll.grE p.1 || p.2.2.2.2.all fun r => match r with
    | .ruleD _ _ _ _ prems => prems.all listIter

/-- **Derivations of `grE` relations go to the erased side**, with `otherwise` read through `O₁`
on the original side and `O'` on the erased side. No swap set. -/
def DerFwdN (env : Env) (O₁ O' : ElseI) : Prop :=
  ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, EraseAll.grE x = true →
    Round6.Reading.DDerivesB env O₁ x op args v →
    Round6.Reading.DDerivesB env O' x op (args.map Swap.eraseA) (Swap.eraseV v)

end Silmaril.Wasm.SpecTec.Sim.Round8.NxDer
