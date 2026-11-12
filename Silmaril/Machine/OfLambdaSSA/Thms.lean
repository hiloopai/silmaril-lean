module

public import Silmaril.Machine.OfLambdaSSA.Defs
import Silmaril.Proofs.Machine.OfLambdaSSA.Main
import Silmaril.Proofs.Machine.OfLambdaSSA.Counterexamples

/-!
# `ofLambdaSSA` is correct on the RTL fragment

The Raw RTL development proves that `toLambdaSSA` (SSA-form RTL to lambda-SSA) preserves
finite outcomes exactly (`toLambdaSSA_eval_iff`), but for `ofLambdaSSA`
(lambda-SSA to SSA-form RTL) it proves only the case of a region that traps at
once (`ofLambdaSSA_eval_iff_trap`). This file states the general theorem.

The general theorem needs the region to be in the fragment (`RootFits`): as
the Raw development states it, for every region that compiles, it is false, and
`pairExample_differs` is a counterexample. A second one, a loop through the root
wrapper whose exit reads the function's argument, was fixed in the
Raw compiler, which now refuses to compile it (`aliasRegion_not_compiles`). Two
further hypotheses are those of `toLambdaSSA_eval_iff`: the call oracle returns
as many words as the callee's signature declares (`MatchesSigs`), and the
frame holds the function's argument in its parameter registers.
-/

@[expose] public section

namespace Silmaril.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

variable {sigs : List RTL.Signature} {oracle : CallOracle}

/-- **Finite outcomes agree exactly.** For a region of the fragment that
compiles, the region reaches external label `0` with the packed returned values
exactly when the compiled function returns them, and label `1` with `unit`
exactly when it traps, with the same final memory. -/
theorem ofLambdaSSA_eval_iff (hsigs : CallOracle.MatchesSigs oracle sigs)
    {r : Region (Opcode sigs)} {a : Ann} {params results : ℕ}
    (hc : Compiles sigs r a params results) (hfit : RootFits sigs r a params results)
    {fr : Frame ℕ} {args : List Word} (hfr : fr.readAll (freshRegs 0 params) = some args)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m m' : Memory} {label : ℕ}
    {value : Value Word} :
    Semantics.Region.Eval (Opcode.step oracle) env r m label value m' ↔
      (label = 0 ∧ ∃ vs, value = packValues vs ∧
          Func.Exec oracle (ofLambdaSSA sigs r a params results) 0 fr m (.returned vs m')) ∨
      (label = 1 ∧ value = .unit ∧
          Func.Exec oracle (ofLambdaSSA sigs r a params results) 0 fr m (.trapped m')) :=
  Silmaril.Proofs.Machine.OfLambdaSSA.ofLambdaSSA_eval_iff hsigs hc hfit hfr henv

/-! ## Without the fragment, the theorem fails -/

/-- `pairExample` compiles, and the function returns `[7]`, but the region does not evaluate
to `packValues [7]`. -/
theorem pairExample_differs (m : Memory) :
    Compiles [] pairExample .br 1 1 ∧
      (Frame.empty.set 0 7 : Frame ℕ).readAll (freshRegs 0 1) = some [7] ∧
      Func.Exec noCalls (ofLambdaSSA [] pairExample .br 1 1) 0
        (Frame.empty.set 0 7) m (.returned [7] m) ∧
      ¬ Semantics.Region.Eval (Opcode.step noCalls)
        (fun _ => packValues [7]) pairExample m 0 (packValues [7]) m :=
  ⟨Proofs.Machine.OfLambdaSSA.pairExample_compiles,
    Proofs.Machine.OfLambdaSSA.pairExample_differs m⟩

/-- A loop through the root wrapper whose exit reads the function's argument is
refused. Before that fix it compiled to a function returning what the back
edge wrote into the argument's register. -/
theorem aliasRegion_not_compiles : ¬ Compiles [] aliasRegion SSA.aliasAnn 1 1 :=
  Silmaril.Machine.RTL.SSA.aliasRegion_not_compiles

/-- The counterexample is not in the fragment. -/
theorem pairExample_not_fits : ¬ RootFits [] pairExample .br 1 1 :=
  Proofs.Machine.OfLambdaSSA.pairExample_not_fits

/-- The loop returning its block's parameter compiles and is in the fragment, so
the theorem covers loops through the root wrapper. -/
theorem loopExample_fits :
    Compiles [] loopExample SSA.aliasAnn 1 1 ∧ RootFits [] loopExample SSA.aliasAnn 1 1 :=
  ⟨Proofs.Machine.OfLambdaSSA.loopExample_compiles, Proofs.Machine.OfLambdaSSA.loopExample_fits⟩

end Silmaril.Machine.OfLambdaSSA
