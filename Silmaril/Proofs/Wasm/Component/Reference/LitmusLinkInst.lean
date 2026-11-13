module

public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkConds
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkIR
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusSoundI
public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkCore

/-!
# The instantiation of the litmus `dblFwdL` without `CoreFactsL`

`dblS_inst` (the doubler is wired as `Simple.toRef` assumes) and `fwdS_noSeg` (the importer
module has no data or element segments) are the remaining conditions of `instBehavioursL_inst`
for `dblFwdL`; `dblFwdL_instBehaviours` applies it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Proofs.Wasm.Component.Reference.Litmus

theorem dblS_inst : dblS.Inst := ⟨⟨dblInst, dbl_isInst⟩, by decide⟩

theorem fwdS_noSeg : fwdS.mod.mod.data = [] ∧ fwdS.mod.mod.elems = [] := ⟨rfl, rfl⟩

section

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store)

/-- **The instantiation of `dblFwdL.toRef`**: `instBehavioursL_inst` with every condition
discharged. -/
theorem dblFwdL_instBehaviours {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type} :
    ∃ (Ie : Silmaril.Wasm.Game.ScalarInstance) (cse : (core3P Pf).Store (CanonHost (core3P Pf)))
      (cie : (core3P Pf).Inst), CoreFacts dblFwdL.exp Ie cse cie ∧
      ∀ (Ii : Silmaril.Wasm.Game.ScalarInstance), dblFwdL.imp.mod.IsInst Ii →
      ∃ r : Store (CanonHost (core3P Pf) × Nat), Store.mapH Prod.snd r = Ii.store ∧
        HostsSat (fun h => ∃ (k : Nat) (hk : k < dblFwdL.imp.imports.length),
          h = (.lowered (dblFwdL.wireFid k) (witFt dblFwdL.imp.imports[k].2) {} ⟨2⟩, k)) r ∧
        ∀ (prof : ProfileKind) (h : Host (core3P Pf) σ) (h₀ : σ),
        ∀ res ∈ instBehaviours prof h (initConfig h₀) dblFwdL.toRef [],
          res = .instance (afterLink Pf (reloc cse (Store.mapH Prod.fst r))
            (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) dblFwdL h₀) ⟨0⟩
            (exportMapL dblFwdL) :=
  instBehavioursL_inst dblS_good dblS_inst fwdS_good fwdS_inst fwdS_arity fwdS_noSeg
    dblFwdL_wireTy dblFwdL_namesOk

end

end Silmaril.Proofs.Wasm.Component.Reference
