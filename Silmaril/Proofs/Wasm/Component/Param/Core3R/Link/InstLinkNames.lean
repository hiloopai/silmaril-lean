module

public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkNames
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstNest
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.InstLinkNames` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.InstLinkNames` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)

/-! ## Return values of programs -/

variable {E : CoreEngine} {σ : Type}

/-! ## Export maps of functions and generated type names -/

variable [∀ a b, Decidable (E.ExternSub a b)] {R : Recurse E σ} {inst : InstId}
  {outer : List (Frame E)} {args : Exports E}

/-! ## The definitions of the translations -/

section Syntax

variable {M : Type}


end Syntax

/-! ## The nested instantiations, with their export maps -/

section Nested

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type}

/-- **The function export `j` of an export map of functions and generated type names is found
by name**, when the function exports are `fb + i` for the export `i` of `xs`, the names of `xs`
are distinct and not generated. -/
theorem lookup_funcExportL {es : Exports (core3R Pf V IR)} (h : TagOrFunc es) {xs : List SimpleExport}
    {fb : Nat} (hx : funcExports es = xs.mapIdx fun i x => (x.name, ⟨fb + i⟩))
    (hnd : (xs.map (·.name)).Nodup) (j : Nat) (hj : j < xs.length)
    (hn : ∀ k, xs[j].name ≠ tag "t" k) :
    lookupExport? es xs[j].name = some (.func ⟨fb + j⟩) := by
  rw [lookup_of_tagOrFunc h hn, hx]
  have e := lookup_mapIdx_val (·.name) (fun i => (⟨i⟩ : FuncId)) fb xs j hj hnd
  rw [e]
  rfl

/-- **The nested instantiation of an import-free simple component** (`instantiateCall_simple`),
with an export map of functions and generated type names. -/
theorem instantiateCall_simple' {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (hF : CoreFacts c I cs ci) (outer : List (Frame (core3R Pf V IR)))
    (cfg : Machine.Config (core3R Pf V IR) σ)
    (hcore : cfg.store.core = (core3R Pf V IR).empty _) (hfuncs : cfg.store.funcs = []) :
    ∃ es, funcExports es = exportMap c ∧ TagOrFunc es ∧
      TRuns (instantiateCallProg ⟨c.toRef, outer⟩ [] : P (core3R Pf V IR) σ (Ret (core3R Pf V IR))) cfg
        (.items es)
        (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := by
  obtain ⟨sc', hr, hx, -⟩ := toRefDefs_run (R := callRecurse)
    (inst := nextInst cfg.store) (outer := outer)
    (args := []) hF { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store }
    hcore hfuncs
  have hmap : funcExports sc'.exports = exportMap c := by
    rw [hx, exportMap]
    simp only [Nat.zero_add]
  have ht : TagOrFunc sc'.exports :=
    SRuns.rets (Q := fun sc : Scope (core3R Pf V IR) => TagOrFunc sc.exports) hr (foldlM_rets (E := core3R Pf V IR) (R := callRecurse) (inst := nextInst cfg.store) (outer := outer)
      (args := []) c.toRef {} (expName_toRef c) TagOrFunc.nil)
  refine ⟨sc'.exports, hmap, ht, ?_⟩
  unfold instantiateCallProg instantiateClosure instantiateComponent
  refine TRuns.bind (f := fun es => Pure.pure (Ret.items es)) ?_ (TRuns.pure _ _)
  have hr' : TRuns (List.foldlM (instantiateDef callRecurse (nextInst cfg.store) outer []) {}
      c.toRef) { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } sc'
      (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := hr
  exact (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind
    (TRuns.bind (a := sc') (b := sc'.exports) hr' (TRuns.pure _ _))

/-- **The nested instantiation of a simple component with imports over a shared store**
(`instantiateCall_simpleI`), with an export map of functions and generated type names. -/
theorem instantiateCall_simpleI' {c : SimpleI} (hc : c.Good) (har : c.Arity)
    {cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {fid : Nat → FuncId} {addr : Nat → Nat}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (outer : List (Frame (core3R Pf V IR))) (vs : Exports (core3R Pf V IR))
    (cfg : Machine.Config (core3R Pf V IR) σ) {fb : Nat}
    (hF : CoreFactsL c cs₀ (nextInst cfg.store) fid addr cs ci)
    (hcore : cfg.store.core = cs₀) (hfb : cfg.store.funcs.length = fb)
    (hb : ImportsBound c vs fid cfg.store) :
    ∃ es, funcExports es = c.exports.mapIdx (fun i x => (x.name, ⟨fb + i⟩)) ∧ TagOrFunc es ∧
      TRuns (instantiateCallProg ⟨c.toRef, outer⟩ vs : P (core3R Pf V IR) σ (Ret (core3R Pf V IR))) cfg
        (.items es)
        { cfg with store := nestStoreI cs cfg.store addr (nextInst cfg.store) c } := by
  obtain ⟨sc', hr, hx⟩ := toRefDefsL_run (R := callRecurse) (inst := nextInst cfg.store)
    (outer := outer) (args := vs) hc har hF
    { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } hcore hfb hb
  have ht : TagOrFunc sc'.exports :=
    SRuns.rets (Q := fun sc : Scope (core3R Pf V IR) => TagOrFunc sc.exports) hr (foldlM_rets (E := core3R Pf V IR) (R := callRecurse) (inst := nextInst cfg.store) (outer := outer)
      (args := vs) c.toRef {} (expName_toRefI c) TagOrFunc.nil)
  refine ⟨sc'.exports, hx, ht, ?_⟩
  unfold instantiateCallProg instantiateClosure instantiateComponent
  refine TRuns.bind (f := fun es => Pure.pure (Ret.items es)) ?_ (TRuns.pure _ _)
  exact (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind
    (TRuns.bind (a := sc') (b := sc'.exports) hr (TRuns.pure _ _))

end Nested

end Silmaril.Proofs.Wasm.Component.Param.Core3R
