module

public import Silmaril.Wasm.Component.Reference.StartI.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.StartBase
public import Silmaril.Proofs.Wasm.Component.Reference.InstImpPhase

/-!
# Components with imports and a start function: the module without its start function

* `ImpModule.IsInstS.noStart`: an instance before the start function of `m` is an instance
  (`ImpModule.IsInst`) of `m.noStart`; `SimpleI.InstS.noStart`: `c.noStart` is wired as
  `SimpleI.toRef` assumes (`SimpleI.Inst`). The call-phase and IR lemmas stated for
  `SimpleI.Inst`/`ImpModule.IsInst` are used through them.
* `CoreFactsIS`, `coreFactsIS`: the core instantiation of the module in the trampoline store
  returns the start address, as `coreFactsI` does without a start function.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **An instance before the start function is an instance of the module without it.** -/
theorem _root_.Silmaril.Wasm.Component.Reference.ImpModule.IsInstS.noStart {m : ImpModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} {start : Option Nat} (h : m.IsInstS I start) :
    m.noStart.IsInst I :=
  ⟨⟨h.1.choose, isInstance_noStart h.1.choose_spec⟩, h.2.1, h.2.2⟩

/-- Without a start function, an instance before the start function is an instance. -/
theorem _root_.Silmaril.Wasm.Component.Reference.ImpModule.IsInstS.isInst_none {m : ImpModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} (h : m.IsInstS I none) : m.IsInst I :=
  ⟨⟨h.1.choose, Silmaril.Wasm.Game.isInstanceStart_none_iff.1 h.1.choose_spec⟩, h.2.1, h.2.2⟩

/-- The instance store before the start function is well formed. -/
theorem _root_.Silmaril.Wasm.Component.Reference.ImpModule.IsInstS.ok {m : ImpModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} {start : Option Nat} (h : m.IsInstS I start) :
    I.WellFormed I.store :=
  h.1.choose_spec.ok.1

/-- The start function has the type `[] → []`. -/
theorem _root_.Silmaril.Wasm.Component.Reference.ImpModule.IsInstS.startTyped {m : ImpModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} {start : Option Nat} (h : m.IsInstS I start) :
    ∀ a ∈ start, Silmaril.Wasm.Game.StartTyped I.store a :=
  h.1.choose_spec.ok.2

/-- **`c.noStart` is wired as `SimpleI.toRef` assumes.** -/
theorem _root_.Silmaril.Wasm.Component.Reference.SimpleI.InstS.noStart {c : SimpleI}
    (hi : c.InstS) : c.noStart.Inst where
  inst := let ⟨I, _, h⟩ := hi.inst; ⟨I, h.noStart⟩
  names := hi.names
  importNames := hi.importNames
  env := hi.env
  importTypes := let ⟨mt, hv, h⟩ := hi.importTypes; ⟨mt, validate?_noStart hv, h⟩

/-- Without a start function, `SimpleI.InstS` is `SimpleI.Inst`. -/
theorem _root_.Silmaril.Wasm.Component.Reference.SimpleI.InstS.inst_none {c : SimpleI}
    (hi : c.InstS) {I : Silmaril.Wasm.Game.ScalarInstance} (h : c.mod.IsInstS I none) : c.Inst :=
  ⟨⟨I, h.isInst_none⟩, hi.names, hi.importNames, hi.env, hi.importTypes⟩

theorem noStart_good {c : SimpleI} (hc : c.Good) : c.noStart.Good :=
  ⟨hc.names, hc.core, hc.imports⟩

/-! ## The core facts with a start function -/

section Facts

open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Instantiate

variable {Pf : Profile}

theorem importTypesE_noStart {m : Module} {mt : Validation.CModuleType}
    (h : Validation.validate? m = some mt) :
    Core3.importTypesE { m with start := none } = Core3.importTypesE m := by
  have h₀ := validate?_noStart h
  unfold Core3.importTypesE
  split
  · rename_i mt₀ h₀'
    split
    · rename_i mt₁ h₁
      obtain rfl : mt₀ = mt := Option.some.inj (h₀'.symm.trans h₀)
      obtain rfl : mt₁ = mt₀ := Option.some.inj (h₁.symm.trans h)
      rfl
    · rename_i h₁
      rw [h] at h₁
      cases h₁
  · rename_i h₀'
    rw [h₀] at h₀'
    cases h₀'

theorem coreImportsFor_noStart {m : Module} {mt : Validation.CModuleType}
    (h : Validation.validate? m = some mt) (s : (core3P Pf).Store (CanonHost (core3P Pf)))
    (args : List (String × Nat)) (fr : Frame (core3P Pf)) :
    coreImportsFor? s ({ m with start := none } : Module) args fr = coreImportsFor? s m args fr := by
  unfold coreImportsFor?
  show (Core3.importTypesE _).mapM _ = (Core3.importTypesE _).mapM _
  rw [importTypesE_noStart h]

/-- The core facts of a `SimpleI.InstS` component with the start function at `st`, over
`core3P Pf` (as `CoreFactsI`). -/
structure CoreFactsIS (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P Pf).Store (CanonHost (core3P Pf))) (ci : (core3P Pf).Inst) (st : Option Nat) :
    Prop where
  isInst : c.mod.IsInstS I st
  store : Store.mapH trampIdx cs = I.store
  tramp : c.TrampOk cs
  prepare : (core3P Pf).prepare? (trampStore Pf c.imports) c.mod.mod
    ((List.range c.imports.length).map ExternAddr.func) = some (cs, ci, st)
  imports : ∀ f : Frame (core3P Pf), f.coreInstance? 0 = some (envExports c.mod.imports) →
    coreImportsFor? (trampStore Pf c.imports) c.mod.mod [("env", 0)] f =
      some ((List.range c.imports.length).map ExternAddr.func)
  lookup : ∀ x ∈ c.exports, lookupExport? ((core3P Pf).exports ci) (coreNameI c x) =
    some (.func (I.addrs.getD x.core 0))

/-- **The core facts hold** for a `SimpleI.InstS` component in the fragment. -/
theorem coreFactsIS {c : SimpleI} (hc : c.Good) (hi : c.InstS) :
    ∃ I st cs ci, CoreFactsIS (Pf := Pf) c I cs ci st := by
  obtain ⟨I, st, hI⟩ := hi.inst
  have hi₀ := hi.noStart
  obtain ⟨⟨mt, hIs⟩, -, -⟩ := id hI
  have hv₀ : Validation.validate? c.noStart.mod.mod = some mt := validate?_noStart hIs.valid
  have hmt : mt.imports = (importDefTypes c.imports).map .func := inst_importTypes hi₀ hv₀
  have hlen : mt.imports.length = c.imports.length := by
    rw [hmt, List.length_map, importDefTypes_length]
  have hfuncs : Validation.CExternType.funcs mt.imports = importDefTypes c.imports := by
    rw [hmt, funcs_map_func]
  obtain ⟨f, st₀, hf, haddr, hrel⟩ := hIs.instantiated
  have hf' : mapS trampIdx (instantiateOnce? (trampStore Pf c.imports) c.mod.mod
      ((List.range c.imports.length).map ExternAddr.func)) = some (I.store, f, st₀) := by
    rw [← instantiateOnce?_mapH, trampStore_mapH, ← hlen]
    rw [hfuncs] at hf
    exact hf
  obtain ⟨cs, ho, hs⟩ := mapS_eq_some hf'
  have hprep : (core3P Pf).prepare? (trampStore Pf c.imports) c.mod.mod
      ((List.range c.imports.length).map ExternAddr.func) = some (cs, f.module, st) := by
    show Core3.prepareE? _ _ _ = _
    simp only [Core3.prepareE?, hIs.valid]
    split
    · erw [ho]
      cases hrel with
      | none => rfl
      | some hx => simp only [hx]; rfl
    · exact absurd (externAddrsOk_tramp (Pf := Pf) hi₀ hv₀) ‹_›
  refine ⟨I, st, cs, f.module, ⟨hI, hs, hostsSat_instantiateOnce trampStore_hosts ho, hprep,
    fun fr hfr => ?_, fun x hx => ?_⟩⟩
  · have h := coreImportsFor_tramp (Pf := Pf) (c := c.noStart) (noStart_good hc) hi₀ fr hfr
    exact (coreImportsFor_noStart hIs.valid (trampStore Pf c.imports) _ fr).symm.trans h
  obtain ⟨n, hn⟩ := hc.core x hx
  have hname : coreNameI c x = n := by rw [coreNameI, hn]; rfl
  rw [hname]
  exact lookup_funcExport_gen hi.names hIs.valid ho haddr hn

end Facts

end Silmaril.Proofs.Wasm.Component.Reference
