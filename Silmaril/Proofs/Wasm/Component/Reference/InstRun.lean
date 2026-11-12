module

public import Silmaril.Proofs.Wasm.Component.Reference.InstExport
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The instantiation phase of `Simple.toRef`

Instantiating `c.toRef` from the empty store is a silent deterministic run (`SRuns`) of the
instantiation program: the root checks pass (no imports), the root instance `0` is allocated,
the core module is instantiated (`prepare_core3P`), and the export definitions allocate one
lifted function per export (`exportsDefs_run`). With the host event before and the end of the
host frame after, every machine run of the instantiation follows it (`DetRunL.inv`), which
proves `instPhase`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)

/-! ## Root checks of an import-free component -/

section Root

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)]

theorem precheckDef_ok (s : CStore E) (args : Exports E) (f : Frame E)
    {d : Syntax.Definition E.Module} (h : ∀ n x, d ≠ .import_ n x) :
    ∃ o, precheckDef s args f d = .ok o := by
  cases d with
  | import_ n x => exact absurd rfl (h n x)
  | «alias» a =>
    cases a <;> simp only [precheckDef] <;> (try split) <;> exact ⟨_, rfl⟩
  | export_ n si o => simp only [precheckDef]; split <;> exact ⟨_, rfl⟩
  | instance_ e => cases e <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

theorem precheckImports_ok (s : CStore E) (args : Exports E) :
    ∀ (f : Frame E) (ds : List (Syntax.Definition E.Module)), NoImport ds →
      precheckImports s args f ds = .ok ()
  | _, [], _ => rfl
  | f, d :: ds, h => by
    obtain ⟨o, ho⟩ := precheckDef_ok s args f (h d List.mem_cons_self)
    have ht : NoImport ds := fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    simp only [precheckImports, ho]
    cases o with
    | none => rfl
    | some f' => exact precheckImports_ok s args f' ds ht

theorem importNames_nil {M : Type} : ∀ {ds : List (Syntax.Definition M)}, NoImport ds →
    importNames ds = []
  | [], _ => rfl
  | d :: ds, h => by
    have ht : NoImport ds := fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    have hd : ∀ n x, d ≠ .import_ n x := h d List.mem_cons_self
    unfold importNames at ht ⊢
    rw [List.filterMap_cons]
    cases d with
    | import_ n x => exact absurd rfl (hd n x)
    | _ => exact importNames_nil ht

end Root

/-! ## The core instance -/

section Core3P

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type} {R : Recurse (core3P Pf) σ}
  {inst : InstId} {outer : List (Frame (core3P Pf))} {args : Exports (core3P Pf)}

/-- `instantiateCore` of an import-free, start-free module: one store read and the update of
the core store. -/
theorem instantiateCore_run (f : Frame (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ)
    {m : Silmaril.Wasm.Module} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} (hm : f.coreModules = [m])
    (himp : (core3P Pf).importTypes m = [])
    (hp : (core3P Pf).prepare? cfg.store.core m [] = some (cs, ci, none)) :
    TRuns (instantiateCore inst f 0 [] : P (core3P Pf) σ _) cfg ((core3P Pf).exports ci)
      { cfg with store := setCoreSt cs cfg.store } := by
  have hmod : f.coreModule? 0 = some m := by rw [Frame.coreModule?, hm]; rfl
  have himps : coreImportsFor? cfg.store.core m [] f = some [] := by
    unfold coreImportsFor?
    rw [himp]
    rfl
  unfold instantiateCore
  rw [hmod]
  refine (TRuns.pure _ cfg).bind ((TRuns.getStore cfg).bind ?_)
  rw [himps]
  refine (TRuns.pure _ cfg).bind ?_
  dsimp only
  rw [hp]
  exact (TRuns.modifyStore (f := setCoreSt cs) (fun _ => rfl) cfg).bind (TRuns.pure _ _)

theorem instDef_coreModule (sc : Scope (core3P Pf)) (m : (core3P Pf).Module) :
    instantiateDef R inst outer args sc (.coreModule m) =
      (Pure.pure { sc with frame := { sc.frame with coreModules := sc.frame.coreModules ++ [m] } } :
        P (core3P Pf) σ (Scope (core3P Pf))) := by
  simp only [instantiateDef, pushEntry, need, Frame.push, orTrap]
  rfl

/-- The frame after the core module and the core instance. -/
noncomputable def coreFrame (m : (core3P Pf).Module) (es₀ : List (String × (core3P Pf).ExternVal)) :
    Frame (core3P Pf) :=
  { (Frame.empty : Frame (core3P Pf)) with coreModules := [m], coreInstances := [es₀] }

/-- The core facts of `Simple.Inst`, over `core3P Pf`. -/
structure CoreFacts (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P Pf).Store (CanonHost (core3P Pf))) (ci : (core3P Pf).Inst) : Prop where
  isInst : c.mod.IsInst I
  store : Store.mapH (fun _ => 0) cs = I.store
  imports : (core3P Pf).importTypes c.mod.mod = []
  prepare : (core3P Pf).prepare? ((core3P Pf).empty _) c.mod.mod [] = some (cs, ci, none)
  lookup : ∀ x ∈ c.exports, lookupExport? ((core3P Pf).exports ci) (coreName c.mod x) =
    some (.func (I.addrs.getD x.core 0))

/-- **The core facts hold** for a `Simple.Inst` component in the fragment. -/
theorem coreFacts {c : Simple} (hc : c.Good) (hi : c.Inst) :
    ∃ I cs ci, CoreFacts (Pf := Pf) c I cs ci := by
  obtain ⟨I, mt, cs, f', hI, hv, hmt, ho, hs, ha⟩ := inst_once
    (H := CanonHost (core3P Pf)) (fun _ => 0) hi
  refine ⟨I, cs, f'.module, ⟨hI, hs, importTypes_core3P Pf hv hmt,
    prepare_core3P Pf hv hmt ho, fun x hx => ?_⟩⟩
  obtain ⟨n, hn⟩ := hc.core x hx
  have hname : coreName c.mod x = n := by rw [coreName, hn]; rfl
  rw [hname, exports_core3P]
  exact lookup_funcExport hi hv ho ha hn

/-- The `core instance` definition of `Simple.toRef`. -/
theorem instDef_coreInstance (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ)
    {m : (core3P Pf).Module} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} (hm : sc.frame.coreModules = [m])
    (himp : (core3P Pf).importTypes m = [])
    (hp : (core3P Pf).prepare? cfg.store.core m [] = some (cs, ci, none)) :
    TRuns (instantiateDef R inst outer args sc (.coreInstance (.instantiate 0 [])))
      cfg { sc with frame := { sc.frame with
        coreInstances := sc.frame.coreInstances ++ [(core3P Pf).exports ci] } }
      { cfg with store := setCoreSt cs cfg.store } :=
  (instantiateCore_run (inst := inst) sc.frame cfg hm himp hp).bind (TRuns.pure _ _)

/-- The store after the core instance and the lifted functions `fs`. -/
noncomputable def liftStore (cs : (core3P Pf).Store (CanonHost (core3P Pf))) (s : CStore (core3P Pf))
    (fs : List (CFuncInst (core3P Pf))) : CStore (core3P Pf) :=
  { setCoreSt cs s with funcs := s.funcs ++ fs }

/-- **The definitions of `c.toRef` run silently** from a store with the empty core store and
no component function: the core instance, then the lifted functions of the exports. -/
theorem toRefDefs_run {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) (cfg : Machine.Config (core3P Pf) σ)
    (hcore : cfg.store.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs = []) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) {} c.toRef) cfg sc'
        { cfg with store :=
            liftStore cs cfg.store (liftedList (fun k => I.addrs.getD k 0) inst c.exports) } ∧
      funcExports sc'.exports = c.exports.mapIdx (fun k x => (x.name, ⟨0 + k⟩)) ∧
      NoImport c.toRef := by
  have hp : (core3P Pf).prepare? cfg.store.core c.mod.mod [] = some (cs, ci, none) := by
    rw [hcore]
    exact hF.prepare
  have h₁ := instDef_coreModule (R := R) (inst := inst) (outer := outer) (args := args) {}
    c.mod.mod
  have h₂ := instDef_coreInstance (R := R) (inst := inst) (outer := outer) (args := args)
    { frame := { (Frame.empty : Frame (core3P Pf)) with coreModules := [] ++ [c.mod.mod] },
      exports := [] } cfg rfl hF.imports hp
  have hinv : ExpInv ((core3P Pf).exports ci) 0 (coreFrame c.mod.mod ((core3P Pf).exports ci)) :=
    ⟨rfl, rfl, rfl⟩
  have hs : (setCoreSt cs cfg.store).funcs.length = 0 := by
    show cfg.store.funcs.length = 0
    rw [hfuncs]
    rfl
  obtain ⟨sc', hr, hx, hn⟩ := exportsDefs_run (R := R) (inst := inst) (outer := outer)
    (args := args) c.mod (fun k => I.addrs.getD k 0) c.exports 0
    { frame := coreFrame c.mod.mod ((core3P Pf).exports ci), exports := [] }
    { cfg with store := setCoreSt cs cfg.store } hinv hs hF.lookup
  have hn' : NoImport c.toRef := by
    unfold Simple.toRef
    refine NoImport.append (fun d hd => ?_) hn
    rcases List.mem_cons.1 hd with rfl | hd
    · intro _ _ e
      cases e
    · rw [List.mem_singleton.1 hd]
      intro _ _ e
      cases e
  refine ⟨sc', ?_, hx, hn'⟩
  unfold Simple.toRef
  exact TRuns.foldlM_append (TRuns.foldlM_cons (TRuns.of_eq cfg h₁)
    (TRuns.foldlM_cons h₂ (TRuns.foldlM_nil _ _))) hr

theorem trapIf_run {b : Bool} (hb : b = false) (r : TrapReason)
    (m : Machine.Config (core3P Pf) σ) : TRuns (trapIf b r : P (core3P Pf) σ Unit) m () m := by
  subst hb
  exact TRuns.pure () m

theorem checkImport_run {r : Except String Unit} (hr : r = .ok ())
    (m : Machine.Config (core3P Pf) σ) :
    TRuns (checkImport r : P (core3P Pf) σ Unit) m () m := by
  subst hr
  exact TRuns.pure () m

/-- The store after root instantiation: instance `0`, the core store and the lifted
functions. -/
noncomputable def instStore (cs : (core3P Pf).Store (CanonHost (core3P Pf)))
    (s : CStore (core3P Pf)) (addr : Nat → Nat) (c : Simple) : CStore (core3P Pf) :=
  liftStore cs (ArenaOps.allocSt ArenaField.insts {} s) (liftedList addr ⟨0⟩ c.exports)

/-- **Root instantiation of `c.toRef` runs silently**: the root checks pass, instance `0` is
allocated, and the definitions run (`toRefDefs_run`). -/
theorem rootCall_run {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) (cfg : Machine.Config (core3P Pf) σ)
    (hcore : cfg.store.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs = [])
    (hinsts : cfg.store.insts = []) :
    ∃ es, funcExports es = exportMap c ∧
      TRuns (instantiateRootCall c.toRef [] : P (core3P Pf) σ _) cfg (⟨0⟩, es)
        { cfg with store := instStore cs cfg.store (fun k => I.addrs.getD k 0) c } := by
  obtain ⟨sc', hr, hx, hn⟩ := toRefDefs_run (R := callRecurse) (inst := ⟨0⟩) (outer := [])
    (args := []) hF { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store }
    hcore hfuncs
  have hac : argsComplete c.toRef ([] : Exports (core3P Pf)) = true := by
    rw [argsComplete, importNames_nil hn]
    rfl
  have hpre : ∀ s : CStore (core3P Pf), precheckImports s [] Frame.empty c.toRef = .ok () :=
    fun s => precheckImports_ok s [] _ _ hn
  have hid : (ArenaField.insts (E := core3P Pf)).mkId (ArenaField.insts.size cfg.store) =
      (⟨0⟩ : InstId) := by
    simp only [ArenaField.size, ArenaField.insts, hinsts, List.length_nil]
  have hmap : funcExports sc'.exports = exportMap c := by
    rw [hx, exportMap]
    simp only [Nat.zero_add]
  refine ⟨sc'.exports, hmap, ?_⟩
  unfold instantiateRootCall instantiateRoot
  refine (trapIf_run ((congrArg (!·) hac).trans rfl) _ cfg).bind ((TRuns.getStore cfg).bind ?_)
  refine (checkImport_run (hpre _) cfg).bind
    ((TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind ?_)
  rw [hid]
  exact (hr.bind (f := fun sc => Pure.pure sc.exports) (TRuns.pure _ _)).bind
    (f := fun es => Pure.pure ((⟨0⟩ : InstId), es)) (TRuns.pure _ _)

/-- **The instantiation program of `c.toRef` runs silently** from the initial configuration
to `afterInst`, observing the root instance `0` and the export map. -/
theorem instProg_run {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) :
    SRuns (instantiateProg c.toRef [] : P (core3P Pf) Unit (Ret (core3P Pf))) (initConfig ())
      [instantiatedObs ⟨0⟩ (exportMap c)] .unit
      (afterInst Pf cs (liftedFuncs Pf (fun k => I.addrs.getD k 0) c)) := by
  obtain ⟨es, hes, hr⟩ := rootCall_run hF
    { (initConfig () : Machine.Config (core3P Pf) Unit) with
      store := DispatchSt.incNestingSt (initConfig () : Machine.Config (core3P Pf) Unit).store }
    rfl rfl rfl
  unfold instantiateProg
  refine SRuns.bind (os₁ := [])
    (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _) ?_
  refine SRuns.bind (os₁ := []) hr ?_
  dsimp only
  rw [hes]
  exact SRuns.bind (os₁ := []) (TRuns.modifyStore (f := DispatchSt.decNestingSt) (fun _ => rfl) _)
    (.emit (.pure _ _))

/-! ## The machine runs of the instantiation -/

variable {prof : ProfileKind} {σ : Type} {hr : HostReady σ}
  {D : Call (core3P Pf) → P (core3P Pf) σ (Ret (core3P Pf))}

/-- The configuration after the instantiation host event. -/
noncomputable def instStart (c : Simple) : Machine.Config (core3P Pf) Unit :=
  { (initConfig () : Machine.Config (core3P Pf) Unit) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg c.toRef []))] }

/-- **The instantiation is one deterministic run** from the host event to `afterInst`. -/
theorem inst_detRunL {hr : HostReady Unit}
    {D : Call (core3P Pf) → P (core3P Pf) Unit (Ret (core3P Pf))} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) :
    ∃ tr, SRuns.Quiet tr ∧ traceObs tr = [instantiatedObs ⟨0⟩ (exportMap c)] ∧
      DetRunL prof hr D (instStart c)
        tr (afterInst Pf cs (liftedFuncs Pf (fun k => I.addrs.getD k 0) c)) := by
  obtain ⟨tr, hq, ho, d⟩ := (instProg_run hF).detRunL (prof := prof) (hr := hr) (dispatch := D)
    rfl none (fun _ => Pure.pure .unit) [] []
  have s : UniqueStep prof hr D
      { afterInst Pf cs (liftedFuncs Pf (fun k => I.addrs.getD k 0) c) with
        ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterInst Pf cs (liftedFuncs Pf (fun k => I.addrs.getD k 0) c)) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  refine ⟨tr ++ [.tau], fun l hl => ?_, ?_, d.trans (.cons rfl s (.refl rfl))⟩
  · rcases List.mem_append.1 hl with hl | hl
    · exact hq l hl
    · exact .inl (List.mem_singleton.1 hl)
  · rw [traceObs_append, ho]
    rfl

/-- The instantiation host event goes to `instStart`. -/
theorem hostRun_inv {m m' : Machine.Config (core3P Pf) σ}
    {p : P (core3P Pf) σ (Ret (core3P Pf))}
    (h : Machine.Step prof hr D m (.host (.run p)) m') :
    m' = { m with ctl := [.ofProg none (StepDefs.runProg p)] } := by
  cases h
  rfl

/-- From a host-in-control configuration, runs without host events do nothing. -/
theorem steps_ctl_nil {m m' : Machine.Config (core3P Pf) σ}
    {tr : List (Label (core3P Pf) σ)} (hc : m.ctl = [])
    (h : Machine.Steps prof hr D m tr m') (hn : ∀ ev, Label.host ev ∉ tr) :
    tr = [] ∧ m' = m := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | cons s _ =>
    obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil hc s
    exact absurd List.mem_cons_self (hn ev)

/-- A quiet deterministic run that ends with the host in control: every run without host
events from its start that ends with the host in control is that run. -/
theorem detRunL_end {m m₂ m' : Machine.Config (core3P Pf) σ}
    {tr tr' : List (Label (core3P Pf) σ)} (d : DetRunL prof hr D m tr m₂)
    (hq : SRuns.Quiet tr) (hc₂ : m₂.ctl = []) (h : Machine.Steps prof hr D m tr' m')
    (hn : ∀ ev, Label.host ev ∉ tr') (hc : m'.ctl = [] ∨ m'.store.lockdown = true) :
    tr' = tr ∧ m' = m₂ := by
  rcases d.inv h with ⟨tr₂, htr, d₂⟩ | ⟨tr'', htr, h''⟩
  · cases d₂ with
    | refl _ => exact ⟨by rw [htr, List.append_nil], rfl⟩
    | cons hl s _ =>
      have hl' : _ ∈ tr := htr ▸ List.mem_append_right tr' List.mem_cons_self
      rcases hc with hc | hc
      · obtain ⟨ev, he⟩ := Step.host_of_ctl_nil hc s.1
        rcases hq _ hl' with e | ⟨o, e⟩ <;> rw [he] at e <;> cases e
      · rw [hc] at hl
        cases hl
  · have hn'' : ∀ ev, Label.host ev ∉ tr'' := fun ev he => hn ev (htr ▸ List.mem_append_right _ he)
    obtain ⟨rfl, rfl⟩ := steps_ctl_nil hc₂ h'' hn''
    exact ⟨by rw [htr, List.append_nil], rfl⟩

/-- **The results of instantiating `c.toRef`**: the only one is the instance at `afterInst`
with root instance `0` and the export map `exportMap c`. -/
theorem instBehaviours_toRef {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) (prof : ProfileKind) :
    ∀ r ∈ instBehaviours prof (refHost Pf) (initConfig ()) c.toRef [],
      r = .instance (afterInst Pf cs (liftedFuncs Pf (fun k => I.addrs.getD k 0) c)) ⟨0⟩
        (exportMap c) := by
  obtain ⟨trD, hq, ho, d⟩ := inst_detRunL (prof := prof) (hr := (refHost Pf).hr)
    (D := (refHost Pf).dispatch) hF
  intro r hr
  cases r with
  | «instance» m' inst es =>
    show InstResult.instance m' inst es = _
    obtain ⟨tr, hs, hn, hc, -, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStart c := hostRun_inv s₁
    obtain ⟨htr, hm⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn (.inl hc)
    have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, exportMap c) := by
      rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
    have hie : (inst, es) = ((⟨0⟩ : InstId), exportMap c) := Option.some.inj (hobs.symm.trans hdec)
    rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
  | traps =>
    obtain ⟨m', tr, hs, hn, -, ht⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStart c := hostRun_inv s₁
    obtain ⟨-, rfl⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn (.inr ht)
    cases ht
  | diverges =>
    obtain ⟨m₁, s₁, dv⟩ := hr
    have he : m₁ = instStart c := hostRun_inv s₁
    exact absurd (d.toDetRun.diverges (he ▸ dv)) (not_diverges_of_ctl_nil rfl)

/-- **The instantiation phase** (`InstPhase`). -/
theorem instPhase : InstPhase := by
  intro Pf prof c hc hi
  obtain ⟨I, cs, ci, hF⟩ := coreFacts (Pf := Pf) hc hi
  exact ⟨I, cs, hF.isInst, hF.store, instBehaviours_toRef hF prof⟩

end Core3P

end Silmaril.Proofs.Wasm.Component.Reference
