module

public import Silmaril.Proofs.Wasm.Resource.MachineTab.Step
public import Silmaril.Proofs.Wasm.Resource.MachineTab.Dispatch
public import Silmaril.Wasm.Spec.Component.RefMulti.Defs

/-!
# Handle tables along instantiations and several calls on one instance

* `calls_tab`: a top-level call (`Calls`, any outcome) from a table-moving configuration is a
  table move to a table-moving configuration (its host events are ticks and cancellations, so
  no host-frame program other than the dispatcher's is run);
* `instantiates_tab`: so is a root instantiation from the initial configuration, given that the
  instantiation program is table-moving;
* `runCalls_tab`: so is a run of resolved calls (`RunCalls`);
* **`refMulti_tables`**: on every multi-call run of a reference component (instantiation,
  resolved calls, then a last call with any outcome), the handle table of every instance is on
  a successful history from `Table.empty`, accepted by `handleProto ℕ r` in both orientations;
  **`refMulti_tables_host`**: the same for every host whose own programs are table-moving
  (`TabHost`, e.g. `tabHost_none`), with no further hypothesis (`tabDispatch_canon`,
  `tabProg_instantiateProg`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Component.Reference

variable {E : CoreEngine} {σ : Type} {j : InstId}
variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

theorem calls_tab (hd : TabDispatch j dispatch) {m m' : Config E σ} {c : CallId} {f : FuncId}
    {args : List Val} {out : CallOutcome} (h : Calls prof hr dispatch m c f args m' out)
    (hm : CfgTab j m) : CfgTab j m' ∧ TabMove j m.store m'.store := by
  obtain ⟨tr, hs, hh, -, -⟩ := h
  refine steps_tab hd hs hm fun p hp => ?_
  rcases List.mem_cons.1 hp with e | hp'
  · cases e
  · rcases hh _ hp' with e | e <;> cases e

theorem instantiates_tab [∀ a b, Decidable (E.ExternSub a b)] (hd : TabDispatch j dispatch)
    {c : Syntax.Component E.Module} {args : Instantiate.Exports E}
    (hp : TabProg j (instantiateProg (σ := σ) c args)) {m m₀ : Config E σ} {inst : InstId}
    {es : List (String × FuncId)} (h : Instantiates prof hr dispatch m c args m₀ inst es)
    (hm : CfgTab j m) : CfgTab j m₀ ∧ TabMove j m.store m₀.store := by
  obtain ⟨tr, hs, hh, -⟩ := h
  refine steps_tab hd hs hm fun p hp' => ?_
  rcases List.mem_cons.1 hp' with e | hp''
  · cases e
    exact hp
  · exact absurd hp'' (hh _)

variable [∀ a b, Decidable (E.ExternSub a b)]

theorem runCalls_tab {h : Host E σ} (hd : TabDispatch j h.dispatch) {X : CIface}
    {names : X.Exp → String} {es : List (String × FuncId)} {m m' : Config E σ} {k : ℕ}
    {ds : List (DoneCall X)} (hr : RunCalls prof h names es m k ds m') (hm : CfgTab j m) :
    CfgTab j m' ∧ TabMove j m.store m'.store := by
  induction hr with
  | nil => exact ⟨hm, TabMove.refl _⟩
  | cons _ hc _ ih =>
    obtain ⟨hm₁, h₁⟩ := calls_tab hd hc hm
    obtain ⟨hm₂, h₂⟩ := ih hm₁
    exact ⟨hm₂, h₁.trans h₂⟩

/-- **The handle tables on multi-call runs**: after instantiating a reference component from the
empty store, running resolved calls `ds` and a last call with any outcome, the handle table of
instance `j` is on a successful table history from `Table.empty`, accepted by the handle
protocol in both orientations: indices are allocated fresh, and only live indices are dropped.
Hypotheses: the dispatcher and the instantiation program are table-moving. -/
theorem refMulti_tables {h : Host E σ} (hd : TabDispatch j h.dispatch) {σ0 : σ} {X : CIface}
    {p : RefProg E X} (hp : TabProg j (instantiateProg (σ := σ) p.comp p.args))
    {m₀ : Config E σ} {inst : InstId} {es : List (String × FuncId)}
    (hi : InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args)
    {ds : List (DoneCall X)} {mₙ : Config E σ} (hr : RunCalls prof h p.names es m₀ 0 ds mₙ)
    {c : CallId} {f : FuncId} {args : List Val} {m' : Config E σ} {out : CallOutcome}
    (hc : Calls prof h.hr h.dispatch mₙ c f args m' out) :
    ∃ evs, Silmaril.Wasm.Component.Runtime.Table.Steps Silmaril.Wasm.Component.Runtime.Table.empty evs (vtab m'.store j) ∧
      ∀ r, (handleProto ℕ r).Accepts (evs.map tableEv) := by
  obtain ⟨hm₀, h₀⟩ := instantiates_tab hd hp hi (cfgTab_init CStore.empty σ0)
  obtain ⟨hmₙ, h₁⟩ := runCalls_tab hd hr hm₀
  obtain ⟨-, h₂⟩ := calls_tab hd hc hmₙ
  obtain ⟨evs, hs⟩ := (h₀.trans h₁).trans h₂
  exact ⟨evs, hs, fun r => table_steps_accepts hs r⟩

/-- **The handle tables on multi-call runs, for the reference dispatcher**: for every host whose
own programs are table-moving (e.g. `HostImpl.none`), every multi-call run of every reference
component keeps every instance's handle table on a successful history from `Table.empty`,
accepted by the handle protocol in both orientations. -/
theorem refMulti_tables_host {h : Host E σ} (hh : TabHost j h.impl) {σ0 : σ} {X : CIface}
    {p : RefProg E X} {m₀ : Config E σ} {inst : InstId} {es : List (String × FuncId)}
    (hi : InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args)
    {ds : List (DoneCall X)} {mₙ : Config E σ} (hr : RunCalls prof h p.names es m₀ 0 ds mₙ)
    {c : CallId} {f : FuncId} {args : List Val} {m' : Config E σ} {out : CallOutcome}
    (hc : Calls prof h.hr h.dispatch mₙ c f args m' out) :
    ∃ evs, Silmaril.Wasm.Component.Runtime.Table.Steps Silmaril.Wasm.Component.Runtime.Table.empty evs (vtab m'.store j) ∧
      ∀ r, (handleProto ℕ r).Accepts (evs.map tableEv) :=
  refMulti_tables (tabDispatch_canon hh h.lim h.q h.hr) (tabProg_instantiateProg _ _) hi hr hc

end Silmaril.Wasm.Resource
