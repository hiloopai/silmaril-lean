module

public import Silmaril.Wasm.Component.FXRes.Reach.Defs
public import Silmaril.Wasm.Resource.MachineTab.Thms
public import Silmaril.Wasm.Resource.Table.Thms

/-!
# Configurations reached by multi-call runs: every handle table is well formed

* `reached_tabMove`: at a reached configuration, the handle table of every instance is on a
  successful history from `Table.empty` (the frame theorems of `Silmaril.Wasm.Resource.MachineTab`,
  for a host whose programs are table-moving);
* **`reached_freeOK`**: hence it satisfies the representation invariant `FreeOK`
  (`Silmaril.Wasm.Resource.table_steps_run` from `freeOK_empty`), the hypothesis of
  `FXRes.Borrow.borrow_not_given`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Reach

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Resource

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type} {prof : ProfileKind}

/-- **At a reached configuration every handle table is on a successful history** from
`Table.empty`, accepted by the handle protocol in both orientations. -/
theorem reached_tabMove {h : Host E σ} {j : InstId} (hh : TabHost j h.impl) {σ0 : σ}
    {X : CIface} {p : RefProg E X} {m : Config E σ} (hm : Reached prof h σ0 p m) :
    ∃ evs, Silmaril.Wasm.Component.Runtime.Table.Steps Silmaril.Wasm.Component.Runtime.Table.empty evs (vtab m.store j) ∧
      ∀ r, (handleProto ℕ r).Accepts (evs.map tableEv) := by
  obtain ⟨m₀, inst, es, ds, mₙ, tr, hi, hr, hs, hn⟩ := hm
  have hd := tabDispatch_canon hh h.lim h.q h.hr
  obtain ⟨hm₀, h₀⟩ := instantiates_tab hd (tabProg_instantiateProg _ _) hi
    (cfgTab_init CStore.empty σ0)
  obtain ⟨hmₙ, h₁⟩ := runCalls_tab hd hr hm₀
  obtain ⟨-, h₂⟩ := steps_tab hd hs hmₙ fun q hq => absurd hq (hn q)
  obtain ⟨evs, hst⟩ := (h₀.trans h₁).trans h₂
  exact ⟨evs, hst, fun r => table_steps_accepts hst r⟩

/-- **At a reached configuration every instance's handle table satisfies `FreeOK`.** -/
theorem reached_freeOK {h : Host E σ} {j : InstId} (hh : TabHost j h.impl) {σ0 : σ}
    {X : CIface} {p : RefProg E X} {m : Config E σ} (hm : Reached prof h σ0 p m) :
    ∀ st, m.store.inst? j = some st → FreeOK st.handles := by
  intro st hst
  obtain ⟨evs, hs, -⟩ := reached_tabMove hh hm
  have hv : vtab m.store j = st.handles := by
    simp only [vtab, handles?, hst, Option.map_some, Option.getD_some]
  rw [← hv]
  obtain ⟨_, -, -, hf⟩ := table_steps_run hs .client freeOK_empty tabRel_empty
  exact hf

end Silmaril.Wasm.Component.FXRes.Reach
