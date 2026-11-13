module

public import Silmaril.Proofs.Wasm.Models.V2Sound.Behaviours

/-!
# Typed host-free stores under the closed host

`HostOk` fails for the closed host `closedV` as soon as a typed store can hold a host function,
so the copied soundness theorems do not apply to closed-host runs directly. This module gets
them back on stores without host functions:

* `Step.host_mono`: a step under a host is a step under any host that admits more outcomes;
* `Step.of_hostFree`: on a host-free store, a step does not depend on the host;
* `Step.funcs_closed`: a closed-host step keeps the store's functions, so host-freeness is
  invariant;
* `divV`: the host whose calls all diverge. It satisfies `HostOk`, and closed-host steps are
  `divV` steps;
* `closed_safe`: from a typed configuration on a host-free store, every closed-host run reaches
  a typed configuration on a host-free store that is terminal or steps;
* `behaviours_nonempty_closed`: a typed call on a typed host-free store has a closed-host
  behaviour.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Sound

open Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models.V2Core (closedV)

variable {H : Type}

/-- A store is **host-free** when none of its functions is a host function. -/
def HostFree (s : Store H) : Prop := ∀ fi ∈ s.funcs, ∀ h : H, fi.code ≠ .host h

/-- Every store is host-free when there are no host functions. -/
theorem hostFree_empty (s : Store Empty) : HostFree s := fun _ _ h => h.elim

/-- Rebuild a step by one of the twenty state-writing rules, whose premises do not mention the
host, from hypotheses in context. -/
local macro "step_state" : tactic => `(tactic| first
    | (apply Step.localSet; all_goals assumption)
    | (apply Step.globalSet; all_goals assumption)
    | (apply Step.tableSetTrap; all_goals assumption)
    | (apply Step.tableSetVal; all_goals assumption)
    | (apply Step.tableGrowSucceed; all_goals assumption)
    | (apply Step.tableGrowFail; all_goals assumption)
    | (apply Step.elemDrop; all_goals assumption)
    | (apply Step.storeIntTrap; all_goals assumption)
    | (apply Step.storeIntVal; all_goals assumption)
    | (apply Step.storeFloatTrap; all_goals assumption)
    | (apply Step.storeFloatVal; all_goals assumption)
    | (apply Step.storePackTrap; all_goals assumption)
    | (apply Step.storePackVal; all_goals assumption)
    | (apply Step.vecStoreOob; all_goals assumption)
    | (apply Step.vecStoreVal; all_goals assumption)
    | (apply Step.vecStoreLaneOob; all_goals assumption)
    | (apply Step.vecStoreLaneVal; all_goals assumption)
    | (apply Step.memoryGrowSucceed; all_goals assumption)
    | (apply Step.memoryGrowFail; all_goals assumption)
    | (apply Step.dataDrop; all_goals assumption))

/-- A step under `host` is a step under any `host'` admitting more outcomes. -/
theorem Step.host_mono {P : Profile} {host host' : HostSemantics H}
    (hmono : ∀ h s vs out, host h s vs out → host' h s vs out) {c c' : Config H}
    (hstep : Step P host c c') : Step P host' c c' := by
  induction hstep with
  | callAddrHost hf hcode hk hh => exact .callAddrHost hf hcode hk (hmono _ _ _ _ hh)
  | callAddrHostDiv hf hcode hk hh => exact .callAddrHostDiv hf hcode hk (hmono _ _ _ _ hh)
  | pure h => exact .pure h
  | read h => exact .read h
  | ctxtInstrs _ hne ih => exact .ctxtInstrs ih hne
  | ctxtLabel _ ih => exact .ctxtLabel ih
  | ctxtFrame _ ih => exact .ctxtFrame ih
  | _ => step_state

/-- **On a host-free store a step does not depend on the host.** -/
theorem Step.of_hostFree {P : Profile} {host host' : HostSemantics H} {c c' : Config H}
    (hstep : Step P host c c') (hfree : HostFree c.store) : Step P host' c c' := by
  induction hstep with
  | callAddrHost hf hcode =>
    exact absurd hcode (hfree _ (List.mem_of_getElem? hf) _)
  | callAddrHostDiv hf hcode =>
    exact absurd hcode (hfree _ (List.mem_of_getElem? hf) _)
  | pure h => exact .pure h
  | read h => exact .read h
  | ctxtInstrs _ hne ih => exact .ctxtInstrs (ih hfree) hne
  | ctxtLabel _ ih => exact .ctxtLabel (ih hfree)
  | ctxtFrame _ ih => exact .ctxtFrame (ih hfree)
  | _ => step_state

/-- **A closed-host step keeps the store's functions.** -/
theorem Step.funcs_closed {P : Profile} {c c' : Config H} (hstep : Step P closedV c c') :
    c'.store.funcs = c.store.funcs := by
  induction hstep with
  | callAddrHost _ _ _ hh => exact hh.elim
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtFrame _ ih => exact ih
  | _ => rfl

/-- The host whose calls all diverge. -/
def divV : HostSemantics H := fun _ _ _ out => out = .diverged

/-- `divV` keeps the host contract. -/
theorem hostOk_divV : HostOk (divV (H := H)) :=
  fun _ _ _ _ _ _ _ _ => ⟨⟨.diverged, rfl⟩, fun _ hout => by subst hout; trivial⟩

/-- A closed-host step is a `divV` step. -/
theorem Step.closed_divV {P : Profile} {c c' : Config H} (hstep : Step P closedV c c') :
    Step P divV c c' :=
  Step.host_mono (fun _ _ _ _ h => h.elim) hstep

/-- **Closed-host type safety on host-free stores.** -/
theorem closed_safe {P : Profile} {c c' : Config H} {ts : List CValType}
    (hfree : HostFree c.store) (hc : ConfigOk c ts) (hsteps : Steps P closedV c c') :
    HostFree c'.store ∧ ConfigOk c' ts ∧ (c'.Terminal ∨ ∃ c'', Step P closedV c' c'') := by
  have hinv : HostFree c'.store ∧ ConfigOk c' ts := by
    induction hsteps with
    | refl => exact ⟨hfree, hc⟩
    | tail _ hstep ih =>
      obtain ⟨hfree', hok⟩ := ih
      have hfuncs := Step.funcs_closed hstep
      refine ⟨fun fi hfi => hfree' fi (hfuncs ▸ hfi),
        (Step.preservation hostOk_divV hok (Step.closed_divV hstep)).1⟩
  refine ⟨hinv.1, hinv.2, ?_⟩
  rcases Config.progress (P := P) hostOk_divV hinv.2 with hterm | ⟨c'', hstep⟩
  · exact .inl hterm
  · exact .inr ⟨c'', Step.of_hostFree hstep hinv.1⟩

/-- **A typed call on a typed host-free store has a closed-host behaviour.** -/
theorem behaviours_nonempty_closed {P : Profile} {s : Store H} {a : FuncAddr} {vs : List Val}
    (hs : StoreOk s) (hfree : HostFree s) (h : InvokeOk s a vs) :
    (behaviours P closedV s a vs).Nonempty := by
  obtain ⟨_, -, hok⟩ := invoke_ok hs h
  exact behavioursOf_nonempty_of_safe fun _ hsteps => (closed_safe hfree hok hsteps).2.2

end Silmaril.Proofs.Wasm.Models.V2Sound
