module

public import Silmaril.Wasm.Models.V2Core.Thms
public import Silmaril.Proofs.Wasm.Models.V2Sound.Closed

/-!
# Type soundness of the own Wasm 2.0 model

The header of the 2.0 type-soundness port. The proofs are the copied
`Silmaril/Raw/Wasm/Versions/V2/Soundness{,/*}.lean` (an earlier development; provenance in
"Port: v2sound"). The statements are about `Silmaril.Wasm.V2.Execution.Step P`, the relation
`v20own P H` observes, at every profile `P` and for every host type `H`.

* **`preservation`**: a step of a typed configuration gives a typed configuration of the same
  result type, over an extending store (`Extend`);
* **`progress`**: a typed configuration is terminal (a value stack or `TRAP`) or steps;
* **`steps_safe`**: every configuration reachable from a typed one is typed, its store extends
  the start store, and it is terminal or steps;
* **`invoke_safe`**: the same from `$invoke` of a typed call on a typed store;
* **`behaviours_nonempty`**: a typed call on a typed point has a behaviour (it does not get
  stuck);
* **`behaviours_returns_typed`**: its returned values have the callee's result types;
* **`v20typed_obs_nonempty`**: in the typed model `v20typed P H`, every typed call of a point of
  the domain is observed;
* **`v20_core_beh_det_hostFree`**: on a typed, well-formed store with no host function, a typed
  call has the same behaviours in 2.0 and in Core 3.0 at `Profile.deterministic g`, under any
  host that preserves well-formedness and keeps functions. This discharges the hypothesis `htot`
  of `v20_core_beh_det_of_closed` by type soundness. `HostOk` fails for the closed host as soon
  as a typed store can hold a host function, so the copied theorems are applied to the host
  `divV` whose calls all diverge: closed-host steps are `divV` steps, keep the store's
  functions, and on a host-free store every `divV` step is a closed-host step
  (`Silmaril/Proofs/Wasm/Models/V2Sound/Closed.lean`);
* `v20_core_beh_det_typed`: the case `H := Empty`, the pure 2.0 machine, with no hypothesis on
  the host.

New statements over the copied proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2Sound

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V2.Execution (Config ConfigOk HostOk StoreOk InvokeOk Extend Step Steps
  FuncInst HostSemantics)

variable {H : Type}

/-! ## Progress and preservation -/

/-- **Preservation.** -/
theorem preservation {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c c' : Config H} {ts : List Silmaril.Wasm.V2.Validation.CValType} (hc : ConfigOk c ts)
    (h : Step P host c c') : ConfigOk c' ts ∧ Extend c.store c'.store :=
  Silmaril.Wasm.V2.Execution.Step.preservation hhost hc h

/-- **Progress.** -/
theorem progress {P : Profile} {host : HostSemantics H} (hhost : HostOk host) {c : Config H}
    {ts : List Silmaril.Wasm.V2.Validation.CValType} (hc : ConfigOk c ts) :
    c.Terminal ∨ ∃ c', Step P host c c' :=
  Silmaril.Wasm.V2.Execution.Config.progress hhost hc

/-- **Type safety.** -/
theorem steps_safe {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c c' : Config H} {ts : List Silmaril.Wasm.V2.Validation.CValType} (hc : ConfigOk c ts)
    (h : Steps P host c c') :
    ConfigOk c' ts ∧ Extend c.store c'.store ∧ (c'.Terminal ∨ ∃ c'', Step P host c' c'') :=
  Silmaril.Wasm.V2.Execution.Steps.safe hhost hc h

/-! ## Calls of typed points -/

/-- **Type safety of `$invoke`** at a typed point. -/
theorem invoke_safe (P : Profile) {p : Pt H} (hp : Typed p) {c : Call} (hc : CallTyped p c)
    {c' : Config H} (h : Steps P p.2 (Silmaril.Wasm.V2.Execution.invoke p.1 c.1 c.2) c') :
    ∃ fi : FuncInst H, p.1.funcInst? c.1 = some fi ∧
      ConfigOk c' (Silmaril.Wasm.V2.Validation.liftResult fi.type.results) ∧
      Extend p.1 c'.store ∧ (c'.Terminal ∨ ∃ c'', Step P p.2 c' c'') :=
  Silmaril.Wasm.V2.Execution.invoke_safe hp.2 hp.1 hc h

/-- **A typed call has a behaviour.** -/
theorem behaviours_nonempty (P : Profile) {p : Pt H} (hp : Typed p) {c : Call}
    (hc : CallTyped p c) :
    (Silmaril.Wasm.V2.Execution.behaviours P p.2 p.1 c.1 c.2).Nonempty := by
  obtain ⟨_, -, hok⟩ := Silmaril.Wasm.V2.Execution.invoke_ok hp.1 hc
  exact Silmaril.Proofs.Wasm.Models.V2Sound.behavioursOf_nonempty hp.2 hok

/-- **Returned values are typed** by the callee's result types. -/
theorem behaviours_returns_typed (P : Profile) {p : Pt H} (hp : Typed p) {c : Call}
    (hc : CallTyped p c) {rs : List VVal}
    (hb : Behaviour.returns rs ∈ Silmaril.Wasm.V2.Execution.behaviours P p.2 p.1 c.1 c.2) :
    ∃ fi : FuncInst H, p.1.funcInst? c.1 = some fi ∧
      List.Forall₂ (fun (v : VVal) (t : Silmaril.Wasm.V2.ValType) => v.type = t) rs
        fi.type.results :=
  Silmaril.Proofs.Wasm.Models.V2Sound.behaviours_returns_typed hp.2 hp.1 hc hb

/-- A typed call names an allocated function. -/
theorem CallTyped.lt {p : Pt H} {c : Call} (hc : CallTyped p c) : c.1 < p.1.funcs.length := by
  obtain ⟨fi, hfi, -⟩ := hc
  exact (List.getElem?_eq_some_iff.mp hfi).1

/-- **Typed calls are observed** in the own model `v20own`. -/
theorem obs_nonempty (P : Profile) {p : Pt H} (hp : Typed p) {c : Call} (hc : CallTyped p c) :
    (obs P p c).Nonempty := by
  obtain ⟨b, hb⟩ := behaviours_nonempty P hp hc
  exact ⟨_, hc.lt, Behaviour.mem_mapSet.mpr ⟨b, hb, rfl⟩⟩

/-- **Typed calls are observed** in the typed model `v20typed P H`. -/
theorem v20typed_obs_nonempty (P : Profile) {p : Pt H} (hp : (v20typed P H).dom p) {c : Call}
    (hc : CallTyped p c) : ((v20typed P H).obs p c).Nonempty := by
  obtain ⟨b, hb⟩ := obs_nonempty P hp.2 hc
  exact ⟨b, hc, hb⟩

/-! ## Equality with Core 3.0 for the pure 2.0 machine -/

/-- Every host is `HostOk` when there are no host functions. -/
theorem hostOk_empty (host : HostSemantics Empty) : HostOk host :=
  fun _ _ h => h.elim

/-- A store is host-free when none of its functions is a host function. -/
abbrev HostFree (s : VStore H) : Prop := Silmaril.Proofs.Wasm.Models.V2Sound.HostFree s

/-- **2.0 and Core 3.0 behaviours of typed calls are equal at the deterministic profile** on a
typed store without host functions. -/
theorem v20_core_beh_det_hostFree (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {s : VStore H} {src : VHost H} {X : CStore H}
    (hwf : Silmaril.Wasm.V2.Execution.StoreWF s)
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X)
    (hp : Silmaril.Wasm.V2.Execution.HostPreserves src) (hk : HostKeepsV src)
    (hs : StoreOk s) (hfree : HostFree s) {a : Nat} {vs : List VVal} (h : InvokeOk s a vs) :
    Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behaviours (Profile.deterministic g) src s a vs) =
      Silmaril.Wasm.Execution.Core.behaviours (Profile.deterministic g) (liftHost src) X a
        (vs.map Silmaril.Wasm.V2.Execution.Val.toCore) :=
  v20_core_beh_det_of_closed g hwf hX hp hk (CallTyped.lt (p := (s, src)) (c := (a, vs)) h) vs
    (Silmaril.Proofs.Wasm.Models.V2Sound.behaviours_nonempty_closed hs hfree h)

/-- **The pure 2.0 machine**: typed calls have equal 2.0 and Core 3.0 behaviours at the
deterministic profile, under every host. -/
theorem v20_core_beh_det_typed (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {s : VStore Empty} {src : VHost Empty} {X : CStore Empty}
    (hwf : Silmaril.Wasm.V2.Execution.StoreWF s)
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) (hs : StoreOk s) {a : Nat}
    {vs : List VVal} (h : InvokeOk s a vs) :
    Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behaviours (Profile.deterministic g) src s a vs) =
      Silmaril.Wasm.Execution.Core.behaviours (Profile.deterministic g) (liftHost src) X a
        (vs.map Silmaril.Wasm.V2.Execution.Val.toCore) :=
  v20_core_beh_det_hostFree g hwf hX (fun h => h.elim) (fun h => h.elim) hs
    (Silmaril.Proofs.Wasm.Models.V2Sound.hostFree_empty s) h

end Silmaril.Wasm.Models.V2Sound
