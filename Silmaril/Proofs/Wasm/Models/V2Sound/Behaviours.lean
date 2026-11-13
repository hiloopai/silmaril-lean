module

public import Silmaril.Wasm.Models.V2Sound.Defs

/-!
# Behaviours of typed 2.0 configurations

Consequences of the copied `Steps.safe` and `invoke_safe`
(`Silmaril/Raw/Wasm/Versions/V2/Soundness.lean`) for the observable behaviours
`Silmaril.Wasm.V2.Execution.behavioursOf`:

* `behavioursOf_nonempty_of_safe`: a configuration whose reachable configurations are terminal
  or step has a behaviour. Either some run reaches a terminal configuration, whose result is a
  behaviour, or every reachable configuration steps and an infinite run exists
  (`InfiniteTrace.coinduct`);
* `behavioursOf_nonempty`: so a typed configuration has a behaviour;
* `valsOk_of_code`: a typed configuration whose code is a value stack types the stack;
* `behaviours_returns_typed`: the values returned by a typed call have the callee's result
  types.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Sound

open Silmaril.Wasm Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- A configuration all of whose reachable configurations are terminal or step has a
behaviour. -/
theorem behavioursOf_nonempty_of_safe {P : Profile} {host : HostSemantics H} {c : Config H}
    (hsafe : ∀ c', Steps P host c c' → c'.Terminal ∨ ∃ c'', Step P host c' c'') :
    (behavioursOf P host c).Nonempty := by
  classical
  by_cases hfin : ∃ c', Steps P host c c' ∧ c'.Terminal
  · obtain ⟨c', hsteps, r, hr⟩ := hfin
    exact ⟨_, mem_behavioursOf hsteps hr⟩
  · have hdiv : Diverges P host c := by
      refine Silmaril.InfiniteTrace.coinduct (fun c' => Steps P host c c') ?_ .refl
      intro c' hc'
      rcases hsafe c' hc' with hterm | ⟨c'', hstep⟩
      · exact absurd ⟨c', hc', hterm⟩ hfin
      · exact ⟨c'', hstep, hc'.tail hstep⟩
    exact ⟨.diverges, Or.inr ⟨rfl, hdiv⟩⟩

/-- **A typed configuration has a behaviour.** -/
theorem behavioursOf_nonempty {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) :
    (behavioursOf P host c).Nonempty :=
  behavioursOf_nonempty_of_safe fun _ h => (Steps.safe hhost hc h).2.2

/-- A typed configuration whose code is the value stack `vs` types `vs`. -/
theorem valsOk_of_code {c : Config H} {ts : Silmaril.Wasm.V2.ResultType} {vs : List Val}
    (hc : ConfigOk c (liftResult ts)) (hcode : c.code = vals vs) :
    List.Forall₂ (ValOk c.store) vs ts := by
  obtain ⟨C, -, hty⟩ := hc
  rw [hcode] at hty
  obtain ⟨ts', hvs, hsub⟩ := hty.vals_inv
  have hlift : ValsOk c.store vs (liftResult ts') := valsOk_liftResult.mpr hvs
  have hsub' : CResultType.Sub (liftResult ts') (liftResult ts) := by
    simpa using hsub
  exact valsOk_liftResult.mp (hlift.sub hsub')

/-- **Returned values are typed.** The values returned by a typed call have the types of the
callee's results. -/
theorem behaviours_returns_typed {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {a : FuncAddr} {vs rs : List Val} (hs : StoreOk s) (h : InvokeOk s a vs)
    (hb : Behaviour.returns rs ∈ behaviours P host s a vs) :
    ∃ fi : FuncInst H, s.funcInst? a = some fi ∧
      List.Forall₂ (fun (v : Val) (t : Silmaril.Wasm.V2.ValType) => v.type = t) rs
        fi.type.results := by
  rcases hb with ⟨c', r, hsteps, hcode, hr⟩ | ⟨hr, -⟩
  · obtain ⟨fi, hfi, hok, -, -⟩ := invoke_safe hhost hs h hsteps
    have hval : r = .values rs := by
      cases r with
      | values ws => cases hr; rfl
      | trap => cases hr
    subst hval
    exact ⟨fi, hfi, (valsOk_of_code hok hcode).imp fun _ _ hv => hv.type_eq⟩
  · cases hr

end Silmaril.Proofs.Wasm.Models.V2Sound
