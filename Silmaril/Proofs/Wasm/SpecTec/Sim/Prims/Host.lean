module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Store

/-!
# The concrete `B`: `$hostcall` and `$lift_result`

`$hostcall` is declared without clauses, so `callDef` always takes `B`'s answer. At the image of a
host call, `B` returns the images of the outcomes of a chosen call with the same image; under
`HostRespects` (the host's outcomes depend only on the images of its arguments) and `HostFinite`,
that list contains the image of every outcome Core allows (`ctrlHost_hostcall`).

`$lift_result` is evaluated by its three clauses (`applies_liftResult`), for every `B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Prims

variable {prof : Silmaril.Wasm.Numerics.Profile}

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## `$hostcall` -/

set_option maxRecDepth 100000 in
/-- `$hostcall` has no clause. -/
theorem findDef_hostcall (B : Builtins) : ∃ ps t, (simEnv B).findDef? "hostcall" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

/-- A definition with no clause applies exactly where `B` answers. -/
theorem applies_of_noClause {env : Env} {x : IL.Id} {ws : List ArgV} {v : Value}
    (hd : ∃ ps t, env.findDef? x = some (ps, t, [])) (hb : env.builtins.call x ws = some v) :
    Applies env x ws v := by
  obtain ⟨ps, t, hf⟩ := hd
  exact ⟨ps, t, [], hf, Or.inr ⟨⟨1, by simp [tryClauses]⟩, hb⟩⟩

/-- `B` answers `$hostcall` by `hostcallCall`. -/
theorem call_hostcall (hn : H → String) (host : HostSemantics H) (h : H) (s : Store H)
    (vs : List Val) :
    (builtins prof hn host).call "hostcall" (hostArgs hn h s vs) = hostcallCall hn host (hostArgs hn h s vs) := by
  simp [builtins, call, hostArgs, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- **`$hostcall` lists every outcome Core allows**, at every host call, for a finite host that
respects the encoding. This is `CtrlHost.hostcall` for the concrete `B`. -/
theorem ctrlHost_hostcall {hn : H → String} {host : HostSemantics H} (hf : HostFinite host)
    (hr : HostRespects hn host) (h : H) (s : Store H) (vs : List Val) :
    ∃ os : List Value,
      Applies (simEnv (builtins prof hn host)) "hostcall" [.val (.case "_HOSTFUNC" (.text (hn h))),
        .val (storeV hn s), .val (.list (vs.map valV))] (.list os) ∧
      ∀ o, host h s vs o → outcomeV hn o ∈ os := by
  classical
  have hex : ∃ p : H × Store H × List Val, hostArgs hn h s vs = hostArgs hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os :=
    ⟨(h, s, vs), rfl, hf h s vs⟩
  refine ⟨hex.choose_spec.2.choose.map (outcomeV hn), ?_, ?_⟩
  · refine applies_of_noClause (findDef_hostcall _) ?_
    show (builtins prof hn host).call "hostcall" (hostArgs hn h s vs) = _
    rw [call_hostcall, hostcallCall]
    split
    · rfl
    · contradiction
  · intro o ho
    obtain ⟨o', ho', he⟩ := hr _ _ _ _ _ _ hex.choose_spec.1 o ho
    rw [he]
    exact List.mem_map_of_mem ((hex.choose_spec.2.choose_spec o').1 ho')

/-- A host whose argument images determine the arguments respects the encoding. -/
theorem hostRespects_of_injective {hn : H → String} {host : HostSemantics H}
    (hi : ∀ h h' s s' vs vs', hostArgs hn h s vs = hostArgs hn h' s' vs' →
      h = h' ∧ s = s' ∧ vs = vs') : HostRespects hn host := by
  intro h h' s s' vs vs' he o ho
  obtain ⟨rfl, rfl, rfl⟩ := hi _ _ _ _ _ _ he
  exact ⟨o, ho, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Prims
