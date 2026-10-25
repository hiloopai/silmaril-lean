module

public import Silmaril.Wasm.Behaviour.Adapters.V2
public import Silmaril.Wasm.V2.Execution.Instantiation

/-! # WebAssembly 2.0 behaviour definitions

`behavioursOf` collects finite-result and infinite-trace observations.
See `Silmaril.Wasm.Behaviour.Semantics.V2.Thms` for its public laws.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The observable behaviours of running the configuration `c` under profile
`P`. -/
def behavioursOf (P : Profile) (host : HostSemantics H) (c : Config H) :
    Set (Behaviour Val) :=
  {b | ∃ (c' : Config H) (r : Result),
        Steps P host c c' ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour} ∪
  {b | b = .diverges ∧ Diverges P host c}

/-- The observable behaviours of invoking function address `a` on `vs` in `s`. -/
def behaviours (P : Profile) (host : HostSemantics H) (s : Store H) (a : FuncAddr)
    (vs : List Val) : Set (Behaviour Val) :=
  behavioursOf P host (invoke s a vs)

@[simp] theorem behaviours_eq (P : Profile) (host : HostSemantics H) (s : Store H)
    (a : FuncAddr) (vs : List Val) :
    behaviours P host s a vs = behavioursOf P host (invoke s a vs) := rfl

/-! ## Introduction -/

/-- A finite run to a configuration whose code is a result exhibits that
result's behaviour. -/
theorem mem_behavioursOf {P : Profile} {host : HostSemantics H} {c c' : Config H}
    {r : Result} (steps : Steps P host c c') (final : c'.code = r.toAdmin) :
    r.toBehaviour ∈ behavioursOf P host c :=
  Or.inl ⟨c', r, steps, final, rfl⟩

/-- A finite run to a configuration whose code is `vs` returns `vs`. -/
theorem returns_mem_behavioursOf {P : Profile} {host : HostSemantics H} {c c' : Config H}
    {vs : List Val} (steps : Steps P host c c') (final : c'.code = vals vs) :
    Behaviour.returns vs ∈ behavioursOf P host c :=
  mem_behavioursOf (r := .values vs) steps final

/-- A finite run to a trapped configuration traps. -/
theorem traps_mem_behavioursOf {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps P host c c') (final : c'.code = [.trap]) :
    (Behaviour.traps : Behaviour Val) ∈ behavioursOf P host c :=
  mem_behavioursOf (r := .trap) steps final


end Silmaril.Wasm.V2.Execution
