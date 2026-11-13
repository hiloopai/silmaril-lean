module

public import Silmaril.Wasm.Component.Reference.Machine.Exec.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Config.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Oracle.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs
public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Machine.Exec`: laws of the component reference

Theorems of the component reference copy `Machine.Exec`, refined out of
`Silmaril.Raw.Wasm.Component.Machine.Exec`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
variable {E : CoreEngine} {σ : Type}
open CStoreOps

section Lemmas

variable (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

/-- Host events require `ctl = [] ∧ ¬ lockdown ∧ nestingDepth = 0`. -/
theorem hostStep?_enabled {hr : HostReady σ} {ev : HostEvent E σ} {m : Config E σ}
    {r : Label E σ × Config E σ} (h : hostStep? hr ev m = some r) :
    m.ctl = [] ∧ m.store.lockdown = false ∧ m.store.nestingDepth = 0 := by
  unfold hostStep? at h
  split at h
  · rename_i hm
    simpa [Config.hostReady, and_assoc] using hm
  · cases h

end Lemmas

end Silmaril.Wasm.Component.Machine
