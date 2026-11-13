module

public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Lift.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Lower.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Callout.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.ErrorContext.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Resource.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Stream.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Task.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Callout.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Lift.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Load.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Lower.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Store.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.StreamOps.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Thms
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Dispatch`: laws of the component reference

Theorems of the component reference copy `Canon.Dispatch`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Dispatch`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI
variable {E : CoreEngine} {σ : Type}

/-- The callout program is the canon code `calloutBody` behind the entry check
`withCalloutEntry`. -/
theorem hostCalloutProg_eq (lim : Limits) (q : Quirks) (hr : HostReady σ) (host : HostImpl E σ)
    (h : CanonHost E) (args : List FlatValue) :
    hostCalloutProg lim q hr host h args =
      withCalloutEntry h fun s th => calloutBody lim q hr host s th h args := rfl

end Silmaril.Wasm.Component.Canon
