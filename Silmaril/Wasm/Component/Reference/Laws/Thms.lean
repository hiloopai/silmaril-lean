module

public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.ErrorContext.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Resource.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Stream.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Task.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Callout.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Thms
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
public import Silmaril.Wasm.Component.Reference.Embedding.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Config.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Exec.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Step.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.StreamOps.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Thms
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Builtins.Thms
public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Check.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Validation.DefTypes.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Defs.Thms
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Thms

/-!
# The laws of the component-model reference copy, as a header for other topics

Proof modules of other topics (`Silmaril.Proofs.Wasm.Resource.**`, the component tools of
`Silmaril.Wasm.Tools.Component`) must not import a Raw module of the component topic directly, so
they import this header for the theorems of the copied reference they use.

It re-exports the `Thms` parts `Silmaril.Wasm.Component.Reference.**.Thms`: the theorems of the
copied modules that these modules use, refined out of `Silmaril.Raw.Wasm.Component.**`, together
with the laws their proofs need. No Raw
module is in its import closure.
-/
