module

public import Silmaril.Wasm.Examples.Common.Defs

/-!
# Straight-line execution and function bodies in the every-run logic: definitions

`bodyPost n post` is the **every-run body postcondition**: the postcondition of a function body
of result arity `n` that ends by falling through with exactly `n` results or by trapping, as
`post` allows (no `return`, no branch out, no exception, no tail call).

It is one of three postconditions of function bodies:

* `Silmaril.Wasm.Logic.Core.funcPost`: the angelic (`WP`) form with tail calls, for `FuncSpec`;
* `Silmaril.Wasm.Logic.VC.fnPost`: every run, ending by falling through, by `return` or by a trap
  (the form `wpc`-based function specifications use);
* `bodyPost`: every run, the no-`return` case of `fnPost`
  (`Silmaril.Wasm.Logic.VC.fnPost_of_bodyPost`).

`Silmaril.Wasm.Logic.Exec.Thms` gives symbolic execution of straight-line code (`Wp.exec1`,
`Wp.exec`, `Wp.exec_eq`) and function specifications from every-run body proofs
(`FSpecValid.of_body_hwp`). A Silmaril addition.

This namespace is the logic-level name of these facilities. The declarations themselves still
live in `Silmaril.Wasm.Examples.Common` (`bodyPost` is the same constant, exported here): moving
them changes `Silmaril.Wasm.Verify.FnSpec.Defs` and rebuilds every project row above it, so the
move is left to a separate change.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Exec

export Silmaril.Wasm.Examples.Common (bodyPost)

end Silmaril.Wasm.Logic.Exec
