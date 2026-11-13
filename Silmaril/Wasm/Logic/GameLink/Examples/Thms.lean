module

public import Silmaril.Proofs.Wasm.Logic.GameLink.Examples

/-!
# The logic and the Wasm game: a worked two-module example

Every profile, partial correctness (proofs in
`Silmaril.Proofs.Wasm.Logic.GameLink.Examples`):

* `incProvider_sat`: an instance whose exports are all the increment function
  `fi₁` at `a₁` (`OpenExamples.incBody`) meets `incISpec I.exports` with the
  invariant `s.funcs[a₁]? = some fi₁`, under every import specification;
* `client_sat`: an instance whose exports are all the client function `fi₂` at
  `a₂` (`OpenExamples.clientBody x`, `x` resolving to the stub `fib` at `b` with
  code `.host 0`), with import `0` of parameter type `[i32]`, meets
  `incISpec I.exports` under `incISpec I.imports`, with the invariant that `fi₂`
  and `fib` are in the store; the stub call is proved by `Open.FSpecAt.stub`,
  without assumptions on the provider's code;
* `inc_link_sound`: for every static link `S` (`Silmaril.Wasm.Game.Linking.Setup`,
  `S.Scalar`) whose provider store `S.sp` and consumer store `S.scs` contain
  these functions at the export addresses, `S.linkedI.σ P ≤ agStrat Ii
  (incISpec S.exportTypes)`; `inc_link_answer`: every terminating host-free run
  of an export call of the linked module on `[i32 m]` returns `m + 1`.

The link data are hypotheses: no concrete `Setup` (a run of `link?` and of
`instantiateOnce?` on concrete modules) is constructed here.
-/
