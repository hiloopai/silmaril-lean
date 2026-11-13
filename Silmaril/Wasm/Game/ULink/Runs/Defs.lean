module

public import Silmaril.Wasm.Game.ULink.Defs

/-!
# Runs of the consumer against the provider, in one store

For a link `L : ULink` over one store (`Silmaril.Wasm.Game.ULink.Defs`), a host-free run of the
linked module in the real store is a run of the consumer in the stubbed store whose stub calls
are answered by runs of the provider in the real store
(`Silmaril.Wasm.Game.ULink.Runs.Thms`). These are the run-level notions:

* `ORuns P Ans c tr d`: host-free steps at `P`, interrupted by the calls of `tr`, each resumed
  with its answer in its returned store, where the answer must be one the oracle `Ans` gives
  **for the store at the call**, the host code and the arguments. (With `Ans` ignoring the
  call, this is `Silmaril.Wasm.Det.Shared.RunsS`.)
* `ULink.provAns L P σ k args r σ'`: the provider's answers. `σ` is the stubbed store of a real
  store `s` with the link's layout, `k` is a stub code with provider address `a`, the
  provider's invocation `$invoke(s, a, args)` runs host-free to the result `r` in the real
  store `s'`, and the returned store is `σ' = L.stubS s'`.

New definitions (no source file).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- An answered call: host code, arguments, answer and returned store. -/
abbrev OCall : Type := Nat × List Val × Result × Store Nat

/-- **Runs against an oracle whose answers depend on the call**: host-free steps at `P`,
interrupted by the calls of the trace, each answered by `Ans` (store at the call, host code,
arguments, answer, returned store) and resumed in the returned store. -/
inductive ORuns (P : Profile) (Ans : Store Nat → Nat → List Val → Result → Store Nat → Prop) :
    Config Nat → List OCall → Config Nat → Prop where
  | stop {c d : Config Nat} (hs : Steps P (Det.noHost (H := Nat)) c d) : ORuns P Ans c [] d
  | call {c d e : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} {r : Result}
      {s' : Store Nat} {tr : List OCall} (hs : Steps P (Det.noHost (H := Nat)) c d)
      (hd : decompose? d.store d.code = some (E, a, h, args)) (hA : Ans d.store h args r s')
      (hk : ORuns P Ans ⟨s', d.frame, E.fill r.toAdmin⟩ tr e) :
      ORuns P Ans c ((h, args, r, s') :: tr) e

namespace ULink

/-- **The provider's answers**: a stub call `k args` asked in the stubbed store of a real store
`s` with the layout is answered by a host-free run of the provider's invocation in `s`, the
returned store being the stubbed final store. -/
def provAns (L : ULink) (P : Profile) (σ : Store Nat) (k : Nat) (args : List Val) (r : Result)
    (σ' : Store Nat) : Prop :=
  ∃ (s : Store Nat) (a : Nat) (s' : Store Nat), σ = L.stubS s ∧ L.Layout s ∧
    L.target k = some a ∧
    Steps P (Det.noHost (H := Nat)) (invoke s a args) ⟨s', {}, r.toAdmin⟩ ∧ σ' = L.stubS s'

end ULink

end Silmaril.Wasm.Game
