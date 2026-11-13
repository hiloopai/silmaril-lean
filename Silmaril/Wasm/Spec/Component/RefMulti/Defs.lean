module

public import Silmaril.Wasm.Spec.Component.Ref.Defs

@[expose] public section

/-!
# Several export calls on one reference instance

`refSem` (`Silmaril.Wasm.Spec.Component.Ref`) observes **one** export call on a fresh instance.
`refMultiSem prof h σ0` observes **sequences** of export calls on one instance: the machine
configuration returned by each resolved top-level call (`Calls`) is the configuration of the
next call.

* `DoneCall X`: a resolved call of export `exp` on `args` with resolution `res` (`none`: the
  call was cancelled); `DoneCall.events`, `doneEvents`: its events `call · ret (returns res)`.
* `RunCalls prof h names es m k ds m'`: the resolved calls `ds` run one after the other from
  configuration `m` as top-level calls `k, k + 1, …`, export `j` being the function value that
  `es` (the instance's function exports) associates with `names j`; `m'` is the configuration
  after the last one.
* `refMultiW prof h σ0 p`: the complete words of `p`: instantiate `p.comp` with `p.args` from the
  empty store, run resolved calls `ds`, then possibly one more call, pending or with any outcome
  of `callBehaviours` (traps, deadlocks, divergence, resolution); a trap or divergence of the
  instantiation is observed at the first call, as in `refSem`; the first call event alone is
  always a word (as in `refSem`).
* `refMultiTraces`: the prefixes of the complete words; `refMultiSem`: the semantics.

What is not observed: concurrent top-level calls (each call resolves before the next is
issued), host ticks between calls (`Calls` allows ticks only during its own call), import
calls (the host implements them), and stream/future traffic. The one-call restriction of
`refMultiSem` is `refSem` (`refTraces_eq_short`, `Silmaril.Wasm.Spec.Component.RefMulti.Thms`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Spec.Component

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component (Calls)
open Silmaril.Wasm.Component.Runtime (FuncId CallId)
open Silmaril.Wasm.Component.Machine (Config)

/-- A resolved export call: export `exp` called on `args`, resolved with `res` (`none`:
cancelled). -/
structure DoneCall (X : CIface) where
  /-- The export called. -/
  exp : X.Exp
  /-- Its arguments. -/
  args : List RVal
  /-- Its resolution. -/
  res : Option (List RVal)

/-- The events of a resolved call. -/
def DoneCall.events {X : CIface} (d : DoneCall X) : List (CEvent X) :=
  [Event.call d.exp d.args, Event.ret d.exp (.returns d.res)]

/-- The events of a sequence of resolved calls. -/
def doneEvents {X : CIface} (ds : List (DoneCall X)) : List (CEvent X) :=
  ds.flatMap DoneCall.events

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- Resolved top-level calls `k, k + 1, …` of the exports of `ds`, from `m` to `m'`. -/
inductive RunCalls (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) {X : CIface}
    (names : X.Exp → String) (es : List (String × FuncId)) :
    Config E σ → ℕ → List (DoneCall X) → Config E σ → Prop where
  | nil (m : Config E σ) (k : ℕ) : RunCalls prof h names es m k [] m
  | cons {m m₁ m₂ : Config E σ} {k : ℕ} {d : DoneCall X} {ds : List (DoneCall X)} {f : FuncId} :
      es.lookup (names d.exp) = some f →
      Calls prof h.hr h.dispatch m ⟨k⟩ f d.args m₁ (.resolved d.res) →
      RunCalls prof h names es m₁ (k + 1) ds m₂ → RunCalls prof h names es m k (d :: ds) m₂

/-- The words that may follow the resolved calls `ds` on an instance with function exports `es`,
reaching `mₙ`: nothing, a pending call, or a call with any of its behaviours. -/
def lastWords (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) {X : CIface}
    (names : X.Exp → String) (es : List (String × FuncId)) (mₙ : Config E σ) (n : ℕ) :
    Set (List (CEvent X)) :=
  {w | w = [] ∨ (∃ j a, w = [Event.call j a]) ∨
    ∃ j a f b, es.lookup (names j) = some f ∧ b ∈ callBehaviours prof h mₙ ⟨n⟩ f a ∧
      w = [Event.call j a, Event.ret j b]}

/-- The complete words of a reference component observed over several calls on one instance. -/
def refMultiW (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ) {X : CIface}
    (p : RefProg E X) : Set (List (CEvent X)) :=
  {w | w = [] ∨ (∃ j a, w = [Event.call j a]) ∨
    (∃ m₀ inst es ds mₙ u,
      InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args ∧
      RunCalls prof h p.names es m₀ 0 ds mₙ ∧ u ∈ lastWords prof h p.names es mₙ ds.length ∧
      w = doneEvents ds ++ u) ∨
    (∃ j a, InstResult.traps ∈ instBehaviours prof h (initConfig σ0) p.comp p.args ∧
      w = [Event.call j a, Event.ret j .traps]) ∨
    (∃ j a, InstResult.diverges ∈ instBehaviours prof h (initConfig σ0) p.comp p.args ∧
      w = [Event.call j a, Event.ret j .diverges])}

/-- The traces of a reference component over several calls on one instance: prefixes of its
complete words. -/
def refMultiTraces (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ)
    {X : CIface} (p : RefProg E X) : Set (List (CEvent X)) :=
  {t | ∃ w ∈ refMultiW prof h σ0 p, t <+: w}

/-- The multi-call traces are good. -/
theorem refMultiTraces_good (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ)
    {X : CIface} (p : RefProg E X) : Good (refMultiTraces prof h σ0 p) where
  nil_mem := ⟨[], .inl rfl, List.nil_prefix⟩
  of_prefix := fun ⟨w, hw, ht⟩ hs => ⟨w, hw, hs.trans ht⟩

/-- **The reference semantics over several calls on one instance.** -/
abbrev refMultiSem (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ) :
    Semantics CFn (List RVal) Outcome where
  Prog := RefProg E
  traces p := refMultiTraces prof h σ0 p
  good p := refMultiTraces_good prof h σ0 p

end Silmaril.Wasm.Spec.Component
