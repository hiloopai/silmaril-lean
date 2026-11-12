module

public import Silmaril.Wasm.Game.Machine.Defs

/-!
# Determinism and statelessness modulo traps and imports (Core 3.0)

Definitions for Core 3.0 code under silmaril-lean's `Step P host` at an **arbitrary** profile
`P`. The profile carries every permitted nondeterminism (NaN payloads, relaxed SIMD, `$ND`,
`memory.grow`/`table.grow` failure); nothing here assumes a deterministic profile. Subsets of
Wasm 3.0 are meant to be syntactic predicates on code, so every result about a subset is a
result about full Wasm 3.0 code that happens to lie in the subset.

## Imports as a shared oracle

A host call is not a host-free step: at a host-call redex (`decompose?`) the code waits for the
environment. The environment is modelled as an **oracle shared by the runs being compared**: a
run records its answered import calls as a list of `Call`s (host code, arguments, answer), and
two runs are compared only when they saw the *same* list of calls and answers. Since the list
records the calls themselves, two runs with the same list made the same import calls with the
same arguments; an oracle answering as a function of the call history gives both runs the same
answers exactly as long as they make the same calls. The host answers with a Core `Result`
and does not write the store (as in the game semantics of `Silmaril.Wasm.Game`).

* `Runs P c tr d`: from `c`, host-free steps (`Steps P Det.noHost`), interrupted by the import
  calls of `tr`, each resumed with its answer (`resumeAt`), reach `d`;
* `OutAt d o`: `d` is a **non-trapping stop** with output `o`: a result other than a trap
  (`Out.ret r`, `r ≠ .trap`; values or an uncaught exception) or a pending import call
  (`Out.call h args`). Traps, divergence and stuck configurations have no output.

## Determinism modulo traps and imports

* `DetCfg P c`: two runs from `c` with the same call history that both reach a non-trapping stop
  have the same output and the same store. Since the history includes the pending call, two
  runs agree on every import call they both make, on its arguments and on the store at that
  call; a trap or divergence on one side is allowed.
* `DetCall P s a vs := DetCfg P (invoke s a vs)`; per function, `DetFn P s a` for every typed
  argument list (`InvokeOk`).
* per module (instance): `Entry` is the set of entry function addresses (exports; for an
  instance `I`, `fun a => ∃ j, I.addr j = a`), `CallReach P Entry s₀ s` the stores reachable from
  `s₀` by finished entry calls (any result, traps included: the store persists across calls)
  against any answers; `DetModule P Entry s₀`: every entry is `DetFn` at every reachable store.
  `DetInst P c₀ Entry` adds an instantiation configuration `c₀` (segment initialisation and the
  start function, e.g. `IsSpecInstanceAt`'s): `c₀` is `DetCfg` and the module is `DetModule`
  from every store at which `c₀` returns without trapping.

## Statelessness modulo traps and imports

* `ObsAgree P c₁ c₂`: two runs, from `c₁` and from `c₂`, with the same call history that both
  reach a non-trapping stop have the same output (stores are not compared).
* `StatelessFn P S a`: for any two stores satisfying `S` and the same typed arguments, the
  invocations of `a` agree (`ObsAgree`); `S` is the set of call states considered, for example
  the reachable stores of the module, or every store holding the same function at `a`.
* `StatelessModule P Entry s₀`: every entry is `StatelessFn` over `CallReach P Entry s₀`.
  Since `s₀` is reachable, outputs after any history of calls are those of the first call.

## Oracle hosts

`oracleHost F` is the Core host answering `F h args` and leaving the store unchanged, for a
function `F` of the call; it is the history-independent instance of the oracle reading. The
headline theorems (`Silmaril.Wasm.Det.Core.Thms`) are stated for plain Core runs
`Steps P (oracleHost F)`.

## Sufficient conditions

* `Doomed P c`: no host-free run from `c` reaches a non-trapping stop (it traps, diverges or
  gets stuck);
* `SegDet P c`: host-free runs from `c` reach at most one non-trapping stop (as a
  configuration);
* `StepDetAt P c`: two host-free steps from `c` are equal or one of them is `Doomed`. This is
  what `Silmaril.Proofs.Wasm.Game.Choice.soft_join` gives when every `Soft` step from `c` is
  `Doomed` (two steps are equal or both `Soft`);
* `DetUpTo P o c`: every host-free step from `c` at `P` is a step at the deterministic profile
  `profile o`, or `Doomed`;
* `Closed P Inv`: `Inv` is closed under host-free steps and under resuming an import call with
  any answer;
* `LockStep P R`: a relation between the configurations of two runs that is preserved in lock
  step (up to `Doomed` steps), relates stops to stops with equal outputs, and is preserved by
  resuming the same call with the same answer; it gives `ObsAgree` (output determinism up to a
  relation, e.g. NaN payloads, and statelessness for two related call states).

New definitions (no source file).
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## Runs against a shared oracle -/

/-- An answered import call: the host code (for instances, the import index), the arguments
and the environment's answer. -/
structure Call where
  host : Nat
  args : List Val
  ans : Result

/-- The output of a non-trapping stop. -/
inductive Out where
  /-- A result other than a trap: values, or an uncaught exception. -/
  | ret (r : Result)
  /-- A pending import call. -/
  | call (h : Nat) (args : List Val)

/-- The configuration `c` is a non-trapping stop with output `o`. -/
inductive OutAt (c : Config Nat) : Out → Prop where
  | ret {r : Result} (hr : r ≠ .trap) (hc : c.code = r.toAdmin) : OutAt c (.ret r)
  | call {E : Ctx} {a h : Nat} {args : List Val}
      (hd : decompose? c.store c.code = some (E, a, h, args)) : OutAt c (.call h args)

/-- The configuration `c` is a non-trapping stop. -/
def Stop (c : Config Nat) : Prop := ∃ o, OutAt c o

/-- Resume the import call at context `E` of `d` with the answer `r` (the store is kept). -/
def resumeAt (d : Config Nat) (E : Ctx) (r : Result) : Config Nat :=
  ⟨d.store, d.frame, E.fill r.toAdmin⟩

/-- Runs from `c` to `d` whose answered import calls are `tr`: host-free Core steps at `P`,
interrupted by import calls (host-call redexes found by `decompose?`), each resumed with its
answer. -/
inductive Runs (P : Profile) : Config Nat → List Call → Config Nat → Prop where
  | stop {c d : Config Nat} (hs : Steps P (Det.noHost (H := Nat)) c d) : Runs P c [] d
  | call {c d e : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} {r : Result}
      {tr : List Call} (hs : Steps P (Det.noHost (H := Nat)) c d)
      (hd : decompose? d.store d.code = some (E, a, h, args))
      (hk : Runs P (resumeAt d E r) tr e) : Runs P c (⟨h, args, r⟩ :: tr) e

/-! ## Determinism and statelessness -/

/-- **Determinism modulo traps and imports** of a configuration: two runs from `c` with the
same import calls and answers that both reach a non-trapping stop have the same output and the
same store. -/
def DetCfg (P : Profile) (c : Config Nat) : Prop :=
  ∀ tr d₁ d₂ o₁ o₂, Runs P c tr d₁ → Runs P c tr d₂ → OutAt d₁ o₁ → OutAt d₂ o₂ →
    o₁ = o₂ ∧ d₁.store = d₂.store

/-- **Output agreement modulo traps and imports**: two runs, from `c₁` and from `c₂`, with the
same import calls and answers that both reach a non-trapping stop have the same output. -/
def ObsAgree (P : Profile) (c₁ c₂ : Config Nat) : Prop :=
  ∀ tr d₁ d₂ o₁ o₂, Runs P c₁ tr d₁ → Runs P c₂ tr d₂ → OutAt d₁ o₁ → OutAt d₂ o₂ → o₁ = o₂

/-- One invocation of the function at address `a` on `vs` is deterministic modulo traps and
imports. -/
def DetCall (P : Profile) (s : Store Nat) (a : Nat) (vs : List Val) : Prop :=
  DetCfg P (invoke s a vs)

/-- **Per function**: every typed invocation of the function at `a` in `s` is deterministic
modulo traps and imports. -/
def DetFn (P : Profile) (s : Store Nat) (a : Nat) : Prop :=
  ∀ vs, InvokeOk s a vs → DetCall P s a vs

/-- **Per function, statelessness**: typed invocations of `a` on the same arguments in any two
call states satisfying `S` have the same non-trapping outputs, against the same answers. -/
def StatelessFn (P : Profile) (S : Store Nat → Prop) (a : Nat) : Prop :=
  ∀ s₁ s₂ vs, S s₁ → S s₂ → InvokeOk s₁ a vs → InvokeOk s₂ a vs →
    ObsAgree P (invoke s₁ a vs) (invoke s₂ a vs)

/-- The call states of a module: the stores reachable from `s₀` by finished calls of entry
functions (any typed arguments, any answers, any result including traps). -/
inductive CallReach (P : Profile) (Entry : Nat → Prop) (s₀ : Store Nat) : Store Nat → Prop where
  | init : CallReach P Entry s₀ s₀
  | call {s : Store Nat} {a : Nat} {vs : List Val} {tr : List Call} {d : Config Nat}
      {r : Result} (hs : CallReach P Entry s₀ s) (ha : Entry a) (hok : InvokeOk s a vs)
      (hr : Runs P (invoke s a vs) tr d) (hd : d.code = r.toAdmin) :
      CallReach P Entry s₀ d.store

/-- **Per module**: every entry function is deterministic modulo traps and imports at every
reachable call state. -/
def DetModule (P : Profile) (Entry : Nat → Prop) (s₀ : Store Nat) : Prop :=
  ∀ s, CallReach P Entry s₀ s → ∀ a, Entry a → DetFn P s a

/-- **Per module, statelessness**: every entry function is stateless over the reachable call
states. -/
def StatelessModule (P : Profile) (Entry : Nat → Prop) (s₀ : Store Nat) : Prop :=
  ∀ a, Entry a → StatelessFn P (CallReach P Entry s₀) a

/-- **Per instance with an instantiation phase** `c₀` (segment initialisation and the start
function): `c₀` is deterministic, and the module is deterministic from every store at which
`c₀` finishes without trapping. -/
def DetInst (P : Profile) (c₀ : Config Nat) (Entry : Nat → Prop) : Prop :=
  DetCfg P c₀ ∧ ∀ tr d (r : Result), Runs P c₀ tr d → d.code = r.toAdmin → r ≠ .trap →
    DetModule P Entry d.store

/-! ## Oracle hosts and profiles -/

/-- The Core host answering the call `h args` with `F h args`, leaving the store unchanged. -/
def oracleHost (F : Nat → List Val → Result) : HostSemantics Nat :=
  fun h s args out => out = .returned s (F h args)

/-- The answers of `tr` are those of `F`. -/
def Answers (F : Nat → List Val → Result) (tr : List Call) : Prop :=
  ∀ x ∈ tr, x.ans = F x.host x.args

/-- Every host-free step at `P'` is a host-free step at `P` (`P'` refines `P`). -/
def ProfileLE (P' P : Profile) : Prop :=
  ∀ c c' : Config Nat, Step P' (Det.noHost (H := Nat)) c c' → Step P Det.noHost c c'

/-! ## Sufficient conditions -/

/-- No host-free run from `c` reaches a non-trapping stop. -/
def Doomed (P : Profile) (c : Config Nat) : Prop :=
  ∀ d, Steps P (Det.noHost (H := Nat)) c d → ¬ Stop d

/-- Host-free runs from `c` reach at most one non-trapping stop. -/
def SegDet (P : Profile) (c : Config Nat) : Prop :=
  ∀ d₁ d₂, Steps P (Det.noHost (H := Nat)) c d₁ → Steps P Det.noHost c d₂ → Stop d₁ → Stop d₂ →
    d₁ = d₂

/-- Two host-free steps from `c` are equal, or one of them is `Doomed`. -/
def StepDetAt (P : Profile) (c : Config Nat) : Prop :=
  ∀ e₁ e₂, Step P (Det.noHost (H := Nat)) c e₁ → Step P Det.noHost c e₂ →
    e₁ = e₂ ∨ Doomed P e₁ ∨ Doomed P e₂

/-- Every host-free step from `c` at `P` is a step at the deterministic profile `profile o`, or
`Doomed`. -/
def DetUpTo (P : Profile) (o : GrowOracle) (c : Config Nat) : Prop :=
  ∀ e, Step P (Det.noHost (H := Nat)) c e → Step (profile o) Det.noHost c e ∨ Doomed P e

/-- `Inv` is closed under host-free steps and under resuming an import call with any answer. -/
structure Closed (P : Profile) (Inv : Config Nat → Prop) : Prop where
  step : ∀ c d, Inv c → Step P (Det.noHost (H := Nat)) c d → Inv d
  resume : ∀ c (E : Ctx) (a h : Nat) (args : List Val) (r : Result), Inv c →
    decompose? c.store c.code = some (E, a, h, args) → Inv (resumeAt c E r)

/-- A **lock-step relation** between configurations of two runs: related configurations step to
related ones (or one side is `Doomed`), are non-trapping stops together, have equal outputs,
and stay related when the same import call is resumed with the same answer. It yields output
agreement (`obsAgree_of_lockStep`): with `R` relating a configuration to itself up to NaN
payloads it gives output determinism; with `R` relating two call states that agree on what the
code reads it gives statelessness. -/
structure LockStep (P : Profile) (R : Config Nat → Config Nat → Prop) : Prop where
  step : ∀ x y x' y', R x y → Step P (Det.noHost (H := Nat)) x x' → Step P Det.noHost y y' →
    R x' y' ∨ Doomed P x' ∨ Doomed P y'
  stop_left : ∀ x y, R x y → Stop x → Stop y
  stop_right : ∀ x y, R x y → Stop y → Stop x
  out : ∀ x y o₁ o₂, R x y → OutAt x o₁ → OutAt y o₂ → o₁ = o₂
  resume : ∀ x y (E₁ E₂ : Ctx) (a₁ a₂ h : Nat) (args : List Val) (r : Result), R x y →
    decompose? x.store x.code = some (E₁, a₁, h, args) →
    decompose? y.store y.code = some (E₂, a₂, h, args) → R (resumeAt x E₁ r) (resumeAt y E₂ r)

end Silmaril.Wasm.Det.Core
