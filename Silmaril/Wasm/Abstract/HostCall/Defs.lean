module

public import Silmaril.Games.Abstract.HostRun.Defs
public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.SingleThreaded.Thread

/-!
# Core 3.0 host calls as a relational host (stage H2, first step)

A Core 3.0 host semantics `host : HostSemantics H` is a relation. For a host
function `h`, a store `s` and arguments `vs`, it allows the outcomes
`.returned s' r` and `.diverged`, possibly several, possibly none. This module
reads it as a `HostRel` of `Silmaril.Games.Abstract.HostRun`:

* `wasmHostSig H`: a host import call is a triple (host function, store,
  arguments), answered by (store, result);
* `coreHostRel host`: an answer `(s', r)` is allowed when `host` returns it, and
  divergence when `host` diverges. A call with no outcome is `blocked`.

The store is part of the call and of the answer, so a log of host answers
fixes every store update the host makes.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Host import calls: host function, store and arguments, answered by store and result. -/
abbrev wasmHostSig (H : Type) : Sig.{0} := ⟨H × Store H × List Val, fun _ => Store H × Result⟩

/-- **A Core 3.0 host semantics as a relational host.** -/
def coreHostRel (host : HostSemantics H) : HostRel (wasmHostSig H) := fun m o =>
  match o with
  | .answer p => host m.1 m.2.1 m.2.2 (.returned p.1 p.2)
  | .diverge => host m.1 m.2.1 m.2.2 .diverged

/-- A Core 3.0 run of exactly `n` steps (the measure of the whole-run backward
simulation: a loop re-runs its tree on a strictly shorter run). -/
inductive StepsN (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    Nat → Config H → Config H → Prop where
  | refl (c : Config H) : StepsN P host 0 c c
  | head {n : Nat} {c₁ c₂ c₃ : Config H} :
      Step P host c₁ c₂ → StepsN P host n c₂ c₃ → StepsN P host (n + 1) c₁ c₃

/-- **A host whose answers are typed**: the second half of Core's `HostOk`, without
its first half (that every call has an outcome). A host may have no outcome
for a call (the `blocked` observation), may diverge, and may answer in several
ways; every answer it gives keeps the store well-typed, extends it, and has the
declared result types. -/
def HostTyped (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (fi : FuncInst H) (h : H) (vs : List Val) (ps rs : Validation.Ty (.list .val)),
    StoreOk s → fi ∈ s.funcs → fi.code = .host h → Validation.Expand fi.type (.func ps rs) →
    List.Forall₂ (ValOk s) vs ps.toList →
      ∀ out, host h s vs out → match out with
        | .diverged => True
        | .returned s' r => StoreOk s' ∧ Extend s s' ∧ ResultTyped s' r rs.toList

/-- The host that also diverges wherever `host` has no outcome. It has every
outcome `host` has, so every Core step with `host` is one with it. -/
def totalize (host : HostSemantics H) : HostSemantics H := fun h s vs out =>
  host h s vs out ∨ (out = .diverged ∧ ∀ o, ¬ host h s vs o)

/-! ## Host events of Core runs -/

/-- **A Core step labelled by its host event.** `none`: a host-free step, or a stutter at a
host call the host may diverge on. `some e`: the answered host call `e.1 = (hh, s, us)` at
the configuration's callout (`decompose?`), answered `e.2 = (s', r)` by the host. -/
def HEvStep (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (c : Config H) :
    Option (Call (wasmHostSig H)) → Config H → Prop
  | none, c' => Step P (fun _ _ _ _ => False) c c' ∨
      (c' = c ∧ ∃ E a hh us, SingleThreaded.decompose? c.store c.code = some (E, a, hh, us) ∧
        host hh c.store us .diverged)
  | some e, c' => ∃ E a, SingleThreaded.decompose? c.store c.code = some (E, a, e.1.1, e.1.2.2) ∧
      e.1.2.1 = c.store ∧ host e.1.1 c.store e.1.2.2 (.returned e.2.1 e.2.2) ∧
      c' = ⟨e.2.1, c.frame, E.fill e.2.2.toAdmin⟩

/-- A finite labelled run, with its host events in order. -/
inductive EvRun (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    Config H → List (Call (wasmHostSig H)) → Config H → Prop where
  | refl (c : Config H) : EvRun P host c [] c
  | silent {c₁ c₂ c₃ : Config H} {cs : List (Call (wasmHostSig H))} :
      HEvStep P host c₁ none c₂ → EvRun P host c₂ cs c₃ → EvRun P host c₁ cs c₃
  | event {c₁ c₂ c₃ : Config H} {e : Call (wasmHostSig H)} {cs : List (Call (wasmHostSig H))} :
      HEvStep P host c₁ (some e) c₂ → EvRun P host c₂ cs c₃ → EvRun P host c₁ (e :: cs) c₃

/-- **Quiescent divergence**: an infinite run without host events. -/
def Quiet (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  Silmaril.InfiniteTrace (fun a b => HEvStep P host a none b) c

/-- **A productive infinite run with host events `ω`**: one Core run from `c`, cut into
segments `g n ⟶ g (n + 1)`, each event-free steps and then the host event `ω n`. -/
def CoreInf (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (c : Config H)
    (ω : Nat → Call (wasmHostSig H)) : Prop :=
  ∃ g : Nat → Config H, g 0 = c ∧ ∀ n, ∃ c₁,
    Relation.ReflTransGen (fun a b => HEvStep P host a none b) (g n) c₁ ∧
      HEvStep P host c₁ (some (ω n)) (g (n + 1))

end Silmaril.Wasm.Abstract
