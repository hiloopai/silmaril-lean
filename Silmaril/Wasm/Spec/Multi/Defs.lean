module

public import Silmaril.Wasm.Spec.Wasm.Thms
public import Silmaril.Wasm.Spec.Basic.Thms
public import Silmaril.Wasm.Game.Adequacy.Thms

@[expose] public section

/-!
# Multi-call specifications: sequences of export calls on one instance

The traces of `wasmSem P` already contain sequences of export calls on one instance: the strategy
persists the store from one call to the next. This topic gives the sentences and the closed-world
reading of such sequences:

* `exportHist`: the logic of **export histories**. A formula at `X` is a predicate `Φ` on the
  sequence of export events (calls with arguments, returns with behaviours); a trace satisfies it
  when its export events do. Since traces are prefix closed, `Φ` is checked on every prefix of
  every session (so it is a safety reading; e.g. "results increase", "`get` after `set v`
  returns `v`").
* `RetPost.toHist`: a return postcondition is an export-history formula (a logic map).
* `Session P I K s l`: a **closed-world session** of Core 3.0: the export calls `l` (each with
  its typed answer) run one after the other, each a Core run `Steps P (hostOf I.imports K)` of
  `$invoke` from the store left by the previous one, ending in a result answered as recorded.
* `sessionEv l`: the upper (export) events of a session; `sessionEvents l`: the same as
  specification events.

Theorems in `Silmaril.Wasm.Spec.Multi.Thms`. A Silmaril addition.
-/

namespace Silmaril.Wasm.Spec.Multi

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {Ty A R : Type}

/-- Export histories at an interface. -/
abbrev Hist (A R : Type) (X : Iface Ty) : Type := List (SideEv A R X.exports.length)

/-- **The logic of export histories.** -/
abbrev exportHist (Ty A R : Type) : Logic Ty A R :=
  Logic.ofTrace (fun X => Hist A R X → Prop) fun Φ t => Φ (exportEvents t)

/-- Return postconditions as export-history formulas. -/
def RetPost.toHist (Ty A R : Type) : LogicMap (retPost Ty A R) (exportHist Ty A R) :=
  LogicMap.ofTrace (fun φ h => ∀ r, SideEv.ans φ.exp r ∈ h → φ.post r) fun _ _ =>
    forall_congr' fun _ => imp_congr_left mem_exportEvents_iff

/-- An export call with its answer. -/
abbrev Call (I : ScalarInstance) : Type := Σ f : I.F.Op, I.F.Ar f

/-- **A closed-world session of Core 3.0 export calls** from store `s`, against the host induced
by `K`, at profile `P`: each call is a Core run from the store left by the previous one. -/
inductive Session (P : Profile) (I : ScalarInstance) (K : Env I.E) : Store Nat → List (Call I) → Prop
  /-- No call. -/
  | nil (s : Store Nat) : Session P I K s []
  /-- A call `f` run by Core to a result answered as `w`, then the rest from the store it
  leaves. -/
  | cons {s : Store Nat} {f : I.F.Op} {w : I.F.Ar f} {rest : List (Call I)} (c' : Config Nat)
      (r : Result) (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
      (final : c'.code = r.toAdmin) (ans : Answer.ofResult? (I.exports.get f.1) r = some w)
      (next : Session P I K c'.store rest) : Session P I K s (⟨f, w⟩ :: rest)

/-- The export events of a session, as moves. -/
def sessionEv {I : ScalarInstance} : List (Call I) → List (Ev I.F)
  | [] => []
  | ⟨f, w⟩ :: rest => .ask f :: .ans f w :: sessionEv rest

/-- The export events of a session of a program at `X`, as specification events. -/
def sessionEvents {X : WIface} : List (Σ f : (ifaceSig X.exports).Op, (ifaceSig X.exports).Ar f) →
    Hist (List Val) (Behaviour Val) X
  | [] => []
  | ⟨f, w⟩ :: rest =>
    .ask f.1 f.2.1 :: .ans f.1 (Answer.toBehaviour (ft := X.exports.get f.1) w) :: sessionEvents rest

end Silmaril.Wasm.Spec.Multi
