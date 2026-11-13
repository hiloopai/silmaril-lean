module

public import Silmaril.Wasm.FX.Logic.EveryRun.Defs
public import Silmaril.Wasm.SingleThreaded.Agreement

/-!
# Host calls in the every-run WasmFX logic: definitions

The every-run logic (`Silmaril.Wasm.FX.Logic.EveryRun`) fixes `noHost`. This module names what a
host relation adds to `StepFX'`, through silmaril-lean's `Step.split_host` (a Core step is
host-free or a host call at the `decompose?` redex):

* **`HostStep P host fx c c'`**: a `StepFX'` step that is a host call, in a sequence, label,
  frame or handler: a Core step whose code decomposes (`decompose?`) into a call of host function
  `hh` that `blockFX host fx` lets return (or diverge);
* `SafeH`, `TSafeH`: the every-run predicates of `EveryRun` over `StepFX' P host fx`;
* `AllFX fx s`: every function of the store with host code is an FX function;
* `NoHostCall P host fx c`: no configuration reachable from `c` without host calls makes a host
  step.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.Host

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Stops)
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **A host-call step of `StepFX'`.** -/
inductive HostStep (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :
    ConfigFX H → ConfigFX H → Prop where
  | call {s : Store H} {K : Conts} {f : Frame} {cs : List Admin} {E : SingleThreaded.Ctx} {a : Nat}
      {hh : H} {args : List Val} {d : Config H}
      (hd : decompose? s cs = some (E, a, hh, args))
      (hr : (∃ s' r, blockFX host fx hh s args (.returned s' r) ∧
          d = ⟨s', f, E.fill r.toAdmin⟩) ∨
        (blockFX host fx hh s args .diverged ∧ d = ⟨s, f, cs⟩)) :
      HostStep P host fx ⟨s, K, f, cs.map .core⟩ ⟨d.store, K, d.frame, d.code.map .core⟩
  | seq {s s' : Store H} {K K' : Conts} {f f' : Frame} {vs : List FVal}
      {es es' rest : List AdminFX} (h : HostStep P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
      (hne : vs ≠ [] ∨ rest ≠ []) :
      HostStep P host fx ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩
  | ctxLabel {s s' : Store H} {K K' : Conts} {f f' : Frame} {n : Nat} {k : List InstrFX}
      {es es' : List AdminFX} (h : HostStep P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      HostStep P host fx ⟨s, K, f, [.label n k es]⟩ ⟨s', K', f', [.label n k es']⟩
  | ctxFrame {s s' : Store H} {K K' : Conts} {f fi fi' : Frame} {n : Nat}
      {es es' : List AdminFX} (h : HostStep P host fx ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
      HostStep P host fx ⟨s, K, f, [.frame n fi es]⟩ ⟨s', K', f, [.frame n fi' es']⟩
  | ctxHandler {s s' : Store H} {K K' : Conts} {f f' : Frame} {hs : List HClause}
      {es es' : List AdminFX} (h : HostStep P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      HostStep P host fx ⟨s, K, f, [.handler hs es]⟩ ⟨s', K', f', [.handler hs es']⟩

/-- **Step-indexed every-run safety with host calls.** -/
def SafeH (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) (Q : PostFX H) :
    Nat → ConfigFX H → Prop
  | 0, _ => True
  | n + 1, c => (∀ o, Stops c.store c.frame o c.code → Q c.store c.conts c.frame o) ∧
      ∀ c', StepFX' P host fx c c' → SafeH P host fx Q n c'

/-- **Total every-run safety with host calls.** -/
inductive TSafeH (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) (Q : PostFX H) :
    ConfigFX H → Prop where
  | intro {c : ConfigFX H}
      (hq : ∀ o, Stops c.store c.frame o c.code → Q c.store c.conts c.frame o)
      (hs : ∀ c', StepFX' P host fx c c' → TSafeH P host fx Q c') : TSafeH P host fx Q c

/-- Every function of the store with host code is an FX function (so `blockFX` refuses every
host call the store can make). -/
abbrev AllFX (fx : H → Option FuncFX) (s : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H) (hh : H), s.funcs[a]? = some fi → fi.code = .host hh →
    fx hh ≠ none

/-- No configuration reachable from `c` without host calls makes a host step. -/
def NoHostCall (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) (c : ConfigFX H) :
    Prop :=
  ∀ d, StepsFX' P noHost fx c d → ∀ d', ¬ HostStep P host fx d d'

end Silmaril.Wasm.FX.Logic.Host
