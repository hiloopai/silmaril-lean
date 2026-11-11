module

public import Silmaril.Wasm.FX.Asyncify.Tool.Pass.Defs
public import Mathlib.Data.Set.Defs

/-!
# Hosts, the two closed systems, and their behaviours

A host is a deterministic state machine answering import calls (`Host`). Behaviours are those of
an export call closed by the host, with the final host state observed (so every trace of import
calls and answers is observable, by choosing the host state to record it).

* **Source** (`srcStep`): the machine; at an import call (`Res.ask f args`), the host answers in
  one step and its answers (`fit`ted to the import's result count) are pushed.
* **Target** (`tgtStep`), the asyncify protocol: the machine never calls an import. When the
  export returns with `state = 1` (unwound), the host reads the request (import index at word 0,
  arguments at words `1 …`), writes its answers at words `0 …`, sets `state := 2` and calls the
  same export again with the same arguments. When the export returns with `state ≠ 1`, its results
  are final.

`beh` gives the set of behaviours (`done`, `trap` or `diverges`) of a deterministic system.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

/-- A deterministic host with state `σ`: answers to an import index and arguments. -/
structure Host (σ : Type) where
  answer : σ → Nat → List W → σ × List W

/-- `vs` cut or padded with zeros to `m` words. -/
def fit (m : Nat) (vs : List W) : List W := (vs ++ List.replicate m 0).take m

/-- Write words `ws` at byte addresses `a, a+4, …`. -/
def writeWords (mem : Nat → W) (a : Nat) : List W → Nat → W
  | [] => mem
  | w :: ws => writeWords (upd mem a w) (a + 4) ws

/-- Observable behaviours. -/
inductive Obs (σ : Type) where
  | done (vs : List W) (s : σ)
  | trap (s : σ)
  | diverges

/-- The result of a step of a closed system. -/
inductive SRes (X σ : Type) where
  | next (x : X)
  | stop (o : Obs σ)

/-- At most `n` steps. -/
def runN {X σ : Type} (step : X → SRes X σ) : Nat → X → SRes X σ
  | 0, x => .next x
  | n + 1, x =>
    match step x with
    | .next x' => runN step n x'
    | .stop o => .stop o

/-- The behaviours of a deterministic system from `x`. -/
def beh {X σ : Type} (step : X → SRes X σ) (x : X) : Set (Obs σ) :=
  {b | ∃ n, runN step n x = .stop b} ∪
  {b | b = .diverges ∧ ∀ n, ∃ x', runN step n x = .next x'}

/-- Push `vs` on the top frame. -/
def pushTop (c : Cfg) (vs : List W) : Cfg :=
  match c.frames with
  | [] => c
  | fr :: rest => { c with frames := { fr with ops := vs ++ fr.ops } :: rest }

/-- The source system: the machine closed by the host. -/
def srcStep {σ : Type} (E : Env) (H : Host σ) : Cfg × σ → SRes (Cfg × σ) σ
  | (c, s) =>
    match step E c with
    | .next c' => .next (c', s)
    | .done vs _ => .stop (.done vs s)
    | .trap => .stop (.trap s)
    | .ask f args c' =>
      let r := H.answer s f args
      .next (pushTop c' (fit ((E.imps[f]?).map Prod.snd |>.getD 0) r.2).reverse, r.1)

/-- A state of the target system: the machine, the host, and the export call to repeat. -/
structure TSt (σ : Type) where
  cfg : Cfg
  host : σ
  fid : Nat
  args : List W

/-- The target system: the machine and the asyncify host protocol. -/
def tgtStep {σ : Type} (E : Env) (H : Host σ) (t : TSt σ) : SRes (TSt σ) σ :=
  match step E t.cfg with
  | .next c' => .next { t with cfg := c' }
  | .done vs c' =>
    if c'.globals[0]? = some 1 then
      let f := (c'.mem 0).toNat
      match E.imps[f]?, E.fns[t.fid - E.imps.length]? with
      | some (n, m), some fn =>
        let r := H.answer t.host f ((List.range n).map fun i => c'.mem (4 * (i + 1)))
        .next ⟨⟨[entry t.fid fn t.args], c'.globals.set 0 2, writeWords c'.mem 0 (fit m r.2)⟩,
          r.1, t.fid, t.args⟩
      | _, _ => .stop (.trap t.host)
    else .stop (.done vs t.host)
  | .trap => .stop (.trap t.host)
  | .ask _ _ _ => .stop (.trap t.host)

/-- The source configuration of a call of defined function `e` (`none` if there is none). -/
def srcInit (E : Env) (e : Nat) (args : List W) : Option Cfg :=
  if E.imps.length ≤ e then
    (E.fns[e - E.imps.length]?).map fun fn => ⟨[entry e fn args], [], fun _ => 0⟩
  else none

/-- The target state of the same call. -/
def tgtInit {σ : Type} (P : Prog) (e : Nat) (args : List W) (s : σ) : Option (TSt σ) :=
  (srcInit (asyncifyProg P) e args).map fun c => ⟨{ c with globals := P.tGlobals }, s, e, args⟩

/-- The shadow stack never needs more than the 32-bit address space: at every source state
reachable from `x`, `SB + 4 F · depth < 2 ^ 32`. -/
def DepthBound {σ : Type} (P : Prog) (H : Host σ) (x : Cfg × σ) : Prop :=
  ∀ n y, runN (srcStep P.env H) n x = .next y → P.sb + 4 * P.frameWords * y.1.frames.length < 2 ^ 32

end Silmaril.Wasm.FX.Asyncify.Tool
