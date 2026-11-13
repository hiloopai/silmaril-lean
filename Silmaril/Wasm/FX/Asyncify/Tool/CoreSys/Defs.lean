module

public import Silmaril.Wasm.FX.Asyncify.Tool.CoreSim.Defs

/-!
# The asyncify host protocol on Core 3.0 stores

The target system of the tool (`tgtStepB`, `Silmaril.Wasm.FX.Asyncify.Tool.Bounded`) runs rounds:
an export call of the asyncified program on the frame machine; when it returns with
`state = 1` (unwound), the host reads the request (import index at word 0, arguments at words
`1 …`), answers, writes the answers at words `0 …`, sets `state := 2` and calls the export
again. Here the same protocol on Core 3.0 configurations of silmaril-lean's `Step`:

* `callA e args`: the Core code of the export call (arguments as values, `call e`);
* `HostUpd`: a store after the host's update: it holds the program, the globals with
  `state := 2`, and the memory with the answers written (as aligned words of its bytes);
* `CoreObs … e args s h o`: the export call of `e` in store `s`, with host state `h`, has
  observation `o` on Core: a Core run of the call to values with `state ≠ 1` (`done`), a Core
  run to a trap (`trap`), a run to values with `state = 1` and an invalid request (`badReq`),
  or such a run with a valid request (`round`) after which, **for every** store that realizes
  the host's update, the next round has observation `o`. Request and answers are aligned words
  in bounds of the store's memory (`MemAre`), so they are determined by its bytes.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The Core code of an export call of defined function `e` with arguments `args`. -/
def callA (e : Nat) (args : List W) : List Admin :=
  vals (args.map Val.i32) ++ [.plain (.call (fidx e))]

/-- A store after the host's update: the program, the globals `gs` with `state := 2`, and the
memory `mem` with the words `ws` written from address 0. -/
def HostUpd {H : Type} (cap : Nat) (E : Env) (mi : ModuleInst) (s : Store H) (gs : List W)
    (mem : Nat → W) (ws : List W) : Prop :=
  HoldsProg s mi E ∧ GlobalsAre s ⟨[], mi⟩ (gs.set 0 2) ∧
    MemAre s ⟨[], mi⟩ (writeWords mem 0 ws) cap

/-- The host's answer to the request in memory `mem`. -/
def hostAns {σ : Type} (Hh : Host σ) (h : σ) (n : Nat) (mem : Nat → W) : σ × List W :=
  Hh.answer h (mem 0).toNat ((List.range n).map fun i => mem (4 * (i + 1)))

/-- **Observations of the asyncify protocol on Core 3.0.** -/
inductive CoreObs {H σ : Type} (Pf : Numerics.Profile) (host : HostSemantics H) (cap : Nat)
    (E : Env) (Hh : Host σ) (mi : ModuleInst) (e : Nat) (args : List W) :
    Store H → σ → Obs σ → Prop where
  | done {s s' : Store H} {h : σ} {vs gs : List W} :
      Execution.Core.Steps Pf host ⟨s, ⟨[], mi⟩, callA e args⟩ ⟨s', ⟨[], mi⟩, stackA vs⟩ →
      GlobalsAre s' ⟨[], mi⟩ gs → gs[0]? ≠ some 1 → CoreObs Pf host cap E Hh mi e args s h (.done vs h)
  | trap {s : Store H} {h : σ} {C' : Config H} :
      Execution.Core.Steps Pf host ⟨s, ⟨[], mi⟩, callA e args⟩ C' → C'.code = [.trap] →
      CoreObs Pf host cap E Hh mi e args s h (.trap h)
  | badReq {s s' : Store H} {h : σ} {vs gs : List W} {mem : Nat → W} :
      Execution.Core.Steps Pf host ⟨s, ⟨[], mi⟩, callA e args⟩ ⟨s', ⟨[], mi⟩, stackA vs⟩ →
      GlobalsAre s' ⟨[], mi⟩ gs → MemAre s' ⟨[], mi⟩ mem cap → gs[0]? = some 1 → 4 ≤ cap →
      E.imps[(mem 0).toNat]? = none → CoreObs Pf host cap E Hh mi e args s h (.trap h)
  | round {s s' : Store H} {h : σ} {vs gs : List W} {mem : Nat → W} {n m : Nat} {o : Obs σ} :
      Execution.Core.Steps Pf host ⟨s, ⟨[], mi⟩, callA e args⟩ ⟨s', ⟨[], mi⟩, stackA vs⟩ →
      GlobalsAre s' ⟨[], mi⟩ gs → MemAre s' ⟨[], mi⟩ mem cap → gs[0]? = some 1 →
      E.imps[(mem 0).toNat]? = some (n, m) → 4 * (n + 1) ≤ cap → 4 * m ≤ cap →
      (∀ s'', HostUpd cap E mi s'' gs mem (fit m (hostAns Hh h n mem).2) →
        CoreObs Pf host cap E Hh mi e args s'' (hostAns Hh h n mem).1 o) →
      CoreObs Pf host cap E Hh mi e args s h o

end Silmaril.Wasm.FX.Asyncify.Tool
