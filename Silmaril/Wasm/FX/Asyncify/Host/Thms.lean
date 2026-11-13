module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Host.Sim
public import Silmaril.Wasm.FX.Asyncify.Selective.Thms
public import Silmaril.Wasm.Atlas.Defs

/-!
# Asyncify with a host: results

The header of `Defs`: the host-closed kernel `hsstep` (a `suspend` that no frame handles is a
blocking call answered by a deterministic host `KHost`), the host-closed asyncify machine
`htstep` (unwinding to the root, the host's answer, rewinding: the tool's protocol), and the
instance `hostScheme V σ o`.

* **`host_correct`**: for every optimization `o`, on the fragment of a sound analysis
  (`Sound o.instr P`), under every host and from every host state, a call has the same
  behaviours in the host-closed kernel and on `compPO o P` under the host protocol. Proof: a
  stuttering simulation (`Host.simRel_host`): the selective relation of `SelSim` with equal host
  states; a blocking call is matched by unwinding every frame, the host step at the root, and
  rewinding every frame.
* `host_compile`: the instance compiles with **the family's compiler**: `hostScheme V σ o` and
  `scheme V .unwind o` produce the same code; they differ only in how the machines are closed
  (a host at the root instead of a trap).
* `host_whole` (no hypothesis), `host_analyze` (the computed analysis of `Selective`, no
  hypothesis).
* `host_comorphism`: a comorphism of behaviour charts, equal on every sentence, from the
  host-closed kernel on the fragment to the host-closed target.
* `blocking_example`: a program whose callee makes a blocking call returns `[214, 5]` in the
  source, in the whole-program target and in the target of the computed analysis.

**The tool as this instance.** The tool `wasm-asyncify` implements the same strategy on Core
code: a blocking import call is the kernel's unhandled `suspend` (tag: the import index, payload:
the arguments), its call-site checks are the `chk` after each call, unwinding to the shadow stack
returns from the export with `state = 1`, and the host re-calls the export with `state = 2`,
which rewinds. The translation of the tool's programs into the kernel and the simulation of
the tool's frame machine by `hsstep` are in `Silmaril.Wasm.FX.Asyncify.Bridge` (`tool_src_kernel`,
with host states observed by `Host.Obs`); the target half is open (`Task.tool_tgt_sim`, see
`docs/projects/wasm-binaryen-tooling.md`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Host

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.Atlas

variable {V σ : Type}

/-- **The host instance is correct for every optimization, on its fragment.** -/
theorem host_correct (o : Opt) : (hostScheme V σ o).Correct :=
  fun P hP test H s f args =>
    (Silmaril.Proofs.Wasm.FX.Asyncify.Host.beh_host o P test H f args hP s).symm

/-- The host instance compiles with the family's compiler. -/
theorem host_compile (o : Opt) :
    (hostScheme V σ o).compile = (scheme V .unwind o).compile := rfl

/-- Whole-program instrumentation under a host: no hypothesis. -/
theorem host_whole (P : Prog (Ins V)) (test : V → Bool) (H : KHost V σ) (s : σ) (f : Nat)
    (args : List (SV V)) :
    beh (htstep (compPO .whole P) test H) (tInit f args, s) = hSrcRun P test H s f args :=
  host_correct .whole P (whole_dom P) test H s f args

/-- **The computed analysis under a host**: no hypothesis. -/
theorem host_analyze (P : Prog (Ins V)) (n : Nat) (test : V → Bool) (H : KHost V σ) (s : σ)
    (f : Nat) (args : List (SV V)) :
    beh (htstep (compPO (Selective.analyzed P n) P) test H) (tInit f args, s) =
      hSrcRun P test H s f args :=
  host_correct (Selective.analyzed P n) P (Selective.analyze_sound P n) test H s f args

/-- The host-closed kernel chart on a fragment: points are programs with a branch test, a host
and its initial state. -/
def hSrcChart (dom : Prog (Ins V) → Prop) : Chart :=
  BChart (Prog (Ins V) × (V → Bool) × KHost V σ × σ) (Nat × List (SV V)) (Obs V)
    (fun p => dom p.1) (fun p c => hSrcRun p.1 p.2.1 p.2.2.1 p.2.2.2 c.1 c.2)

/-- The target chart of a host instance. -/
def HScheme.tgtChart (A : HScheme V σ) : Chart :=
  BChart (A.TP × (V → Bool) × KHost V σ × σ) (Nat × List (SV V)) (Obs V) (fun _ => True)
    (fun q c => A.run q.1 q.2.1 q.2.2.1 q.2.2.2 c.1 c.2)

/-- **A correct host instance is a comorphism** (equal on every behaviour sentence). -/
def HScheme.comorphism (A : HScheme V σ) (h : A.Correct) :
    Transition (hSrcChart (σ := σ) A.dom) A.tgtChart :=
  BTrans.ofEq (fun p => (A.compile p.1, p.2)) id (fun _ _ => trivial)
    (fun p hp c => h p.1 hp p.2.1 p.2.2.1 p.2.2.2 c.1 c.2)

/-- The host instance of every optimization as a comorphism. -/
def host_comorphism (o : Opt) :
    Transition (hSrcChart (σ := σ) (hostScheme V σ o).dom) (hostScheme V σ o).tgtChart :=
  (hostScheme V σ o).comorphism (host_correct o)

/-! ## An example -/

/-- Function 0 pushes 5, calls 1 and doubles the result; function 1 makes a blocking call of
import 7 with argument 1. -/
def blockP : Prog (Ins Nat)
  | 0 => some (0, [.push 5, .call 1, .prim 1 fun l => l.map (· * 2)])
  | 1 => some (0, [.push 1, .suspend 7 1])
  | _ => none

/-- A host answering `t + 100` and counting its calls. -/
def countHost : KHost Nat Nat := ⟨fun s t _ => (s + 1, [.val (t + 100)])⟩

/-- The branch test of the example. -/
def blockTest (v : Nat) : Bool := v != 0

theorem blocking_src : runN (hsstep blockP blockTest countHost) 20 (sInit 0 [], 0) =
    .stop (.done [.val 214, .val 5]) := rfl

theorem blocking_whole :
    runN (htstep (compPO .whole blockP) blockTest countHost) 40 (tInit 0 [], 0) =
      .stop (.done [.val 214, .val 5]) := rfl

theorem blocking_analyzed :
    runN (htstep (compPO (Selective.analyzed blockP 4) blockP) blockTest countHost) 40
      (tInit 0 [], 0) = .stop (.done [.val 214, .val 5]) := rfl

/-- **The example**: one behaviour, the same in the source and both targets. -/
theorem blocking_example :
    hSrcRun blockP blockTest countHost 0 0 [] = {.done [.val 214, .val 5]} ∧
    beh (htstep (compPO .whole blockP) blockTest countHost) (tInit 0 [], 0) =
      {.done [.val 214, .val 5]} ∧
    beh (htstep (compPO (Selective.analyzed blockP 4) blockP) blockTest countHost)
      (tInit 0 [], 0) = {.done [.val 214, .val 5]} :=
  ⟨Silmaril.Wasm.FX.Asyncify.RelSim.beh_of_stop blocking_src,
    Silmaril.Wasm.FX.Asyncify.RelSim.beh_of_stop blocking_whole,
    Silmaril.Wasm.FX.Asyncify.RelSim.beh_of_stop blocking_analyzed⟩

/-- Without the host, the kernel traps on the same program (no frame handles tag 7). -/
theorem blocking_kernel_traps : runN (sstep blockP blockTest) 20 (sInit 0 []) = .stop .trap := rfl

/-- info: 'Silmaril.Wasm.FX.Asyncify.Host.host_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms host_correct

end Silmaril.Wasm.FX.Asyncify.Host
