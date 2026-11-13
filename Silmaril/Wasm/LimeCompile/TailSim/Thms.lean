module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.Module
public import Silmaril.Wasm.LimeCompile.AgreeTail.Thms

/-!
# The two-way simulation of the tail-call rewrite: results

The relation of `Silmaril.Wasm.LimeCompile.TailSim.Defs` (source on the left, target on the
right; `fw` selects the direction) gives two stuttering simulations of `Step` with itself
between typed configurations with `FRel`-related stores and equal frames:

* forwards (`Raw/…/TailSim/FwdSim.lean`, `fwdSim`): the target matches every source step,
  by induction on the size of the source's code; after a source `return_call_ref` the target's
  `call_ref; return` is *ahead* (`R.bub`, and the callee wrapped in the caller's frame and labels,
  `CE.wrap`);
* backwards (`Raw/…/TailSim/BwdSim.lean`, `bwdSim`): the source matches every target step,
  by induction on the size of the target's code; when the target makes the rewritten call inside
  the caller's labels the source catches up in one run (bubble out of the labels, leave the frame
  with `return_call_ref-frame-addr`, make the call; `ce_frame_pend`), and when the callee has
  returned inside the wrapper the source waits while the target's `return` leaves the labels and
  the frame (`CE.vals`).

The callee's arity (the caller's frame arity, so that the target's `return` carries the callee's
results) comes from the typing of the source's `return_call_ref` (an inversion of the
`return_call_ref` typing rule, `frameAddr_arity`), with `Step.preservation` keeping both sides
typed.

Proved here (no `Task`):

* **`tailSim`**: the open target `Tail.Task.tailSim` holds: a valid module and its tail rewrite
  are exactly export-equivalent at every profile and every code-parametric host with the host
  contract `HostOk`;
* **`compile_correct'`**: `Tail.compile` is correct, unconditionally;
* **`tail_agree'`**: the tail compiler agrees with every compiler correct on a fragment.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The tail-call rewrite is exact** (`Tail.Task.tailSim`). -/
theorem tailSim : Tail.Task.tailSim := fun _ _ _ hpar hok _ hm =>
  Silmaril.Raw.Wasm.LimeCompile.TailSim.exportEquiv_tail hpar hok hm
    (let ⟨_, h⟩ := hm; ⟨_, Tail.tailModule_valid h⟩)

/-- **The tail compiler is correct**: a valid Core 3.0 module and the Core image of its
compilation are exactly export-equivalent, at every profile and every code-parametric host with
the host contract. -/
theorem compile_correct' (hhost : Execution.Core.Sim.HostParametric host) (hok : HostOk host)
    {m : Module} {l : Lime1.Module} (h : Tail.compile m = some l) (hm : ∃ mt, ModuleOk m mt) :
    ExportEquiv (· = ·) P host m l.toCore :=
  Tail.compile_correct tailSim hhost hok h hm

/-- **Agreement**: on a valid input in `S` that both compile, the tail compiler and any compiler
correct on `S` give exactly export-equivalent outputs. -/
theorem tail_agree' {S : Module → Prop} {c : Module → Option Lime1.Module}
    (hc : AgreeTail.CorrectOnOk S c) (hp : Execution.Core.Sim.HostParametric host)
    (hok : HostOk host) {m : Module} {l l' : Lime1.Module} (hm : ∃ mt, ModuleOk m mt) (hS : S m)
    (ht : Tail.compile m = some l) (hc' : c m = some l') :
    ExportEquiv (· = ·) P host l.toCore l'.toCore :=
  AgreeTail.tail_agree tailSim hc hp hok hm hS ht hc'

/-- info: 'Silmaril.Wasm.LimeCompile.TailSim.tailSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tailSim

/-- info: 'Silmaril.Wasm.LimeCompile.TailSim.compile_correct'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compile_correct'

/-- info: 'Silmaril.Wasm.LimeCompile.TailSim.tail_agree'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_agree'

end Silmaril.Wasm.LimeCompile.TailSim
