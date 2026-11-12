module

public import Silmaril.Wasm.LimeCompile.Agree.Thms
public import Silmaril.Wasm.LimeCompile.Tail.Thms
public import Silmaril.Proofs.Wasm.LimeCompile.AgreeTail.Count

/-!
# The tail-call compiler, related to the pass-1 routes

`Tail.compile` (select lowering, then `return_call`/`return_call_indirect` to call and `return`
outside `try_table`) extends the pass-1 direct compiler:

* **`tail_of_direct`**: wherever `Direct.compile` succeeds, `Tail.compile` gives the same Lime1
  module (a module `Direct.compile` accepts has no tail call left);
* `tail_eq_direct_of_frag`: on the container's fragment the two compilers are equal;
* `tail_limePreserving`, `limePres_tail`: `Tail.compile` is Lime-preserving, so `limePres` leaves
  it unchanged;
* **`container_tail_agree`**: on the container's fragment, if `Tail.compile` succeeds, the
  container's output and `Tail.compile`'s are exactly export-equivalent (hosts that respect
  `select` erasure and are code-parametric), unconditionally;
* `tail_correctOn`, **`tail_agree`**: given the open `Tail.Task.tailSim`, `Tail.compile` is
  correct on valid modules for code-parametric hosts with the host contract, and agrees (exact
  export equivalence of the outputs) with every compiler correct on a fragment at those hosts.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.AgreeTail

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.LimeCompile.Preserve (LimePreserving limePres)
open Silmaril.Proofs.Wasm.LimeCompile.AgreeTail

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The tail compiler extends the direct compiler**: same output wherever the latter succeeds. -/
theorem tail_of_direct {m : Module} {l : Lime1.Module} (h : Direct.compile m = some l) :
    Tail.compile m = some l := by
  have hl : l.toCore = Direct.lowerModule m := Direct.compile_toCore h
  have hlow : Tail.lower m = Direct.lowerModule m := by
    rw [Tail.lower, ← hl, Silmaril.Proofs.Wasm.LimeCompile.Tail.tailModule_toCore]
  unfold Tail.compile
  rw [hlow]
  exact h

/-- On the container's fragment the tail compiler is the direct compiler. -/
theorem tail_eq_direct_of_frag {m : Module} (hF : Container.Frag m) :
    Tail.compile m = Direct.compile m := by
  obtain ⟨-, L, -, hL⟩ := hF
  exact Tail.compile_eq_direct (noTail_of_selM hL)

/-- The tail compiler is the identity on Lime-only code. -/
theorem tail_limePreserving : LimePreserving Tail.compile :=
  Tail.compile_lime

theorem limePres_tail : limePres Tail.compile = Tail.compile :=
  (Preserve.limePres_eq_self_iff _).2 tail_limePreserving

/-- **Container and tail compiler agree** on the container's fragment (no `Task`). -/
theorem container_tail_agree (hr : Select.HostResp host) (hp : Sim.HostParametric host)
    {m : Module} {l : Lime1.Module} (hF : Container.Frag m) (ht : Tail.compile m = some l) :
    ∃ L, Container.compile m = some L ∧ Lime1.Validation.ModuleValid L ∧
      ExportEquiv (· = ·) P host L.toCore l.toCore := by
  have hd : Direct.compile m = some l := by rw [← tail_eq_direct_of_frag hF]; exact ht
  exact Agree.container_direct_agree hr hp hF hd

/-- A compiler is correct on `S` at the hosts that are code-parametric and satisfy the host
contract. -/
def CorrectOnOk (S : Module → Prop) (c : Module → Option Lime1.Module) : Prop :=
  ∀ (H : Type) (P : Profile) (host : HostSemantics H), Sim.HostParametric host → HostOk host →
    ∀ m l, S m → c m = some l → ExportEquiv (· = ·) P host m l.toCore

/-- Correctness for all code-parametric hosts implies it for those with the host contract. -/
theorem CorrectOnOk.of_correctOn {S : Module → Prop} {c : Module → Option Lime1.Module}
    (h : DirectAgree.CorrectOn S c) : CorrectOnOk S c :=
  fun H P host hp _ => h H P host hp

/-- Given `Task.tailSim`, the tail compiler is correct on valid modules. -/
theorem tail_correctOn (hT : Tail.Task.tailSim) :
    CorrectOnOk (fun m => ∃ mt, ModuleOk m mt) Tail.compile :=
  fun _ _ _ hp hok _ _ hm h => Tail.compile_correct hT hp hok h hm

/-- **Agreement**, given `Task.tailSim`: on a valid input in `S` that both compile, the tail
compiler and any compiler correct on `S` give exactly export-equivalent outputs. -/
theorem tail_agree (hT : Tail.Task.tailSim) {S : Module → Prop} {c : Module → Option Lime1.Module}
    (hc : CorrectOnOk S c) (hp : Sim.HostParametric host) (hok : HostOk host) {m : Module}
    {l l' : Lime1.Module} (hm : ∃ mt, ModuleOk m mt) (hS : S m) (ht : Tail.compile m = some l)
    (hc' : c m = some l') : ExportEquiv (· = ·) P host l.toCore l'.toCore :=
  DirectAgree.exportEquiv_trans (DirectAgree.exportEquiv_symm (Tail.compile_correct hT hp hok ht hm))
    (hc H P host hp hok m l' hS hc')

/-- info: 'Silmaril.Wasm.LimeCompile.AgreeTail.container_tail_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms container_tail_agree

end Silmaril.Wasm.LimeCompile.AgreeTail
