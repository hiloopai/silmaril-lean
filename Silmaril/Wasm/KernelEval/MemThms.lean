module

public import Silmaril.Wasm.KernelEval.Memories
import Silmaril.Proofs.Wasm.KernelEval.Memories

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: memory representations, results

Proofs in `Silmaril.Proofs.Wasm.KernelEval.Memories`.

* `run_mapMem_on`, `returns_mapMem_on`: a simulation valid on `inv` (`MemSimOn`) lifts to
  runs from a memory satisfying `inv` (stores preserve it, `step_memInv`);
* `memSimOn_ofView`: a simulation from pointwise facts: loads decode bytes, and a store changes
  exactly the written bytes and keeps the size and the validity condition;
* **`memSimOn_overlay`** (no validity condition) and **`memSimOn_pageMem`** (`PageMem.Wf`,
  true of `PageMem.zeros`, `wf_zeros`): both representations are the list reference;
* `overlay_zeros_toList`, `pageMem_zeros_toList`: their zero memories denote zero bytes.
-/

namespace Silmaril.Wasm.KernelEval

variable {M : Type} [MemOps M] {N : Type} [MemOps N] {g : M → N} {inv : M → Prop}

theorem run_mapMem_on (h : MemSimOn inv g) (n : Nat) (c : Config M) (hc : inv c.mem) :
    run n (c.mapMem g) = (run n c).mapMem g :=
  Proofs.Wasm.KernelEval.run_mapMem_on h n c hc

theorem returns_mapMem_on (h : MemSimOn inv g) (fuel : Nat) (body : List Instr)
    (locals : List (BitVec 32)) (m : M) (hm : inv m) (v : BitVec 32) :
    returns fuel body locals (g m) v = returns fuel body locals m v :=
  Proofs.Wasm.KernelEval.returns_mapMem_on h fuel body locals m hm v

theorem memSimOn_of_memSim (h : MemSim g) : MemSimOn (fun _ => True) g :=
  Proofs.Wasm.KernelEval.memSimOn_of_memSim h

theorem memSimOn_ofView {R : Type} [MemOps R] (inv : R → Prop) (size : R → Nat)
    (byte : R → Nat → BitVec 8)
    (hload : ∀ r, inv r → ∀ a k, MemOps.load r a k =
      if a + k ≤ size r then some (loadBytes (byte r) a k) else none)
    (hstore : ∀ r, inv r → ∀ a k v, a + k ≤ size r → ∃ r', MemOps.store r a k v = some r' ∧
      inv r' ∧ size r' = size r ∧
      ∀ i, i < size r → byte r' i = if a ≤ i ∧ i < a + k then encByte v (i - a) else byte r i)
    (hnone : ∀ r, inv r → ∀ a k v, ¬ a + k ≤ size r → MemOps.store r a k v = none) :
    MemSimOn inv (fun r => ListMem.ofView (size r) (byte r)) :=
  Proofs.Wasm.KernelEval.memSimOn_ofView inv size byte hload hstore hnone

theorem memSimOn_overlay : MemSimOn (fun _ : Overlay => True) Overlay.toList :=
  Proofs.Wasm.KernelEval.memSimOn_overlay

theorem memSimOn_pageMem : MemSimOn PageMem.Wf PageMem.toList :=
  Proofs.Wasm.KernelEval.memSimOn_pageMem

theorem wf_zeros (pbits depth : Nat) : (PageMem.zeros pbits depth).Wf :=
  Proofs.Wasm.KernelEval.wf_zeros pbits depth

theorem overlay_zeros_toList (n : Nat) :
    (Overlay.ofBase (NatMem.zeros n)).toList = ⟨List.replicate n 0⟩ :=
  Proofs.Wasm.KernelEval.overlay_zeros_toList n

theorem pageMem_zeros_toList (pbits depth : Nat) :
    (PageMem.zeros pbits depth).toList = ⟨List.replicate (2 ^ depth * 2 ^ pbits) 0⟩ :=
  Proofs.Wasm.KernelEval.pageMem_zeros_toList pbits depth

end Silmaril.Wasm.KernelEval
