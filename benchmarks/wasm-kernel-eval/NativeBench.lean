import Silmaril.Wasm.KernelEval.Examples
import Silmaril.Wasm.KernelEval.Memories
import Silmaril.Wasm.KernelEval.KBytesMem
/-! Native (compiled) timings of the memory representations of `Silmaril.Wasm.KernelEval`.
`ByteMem` is a copy of the algorithm of Core's `Memory.load`/`Memory.store`
(`ByteArray.extract`, `copySlice`; `Silmaril.Wasm.Execution.Memory`) on the core-only side,
since that module's closure is not compiled natively here; it is not proved here.
Prints one JSON object per case. -/
open Silmaril.Wasm.KernelEval Examples

structure ByteMem where
  bytes : ByteArray

def decodeLE (b : ByteArray) : Nat := b.data.foldr (fun x r => x.toNat + 256 * r) 0
def encodeLE : Nat → Nat → ByteArray
  | 0, _ => .empty
  | k + 1, n => ⟨#[UInt8.ofNat n]⟩ ++ encodeLE k (n / 256)

instance : MemOps ByteMem where
  load m a k := if a + k ≤ m.bytes.size then some (decodeLE (m.bytes.extract a (a + k))) else none
  store m a k v :=
    let e := encodeLE k v
    if a + e.size ≤ m.bytes.size then some ⟨e.copySlice 0 m.bytes a e.size⟩ else none

def ByteMem.zeros (n : Nat) : ByteMem := ⟨⟨Array.replicate n 0⟩⟩

def time (reps : Nat) (f : Unit → IO String) : IO (Float × String) := do
  let t0 ← IO.monoNanosNow
  let mut r := ""
  for _ in [0:reps] do r ← f ()
  let t1 ← IO.monoNanosNow
  return ((t1 - t0).toFloat / 1e6 / reps.toFloat, r)

def emit (work rep : String) (size reps : Nat) (f : Unit → IO String) : IO Unit := do
  let (ms, r) ← time reps f
  IO.println s!"\{\"workload\": \"{work}\", \"rep\": \"{rep}\", \"size\": {size}, \"ms\": {ms}, \"result\": \"{r}\"}"

def prog {M} [MemOps M] (body : List Instr) (locals : List (BitVec 32)) (m : M) : Unit → IO String :=
  fun _ => pure (toString ((run 100000000 (Config.init body locals m)).top?.map BitVec.toNat))

def allReps (work : String) (size reps : Nat)
    (f : ∀ {M : Type} [MemOps M], M → Unit → IO String) : IO Unit := do
  emit work "NatMem" size reps (f (NatMem.zeros size))
  emit work "Overlay(NatMem)" size reps (f (Overlay.ofBase (NatMem.zeros size)))
  let pb := 12; let d := Nat.log2 (size / 4096)
  emit work "PageMem 4KiB" size reps (f (PageMem.zeros pb d))
  emit work "KBytes rope stores (KRope)" size reps (f (KRope.mk (kzeros size)))
  emit work "KBytes path stores (KPath)" size reps (f (KPath.mk (kzeros size)))
  emit work "KBytes rope stores, one-leaf zero" size reps (f (KRope.mk (kzero1 size)))
  emit work "KBytes path stores, one-leaf zero" size reps (f (KPath.mk (kzero1 size)))
  emit work "ByteMem (Core algorithm)" size reps (f (ByteMem.zeros size))
  if size ≤ 65536 then emit work "ListMem" size (max 1 (reps / 10)) (f (⟨List.replicate size 0⟩ : ListMem))

def main : IO Unit := do
  for (n, size) in [(16, 65536), (32, 65536)] do
    allReps s!"fillSort {n}" size 20 fun m => prog fillSort (fillSortLocals n) m
  for size in [65536, 1048576] do
    allReps "scatter 128" size 5 fun m => prog scatter (scatterLocals 128 (size / 128 - 4)) m
  for size in [65536, 1048576] do
    allReps "updates 200" size 5 fun m => fun _ => pure (toString (updates m 200 (size / 200 - 4)))
  for size in [65536, 1048576] do
    allReps "sharing 64" size 5 fun m => fun _ =>
      pure (toString (sharingCheck (fillWords m 64) ((List.range 64).map (· * (size / 64 - 4))) 8))
