module

public import Silmaril.Compiler.Core.Verified.PrintLink.Defs

/-! # The output of a control-flow graph's run, in Lir's memory

`OutMem mem s`: Lir's memory `mem` holds the output `s` that Core has written. The output buffer
that control words 6 (address) and 3 (length) name is `coreBytes s` and lies in the memory, and
it is empty or at `PrintLink.outBase`, above the control block, so the abort store (control
word 5) leaves it alone.

* The initial memory of an artifact with an empty image holds the empty output (`initial`).
* A return observes the exit with the output `s` (`OutMem.obs`).
* The trap after the abort store observes the abort with the output `s` (`OutMem.abortObs`).
* In `PrintLink`'s terms (`OutMem.toBuf`, `ofBuf`): the buffer at `outBase` holds `coreBytes s`
  (`PrintLink.Buf`), control word 3 is its length and it fits in the memory; with control word 6
  set to `outBase` this is `OutMem` again. A print block reads the length, writes as `PrintLink`
  writes, and stores the length and the address back.

`Cfg.Rel` carries `OutMem` as its output invariant. A node that prints appends to the buffer and
keeps `OutMem` with the longer output, so the graph's nodes need not keep Lir's memory fixed or
Core's output empty. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgOut

open Silmaril.Machine
open Spec Backend
open PrintLink (outBase)

/-- Lir's memory `mem` holds the output `s`. -/
structure OutMem (mem : Lir.Memory) (s : String) : Prop where
  stdout : memStdout? mem = some (coreBytes s)
  apart : memWord mem (ctlAddr + 24) = 0 ∨ memWord mem (ctlAddr + 48) = outBase
  size : mem.size = Silmaril.Compile.Forks.CoreComp.Target.memSize

/-- A return observes the exit with the output. -/
theorem OutMem.obs {mem : Lir.Memory} {s : String} {w : Lir.Word} {o : Obs} (h : OutMem mem s)
    (ho : LirObs (.returned [w] mem) o) : o = .exit (w.toNat % 256) (coreBytes s) := by
  obtain ⟨k, out, rfl, hk, hout⟩ := ho
  rw [hk w rfl, hout _ h.stdout]

/-- A store to control word 5 keeps the output buffer. -/
theorem OutMem.stdout_store {mem mem' : Lir.Memory} {s : String} {v : Lir.Word} (h : OutMem mem s)
    (hst : mem.store .b8 (ctlAddr + 40) v = some mem') : memStdout? mem' = some (coreBytes s) := by
  have h24 : memWord mem' (ctlAddr + 24) = memWord mem (ctlAddr + 24) :=
    PrintLink.memWord_outside hst (by left; decide)
  have h48 : memWord mem' (ctlAddr + 48) = memWord mem (ctlAddr + 48) :=
    PrintLink.memWord_outside hst (by right; decide)
  have hsz : mem'.size = mem.size := Lir.Memory.store_size hst
  have e : (List.ofFn fun i : Fin (memWord mem (ctlAddr + 24)) =>
      mem'.bytes (memWord mem (ctlAddr + 48) + i)) =
      List.ofFn fun i : Fin (memWord mem (ctlAddr + 24)) => mem.bytes (memWord mem (ctlAddr + 48) + i) := by
    apply List.ofFn_inj.mpr
    funext i
    have := i.isLt
    rcases h.apart with he | hb
    · omega
    · exact PrintLink.store_bytes_outside hst
        (by right; simp only [Lir.Width.bytes, outBase] at hb ⊢; omega)
  rw [← h.stdout]
  simp only [memStdout?, h24, h48, hsz, Fin.val_cast, e]

/-- A byte read back from its `UInt8`. -/
theorem byte_toUInt8 (b : Lir.Byte) : BitVec.ofNat 8 b.toNat.toUInt8.toNat = b := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.toUInt8, UInt8.toNat]

/-- The output in `PrintLink`'s terms: the buffer at `outBase` holds it, control word 3 is its
length, and it fits in the memory. -/
theorem OutMem.toBuf {mem : Lir.Memory} {s : String} (h : OutMem mem s) :
    PrintLink.Buf mem (coreBytes s) ∧ memWord mem (ctlAddr + 24) = (coreBytes s).length ∧
      outBase + (coreBytes s).length ≤ mem.size := by
  have hs := h.stdout
  simp only [memStdout?] at hs
  split at hs
  · rename_i hfit
    simp only [Option.some.injEq] at hs
    have hlen : memWord mem (ctlAddr + 24) = (coreBytes s).length := by
      rw [← hs]; simp
    refine ⟨?_, hlen, ?_⟩
    · intro i hi
      rcases h.apart with he | hb
      · omega
      · have hi' : i < memWord mem (ctlAddr + 24) := by omega
        have e : (coreBytes s)[i] = (mem.bytes (outBase + i)).toNat.toUInt8 := by
          simp only [← hs, List.getElem_map, List.getElem_ofFn, hb]
        rw [e, byte_toUInt8]
    · rcases h.apart with he | hb
      · rw [← hlen, he, h.size]; decide
      · rw [← hlen, ← hb]; exact hfit
  · cases hs

/-- The output in `PrintLink`'s terms, with control word 6 at the buffer, is `OutMem`. -/
theorem ofBuf {mem : Lir.Memory} {s : String}
    (h24 : memWord mem (ctlAddr + 24) = (coreBytes s).length)
    (h48 : memWord mem (ctlAddr + 48) = outBase) (hbuf : PrintLink.Buf mem (coreBytes s))
    (hroom : outBase + (coreBytes s).length ≤ mem.size) (hsize : mem.size = Silmaril.Compile.Forks.CoreComp.Target.memSize) :
    OutMem mem s := by
  refine ⟨?_, .inr h48, hsize⟩
  simp only [memStdout?, h24, h48, hroom, ↓reduceIte, Option.some.injEq]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_ofFn, Fin.val_cast]
  rw [hbuf i h2]
  simp [Nat.toUInt8]

/-- The trap after the abort store observes the abort with the output. -/
theorem OutMem.abortObs {mem mem' : Lir.Memory} {s : String} {o : Obs} (h : OutMem mem s)
    (hst : mem.store .b8 (ctlAddr + 40) (BitVec.ofNat 64 2) = some mem')
    (ho : LirObs (.trapped mem') o) : o = .abort (coreBytes s) := by
  obtain ⟨out, rfl, hout⟩ := ho
  have h40 : memWord mem' (ctlAddr + 40) = 2 := by
    rw [PrintLink.memWord_store hst]; rfl
  rw [hout _ (h.stdout_store hst)]
  simp [trapObs, h40]

/-- The initial memory of an artifact with an empty image holds no output. -/
theorem initial {a : Artifact} (himg : a.image = .empty) (hbase : a.argBase = Silmaril.Compile.Forks.CoreComp.Target.argBase)
    (args : List String) (hsize : (a.lmem args).size = Silmaril.Compile.Forks.CoreComp.Target.memSize) : OutMem (a.lmem args) "" := by
  have hzero (addr : Nat) (hi : addr + 8 ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase) : memWord (a.lmem args) addr = 0 := by
    apply ConstLink.memWord_zero
    intro i
    apply ConstLink.lmem_bytes_empty himg
    rw [hbase]
    have := i.isLt
    omega
  have h24 := hzero (ctlAddr + 24) (by decide)
  have h48 := hzero (ctlAddr + 48) (by decide)
  refine ⟨?_, .inl h24, hsize⟩
  simp [memStdout?, h24, h48, coreBytes]

end Silmaril.Compile.Core.Verified.CfgOut
