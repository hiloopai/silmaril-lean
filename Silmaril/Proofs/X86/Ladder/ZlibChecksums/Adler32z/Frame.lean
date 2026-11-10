module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Listing
public import Silmaril.X86.Stencils.TableFold.Defs
public import Silmaril.X86.Stencils.ByteLoop.Defs

/-!
# `adler32_z`: the call context and its stack frame

`Ctx` fixes the entry state `m0` and the load address. `adler32_z` pushes six callee-saved
registers and spills six words in the red zone below them, so it writes exactly the 96 bytes
`[rsp₀ - 96, rsp₀)` (`area`). `FM c mem`: `mem` is the entry memory changed only there. From
it and the contract's separation facts follow: the code stays loaded, the buffer still reads
as at entry, and the return address is untouched. Stores into the area keep `FM`, and slot
facts (`HoldsLE`) survive stores to other slots.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN HoldsLE Stored leBytes)
open Silmaril.Process (Memory)
open Silmaril.X86
open Silmaril.X86.Ladder.ZlibChecksums
open Silmaril.X86.Stencils.TableFold (bytesAt byteAt)
open Silmaril.X86.Stencils.ByteLoop (Readable Writable Apart arg1 arg2)

/-- The call: load address and entry state. -/
structure Ctx where
  base : Word
  m0 : MState

namespace Ctx

variable (c : Ctx)

/-- The entry stack pointer (the return address is at `[r0]`). -/
def r0 : Word := c.m0.core.read .rsp
/-- The stack pointer after the six pushes. -/
def sp : Word := c.r0 - 48#64
/-- The lowest byte `adler32_z` writes. -/
def lo : Nat := c.r0.toNat - 96
/-- The 96 bytes `adler32_z` may write. -/
def area (a : Nat) : Prop := c.lo ≤ a ∧ a < c.lo + 96
/-- The buffer and its length. -/
def p : Word := c.m0.core.read .rsi
def n : Nat := (c.m0.core.read .rdx).toNat
/-- The input bytes. -/
def bs : List Byte := buf c.m0

/-- What the entry provides: System V entry obligations and the contract's precondition. -/
structure Pre : Prop where
  abi : FnContract.AbiEntry c.m0.core c.m0.memory
  rip : c.m0.core.rip = c.base
  loaded : Loaded c.m0.memory c.base adler32zCode
  room : 96 ≤ c.r0.toNat
  writable : Writable c.m0.memory c.lo 96
  readable : StackReadable c.m0.memory c.lo
  codeApart : Apart c.lo 96 c.base.toNat adler32zCode.length
  buf : c.p.toNat ≠ 0 → Readable c.m0.memory c.p.toNat c.n ∧ Apart c.lo 96 c.p.toNat c.n
  ok : AdlerOk c.m0 c.n

end Ctx

theorem pre_of {base : Word} {m0 : MState} (hab : FnContract.AbiEntry m0.core m0.memory)
    (he : (adler32zContract base).entry m0) : Ctx.Pre ⟨base, m0⟩ := by
  obtain ⟨hrip, hl, hroom, hw, hr, hca, hbuf, hok⟩ := he
  exact ⟨hab, hrip, hl, hroom, hw, hr, hca, hbuf, hok⟩

/-- The memory is the entry memory changed only inside the area. -/
def FM (c : Ctx) (mem : Memory) : Prop := c.m0.memory.WritesWithin mem c.area

namespace FM

variable {c : Ctx}

theorem refl : FM c c.m0.memory := Memory.WritesWithin.refl _ _

theorem loaded {mem : Memory} (hP : c.Pre) (h : FM c mem) : Loaded mem c.base adler32zCode := by
  unfold Loaded
  have := hP.loaded
  unfold Loaded at this
  rw [h.fetchBytes]
  · exact this
  · intro i hi ha
    have hc := hP.codeApart
    simp only [Ctx.area, Apart] at ha hc
    omega

theorem permitted {mem : Memory} (hP : c.Pre) (h : FM c mem) {o : Nat} (ho : o + 8 ≤ 96) :
    mem.Permitted .write (c.lo + o) 8 ∧ mem.Permitted .read (c.lo + o) 8 := by
  have hroom := hP.room
  have hr0 := c.r0.isLt
  constructor
  · rw [h.permitted_iff]
    simp only [Memory.Permitted, Memory.checkSpan_iff, Silmaril.Process.addressLimit]
    refine ⟨by simp only [Ctx.lo]; omega, by simp only [Ctx.lo]; omega, fun i hi => ?_⟩
    have := (hP.writable (o + i) (by omega)).2
    rwa [← Nat.add_assoc] at this
  · rw [h.permitted_iff]
    simp only [Memory.Permitted, Memory.checkSpan_iff, Silmaril.Process.addressLimit]
    refine ⟨by simp only [Ctx.lo]; omega, by simp only [Ctx.lo]; omega, fun i hi => ?_⟩
    have := hP.readable (o + i) (by omega)
    rwa [← Nat.add_assoc] at this

/-- A store into the area keeps `FM`. -/
theorem store {mem after : Memory} (h : FM c mem) {A v : Word} {o : Nat}
    (hst : storeN mem A 8 v = some after) (hA : A.toNat = c.lo + o) (ho : o + 8 ≤ 96) :
    FM c after := by
  refine h.trans ((Stored.of_storeN hst).writesWithin ?_)
  intro i hi
  simp only [Silmaril.X86.Ext.length_leBytes] at hi
  simp only [Ctx.area, hA]; omega

theorem holds_self {mem after : Memory} (hP : c.Pre) (h : FM c mem) {A v : Word} {o : Nat}
    (hst : storeN mem A 8 v = some after) (hA : A.toNat = c.lo + o) (ho : o + 8 ≤ 96) :
    HoldsLE after A.toNat 8 v :=
  Silmaril.X86.Ext.holdsLE_of_stored hst (by rw [hA]; exact (h.permitted hP ho).2)

theorem holds_other {mem after : Memory} {A v w : Word} {B : Nat}
    (hst : storeN mem A 8 v = some after) (hB : HoldsLE mem B 8 w)
    (hd : B + 8 ≤ A.toNat ∨ A.toNat + 8 ≤ B) : HoldsLE after B 8 w :=
  Silmaril.X86.Ext.HoldsLE.of_stored_disjoint (Stored.of_storeN hst) hB
    (by simpa using hd)

/-- A reads outside the area sees the entry memory. -/
theorem readBytes_eq {mem : Memory} (h : FM c mem) {a k : Nat} (hout : a + k ≤ c.lo ∨ c.lo + 96 ≤ a) :
    mem.readBytes a k = c.m0.memory.readBytes a k := by
  apply Memory.WritesWithin.readBytes h
  intro i hi ha
  simp only [Ctx.area] at ha
  omega

end FM

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
