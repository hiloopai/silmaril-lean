module

public import Silmaril.Proofs.X86.Atomic9.Step

/-!
# `Atomic9`: semantic lemmas

Proofs for `Silmaril/X86/Atomic9/Thms.lean`.

* `install_readBacking`, `storeN_self`: writing back the bytes just read leaves memory equal.
* `decodeL_lockOr_rsp`: the SQLite fence `f0 48 83 0c 24 00` decodes as
  `lock or qword ptr [rsp], 0` (`decide`).
* `lockOr_rsp_zero_fence`: that fence is one step that changes only `rip` and the flags;
  memory is unchanged (equal, not just equal on reads).
* `execNew_fence`, `execNew_pause`: fences and `pause` only advance `rip`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Atomic9

open Silmaril.X86 (State MState Word Byte)
open Silmaril.X86.Ext (Mem leValue leBytes loadN storeN)
open Silmaril.Process (Memory ByteMemory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Atomic9

/-- Re-installing bytes read from the backing map changes nothing. -/
theorem install_readBacking {bytes : ByteMemory} :
    ∀ (n a : Nat) (bs : List Byte), Memory.readBacking bytes a n = some bs →
      Memory.install bytes a bs = bytes
  | 0, a, bs, h => by
    simp only [Memory.readBacking, Option.some.injEq] at h
    subst h; rfl
  | n + 1, a, bs, h => by
    simp only [Memory.readBacking, Std.ExtHashMap.get?_eq_getElem?, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, t, ht, rfl⟩ := h
    simp only [Memory.install]
    rw [install_readBacking n (a + 1) t ht]
    ext k : 1
    rw [Std.ExtHashMap.getElem?_insert]
    split
    · rename_i hk
      have : a = k := by simpa using hk
      subst this
      exact hb.symm
    · rfl

/-- **Storing the value just loaded leaves memory equal** (8 bytes, writable span). -/
theorem storeN_self {memory : Memory} {a : Word} {bs : List Byte}
    (hr : memory.readBytes a.toNat 8 = some bs) (hw : memory.Permitted .write a.toNat 8) :
    storeN memory a 8 (BitVec.ofNat 64 (leValue bs)) = some memory := by
  have hlen : bs.length = 8 := Memory.readWith_length hr
  have hle : leBytes (BitVec.ofNat 64 (leValue bs)) 8 = bs := by
    have := Silmaril.X86.Ext.leBytes_leValue bs (by omega)
    rwa [hlen] at this
  have hrb : Memory.readBacking memory.bytes a.toNat 8 = some bs := by
    unfold Memory.readBytes Memory.readWith at hr
    split at hr
    · exact hr
    · cases hr
  unfold storeN Memory.writeBytes
  rw [hle, hlen]
  have hw' : memory.checkSpan .write a.toNat 8 = true := hw
  simp only [hw', ↓reduceIte, install_readBacking 8 a.toNat bs hrb]

/-- The SQLite fence `f0 48 83 0c 24 00` is `lock or qword ptr [rsp], 0`. -/
theorem decodeL_lockOr_rsp :
    decodeL [0xf0, 0x48, 0x83, 0x0c, 0x24, 0x00] =
      some (.lockAluI .q .or (Mem.ofReg .rsp none 0) 0, 6) := by
  decide

/-- **gcc's sequentially consistent fence `lock or qword ptr [rsp], 0` is one step that
changes only `rip` and the flags** (those of `or` of the stack word with `0`); memory is
unchanged. Needs the stack word readable and writable (a locked RMW writes). -/
theorem lockOr_rsp_zero_fence {m : MState} {bs : List Byte}
    (hf : m.memory.fetchBytes m.core.rip.toNat 6 = some [0xf0, 0x48, 0x83, 0x0c, 0x24, 0x00])
    (hr : m.memory.readBytes (m.core.read .rsp).toNat 8 = some bs)
    (hw : m.memory.Permitted .write (m.core.read .rsp).toNat 8) :
    step m = some ⟨{ m.core with
        rip := m.core.rip + BitVec.ofNat 64 6
        flags := Silmaril.X86.Ext.AluOp.flagsN .or (BitVec.ofNat 64 (leValue bs)) 0#64 },
      m.memory⟩ := by
  refine step_of_fetch_new hf decodeL_lockOr_rsp ?_
  have haddr : ∀ next, (Mem.ofReg .rsp none 0).addr m.core next = m.core.read .rsp := by
    intro next
    simp [Mem.addr, Mem.ofReg]
  have hload : loadN m.memory (m.core.read .rsp) 8 = some (BitVec.ofNat 64 (leValue bs)) :=
    Silmaril.X86.Ext.loadN_of_readBytes hr
  simp only [execNew, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.writeRM, haddr, Silmaril.X86.Ext.Sz.bytes, hload, Option.map_some]
  have hstore : storeN m.memory (m.core.read .rsp) 8 (BitVec.ofNat 64 (leValue bs) ||| 0#64) =
      some m.memory := by
    rw [BitVec.or_zero]; exact storeN_self hr hw
  simp [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.retire]
  erw [hstore]
  rfl

/-- A fence only advances `rip`. -/
theorem execNew_fence (k : FenceKind) (s : State) (memory : Memory) (next : Word) :
    execNew (.fence k) s memory next = .ok { s with rip := next } memory := rfl

/-- `pause` only advances `rip`. -/
theorem execNew_pause (s : State) (memory : Memory) (next : Word) :
    execNew .pause s memory next = .ok { s with rip := next } memory := rfl

end Silmaril.Proofs.X86.Atomic9
