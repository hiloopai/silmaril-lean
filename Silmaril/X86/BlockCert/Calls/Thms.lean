module

public import Silmaril.X86.BlockCert.Calls.Defs
public import Silmaril.X86.BlockCert.Store.Thms
public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.Ext.Store
import Silmaril.Proofs.X86.BlockCert.Calls.Assemble

/-!
# Function certificates with contract calls: steps and assembly

* `runL_push`, `runL_call`: **`push r` and `call rel32` as one-instruction listings**, from a
  state whose slot below `rsp` is writable: the successor core, with the successor memory left
  opaque and characterised by `Stored` (the pushed register, or the return address);
* `call_abiEntry`: after a `call` from a 16-byte-aligned stack pointer whose slot is also
  readable, **the callee's System V entry obligations** hold and the return address
  (`FnContract.retOf`) is the instruction after the call;
* `CallCert.next_of`, `CallCert.vc_of_blocks`: building `NextC` and `VC`;
* `CallCert.total`, `CallCert.contract`: **a function certificate with contract calls whose
  VCs hold is a total System V `FnContract` on the open machine.** The callee's run is not
  measured; its contract's totality supplies it.

What a callee result gives the caller (`rip` at the return address, `rsp` back, the
callee-saved registers kept, memory changed only inside the callee's footprint) is in
`FnContract.Result` (`Result.rip_eq`, `Result.reg`, `Result.readBytes`, `Result.stable`).
-/

@[expose] public section

namespace Silmaril.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded Stored)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- **`push r`** as a one-instruction listing of length `l`. -/
theorem runL_push {m : MState} {r : Reg} {l : Nat}
    (hp : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8) :
    ∃ mem', runL [(.ext (.push r), l)] m =
        some ⟨{ m.core.write .rsp (m.core.read .rsp - 8#64) with
          rip := m.core.rip + BitVec.ofNat 64 l }, mem'⟩ ∧
      Stored m.memory mem' (m.core.read .rsp - 8#64).toNat (encodeWords [m.core.read r]) :=
  Silmaril.Proofs.X86.BlockCert.Calls.runL_push hp

/-- **`call rel32`** as a one-instruction listing. -/
theorem runL_call {m : MState} {rel : BitVec 32}
    (hp : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8) :
    ∃ mem', runL [(.ext (.call rel), 5)] m =
        some ⟨{ m.core.write .rsp (m.core.read .rsp - 8#64) with
          rip := m.core.rip + 5#64 + rel.signExtend 64 }, mem'⟩ ∧
      Stored m.memory mem' (m.core.read .rsp - 8#64).toNat (encodeWords [m.core.rip + 5#64]) :=
  Silmaril.Proofs.X86.BlockCert.Calls.runL_call hp

/-- **The callee's entry obligations after a `call`** from a 16-byte-aligned stack pointer
whose slot is readable, and the return address is the instruction after the call. -/
theorem call_abiEntry {m : MState} {mem' : Memory} {target : Word}
    (hal : (m.core.read .rsp).toNat % 16 = 0) (h8 : 8 ≤ (m.core.read .rsp).toNat)
    (hr : m.memory.Permitted .read (m.core.read .rsp - 8#64).toNat 8)
    (hs : Stored m.memory mem' (m.core.read .rsp - 8#64).toNat (encodeWords [m.core.rip + 5#64])) :
    let c : State := { m.core.write .rsp (m.core.read .rsp - 8#64) with rip := target }
    FnContract.AbiEntry c mem' ∧ FnContract.retOf c mem' = m.core.rip + 5#64 :=
  Silmaril.Proofs.X86.BlockCert.Calls.call_abiEntry hal h8 hr hs

namespace CallCert

/-- Arriving at an annotated block with a smaller measure, the code still loaded. -/
theorem next_of {F : CallCert} {Q : MState → MState → Prop} {m0 m' : MState} {μ : Nat}
    (b : CBlk) (hb : b ∈ F.blocks) (hrip : m'.core.rip = F.base + BitVec.ofNat 64 b.off)
    (hl : Loaded m'.memory F.base F.code) (ha : F.ann b.off m0 m')
    (hμ : F.measure b.off m0 m' < μ) : F.NextC Q m0 μ m' :=
  .inr ⟨b, hb, hrip, hl, ha, hμ⟩

theorem vc_of_blocks {F : CallCert} {Q : MState → MState → Prop}
    (h : ∀ b ∈ F.blocks, F.BlockVC Q b) : F.VC Q := h

/-- **Total correctness from a function certificate with contract calls.** -/
theorem total {F : CallCert} (S : FnContract.Spec MState) {entry : CBlk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa :=
  Silmaril.Proofs.X86.BlockCert.Calls.total S hentry hc hvc hpre

/-- **The function contract** of a certificate with contract calls. -/
def contract (F : CallCert) (S : FnContract.Spec MState) {entry : CBlk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    FnContract Open.isa :=
  ⟨S, total S hentry hc hvc hpre⟩

end CallCert

end Silmaril.X86.BlockCert
