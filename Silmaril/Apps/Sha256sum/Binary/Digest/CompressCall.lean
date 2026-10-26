module

public import Silmaril.Apps.Sha256sum.Binary
public import Silmaril.Apps.Sha256sum.X86Sys.SegVC

/-! # `sha256_compress` as a contracted call of the segment VC generator

`compressCall r11Of` is the linked `sha256_compress` of `sha256sum-min` as a `SegVC.Call` of
the process machine (`X86Sys.Isa.sys`): at the callee's entry (after the `call`), the
System V precondition `SysVEntry` of the pilot contract with the arguments in `rdi`, `rsi`,
the stack pointer `rsp` and the return address at `[rsp]`; after it, the pilot `Post` and
`rip` at the return address. The proof is `Binary.compress_contract` and
`Sha256O2.sha256_compress_O2_live` through the call bridge `X86Sys.Call.ofReturns`: the
callee is never executed symbolically by the caller's VCs.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest

open Silmaril.X86 (State MState Word)
open Silmaril.Process (Memory)
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Crypto.X86.Sha256O2

/-- The return address at the top of the stack (0 if unreadable). -/
def retOf (m : MState) : Word :=
  ((m.memory.readBytes (m.core.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes?).getD 0

/-- A designated return pops `exit`. -/
theorem rip_of_returned {exit : Word} {m fin : MState} (h : X86.Ext.step exit m = .returned fin) :
    fin.core.rip = exit := by
  unfold X86.Ext.step at h
  split at h
  · cases h
  · cases h
  · split at h
    · split at h
      · cases h; rename_i hh; exact hh.2
      · cases h
    all_goals cases h

/-- The callee precondition at its entry. -/
def CompressPre (m : MState) : Prop :=
  SysVEntry (layout (retOf m)) (m.core.read .rdi) (m.core.read .rsi) (m.core.read .rsp)
    frameSize m

/-- The callee postcondition, from its entry state. -/
def CompressPost (m fin : MState) : Prop :=
  Post (layout (retOf m)) (m.core.read .rdi) (m.core.read .rsi) (m.core.read .rsp) frameSize
    m fin ∧ fin.core.rip = retOf m

/-- **VERIFIED.** The linked `sha256_compress`, as a contracted call of the process machine. -/
def compressCall (r11Of : Core → Word) : Silmaril.X86.SegVC.Call (Isa.sys r11Of) :=
  Call.ofReturns r11Of (fun s => CompressPre (toExtState s))
    (fun s t => ∃ fin, t = withExtState s fin ∧ CompressPost (toExtState s) fin)
    (by
      intro s _ hpre
      obtain ⟨fin, hret⟩ := sha256_compress_O2_live _ _ _ _ _ hpre
      refine ⟨_, fin, hret, fin, rfl, compress_contract _ _ _ _ _ _ hpre hret, ?_⟩
      obtain ⟨n, mid, _, hlast⟩ := hret
      exact rip_of_returned hlast)

end Silmaril.Apps.Sha256sum.Binary.Digest
