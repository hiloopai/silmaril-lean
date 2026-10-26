module

public import Silmaril.Process.LPS.SoundReference
public import Silmaril.Process.LPS.Checks.UserAbi

/-! # Checks on the sound riscv64 reference table

One message header at `0x1fc8` naming two descriptors at `0x2000`: ten bytes at `0x3000`,
then ten bytes at `base1`. With `base1` in the non-canonical half, LPS's `copy_iovecs_aux`
accepts the vector (so LPS's `sendmsg_spec` goes on to send) while Linux's `__import_iovec`
with the Sv48 `access_ok` refuses it; the sound arm declines exactly there. With an ordinary
`base1` the two imports agree and the sound arm is LPS's.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Checks.SoundReference

open Silmaril.Process.LPS Silmaril.Process.LPS.SoundReference Sys
open Silmaril.Process.LPS.Checks.UserAbi (memOf)

/-- `struct user_msghdr` at `0x1fc8` (`msg_iov = 0x2000`, `msg_iovlen = 2`, everything else
zero), immediately followed by the two descriptors. -/
def msgMem (base1 : Word) : Word → Option Byte :=
  memOf 0x1fc8 (wordLe8 0 ++ wordLe8 0 ++ wordLe8 0x2000 ++ wordLe8 2 ++ wordLe8 0 ++
    wordLe8 0 ++ wordLe8 0 ++ wordLe8 0x3000 ++ wordLe8 10 ++ wordLe8 base1 ++ wordLe8 10)

/-- A non-canonical segment base. -/
def badBase : Word := 0xffff800000000000

/-- LPS accepts the vector Linux refuses: an error turned into a specific success. -/
theorem lps_sends_where_linux_faults :
    copyIovecsAux (msgMem badBase) 0x2000 2 = .ok [(0x3000, 10), (badBase, 10)] ∧
      importIovecs (msgMem badBase) 0x2000 2 = .fault := by
  decide

/-- Negative: the imports disagree at the bad vector. -/
theorem imports_disagree : sendmsgImportsAgree (msgMem badBase) 0x1fc8 = false := by decide

/-- Positive: the imports agree at an ordinary vector. -/
theorem imports_agree : sendmsgImportsAgree (msgMem 0x4000) 0x1fc8 = true := by decide

/-- The sound arm only declines at the bad vector, whatever the descriptor and model. -/
theorem sound_declines (fd flags : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (hmem : i.mem = msgMem badBase) :
    sendmsgSpecSound fd 0x1fc8 flags i m o ↔ o = .unmodeled := by
  unfold sendmsgSpecSound
  split
  · rename_i hc; rw [hmem] at hc; exact absurd hc (by decide)
  · exact Iff.rfl

/-- At the ordinary vector the sound arm is LPS's arm and Linux's arm. -/
theorem sound_is_lps (fd flags : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (hmem : i.mem = msgMem 0x4000) :
    (sendmsgSpecSound fd 0x1fc8 flags i m o ↔ sendmsgSpec fd 0x1fc8 flags i m o) ∧
      (sendmsgSpecSound fd 0x1fc8 flags i m o ↔ sendmsgSpecLinux fd 0x1fc8 flags i m o) := by
  unfold sendmsgSpecSound
  split
  · rename_i hc; exact ⟨Iff.rfl, sendmsgSpec_eq_linux fd _ flags i m o hc⟩
  · rename_i hc; rw [hmem] at hc; exact absurd (by decide) hc

/-- The sound table dispatches the sound arm at `sendmsg` (211) and LPS's arm elsewhere. -/
theorem soundTable_sendmsg :
    lookupArm soundSpecTable 211 = some (sendmsgArmWith sendmsgSpecSound) := by
  rw [soundSpecTable, lookupArm_withSendmsg]; rfl

theorem soundTable_other (n : Nat) (h : n ≠ 211) :
    lookupArm soundSpecTable n = lookupArm specTable n := by
  rw [soundSpecTable, lookupArm_withSendmsg]; simp [h]

end Silmaril.Process.LPS.Checks.SoundReference
