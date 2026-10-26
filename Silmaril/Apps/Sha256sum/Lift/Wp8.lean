module

public import Silmaril.Apps.Sha256sum.Lift.Listing
public import Silmaril.Apps.Sha256sum.Lift.Sim

/-! # The VC generator for `sha256sum-min`, one instruction at a time

`Sys.wp` (`Lift.Sim`) is generic in the machine. This file instantiates its step for
`X86Sys.x86Machine8` at the lifted listing `Gen.listing`:

* `wp_instr`: at a listed address, the next `wp` layer is the execution of the listed
  instruction — and *only* in the retiring case: a fault makes the machine stuck, which needs
  nothing for safety. The next state's memory satisfies `Code` again (`Code.of_ro`), and that
  is handed to the continuation, so `Code` is threaded with no per-step proof.
* `wp_syscall`: at the single `syscall` (0x40101c, in `sc3`), the request is decoded by
  `X86Sys.decode`; a call must be matched by the reference machine.

`instrAt` is a lookup in the listing's address-bounded chunks; at a literal address it is evaluated by `rfl`
(`decide`), which is how a tactic finds the instruction without a lemma per address.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Lift

open Silmaril.Apps.Sha256sum
open Silmaril.Apps.Sha256sum.Sys
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Process (Memory Byte)
open Silmaril.Process.CLI
open Silmaril.X86 (Word maxInstrLength)

/-- The lifted program: the instruction at an address of the driver. -/
def instrAt (a : Nat) : Option (X86.Ext8.Instr × Nat) := lookupChunks Gen.chunks a

theorem instrAt_ok {a : Nat} {i : X86.Ext8.Instr} {n : Nat} (h : instrAt a = some (i, n)) :
    EntryOk a i n :=
  Listing.sound Gen.listing_ok (lookupChunks_mem h)

/-- The system step at a listed instruction. -/
theorem step8_instr {r11Of : Core → Word} {s : XState} (hf : s.faulted = false)
    (hc : Code s.memory) {i : X86.Ext8.Instr} {n : Nat}
    (hl : instrAt s.core.rip.toNat = some (i, n)) :
    step8 r11Of s = match X86.Ext8.exec i s.core s.memory n with
      | .ok c m => .tau { s with core := c, memory := m }
      | _ => .stuck := by
  have e := instrAt_ok hl
  unfold step8 stepWith
  rw [ite_eq_right (by simp [hf]), hc.step e.inText rfl e.notSyscall e.decode e.pos e.le]
  cases X86.Ext8.exec i s.core s.memory n <;> rfl

variable {A : Machine} {E : Sys.Env}

/-- **One instruction of the VC.** -/
theorem wp_instr {r11Of : Core → Word}
    {R : (x86Machine8 r11Of).State → KState → A.State → Prop}
    {isCut : (x86Machine8 r11Of).State → Bool} {fuel : Nat} {s : XState} {k : KState} {a : A.State}
    (hf : s.faulted = false) (hc : Code s.memory) {i : X86.Ext8.Instr} {n : Nat}
    (hl : instrAt s.core.rip.toNat = some (i, n))
    (h : match X86.Ext8.exec i s.core s.memory n with
      | .ok c m => Code m →
          wpNext (B := x86Machine8 r11Of) R isCut (wp (B := x86Machine8 r11Of) E R isCut fuel) ({ s with core := c, memory := m } : XState) k a
      | _ => True) :
    wp (B := x86Machine8 r11Of) E R isCut (fuel + 1) s k a := by
  refine Sys.wp_succ.mpr ?_
  have e : (x86Machine8 r11Of).step s = step8 r11Of s := rfl
  rw [e, step8_instr hf hc hl]
  cases hx : X86.Ext8.exec i s.core s.memory n with
  | ok c m =>
    rw [hx] at h
    exact h (hc.of_ro (X86.Ext8.exec8_ro hx))
  | _ => trivial

/-- `wp_instr` at a literal address: `hrip` is the address equation (often `rfl` once the
state is normalised), and `hl` is closed by `rfl`. -/
theorem wp_instr' {r11Of : Core → Word}
    {R : (x86Machine8 r11Of).State → KState → A.State → Prop}
    {isCut : (x86Machine8 r11Of).State → Bool} {fuel : Nat} {s : XState} {k : KState}
    {a : A.State} (hf : s.faulted = false) (hc : Code s.memory) {addr : Nat}
    (hrip : s.core.rip = BitVec.ofNat 64 addr) {i : X86.Ext8.Instr} {n : Nat}
    (hl : instrAt addr = some (i, n))
    (h : match X86.Ext8.exec i s.core s.memory n with
      | .ok c m => Code m →
          wpNext (B := x86Machine8 r11Of) R isCut (wp (B := x86Machine8 r11Of) E R isCut fuel)
            ({ s with core := c, memory := m } : XState) k a
      | _ => True) :
    wp (B := x86Machine8 r11Of) E R isCut (fuel + 1) s k a := by
  have e := instrAt_ok hl
  have hb : addr < 2 ^ 64 := by
    have := e.inText.2; unfold textBase textSize maxInstrLength at this; omega
  refine wp_instr hf hc ?_ h
  rw [hrip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]; exact hl

/-! ## The system call -/

/-- The only `syscall` instruction of the binary (in `sc3`). -/
def syscallAddr : Nat := 0x40101c

theorem syscall_inText : InText syscallAddr := by decide
theorem syscall_window : (window syscallAddr).take 2 = X86Linux.syscallBytes := by decide +kernel

/-- **The system call of the VC.** `trapped` is the core the kernel sees. -/
theorem wp_syscall {r11Of : Core → Word}
    {R : (x86Machine8 r11Of).State → KState → A.State → Prop}
    {isCut : (x86Machine8 r11Of).State → Bool} {fuel : Nat} {s : XState} {k : KState} {a : A.State}
    (hf : s.faulted = false) (hc : Code s.memory) (hrip : s.core.rip.toNat = syscallAddr)
    (h : let c := { s.core with rip := s.core.rip + 2 }
      match X86Sys.decode c s.memory with
      | none => True
      | some (.exit st) => ∃ a', Taus A a a' ∧ A.step a' = .exit st
      | some (.brk addr) => wpNext (B := x86Machine8 r11Of) R isCut (wp (B := x86Machine8 r11Of) E R isCut fuel) (brkStep r11Of s c addr) k a
      | some (.call call) => ∃ a' g, Taus A a a' ∧ A.step a' = .call call g ∧
          ∀ r k', E k call r k' →
            wpNext (B := x86Machine8 r11Of) R isCut (wp (B := x86Machine8 r11Of) E R isCut fuel) (resume r11Of s c call r) k' (g r)) :
    wp (B := x86Machine8 r11Of) E R isCut (fuel + 1) s k a := by
  refine Sys.wp_succ.mpr ?_
  have e : (x86Machine8 r11Of).step s = step8 r11Of s := rfl
  rw [e]
  unfold step8 stepWith
  rw [ite_eq_right (by simp [hf]), hc.step_syscall syscall_inText hrip syscall_window]
  simp only at h ⊢
  revert h
  cases X86Sys.decode { s.core with rip := s.core.rip + 2 } s.memory with
  | none => intro; trivial
  | some req =>
    cases req with
    | exit st => exact id
    | brk addr => exact id
    | call call => exact id

/-- `resume` keeps `Code` (a `read` reply is stored by `writeBytes`, or the state faults). -/
theorem code_resume {r11Of : Core → Word} {s : XState} (hc : Code s.memory) (c : Core)
    (call : Call) (r : Ret) : Code (X86Sys.resume r11Of s c call r).memory := by
  unfold X86Sys.resume
  split
  · split
    · rename_i m hm; exact hc.of_ro (X86.Ext.writeBytes_ro hm)
    · exact hc
  · exact hc

end Silmaril.Apps.Sha256sum.Lift
