module

public import Silmaril.X86.Concurrency.Bridge.Crit.Defs
public import Silmaril.X86.Concurrency.Bridge.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.Robust.Thms

/-!
# The compiled mutex caller: kernel checks

One `decide +kernel` per fact: the caller checker accepts the
pinned image at `crit_add2` (about a second), and the explorer facts for the two-thread
instances `critC` and `racyC` (about 10 s together).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.Crit

open Silmaril.X86.Concurrency.Bridge
open Silmaril.X86.Concurrency.Bridge.Crit
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust

theorem ltv_thr : ltv (Prim.thr Code.image) Code.critOff cert = true := by decide +kernel

theorem crit_four : tsoCheck 2 Prim.Clients.fuel critC (xIs 4) = true := by decide +kernel

theorem crit_fin :
    (tsoStates 2 Prim.Clients.fuel critC).any (fun c => c.doneB 2 && c.drainedB && xIs 4 c) =
      true := by decide +kernel

theorem racy_two :
    (tsoStates 2 Prim.Clients.fuel racyC).any (fun c => c.doneB 2 && c.drainedB && xIs 2 c) =
      true := by decide +kernel

theorem rejects :
    ltv (Prim.thr Code.image) Code.critOff swapped = false ∧
    ltv (Prim.thr (Code.image.set 0x41 0xeb)) Code.critOff cert = false ∧
    ltv (Prim.thr (Code.image.set 0x49 0x01)) Code.critOff cert = false := by decide +kernel

/-! ## The minimal caller, run concretely -/

open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte

theorem mini_slot : encodeWords [miniS0.rip + 5] = miniSlot := by decide +kernel

theorem mini_l1 : Silmaril.X86.Ext.Loaded miniM1 0x1000 miniCode := by
  simp only [Silmaril.X86.Ext.Loaded, Memory.fetchBytes, Memory.readWith]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  simp [miniM1, miniCode, Memory.install, Memory.readBacking, Std.ExtHashMap.getElem_insert]

theorem mini_l2 : Silmaril.X86.Ext.Loaded miniM2 0x1000 miniCode := by
  simp only [Silmaril.X86.Ext.Loaded, Memory.fetchBytes, Memory.readWith]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  simp [miniM2, miniM1, miniCode, miniSlot, Memory.install, Memory.readBacking,
    Std.ExtHashMap.getElem_insert]

theorem mini_r2 :
    miniM2.readBytes (miniS1.read .rsp).toNat 8 = some (encodeWords [miniS0.rip + 5]) := by
  rw [mini_slot, show (miniS1.read .rsp).toNat = 0x2008 by decide +kernel]
  simp only [Memory.readBytes, Memory.readWith]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  simp [miniM2, miniM1, miniCode, miniSlot, Memory.install, Memory.readBacking,
    Std.ExtHashMap.getElem_insert]

theorem mini_w1 :
    miniM1.writeBytes (miniS0.read .rsp - 8).toNat (encodeWords [miniS0.rip + 5]) =
      some miniM2 := by
  rw [mini_slot, show (miniS0.read .rsp - 8).toNat = 0x2008 by decide +kernel]
  simp only [Memory.writeBytes]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  rfl

theorem mini_call : Atomic9.step ⟨miniS0, miniM1⟩ = some ⟨miniS1, miniM2⟩ := by
  refine Atomic9.step_of_listed (o := 0) (l := 5) (i := .open9 (.ext8 (.base (.call 0))))
    mini_l1 (by decide +kernel) (by decide) (by decide +kernel) ?_
  simp only [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.pushWord]
  erw [mini_w1]
  rfl

theorem mini_ret : Atomic9.step ⟨miniS1, miniM2⟩ = some ⟨miniS2, miniM2⟩ := by
  refine Atomic9.step_of_listed (o := 5) (l := 1) (i := .open9 (.ext8 (.base .ret)))
    mini_l2 (by decide +kernel) (by decide) (by decide +kernel) ?_
  simp only [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.popWord]
  erw [mini_r2]
  simp only [Option.bind_eq_bind, Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords,
    Option.pure_def]
  rfl

theorem mini_ltv : ltv miniT 0 miniCert = true := by decide +kernel

theorem mini_run :
    LRun miniT 0 miniCert.parts miniCert.lastLen miniCert.lastCert miniS0 miniObs miniS2 :=
  LRun.call (p := ⟨0, empty, ⟨5, 0, empty⟩⟩) (ps := []) (xs := []) (ys := [])
    (qc := ⟨miniM1, miniS1, miniM2⟩) (qr := ⟨miniM2, miniS2, miniM2⟩)
    (A9Run.nil miniS0) (by decide +kernel) rfl mini_l1 mini_call (A9Run.nil miniS1)
    (by decide +kernel) rfl mini_l2 mini_r2 mini_ret (LRun.last (A9Run.nil miniS2) (by decide +kernel))

end Silmaril.Proofs.X86.Concurrency.Bridge.Crit
