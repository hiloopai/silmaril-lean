module

public import Silmaril.Servers.LinuxHello.Defs
public import Silmaril.Process.LPS.Table

/-!
# A Linux hello server loop: its arms are LPS's

For `Silmaril.Servers.LinuxHello.Thms`: the four arms of `serverTable` are the arms of LPS's
generic table, and the loop only traps with their numbers, so its runs under `serverSpec` are
exactly its runs under LPS's whole table `syscallSpec`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.LinuxHello

open Silmaril.Process Silmaril.Process.LPS Silmaril.Servers.LinuxHello

theorem lookupArm_eq (n : Nat) (h : n = 202 ∨ n = 63 ∨ n = 206 ∨ n = 57) :
    lookupArm specTable n = lookupArm serverTable n := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem pending_mem {s : St} {x : Word} (h : pending s = some x) :
    x.toNat = 202 ∨ x.toNat = 63 ∨ x.toNat = 206 ∨ x.toNat = 57 := by
  unfold pending at h
  split at h <;> cases h <;> decide

theorem serverSpec_iff (i : SyscallInput) (m : LPS.Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat = 202 ∨ i.sysno.toNat = 63 ∨ i.sysno.toNat = 206 ∨ i.sysno.toNat = 57) :
    serverSpec i m o ↔ syscallSpec i m o := by
  unfold serverSpec syscallSpec dispatch
  rw [lookupArm_eq _ h]

theorem lstep_iff {segs : List Segment} {refused : RefusalFilter} {c c' : Config isa}
    {r : StepRecord} : LStep segs serverSpec refused c r c' ↔ LStep segs syscallSpec refused c r c' := by
  constructor
  · intro s
    cases s with
    | instr a b d => exact .instr a b d
    | @syscall ms _ x8 _ _ _ _ a b d e f g =>
      exact .syscall a b ((serverSpec_iff (sysInput isa segs ms x8) _ _
        (pending_mem (s := ms) b)).1 d) e f g
    | @exit ms _ x8 _ _ _ _ a b d e f =>
      exact .exit a b ((serverSpec_iff (sysInput isa segs ms x8) _ _
        (pending_mem (s := ms) b)).1 d) e f
    | @killed ms _ x8 _ _ _ _ a b d e =>
      exact .killed a b ((serverSpec_iff (sysInput isa segs ms x8) _ _
        (pending_mem (s := ms) b)).1 d) e
  · intro s
    cases s with
    | instr a b d => exact .instr a b d
    | @syscall ms _ x8 _ _ _ _ a b d e f g =>
      exact .syscall a b ((serverSpec_iff (sysInput isa segs ms x8) _ _
        (pending_mem (s := ms) b)).2 d) e f g
    | @exit ms _ x8 _ _ _ _ a b d e f =>
      exact .exit a b ((serverSpec_iff (sysInput isa segs ms x8) _ _
        (pending_mem (s := ms) b)).2 d) e f
    | @killed ms _ x8 _ _ _ _ a b d e =>
      exact .killed a b ((serverSpec_iff (sysInput isa segs ms x8) _ _
        (pending_mem (s := ms) b)).2 d) e

theorem hstar_iff {segs : List Segment} {refused : RefusalFilter} {c c' : Config isa}
    {h : List StepRecord} :
    HStar segs serverSpec refused c h c' ↔ HStar segs syscallSpec refused c h c' := by
  constructor
  · intro s
    induction s with
    | refl => exact .refl _
    | step st _ ih => exact .step (lstep_iff.1 st) ih
  · intro s
    induction s with
    | refl => exact .refl _
    | step st _ ih => exact .step (lstep_iff.2 st) ih

end Silmaril.Proofs.Servers.LinuxHello
