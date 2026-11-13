module

public import Silmaril.Machine.X86.Lir.Step.Defs

/-!
# PUSH, POP, CALL and RET on the compiled stack

Instruction facts for the stack instructions of prologues, epilogues and call
sites, stated with `WordAt` on stack addresses given as natural numbers.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

set_option linter.unusedSectionVars false

theorem sub8_toNat {e : Nat} (h8 : 8 ≤ e) (he : e < 2 ^ 64) :
    (BitVec.ofNat 64 e - 8#64).toNat = e - 8 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]
  simp only [Nat.reducePow, Nat.reduceMod]
  omega

theorem sub8_eq {e : Nat} (h8 : 8 ≤ e) (he : e < 2 ^ 64) :
    BitVec.ofNat 64 e - 8#64 = BitVec.ofNat 64 (e - 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [sub8_toNat h8 he, BitVec.toNat_ofNat]
  omega

theorem add8_eq (e : Nat) : BitVec.ofNat 64 e + 8#64 = BitVec.ofNat 64 (e + 8) := by
  rw [BitVec.ofNat_add]

theorem ofNat_toNat_lt {e : Nat} (he : e < 2 ^ 64) : (BitVec.ofNat 64 e).toNat = e := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]

theorem exec_push_ok (s : State) (m : Memory) (r : Reg) {m' : Memory}
    (h : X86.pushWord s m (s.read r) = some (s.write .rsp (s.read .rsp - 8#64), m')) :
    Ext.exec (.push r) s m =
      .ok { s.write .rsp (s.read .rsp - 8#64) with
        rip := s.rip + BitVec.ofNat 64 (Ext.encode (.push r)).length } m' := by
  simp only [Ext.exec, h, Ext.retire]; rfl

theorem exec_pop_ok (s : State) (m : Memory) (r : Reg) {v : Word}
    (h : X86.popWord s m = some (v, s.write .rsp (s.read .rsp + 8#64))) :
    Ext.exec (.pop r) s m =
      .ok { (s.write .rsp (s.read .rsp + 8#64)).write r v with
        rip := s.rip + BitVec.ofNat 64 (Ext.encode (.pop r)).length } m := by
  simp only [Ext.exec, h, Ext.retire, Option.map_some]; rfl

theorem exec_ret_ok (s : State) (m : Memory) {v : Word}
    (h : X86.popWord s m = some (v, s.write .rsp (s.read .rsp + 8#64))) :
    Ext.exec .ret s m = .ok { s.write .rsp (s.read .rsp + 8#64) with rip := v } m := by
  simp only [Ext.exec, h]

theorem exec_call_ok (s : State) (m : Memory) (rel : BitVec 32) {m' : Memory}
    (h : X86.pushWord s m (s.rip + BitVec.ofNat 64 5) =
      some (s.write .rsp (s.read .rsp - 8#64), m')) :
    Ext.exec (.call rel) s m =
      .ok { s.write .rsp (s.read .rsp - 8#64) with
        rip := s.rip + BitVec.ofNat 64 5 + rel.signExtend 64 } m' := by
  simp only [Ext.exec, show Ext.Instr.length (.call rel) = 5 from rfl, h]

section

variable {S : Space} {n : Nat} (hv : S.Valid n)
include hv

/-- A push below the stack pointer `e`. -/
theorem push_at {s : State} {m : Memory} (hreg : m.regions = S.regions n) {e : Nat}
    (hrsp : s.read .rsp = BitVec.ofNat 64 e) (hlo : S.stackLo + 8 ≤ e) (hhi : e ≤ S.stackHi)
    (v : Word) :
    ∃ m', X86.pushWord s m v = some (s.write .rsp (BitVec.ofNat 64 (e - 8)), m') ∧
      WordAt m' (e - 8) v ∧ Memory.WritesOnly m m' (e - 8) 8 := by
  have he : e < 2 ^ 64 := by have := hv.stack_end; omega
  have hp : m.Permitted .write (s.read .rsp - 8#64).toNat 8 := by
    rw [hrsp, sub8_toNat (by omega) he]
    exact permitted_stack hreg hv .write (by decide) (by omega) (by omega)
  obtain ⟨m', h1, h2, h3⟩ := pushWord_some v hp
  rw [hrsp, sub8_eq (by omega) he] at h1
  rw [hrsp, sub8_toNat (by omega) he] at h2 h3
  exact ⟨m', h1, h2, h3⟩

/-- A pop of the word at the stack pointer `e`. -/
theorem pop_at {s : State} {m : Memory} (hreg : m.regions = S.regions n) {e : Nat}
    (hrsp : s.read .rsp = BitVec.ofNat 64 e) (hlo : S.stackLo ≤ e) (hhi : e + 8 ≤ S.stackHi)
    {v : Word} (hw : WordAt m e v) :
    X86.popWord s m = some (v, s.write .rsp (BitVec.ofNat 64 (e + 8))) := by
  have he : e < 2 ^ 64 := by have := hv.stack_end; omega
  have := popWord_of_wordAt (s := s) (m := m) (v := v) (by rw [hrsp, ofNat_toNat_lt he]; exact hw)
    (by rw [hrsp, ofNat_toNat_lt he]; exact permitted_stack hreg hv .read (by decide) hlo hhi)
  rw [this, hrsp, add8_eq]

end

end Silmaril.X86.Backend
