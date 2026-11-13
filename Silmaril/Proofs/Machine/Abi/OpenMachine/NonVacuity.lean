module

public import Silmaril.Proofs.Machine.Abi.OpenMachine.LeafArith
/-!
# Non-vacuity of `clamp_sat`

A concrete `Ffi.State` that places `clamp_i32(5, 0, 3)` by the System V plan and meets the
room: the 181 code bytes at `base = 0x401370`, `rip` at `clamp_i32`, return address
`0x401000` (outside the code) at `rsp = 0x8ff8`. One region maps every address. The memory
construction follows track A's `LibMini.NonVacuity` (copied, since that module is a `Proofs`
module of another topic). Applying `clamp_sat` to it gives an outcome of `callModel`,
observed by the System V read-back as the C value `3`. `clamp_rejects_id` shows that the
same bridge refutes a mutated contract (`clampIdC`: return the first argument).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.OpenMachine.NonVacuity

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region addressLimit)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.X86.Ladder.LeafArith
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options callOf)
open Silmaril.Machine.Abi.OpenMachine
open Silmaril.Proofs.Machine.Abi.OpenMachine

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩
def retAt : Word := 0x401000
def retEnc : List Byte := Silmaril.Machine.LittleEndian.encodeWords [retAt]

/-- Return address at `0x8ff8`, the rung 01 code at `0x401370`. -/
def mem : Memory :=
  ⟨[allRegion], Memory.install (Memory.install ∅ 0x8ff8 retEnc) 0x401370 code⟩

/-- `rip` at `clamp_i32`, `rsp = 0x8ff8`, arguments `5, 0, 3`. -/
def st : MState :=
  ⟨⟨fun r => match r with | .rdi => 5 | .rsi => 0 | .rdx => 3 | .rsp => 0x8ff8 | _ => 0,
    base + BitVec.ofNat 64 0x30, ⟨none, none, none, none, none, none⟩, 0⟩, mem⟩

def ffiSt : Ffi.State :=
  ⟨st, fun _ => 0, fun _ => 0, false, true, 0, 0, 0⟩

theorem permits_all (acc) (a : Nat) (ha : a < 2 ^ 64) : mem.permits acc a = true := by
  have : a < 18446744073709551616 := ha
  cases acc <;>
    simp [Memory.permits, mem, allRegion, Silmaril.Process.Region.Contains,
      Silmaril.Process.Permissions.allows, this]

theorem permitted (acc) (a n : Nat) (h : a + n < 2 ^ 64) : mem.Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  exact ⟨by simp only [addressLimit]; omega, by simp only [addressLimit]; omega,
    fun i _ => permits_all acc _ (by omega)⟩

theorem code_get (i : Nat) (hi : i < code.length) :
    mem.bytes.get? (0x401370 + i) = some Ladder.LeafArith.code[i] :=
  Memory.install_get _ _ _ _ hi

theorem ret_get (i : Nat) (hi : i < retEnc.length) :
    mem.bytes.get? (0x8ff8 + i) = some retEnc[i] := by
  simp only [retEnc, Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
    List.length_nil] at hi
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  exact Memory.install_get _ _ _ _ (by simp [retEnc]; omega)

theorem code_length : code.length = 181 := by decide +kernel

theorem loaded : Silmaril.X86.Ext.Loaded mem base code :=
  Memory.readWith_eq _ _ _ code
    (permitted _ _ _ (by rw [show base.toNat = 0x401370 from rfl, code_length]; omega)) code_get

theorem ret_read : mem.readBytes 0x8ff8 8 = some retEnc :=
  Memory.readWith_eq _ _ _ retEnc (permitted _ _ _ (by decide)) ret_get

theorem retOf_st : FnContract.retOf st.core st.memory = retAt := by
  simp only [FnContract.retOf]
  rw [show (st.core.read .rsp).toNat = 0x8ff8 from rfl, show st.memory = mem from rfl, ret_read]
  decide

/-- The C arguments `5, 0, 3`. -/
def args : vocab.Args clampProto :=
  .cons (5 : BitVec 32) (.cons (0 : BitVec 32) (.cons (3 : BitVec 32) .nil))

theorem entry (o : Options) : (sysv o).Entry clampProto args ffiSt := by
  refine ⟨retAt, rfl, ⟨⟨rfl, _, rfl, (chunk32_iff _ .rdi _).2 rfl⟩,
    ⟨rfl, _, rfl, (chunk32_iff _ .rsi _).2 rfl⟩, ⟨rfl, _, rfl, (chunk32_iff _ .rdx _).2 rfl⟩,
    trivial⟩, ?_, ?_, ret_read, rfl, rfl, rfl, fun _ h => nomatch h⟩
  · change ((0x8ff8 : Word).toNat + 8) % 16 = 0
    decide
  · change (0x8ff8 : Word).toNat + 8 + alignUp (8 * (3 - 6)) 16 ≤ 2 ^ 64
    decide

theorem room : Room base code 0x30 ffiSt := by
  refine ⟨loaded, rfl, fun o ho => ?_⟩
  rw [code_length] at ho
  show FnContract.retOf st.core st.memory ≠ _
  rw [retOf_st]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show retAt.toNat = 0x401000 from rfl,
    show base.toNat = 0x401370 from rfl] at this
  omega

/-- **`clamp_sat` is not vacuous**: on the concrete entry state, `callModel` has an outcome,
and the System V read-back observes the C value `clamp_i32(5, 0, 3) = 3`. -/
theorem clamp_nonvacuous (o : Options) :
    ∃ t ∈ callModel ffiSt, (sysv o).Observe clampProto ffiSt t (some (3 : BitVec 32)) := by
  have pre : (within ((sysv o).translate clampProto clampC) (Room base code 0x30)).pre ffiSt :=
    ⟨⟨args, entry o, trivial⟩, room⟩
  obtain ⟨⟨t, ran⟩, post⟩ := clamp_sat o ffiSt pre
  refine ⟨t, ran, ?_⟩
  obtain ⟨ob, observed⟩ := (sysv o).observe_total clampProto ffiSt t
  have h := post t ran args (entry o) trivial ob observed
  have h3 : clampSpec 5 0 3 = 3 := by decide
  have h' : ob = some (clampSpec 5 0 3) := h
  rw [h3] at h'
  exact h' ▸ observed

theorem clamp_exists (o : Options) :
    ∃ s, (within ((sysv o).translate clampProto clampC) (Room base code 0x30)).pre s ∧
      ∃ t ∈ callModel s, (sysv o).Observe clampProto s t (some (3 : BitVec 32)) :=
  ⟨ffiSt, ⟨⟨args, entry o, trivial⟩, room⟩, clamp_nonvacuous o⟩

/-- **The bridge discriminates contracts**: the decoded `clamp_i32` does *not* satisfy the
System V translation of the mutated contract `clampIdC` (on the concrete state, the read-back is
`3`, not the first argument `5`). -/
theorem clamp_rejects_id (o : Options) :
    ¬ Contracts.Sat callModel
      (within ((sysv o).translate clampProto clampIdC) (Room base code 0x30)) := by
  intro bad
  have pre : (within ((sysv o).translate clampProto clampC) (Room base code 0x30)).pre ffiSt :=
    ⟨⟨args, entry o, trivial⟩, room⟩
  obtain ⟨⟨t, ran⟩, post⟩ := clamp_sat o ffiSt pre
  obtain ⟨-, post'⟩ := bad ffiSt ⟨⟨args, entry o, trivial⟩, room⟩
  obtain ⟨ob, observed⟩ := (sysv o).observe_total clampProto ffiSt t
  have h : ob = some (clampSpec 5 0 3) := post t ran args (entry o) trivial ob observed
  have h' : ob = some (5 : BitVec 32) := post' t ran args (entry o) trivial ob observed
  have h3 : clampSpec 5 0 3 = 3 := by decide
  rw [h, h3] at h'
  exact absurd (Option.some.inj h') (by decide)

end Silmaril.Proofs.Machine.Abi.OpenMachine.NonVacuity
