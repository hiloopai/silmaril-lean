module

public import Silmaril.X86.Ladder.LibMini.Defs
public import Silmaril.Proofs.X86.Ladder.LibMini.Memcpy
public import Silmaril.Proofs.X86.Ladder.LibMini.Memset
public import Silmaril.Proofs.X86.Ladder.LibMini.Strlen

/-!
# Proofs: the libmini contracts are not vacuous

Concrete machine states that meet the System V entry obligations (`FnContract.AbiEntry`) and
the entry conditions of `copyContract`, `fillContract` and `scanContract`, with nonzero
lengths. One region maps every address read/write/execute; the function's code is at
`codeAt = 0x400000`, the return address `retAt = 0x401000` at `rsp = 0x8ff8`, and the data at
`0x9000`. Applying `memcpy_total`, `memset_total`, `strlen_total` to them gives concrete
open-machine runs: `memcpy` copies `68 69` from `0x9000` to `0xa000`, `memset` writes three
bytes `0x41` (the low byte of `rsi = 0x12345641`; `n = 3` takes the peeled odd byte and one
unrolled iteration), `strlen` of `68 69 00` returns `2`. All return to `retAt` with
`rsp = 0x9000`.

The witnesses are kernel-checked through the memory lemmas `Memory.install_get`,
`Memory.install_outside` and `Memory.readWith_eq` (the hash-map memory does not reduce by
`decide`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.LibMini.NonVacuity

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region addressLimit)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86 Silmaril.X86.Stencils.ByteLoop Silmaril.X86.Ladder.LibMini

/-- One region mapping every address read/write/execute. -/
def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩
def codeAt : Word := 0x400000
def retAt : Word := 0x401000
def retEnc : List Byte := Silmaril.Machine.LittleEndian.encodeWords [retAt]
/-- Return address at `0x8ff8`, `data` at `0x9000`, `code` at `0x400000`. -/
def mem (code data : List Byte) : Memory :=
  ⟨[allRegion], Memory.install (Memory.install (Memory.install ∅ 0x8ff8 retEnc) 0x9000 data)
    0x400000 code⟩
/-- The entry state: `rip = codeAt`, `rsp = 0x8ff8`, three argument registers. -/
def st (code data : List Byte) (rdi rsi rdx : Word) : MState :=
  ⟨⟨fun r => match r with | .rdi => rdi | .rsi => rsi | .rdx => rdx | .rsp => 0x8ff8 | _ => 0,
    codeAt, ⟨none, none, none, none, none, none⟩, 0⟩, mem code data⟩

variable {code data : List Byte}

theorem permits_all (acc) (a : Nat) (ha : a < 2 ^ 64) : (mem code data).permits acc a = true := by
  have : a < 18446744073709551616 := ha
  cases acc <;>
    simp [Memory.permits, mem, allRegion, Region.Contains, Silmaril.Process.Permissions.allows, this]

theorem permitted (acc) (a n : Nat) (h : a + n < 2 ^ 64) : (mem code data).Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  exact ⟨by simp only [addressLimit]; omega, by simp only [addressLimit]; omega,
    fun i _ => permits_all acc _ (by omega)⟩

theorem code_get (i : Nat) (hi : i < code.length) :
    (mem code data).bytes.get? (0x400000 + i) = some code[i] :=
  Memory.install_get _ _ _ _ hi

theorem data_get (hd : data.length < 0x1000) (i : Nat) (hi : i < data.length) :
    (mem code data).bytes.get? (0x9000 + i) = some data[i] := by
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  exact Memory.install_get _ _ _ _ hi

theorem ret_get (i : Nat) (hi : i < retEnc.length) :
    (mem code data).bytes.get? (0x8ff8 + i) = some retEnc[i] := by
  simp only [retEnc, Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
    List.length_nil] at hi
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  exact Memory.install_get _ _ _ _ (by simp [retEnc]; omega)

theorem loaded (hc : code.length < 0x1000) : Silmaril.X86.Ext.Loaded (mem code data) codeAt code :=
  Memory.readWith_eq _ _ _ code (permitted _ _ _ (by rw [show codeAt.toNat = 0x400000 from rfl]; omega))
    code_get

theorem ret_read : (mem code data).readBytes 0x8ff8 8 = some retEnc :=
  Memory.readWith_eq _ _ _ retEnc (permitted _ _ _ (by decide)) ret_get

theorem retOf_st {a b c : Word} :
    FnContract.retOf (st code data a b c).core (st code data a b c).memory = retAt := by
  simp only [FnContract.retOf]
  rw [show ((st code data a b c).core.read .rsp).toNat = 0x8ff8 from rfl,
    show (st code data a b c).memory = mem code data from rfl, ret_read]; decide

theorem abi {a b c : Word} :
    FnContract.AbiEntry (st code data a b c).core (st code data a b c).memory :=
  ⟨show (0x8ff8 : Word).toNat % 16 = 8 by decide, by rw [retOf_st]; exact ret_read⟩

/-- `memcpy` of two bytes `68 69` from `0x9000` to `0xa000`: the entry conditions hold. -/
theorem memcpy_witness : FnContract.AbiEntry (st memcpyCode [0x68, 0x69] 0xa000 0x9000 2).core
      (st memcpyCode [0x68, 0x69] 0xa000 0x9000 2).memory ∧
    (copyContract memcpyCode codeAt).entry (st memcpyCode [0x68, 0x69] 0xa000 0x9000 2) := by
  refine ⟨abi, rfl, loaded (by decide), fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
  · have : i < 2 := hi
    rw [show arg0 (st memcpyCode [0x68, 0x69] 0xa000 0x9000 2) = 0xa000 from rfl]
    exact ⟨by simp only [addressLimit]; omega, permits_all _ _ (by omega)⟩
  · have : i < 2 := hi
    rw [show arg1 (st memcpyCode [0x68, 0x69] 0xa000 0x9000 2) = 0x9000 from rfl,
      show (st _ _ _ _ _).memory = mem memcpyCode [0x68, 0x69] from rfl,
      data_get (by decide) i (by simpa using this)]
    exact ⟨by simp only [addressLimit]; omega, permits_all _ _ (by omega), rfl⟩
  all_goals (right; right; decide)

/-- `memset(0xa000, 0x12345641, 3)`: the entry conditions hold. -/
theorem memset_witness : FnContract.AbiEntry (st memsetCode [] 0xa000 0x12345641 3).core
      (st memsetCode [] 0xa000 0x12345641 3).memory ∧
    (fillContract memsetCode codeAt).entry (st memsetCode [] 0xa000 0x12345641 3) := by
  refine ⟨abi, rfl, loaded (by decide), fun i hi => ?_, ?_, ?_⟩
  · have : i < 3 := hi
    rw [show arg0 (st memsetCode [] 0xa000 0x12345641 3) = 0xa000 from rfl]
    exact ⟨by simp only [addressLimit]; omega, permits_all _ _ (by omega)⟩
  all_goals (right; right; decide)

/-- `strlen` of `68 69 00` at `0x9000`: the entry conditions hold, with length `2`. -/
theorem strlen_witness : FnContract.AbiEntry (st strlenCode [0x68, 0x69, 0] 0x9000 0 0).core
      (st strlenCode [0x68, 0x69, 0] 0x9000 0 0).memory ∧
    CStr (st strlenCode [0x68, 0x69, 0] 0x9000 0 0).memory (arg0 (st strlenCode [0x68, 0x69, 0] 0x9000 0 0)) 2 := by
  refine ⟨abi, ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩⟩
  all_goals rw [show arg0 _ = 0x9000 from rfl, show (st _ _ _ _ _).memory = mem strlenCode [0x68, 0x69, 0] from rfl]
  · refine ⟨by simp only [addressLimit]; omega, permits_all _ _ (by omega), ?_⟩
    rw [data_get (by decide) i (by simpa using hi)]; rfl
  · rw [data_get (by decide) j (by simp; omega)]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp
  · exact data_get (by decide) 2 (by decide)

/-- **`memcpy` runs**: the concrete call copies the two bytes and returns `0xa000`. -/
theorem memcpy_concrete : ∃ fin, Reaches Open.step (st memcpyCode [0x68, 0x69] 0xa000 0x9000 2) fin ∧
    fin.core.rip = retAt ∧ fin.core.read .rax = 0xa000 ∧ fin.core.read .rsp = 0x9000 ∧
    fin.memory.bytes.get? 0xa000 = some 0x68 ∧ fin.memory.bytes.get? 0xa001 = some 0x69 := by
  obtain ⟨fin, hrun, hres⟩ := memcpy_total codeAt _ trivial memcpy_witness.1 memcpy_witness.2
  have hp := hres.post.2.2
  refine ⟨fin, hrun, ?_, hres.post.1, hres.abi.stack, ?_, ?_⟩
  · rw [hres.abi.pc]; exact retOf_st
  · exact (hp 0 (by decide)).trans (data_get (by decide) 0 (by decide))
  · exact (hp 1 (by decide)).trans (data_get (by decide) 1 (by decide))

/-- **`memset` runs**: three bytes `0x41`, returning `0xa000`. -/
theorem memset_concrete : ∃ fin, Reaches Open.step (st memsetCode [] 0xa000 0x12345641 3) fin ∧
    fin.core.rip = retAt ∧ fin.core.read .rax = 0xa000 ∧ fin.core.read .rsp = 0x9000 ∧
    ∀ i < 3, fin.memory.bytes.get? (0xa000 + i) = some 0x41 := by
  obtain ⟨fin, hrun, hres⟩ := memset_total codeAt _ trivial memset_witness.1 memset_witness.2
  refine ⟨fin, hrun, by rw [hres.abi.pc]; exact retOf_st, hres.post.1, hres.abi.stack, ?_⟩
  intro i hi
  exact hres.post.2.2 i hi

/-- **`strlen` runs**: it returns `2`. -/
theorem strlen_concrete : ∃ fin, Reaches Open.step (st strlenCode [0x68, 0x69, 0] 0x9000 0 0) fin ∧
    fin.core.rip = retAt ∧ fin.core.read .rax = 2 ∧ fin.core.read .rsp = 0x9000 := by
  obtain ⟨fin, hrun, hres⟩ := strlen_total codeAt _ trivial strlen_witness.1
    ⟨rfl, loaded (by decide), 2, strlen_witness.2⟩
  exact ⟨fin, hrun, by rw [hres.abi.pc]; exact retOf_st, hres.post.1 2 strlen_witness.2,
    hres.abi.stack⟩

end Silmaril.Proofs.X86.Ladder.LibMini.NonVacuity
