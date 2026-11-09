module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Crc32z
public import Silmaril.X86.Ladder.ZlibChecksums.Spec.Thms

/-!
# Proofs: the `crc32_z` contract is not vacuous

A concrete machine state meeting the System V entry obligations (`FnContract.AbiEntry`) and
`crc32zContract`'s entry condition: one region maps every address read/write/execute;
`crc32_z`'s code is at `codeAt = 0x400000`, the return address `retAt = 0x401000` at
`rsp = 0x8ff8`, the input `"123456789"` at `0x9000`, and `crc_table`'s 2048 bytes at
`0x4021e0`. Nine bytes take one pass of the 8× unrolled body and one byte of the tail loop.
Applying `crc32z_total` gives a concrete open-machine run returning the published check value
`0xcbf43926` to `retAt` with `rsp = 0x9000`.

Same construction as libmini's non-vacuity witnesses (kernel-checked through
`Memory.install_get`, `Memory.install_outside`, `Memory.readWith_eq`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.NonVacuity

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region addressLimit)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86 Silmaril.X86.Stencils.ByteLoop Silmaril.X86.Ladder.ZlibChecksums

/-- One region mapping every address read/write/execute. -/
def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩
def codeAt : Word := 0x400000
def retAt : Word := 0x401000
def retEnc : List Byte := Silmaril.Machine.LittleEndian.encodeWords [retAt]

/-- Return address at `0x8ff8`, `nine` at `0x9000`, the table at `0x4021e0`, the code at
`0x400000`. -/
def mem : Memory :=
  ⟨[allRegion], Memory.install (Memory.install (Memory.install (Memory.install ∅ 0x8ff8 retEnc)
    0x9000 nine) 0x4021e0 crcTableBytes) 0x400000 crc32zCode⟩

/-- The entry state: `crc32_z(0, "123456789", 9)`. -/
def st : MState :=
  ⟨⟨fun r => match r with | .rsi => 0x9000 | .rdx => 9 | .rsp => 0x8ff8 | _ => 0,
    codeAt, ⟨none, none, none, none, none, none⟩, 0⟩, mem⟩

theorem permits_all (acc) (a : Nat) (ha : a < 2 ^ 64) : mem.permits acc a = true := by
  have : a < 18446744073709551616 := ha
  cases acc <;>
    simp [Memory.permits, mem, allRegion, Region.Contains, Silmaril.Process.Permissions.allows, this]

theorem permitted (acc) (a n : Nat) (h : a + n < 2 ^ 64) : mem.Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  exact ⟨by simp only [addressLimit]; omega, by simp only [addressLimit]; omega,
    fun i _ => permits_all acc _ (by omega)⟩

theorem code_len : crc32zCode.length = 291 := by decide +kernel
theorem tbl_len : crcTableBytes.length = 2048 := by decide +kernel

theorem code_get (i : Nat) (hi : i < crc32zCode.length) :
    mem.bytes.get? (0x400000 + i) = some crc32zCode[i] :=
  Memory.install_get _ _ _ _ hi

theorem tbl_get (i : Nat) (hi : i < crcTableBytes.length) :
    mem.bytes.get? (0x4021e0 + i) = some crcTableBytes[i] := by
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by rw [code_len]; omega)]
  exact Memory.install_get _ _ _ _ hi

theorem data_get (i : Nat) (hi : i < nine.length) :
    mem.bytes.get? (0x9000 + i) = some nine[i] := by
  have : i < 9 := hi
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  exact Memory.install_get _ _ _ _ hi

theorem ret_get (i : Nat) (hi : i < retEnc.length) :
    mem.bytes.get? (0x8ff8 + i) = some retEnc[i] := by
  simp only [retEnc, Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
    List.length_nil] at hi
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by omega)]
  exact Memory.install_get _ _ _ _ (by simp [retEnc]; omega)

theorem loaded : Silmaril.X86.Ext.Loaded mem codeAt crc32zCode :=
  Memory.readWith_eq _ _ _ crc32zCode
    (permitted _ _ _ (by rw [show codeAt.toNat = 0x400000 from rfl, code_len]; omega)) code_get

theorem tableAt : Stencils.TableFold.TableAt mem crcTblAddr.toNat 256 crcT := by
  rw [show crcTblAddr.toNat = 0x4021e0 from rfl]
  apply tableAt_of_readBytes
  have := Memory.readWith_eq mem .read 0x4021e0 crcTableBytes
    (permitted _ _ _ (by rw [tbl_len]; omega)) tbl_get
  rwa [tbl_len] at this

theorem ret_read : mem.readBytes 0x8ff8 8 = some retEnc :=
  Memory.readWith_eq _ _ _ retEnc (permitted _ _ _ (by decide)) ret_get

theorem retOf_st : FnContract.retOf st.core st.memory = retAt := by
  simp only [FnContract.retOf]
  rw [show (st.core.read .rsp).toNat = 0x8ff8 from rfl, show st.memory = mem from rfl, ret_read]
  decide

theorem abi : FnContract.AbiEntry st.core st.memory :=
  ⟨show (0x8ff8 : Word).toNat % 16 = 8 by decide, by rw [retOf_st]; exact ret_read⟩

theorem buf_st : buf st = nine := by
  apply List.ext_getElem (by
    simp only [buf, Stencils.TableFold.bytesAt, List.length_map, List.length_range]
    rfl)
  intro i h1 h2
  have hi : i < 9 := by simpa [nine] using h2
  simp only [buf, Stencils.TableFold.bytesAt, List.getElem_map, List.getElem_range,
    Stencils.TableFold.byteAt]
  rw [show arg1 st = 0x9000 from rfl, show st.memory = mem from rfl,
    data_get i (by simpa [nine] using hi)]
  rfl

/-- **The entry conditions hold** for `crc32_z(0, "123456789", 9)`. -/
theorem crc32z_witness : FnContract.AbiEntry st.core st.memory ∧ (crc32zContract codeAt).entry st := by
  refine ⟨abi, rfl, loaded, tableAt, fun _ i hi => ?_⟩
  have : i < 9 := hi
  rw [show arg1 st = 0x9000 from rfl, show st.memory = mem from rfl,
    data_get i (by simpa [nine] using this)]
  exact ⟨by simp only [addressLimit]; omega, permits_all _ _ (by omega), rfl⟩

/-- **`crc32_z` runs**: the concrete call returns the check value `0xcbf43926` to `retAt`. -/
theorem crc32z_concrete : ∃ fin, Reaches Open.step st fin ∧
    fin.core.rip = retAt ∧ fin.core.read .rax = 0xcbf43926 ∧ fin.core.read .rsp = 0x9000 := by
  obtain ⟨fin, hrun, hres⟩ := crc32z_total codeAt st trivial crc32z_witness.1 crc32z_witness.2
  refine ⟨fin, hrun, by rw [hres.abi.pc]; exact retOf_st, ?_, hres.abi.stack⟩
  have hp := hres.post
  simp only [crc32zContract] at hp
  have h0 : ¬ arg1 st = 0 := by rw [show arg1 st = 0x9000 from rfl]; decide
  rw [hp, ite_eq_right h0, buf_st,
    show (st.core.read .rdi).setWidth 32 = 0#32 from rfl, show crc32 0#32 nine = 0xcbf43926#32 from crc32_check]
  rfl

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.NonVacuity
