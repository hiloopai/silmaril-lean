module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Main

/-!
# `adler32_z`: a concrete run through both `DO16` loops

Like `Witness` (which has `len = 9` and so never reaches a `DO16` loop), but with a
6000-byte buffer `dat` (`dat[i] = i mod 251`) at `0x9000`. Since `6000 ≥ NMAX = 5552`, the
run goes through the `NMAX` chunk loop `0x80` (`VcA`) once and then, for the remaining 448
bytes, through the last-chunk loop `0x2e3` (`VcC`). The entry conditions of the full
`adler32zContract` hold (`witness`, with `len ≥ 16`), so the round-4 loop VCs are not
vacuously true on the inputs they are meant for; `total` (no Task) then gives a concrete
`Open9` run returning `0xc2bd67b2` (independently cross-checked against a Python
implementation of RFC 1950's definition).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.WitnessLong

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region addressLimit)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86 Silmaril.X86.Stencils.ByteLoop Silmaril.X86.Ladder.ZlibChecksums

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩
def codeAt : Word := 0x400000
def retAt : Word := 0x401000
def retEnc : List Byte := Silmaril.Machine.LittleEndian.encodeWords [retAt]

/-- The 6000 input bytes, `i mod 251`. -/
def dat : List Byte := (List.range 6000).map fun i => BitVec.ofNat 8 (i % 251)

theorem dat_len : dat.length = 6000 := by simp [dat]

def mem : Memory :=
  ⟨[allRegion], Memory.install (Memory.install (Memory.install ∅ 0x8ff8 retEnc)
    0x9000 dat) 0x400000 adler32zCode⟩

/-- The entry state: `adler32_z(1, dat, 6000)`. -/
def st : MState :=
  ⟨⟨fun r => match r with | .rdi => 1 | .rsi => 0x9000 | .rdx => 6000 | .rsp => 0x8ff8 | _ => 0,
    codeAt, ⟨none, none, none, none, none, none⟩, 0⟩, mem⟩

theorem permits_all (acc) (a : Nat) (ha : a < 2 ^ 64) : mem.permits acc a = true := by
  have : a < 18446744073709551616 := ha
  cases acc <;>
    simp [Memory.permits, mem, allRegion, Region.Contains, Silmaril.Process.Permissions.allows, this]

theorem permitted (acc) (a n : Nat) (h : a + n < 2 ^ 64) : mem.Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  exact ⟨by simp only [addressLimit]; omega, by simp only [addressLimit]; omega,
    fun i _ => permits_all acc _ (by omega)⟩

theorem code_len : adler32zCode.length = 1135 := by decide +kernel

theorem code_get (i : Nat) (hi : i < adler32zCode.length) :
    mem.bytes.get? (0x400000 + i) = some adler32zCode[i] :=
  Memory.install_get _ _ _ _ hi

theorem data_get (i : Nat) (hi : i < dat.length) :
    mem.bytes.get? (0x9000 + i) = some dat[i] := by
  have : i < 6000 := dat_len ▸ hi
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
  rw [Memory.install_outside _ _ _ _ (by rw [dat_len]; omega)]
  exact Memory.install_get _ _ _ _ (by simp [retEnc]; omega)

theorem loaded : Silmaril.X86.Ext.Loaded mem codeAt adler32zCode :=
  Memory.readWith_eq _ _ _ adler32zCode
    (permitted _ _ _ (by rw [show codeAt.toNat = 0x400000 from rfl, code_len]; omega)) code_get

theorem ret_read : mem.readBytes 0x8ff8 8 = some retEnc :=
  Memory.readWith_eq _ _ _ retEnc (permitted _ _ _ (by decide)) ret_get

theorem retOf_st : FnContract.retOf st.core st.memory = retAt := by
  simp only [FnContract.retOf]
  rw [show (st.core.read .rsp).toNat = 0x8ff8 from rfl, show st.memory = mem from rfl, ret_read]
  decide

theorem abi : FnContract.AbiEntry st.core st.memory :=
  ⟨show (0x8ff8 : Word).toNat % 16 = 8 by decide, by rw [retOf_st]; exact ret_read⟩

theorem buf_st : buf st = dat := by
  apply List.ext_getElem (by
    simp only [buf, Stencils.TableFold.bytesAt, List.length_map, List.length_range, dat_len]
    rfl)
  intro i h1 h2
  simp only [buf, Stencils.TableFold.bytesAt, List.getElem_map, List.getElem_range,
    Stencils.TableFold.byteAt]
  rw [show arg1 st = 0x9000 from rfl, show st.memory = mem from rfl, data_get i h2]
  rfl

/-- **The entry conditions of `adler32zContract` hold** for `adler32_z(1, dat, 6000)`, a call
with `len ≥ NMAX` (so it reaches both `DO16` loops). -/
theorem witness : FnContract.AbiEntry st.core st.memory ∧ (adler32zContract codeAt).entry st ∧
    NMAX ≤ arg2 st := by
  refine ⟨abi, ⟨rfl, loaded, by decide, fun i hi => ?_, fun i hi => ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_⟩,
    by decide⟩
  · have : i < 96 := hi
    exact ⟨by simp only [addressLimit]; decide +revert, permits_all _ _ (by decide +revert)⟩
  · exact permits_all _ _ (by have : i < 96 := hi; decide +revert)
  · right; right; left
    rw [show codeAt.toNat = 0x400000 from rfl]; decide
  · intro i hi
    have : i < 6000 := hi
    rw [show arg1 st = 0x9000 from rfl, show st.memory = mem from rfl,
      data_get i (by rw [dat_len]; exact this)]
    exact ⟨by simp only [addressLimit]; omega, permits_all _ _ (by omega), rfl⟩
  · right; right; left; decide
  · refine ⟨by decide, by decide, fun h => absurd h (by decide)⟩

theorem adler32_dat : adler32 1 dat = 0xc2bd67b2 := by decide +kernel

/-- **`adler32_z` runs through both loops** (no Task): `adler32_z(1, dat, 6000)` returns
`0xc2bd67b2` to `retAt`, with `rsp` popped. -/
theorem concrete : ∃ fin, Reaches Open9.step st fin ∧
    fin.core.rip = retAt ∧ fin.core.read .rax = 0xc2bd67b2 ∧ fin.core.read .rsp = 0x9000 := by
  obtain ⟨fin, hrun, hres⟩ := total codeAt st trivial witness.1 witness.2.1
  refine ⟨fin, hrun, by rw [hres.abi.pc]; exact retOf_st, ?_, hres.abi.stack⟩
  have hp := hres.post
  simp only [adler32zContract] at hp
  have h0 : ¬ arg1 st = 0 := by rw [show arg1 st = 0x9000 from rfl]; decide
  rw [hp, ite_eq_right h0, buf_st, show (st.core.read .rdi).toNat = 1 from rfl, adler32_dat]
  rfl

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.WitnessLong
