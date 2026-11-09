module

public import Silmaril.X86.Ladder.ZlibChecksums.Defs
public import Silmaril.X86.Ladder.ZlibChecksums.Spec.Thms
public import Silmaril.X86.Open9.Thms
public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Main
import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Tu
import Silmaril.Proofs.X86.Ladder.ZlibChecksums.NonVacuity
public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Witness
public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.WitnessLong
public import Silmaril.X86.Ladder.ZlibChecksums.Rfc1950.Thms

/-!
# zlib 1.3.1 checksums (rung 03, `-O2`, `-DZ_SOLO`): the translation-unit contract

**Per function** (each for every load address `entry`):

* `crc32z_total`: `crc32_z` (byte-wise table CRC, 8× unrolled) meets `crc32zContract`:
  `rax = crc32 (rdi mod 2^32) (bytes)` zero-extended, `0` for a null buffer, nothing written.
  From the `Ext8` certificate `crc32zCert` (ten blocks; the body is eight instances of
  the table-fold stencil) and the reference facts of `Spec` (`fold_crcT`: the table fold is the
  bitwise CRC);
* `crc32_total`: the `uInt` wrapper `crc32` (`mov %edx,%edx; jmp crc32_z`) meets
  `crc32Contract`, through the tail-call lemma;
* `adler32z_total`: `adler32_z` meets `adler32zContract` on the open machine over `Ext9`
  (`Open9.isa`; `Open.decode` rejects its `imul r64, r/m64, imm32`, `adler32z_imul_undecoded`,
  and `Open9.decode` reads it, `adler32z_imul_decoded9`), for every length, from all six
  segment VCs (prologue, dispatch, short byte loop, byte tail, and the two `DO16` loops `0x80`
  and `0x2e3`) and the assembly (`Proofs/X86/Ladder/ZlibChecksums/Adler32z/`).
  `adler32z_loops` proves the two loop VCs, stated as `Task.adler32z_loops`;
  `adler32z_total_of` is the form conditional on it;
* `adler32_post_rfc`: under the contract's `AdlerOk`, the value `adler32_z` returns
  (`adler32 (rdi) (bytes)`) is RFC 1950's Adler-32 continued from `rdi` (`Rfc1950.rfcFrom`;
  `Rfc1950.adler32_one_eq_rfc1950` for the initial value `1`);
* `adler32z_total_short`: `adler32_z` meets `adler32zShortContract` (the same contract with
  `len < 16`) on `Open9`, without the loop VCs: such calls never reach the loop heads with their
  invariants. `adler32z_witness`/`adler32z_concrete`: the entry conditions hold for
  `adler32_z(1, "Wikipedia", 9)`, which returns `0x11e60398`; `adler32z_concrete_long`: the
  full contract's entry conditions hold for a 6000-byte call (through both `DO16` loops), which
  returns `0xc2bd67b2` by `adler32z_total`;
* `adler32_total`: the wrapper `adler32` meets `adler32Contract` on `Open9`.

**The translation unit** (`exports`, `exports_hold`): the proved exports as
(symbol, offset from `crc32_z`, contract family); `exportsAll_hold9`: all four on `Open9`.
Offsets are those of the linked rung binary (`crc32 = crc32_z + 0x130`,
`adler32 = adler32_z + 0x470`); `crc32_z` also fixes `crc_table`'s absolute address
(`crcTblAddr = 0x4021e0`), so these are contracts of the *linked* code, not of the
relocatable object.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.ZlibChecksums

open Silmaril.X86 (MState Word Byte)

theorem crc32z_total (entry : Word) : (crc32zContract entry).Total Open.isa :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.crc32z_total entry

theorem crc32_total (entry : Word) : (crc32Contract entry).Total Open.isa :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.crc32_total entry

/-- The segment VCs of `adler32_z`'s two `DO16` loops, path budgets 200: `0x80`, the `NMAX`
chunk loop, and `0x2e3`, the last-chunk loop, proved by `adler32z_loops`. -/
def Task.adler32z_loops : Prop :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.VcA 200 ∧
    Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.VcC 200

/-- **`Task.adler32z_loops` holds** (`vcA`, `vcC`). -/
theorem adler32z_loops : Task.adler32z_loops :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.loops_holds

/-- **`adler32_z` is totally correct on `Open9`**, given `Task.adler32z_loops`. -/
theorem adler32z_total_of (h : Task.adler32z_loops) (entry : Word) :
    (adler32zContract entry).Total Open9.isa :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.total_of_vcAC h.1 h.2 entry

/-- **`adler32` is totally correct on `Open9`**, given `Task.adler32z_loops`. -/
theorem adler32_total_of (h : Task.adler32z_loops) (entry : Word) :
    (adler32Contract entry).Total Open9.isa :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.adler32_total9_of (adler32z_total_of h) entry

/-- **`adler32_z` is totally correct on `Open9`**, for every input. -/
theorem adler32z_total (entry : Word) : (adler32zContract entry).Total Open9.isa :=
  adler32z_total_of adler32z_loops entry

/-- **`adler32` is totally correct on `Open9`**, for every input. -/
theorem adler32_total (entry : Word) : (adler32Contract entry).Total Open9.isa :=
  adler32_total_of adler32z_loops entry

/-- Under the contract's `AdlerOk`, the reference value in `adler32zContract`'s postcondition is
RFC 1950's Adler-32 continued from `rdi`. -/
theorem adler32_post_rfc {m : MState} {len : Nat} (h : AdlerOk m len) (bs : List Byte) :
    adler32 (m.core.read .rdi).toNat bs = Rfc1950.rfcFrom (m.core.read .rdi).toNat bs :=
  Rfc1950.adler32_eq_rfcFrom _ _ h.1 h.2.1

/-- `Open9.decode` reads `adler32_z`'s first `imul $0xfff1, %rdx, %rax` (offset `0x183`). -/
theorem adler32z_imul_decoded9 :
    Open9.decode ((adler32zCode.drop 0x183).take 7) =
      some (.new (.imulI .q .rax (.reg .rdx) 0xfff1#32), 7) := by
  decide +kernel

/-- **`adler32_z` is totally correct on `Open9` for `len < 16`** (no Task). -/
theorem adler32z_total_short (entry : Word) : (adler32zShortContract entry).Total Open9.isa :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Short.total_short entry

open Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Witness in
/-- The `adler32_z` contract is satisfiable: a concrete System V entry state for
`adler32_z(1, "Wikipedia", 9)` meets every conjunct (hence `adler32zContract`'s too). -/
theorem adler32z_witness :
    FnContract.AbiEntry st.core st.memory ∧ (adler32zShortContract codeAt).entry st :=
  witness

open Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Witness in
/-- **A concrete `Open9` run of `adler32_z`** (no Task): `adler32_z(1, "Wikipedia", 9)` returns
the published check value `0x11e60398` to its return address. -/
theorem adler32z_concrete : ∃ fin, Silmaril.Machine.Execution.Reaches Open9.step st fin ∧
    fin.core.rip = retAt ∧ fin.core.read .rax = 0x11e60398 ∧ fin.core.read .rsp = 0x9000 :=
  concrete

open Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.WitnessLong in
/-- **The long-input contract is not vacuous**: a concrete entry state for
`adler32_z(1, dat, 6000)` (`dat[i] = i mod 251`, `6000 ≥ NMAX`, so the call passes through both
`DO16` loops) meets `adler32zContract`'s entry condition, and `adler32z_total` turns it into an
`Open9` run returning `0xc2bd67b2` to its return address. -/
theorem adler32z_concrete_long : FnContract.AbiEntry st.core st.memory ∧
    (adler32zContract codeAt).entry st ∧ NMAX ≤ Silmaril.X86.Stencils.ByteLoop.arg2 st ∧
    ∃ fin, Silmaril.Machine.Execution.Reaches Open9.step st fin ∧
      fin.core.rip = retAt ∧ fin.core.read .rax = 0xc2bd67b2 ∧ fin.core.read .rsp = 0x9000 :=
  ⟨witness.1, witness.2.1, witness.2.2, concrete⟩

theorem adler32z_imul_undecoded : Open.decode ((adler32zCode.drop 0x183).take 7) = none :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.adler32z_imul_undecoded

/-- **`crc32_z`'s contract is not vacuous**: a concrete state (code at `0x400000`, the table at
`0x4021e0`, `"123456789"` at `0x9000`, a return address on an aligned stack) meets the System V
entry obligations and the contract's entry condition, and `crc32z_total` turns it into an
open-machine run returning the published check value `0xcbf43926`. -/
theorem crc32z_nonvacuous : ∃ s : MState, FnContract.AbiEntry s.core s.memory ∧
    (crc32zContract 0x400000).entry s ∧ ∃ fin, Silmaril.Machine.Execution.Reaches Open.step s fin ∧
      fin.core.read .rax = 0xcbf43926 := by
  open Silmaril.Proofs.X86.Ladder.ZlibChecksums.NonVacuity in
  obtain ⟨fin, hrun, -, hrax, -⟩ := crc32z_concrete
  exact ⟨st, crc32z_witness.1, crc32z_witness.2, fin, hrun, hrax⟩

/-- The `crc32_z` listing check, by `decide +kernel` (load-address independent). -/
theorem crc32z_checked (entry : Word) : (crc32zCert entry).checked = true :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.crc32z_checked entry

/-- **`crc32_z` as a total System V `FnContract`** on the open machine. -/
def crc32zFn (entry : Word) : FnContract Open.isa := ⟨crc32zContract entry, crc32z_total entry⟩

/-- **`crc32` as a total System V `FnContract`**. -/
def crc32Fn (entry : Word) : FnContract Open.isa := ⟨crc32Contract entry, crc32_total entry⟩

/-- A TU export: symbol, offset of its entry from the TU base (`crc32_z`), and its contract
at a given entry address. -/
structure Export where
  name : String
  off : Int
  spec : Word → FnContract.Spec MState

/-- An export holds: its contract is totally correct at every entry address. -/
def Export.Holds (e : Export) : Prop := ∀ entry : Word, (e.spec entry).Total Open.isa

/-- An export holds on the open machine over `Ext9`. -/
def Export.Holds9 (e : Export) : Prop := ∀ entry : Word, (e.spec entry).Total Open9.isa

theorem Export.Holds.toOpen9 {e : Export} (h : e.Holds) : e.Holds9 :=
  fun entry => (h entry).toOpen9

/-- **The proved exports** of the checksum TU. -/
def exports : List Export :=
  [⟨"crc32_z", 0, crc32zContract⟩, ⟨"crc32", 0x130, crc32Contract⟩]

/-- All four checksum exports (offsets from `crc32_z` in the rung binary). -/
def exportsAll : List Export :=
  exports ++ [⟨"adler32_z", -0x580, fun e => adler32zContract e⟩,
    ⟨"adler32", -0x110, adler32Contract⟩]

/-- **The TU contract**: every proved export holds. -/
theorem exports_hold : ∀ e ∈ exports, e.Holds := by
  simp only [exports, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl)
  exacts [crc32z_total, crc32_total]

/-- All four exports hold on `Open9`, given `Task.adler32z_loops`. -/
theorem exportsAll_hold9_of (h : Task.adler32z_loops) : ∀ e ∈ exportsAll, e.Holds9 := by
  simp only [exportsAll, exports, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl)
  exacts [Export.Holds.toOpen9 crc32z_total, Export.Holds.toOpen9 crc32_total,
    adler32z_total_of h, adler32_total_of h]

/-- **All four exports hold on `Open9`.** -/
theorem exportsAll_hold9 : ∀ e ∈ exportsAll, e.Holds9 := exportsAll_hold9_of adler32z_loops

end Silmaril.X86.Ladder.ZlibChecksums
