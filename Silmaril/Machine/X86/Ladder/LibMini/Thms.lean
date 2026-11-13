module

public import Silmaril.Machine.X86.Ladder.LibMini.Defs
public import Silmaril.Machine.X86.Stencils.ByteLoop.Thms
public import Silmaril.Machine.X86.Cert.Kinds.Thms
import Silmaril.Proofs.Machine.X86.Ladder.LibMini.Memcpy
import Silmaril.Proofs.Machine.X86.Ladder.LibMini.Memset
import Silmaril.Proofs.Machine.X86.Ladder.LibMini.Strlen
import Silmaril.Proofs.Machine.X86.Ladder.LibMini.Realizes
import Silmaril.Proofs.Machine.X86.Ladder.LibMini.NonVacuity
import Silmaril.Proofs.Machine.X86.Ladder.LibMini.Strict

/-!
# libmini (ladder rung 02) at `-O2`: the translation-unit contract

**Per function** (each for every load address `entry`; the code is position-independent):

* `memcpy_total`, `memset_total`, `strlen_total`: the state-level stencil contracts
  (`copyContract`, `fillContract`, `scanContract`) are totally correct on the open machine,
  from the function certificates `memcpyCert`, `memsetCert`, `strlenCert`;
* `memcpy_strict`, `memset_strict`, `strlen_strict`: the same contracts are **strictly**
  (first-return) totally correct on entries whose return address lies outside the code,
  from the same certificates through the generic `BlockCert.FunCert.strictW`;
  `memcpy_strict_nonvacuous`, `memset_strict_nonvacuous`, `strlen_strict_nonvacuous`: the
  concrete entry states meet the restricted entry and reach their **first** return;
* `memcpy_sat`, `memset_sat`, `strlen_sat`: **the System V separation-logic specs**
  `copySpec`, `fillSpec`, `scanSpec` hold of the code, by the stencil theorems
  `copy_sat`, `fill_sat`, `scan_sat`;
* `memcpyContract`, `memsetContract`, `strlenContract`: the same as WP3 `FnContract`s on the
  open machine (`FnSpec.Sat.toFnContract`);
* `memcpy_realizes`, `memset_realizes`, `strlen_realizes`: the state-level contracts as integer
  System V `Silmaril.Machine.SystemV.Realizes` certificates for the C signatures `sigCopy`,
  `sigFill`, `sigScan` (through `FnContract.toRealizes`; the domain is the contract's entry
  condition; `strlen`'s is indexed by the string length). The typed FFI variant
  (`toFfiRealizes`) is not instantiated.

**The translation unit** (`exports`, `exports_sat`): libmini's export list restricted to the
three certified functions, as (symbol, code, `FnSpec`) entries; every entry meets its spec
wherever its code is loaded. `memmove` and `memcmp` are not certified (see the package notes).

**Non-vacuity** (`memcpy_nonvacuous`, `memset_nonvacuous`, `strlen_nonvacuous`): concrete
states meet each contract's entry condition and the System V entry obligations with a nonzero
length, and the total-correctness theorems run them to the expected result (`memcpy` copies two
bytes, `memset` writes three, `strlen` returns `2`). These are state-level witnesses; no
separation-logic precondition witness is given for `copySpec`, `fillSpec` or `scanSpec`.

**Transcript ties**: `memcpyCode_eq`, `memsetCode_eq`, `strlenCode_eq`: each code list is the
slice of the transcribed region at the function's partition entry and size, and
`Transcript.transcript_verify`/`StrlenTranscript.transcript_verify` check by `decide +kernel`
that the model's decoder reads those bytes as the transcribed listings. The **binary tie**
(the transcribed regions are the bytes the committed executable
`examples/elf-ladder/02-mem-loops/pinned/mem-loops` loads at those addresses) is
`Silmaril.Machine.X86.Ladder.Pinned.memLoops_region` / `memLoops_strlen`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Ladder.LibMini

open Silmaril.X86 (MState Word Byte)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Stencils.ByteLoop

/-! ## Transcript ties (binary tie: `Ladder.Pinned.memLoops_region`) -/

theorem memcpyCode_eq : memcpyCode = (Transcript.region.bytes.drop
    (Transcript.fn_memcpy.entry - Transcript.region.base)).take Transcript.fn_memcpy.size := rfl

theorem memsetCode_eq : memsetCode = (Transcript.region.bytes.drop
    (Transcript.fn_memset.entry - Transcript.region.base)).take Transcript.fn_memset.size := rfl

theorem strlenCode_eq : strlenCode = (StrlenTranscript.region.bytes.drop
    (StrlenTranscript.fn_strlen.entry - StrlenTranscript.region.base)).take
      StrlenTranscript.fn_strlen.size := by
  decide +kernel

/-! ## Rejection tests of the writing-block check

`listingAtW` would make the certificates vacuous if it accepted anything; by `decide +kernel`
it rejects the unsplit `memcpy` loop body (its store is not the last instruction) and a store
listed with the wrong base register. -/

theorem rejects_store_not_last :
    BlockCert.listingAtW memcpyCode 0x10 Bir.memcpy.L_401310 = false := by decide +kernel

theorem rejects_wrong_store :
    BlockCert.listingAtW memcpyCode 0x10
      [(.ext (.movx false .d .b .r8 (.mem (Silmaril.X86.Ext.Mem.ofReg .rsi
        (some (Silmaril.X86.Lift.Bir.ix .rcx 0)) 0x0))), 5),
       (.ext (.store .b (.mem (Silmaril.X86.Ext.Mem.ofReg .rdx
        (some (Silmaril.X86.Lift.Bir.ix .rcx 0)) 0x0)) .r8), 4)] = false := by decide +kernel

/-! ## State-level contracts -/

theorem memcpy_total (entry : Word) :
    (copyContract memcpyCode entry).Total Silmaril.Machine.X86.Open.isa :=
  Silmaril.Proofs.Machine.X86.Ladder.LibMini.memcpy_total entry

theorem memset_total (entry : Word) :
    (fillContract memsetCode entry).Total Silmaril.Machine.X86.Open.isa :=
  Silmaril.Proofs.Machine.X86.Ladder.LibMini.memset_total entry

theorem strlen_total (entry : Word) :
    (scanContract strlenCode entry).Total Silmaril.Machine.X86.Open.isa :=
  Silmaril.Proofs.Machine.X86.Ladder.LibMini.strlen_total entry

/-! ## First-return contracts (through the generic certificate) -/

/-- `memcpy`'s contract read at the **first** return (`Spec.Strict`). -/
theorem memcpy_strict (entry : Word) :
    ((copyContract memcpyCode entry).restrict
      (FnContract.RetOutside Silmaril.Machine.X86.Open.isa entry memcpyCode.length)).Strict
        Silmaril.Machine.X86.Open.isa :=
  Silmaril.Proofs.Machine.X86.Ladder.LibMini.memcpy_strict entry

/-- `memset`'s contract read at the **first** return (`Spec.Strict`). -/
theorem memset_strict (entry : Word) :
    ((fillContract memsetCode entry).restrict
      (FnContract.RetOutside Silmaril.Machine.X86.Open.isa entry memsetCode.length)).Strict
        Silmaril.Machine.X86.Open.isa :=
  Silmaril.Proofs.Machine.X86.Ladder.LibMini.memset_strict entry

/-- `strlen`'s contract read at the **first** return (`Spec.Strict`). -/
theorem strlen_strict (entry : Word) :
    ((scanContract strlenCode entry).restrict
      (FnContract.RetOutside Silmaril.Machine.X86.Open.isa entry strlenCode.length)).Strict
        Silmaril.Machine.X86.Open.isa :=
  Silmaril.Proofs.Machine.X86.Ladder.LibMini.strlen_strict entry

/-! ## System V separation-logic specs -/

/-- **`memcpy` meets `copySpec`** wherever it is loaded. -/
theorem memcpy_sat (entry : Word) : copySpec.Sat (codePt entry.toNat memcpyCode) entry :=
  copy_sat (by decide) (memcpy_total entry)

/-- **`memset` meets `fillSpec`** wherever it is loaded. -/
theorem memset_sat (entry : Word) : fillSpec.Sat (codePt entry.toNat memsetCode) entry :=
  fill_sat (by decide) (memset_total entry)

/-- **`strlen` meets `scanSpec`** wherever it is loaded. -/
theorem strlen_sat (entry : Word) : scanSpec.Sat (codePt entry.toNat strlenCode) entry :=
  scan_sat (by decide) (strlen_total entry)

/-- `memcpy` as a total WP3 function contract on the open machine. -/
def memcpyContract (entry : Word) : Silmaril.Machine.X86.FnContract Silmaril.Machine.X86.Open.isa :=
  (memcpy_sat entry).toFnContract

/-- `memset` as a total WP3 function contract on the open machine. -/
def memsetContract (entry : Word) : Silmaril.Machine.X86.FnContract Silmaril.Machine.X86.Open.isa :=
  (memset_sat entry).toFnContract

/-- `strlen` as a total WP3 function contract on the open machine. -/
def strlenContract (entry : Word) : Silmaril.Machine.X86.FnContract Silmaril.Machine.X86.Open.isa :=
  (strlen_sat entry).toFnContract

/-! ## Integer System V certificates -/

theorem memcpy_realizes (entry : Word) :
    Silmaril.Machine.SystemV.Realizes sigCopy firstResult blockWrites
      (fun _ call => (copyContract memcpyCode entry).entry call.initial)
      (fun call final => Silmaril.Machine.Execution.Reaches Silmaril.Machine.X86.Open.step
        call.initial final) :=
  Silmaril.Proofs.Machine.X86.Ladder.LibMini.memcpy_realizes entry

theorem memset_realizes (entry : Word) :
    Silmaril.Machine.SystemV.Realizes sigFill firstResult blockWrites
      (fun _ call => (fillContract memsetCode entry).entry call.initial)
      (fun call final => Silmaril.Machine.Execution.Reaches Silmaril.Machine.X86.Open.step
        call.initial final) :=
  Silmaril.Proofs.Machine.X86.Ladder.LibMini.memset_realizes entry

theorem strlen_realizes (entry : Word) (k : Nat) :
    Silmaril.Machine.SystemV.Realizes sigScan (fun _ => BitVec.ofNat 64 k) (fun _ _ => False)
      (fun _ call => (scanContract strlenCode entry).entry call.initial ∧
        CStr call.initial.memory (arg0 call.initial) k)
      (fun call final => Silmaril.Machine.Execution.Reaches Silmaril.Machine.X86.Open.step
        call.initial final) :=
  Silmaril.Proofs.Machine.X86.Ladder.LibMini.strlen_realizes entry k

/-! ## Non-vacuity

Concrete entry states (code at `0x400000`, return address `0x401000` at `rsp = 0x8ff8`, data at
`0x9000`), from `Proofs/.../LibMini/NonVacuity.lean`. -/

/-- A concrete `memcpy(0xa000, 0x9000, 2)` call meets the contract's entry condition and runs to
`ret` with the two bytes copied. -/
theorem memcpy_nonvacuous : ∃ m : MState, FnContract.AbiEntry m.core m.memory ∧
    (copyContract memcpyCode 0x400000).entry m ∧ arg2 m = 2 ∧
    ∃ fin, Silmaril.Machine.Execution.Reaches Silmaril.Machine.X86.Open.step m fin ∧
      fin.core.rip = 0x401000 ∧ fin.core.read .rax = 0xa000 ∧
      fin.memory.bytes.get? 0xa000 = some 0x68 ∧ fin.memory.bytes.get? 0xa001 = some 0x69 := by
  open Silmaril.Proofs.Machine.X86.Ladder.LibMini.NonVacuity in
  obtain ⟨fin, h, hrip, hrax, -, h0, h1⟩ := memcpy_concrete
  exact ⟨_, memcpy_witness.1, memcpy_witness.2, rfl, fin, h, hrip, hrax, h0, h1⟩

/-- A concrete `memset(0xa000, 0x12345641, 3)` call meets the contract's entry condition and
runs to `ret` with three bytes `0x41` written. -/
theorem memset_nonvacuous : ∃ m : MState, FnContract.AbiEntry m.core m.memory ∧
    (fillContract memsetCode 0x400000).entry m ∧ arg2 m = 3 ∧
    ∃ fin, Silmaril.Machine.Execution.Reaches Silmaril.Machine.X86.Open.step m fin ∧
      fin.core.rip = 0x401000 ∧ fin.core.read .rax = 0xa000 ∧
      ∀ i < 3, fin.memory.bytes.get? (0xa000 + i) = some 0x41 := by
  open Silmaril.Proofs.Machine.X86.Ladder.LibMini.NonVacuity in
  obtain ⟨fin, h, hrip, hrax, -, hb⟩ := memset_concrete
  exact ⟨_, memset_witness.1, memset_witness.2, rfl, fin, h, hrip, hrax, hb⟩

/-- A concrete `strlen` call on `68 69 00` meets the contract's entry condition and runs to
`ret` with `rax = 2`. -/
theorem strlen_nonvacuous : ∃ m : MState, FnContract.AbiEntry m.core m.memory ∧
    (scanContract strlenCode 0x400000).entry m ∧ CStr m.memory (arg0 m) 2 ∧
    ∃ fin, Silmaril.Machine.Execution.Reaches Silmaril.Machine.X86.Open.step m fin ∧
      fin.core.rip = 0x401000 ∧ fin.core.read .rax = 2 := by
  open Silmaril.Proofs.Machine.X86.Ladder.LibMini.NonVacuity in
  obtain ⟨fin, h, hrip, hrax, -⟩ := strlen_concrete
  exact ⟨_, strlen_witness.1, ⟨rfl, loaded (by decide), 2, strlen_witness.2⟩, strlen_witness.2,
    fin, h, hrip, hrax⟩

/-- **First-return non-vacuity**: the concrete `memcpy` entry satisfies the strict spec's
restricted entry (`RetOutside`), and its result is the *first* return of the open-machine run. -/
theorem memcpy_strict_nonvacuous : ∃ m : MState, FnContract.AbiEntry m.core m.memory ∧
    ((copyContract memcpyCode 0x400000).restrict
      (FnContract.RetOutside Silmaril.Machine.X86.Open.isa 0x400000 memcpyCode.length)).entry m ∧
    ∃ fin, FnContract.FirstReturn Silmaril.Machine.X86.Open.isa m fin ∧
      fin.core.rip = 0x401000 ∧ fin.core.read .rax = 0xa000 ∧
      fin.memory.bytes.get? 0xa000 = some 0x68 ∧ fin.memory.bytes.get? 0xa001 = some 0x69 := by
  open Silmaril.Proofs.Machine.X86.Ladder.LibMini.NonVacuity in
  obtain ⟨fin, h, hrip, hrax, -, h0, h1⟩ := memcpy_strict_concrete
  exact ⟨_, memcpy_witness.1, ⟨memcpy_witness.2, retOutside_st (by decide)⟩, fin, h, hrip, hrax,
    h0, h1⟩

/-- **First-return non-vacuity** for `memset` (as `memcpy_strict_nonvacuous`). -/
theorem memset_strict_nonvacuous : ∃ m : MState, FnContract.AbiEntry m.core m.memory ∧
    ((fillContract memsetCode 0x400000).restrict
      (FnContract.RetOutside Silmaril.Machine.X86.Open.isa 0x400000 memsetCode.length)).entry m ∧
    ∃ fin, FnContract.FirstReturn Silmaril.Machine.X86.Open.isa m fin ∧
      fin.core.rip = 0x401000 ∧ fin.core.read .rax = 0xa000 ∧
      ∀ i < 3, fin.memory.bytes.get? (0xa000 + i) = some 0x41 := by
  open Silmaril.Proofs.Machine.X86.Ladder.LibMini.NonVacuity in
  obtain ⟨fin, h, hrip, hrax, -, hb⟩ := memset_strict_concrete
  exact ⟨_, memset_witness.1, ⟨memset_witness.2, retOutside_st (by decide)⟩, fin, h, hrip, hrax,
    hb⟩

/-- **First-return non-vacuity** for `strlen` (as `memcpy_strict_nonvacuous`). -/
theorem strlen_strict_nonvacuous : ∃ m : MState, FnContract.AbiEntry m.core m.memory ∧
    ((scanContract strlenCode 0x400000).restrict
      (FnContract.RetOutside Silmaril.Machine.X86.Open.isa 0x400000 strlenCode.length)).entry m ∧
    ∃ fin, FnContract.FirstReturn Silmaril.Machine.X86.Open.isa m fin ∧
      fin.core.rip = 0x401000 ∧ fin.core.read .rax = 2 := by
  open Silmaril.Proofs.Machine.X86.Ladder.LibMini.NonVacuity in
  obtain ⟨fin, h, hrip, hrax, -⟩ := strlen_strict_concrete
  exact ⟨_, strlen_witness.1, ⟨⟨rfl, loaded (by decide), 2, strlen_witness.2⟩,
    retOutside_st (by decide)⟩, fin, h, hrip, hrax⟩

/-! ## The translation unit -/

/-- An exported function of a translation unit: its symbol, its (position-independent)
code and its System V spec. -/
structure Export where
  name : String
  code : List Byte
  spec : FnSpec

/-- An export meets its spec wherever its code is loaded. -/
def Export.Holds (e : Export) : Prop :=
  ∀ entry : Word, e.spec.Sat (codePt entry.toNat e.code) entry

/-- **libmini's certified exports** (`memmove` and `memcmp` are not yet certified). -/
def exports : List Export :=
  [⟨"memcpy", memcpyCode, copySpec⟩, ⟨"memset", memsetCode, fillSpec⟩,
    ⟨"strlen", strlenCode, scanSpec⟩]

/-- **The libmini TU contract**: every certified export meets its spec. -/
theorem exports_sat : ∀ e ∈ exports, e.Holds := by
  simp only [exports, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl)
  exacts [memcpy_sat, memset_sat, strlen_sat]

/-- The exports at their addresses in the transcribed `mem-loops` binary. -/
theorem exports_in_binary :
    copySpec.Sat (codePt memcpyAddr.toNat memcpyCode) memcpyAddr ∧
      fillSpec.Sat (codePt memsetAddr.toNat memsetCode) memsetAddr ∧
      scanSpec.Sat (codePt strlenAddr.toNat strlenCode) strlenAddr :=
  ⟨memcpy_sat _, memset_sat _, strlen_sat _⟩

end Silmaril.Machine.X86.Ladder.LibMini
