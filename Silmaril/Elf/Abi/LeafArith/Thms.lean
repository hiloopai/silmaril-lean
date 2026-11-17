module

public import Silmaril.Elf.Abi.LeafArith.Defs
public import Silmaril.Elf.Abi.Thms
public import Silmaril.Machine.Abi.Conformance.LeafArith.Thms
import Silmaril.Proofs.Elf.Abi.LeafArith

/-! # ABI conformance rows of `leaf-arith`: proved and open

PROVED (standard axioms), proofs in `Silmaril.Proofs.Elf.Abi.LeafArith`. Every row is on the open
machine model `Open`, not real x86 (`Conforms.onRef` reads a row on a reference machine under
`Faithful`):

* `clamp_row`, `sat_row`: **the rows `silmaril.elf.abi.leaf_arith.clamp_i32` and
  `….sat_add_u32`** (total, frame 0, no precondition). The `.symtab` entries are `STT_FUNC`
  symbols named `clamp_i32` and `sat_add_u32` at `0x4013a0` (19 bytes) and `0x401400`
  (29 bytes). The file maps the 181 code bytes at `0x401370` read-only executable, and the
  code's image is the file's four `PT_LOAD` ranges. No dynamic relocation touches the code.
  The file is `ET_EXEC`, so its only load base is `0`. The code conforms
  (`Machine.Abi.Conformance.LeafArith.clamp_conforms`, `sat_conforms`);
* `header_row`: **the row `silmaril.elf.abi.leaf_arith.arith_h`** (partial header
  satisfaction):
  - the coverage of `arith.h` is checked against the header;
  - the nine `absent` declarations (`rt_write`, `memcpy`, …) have no defined symbol in any table
    of the file;
  - every `unclaimed` declaration is a function present in the file;
  - the two claimed functions are the rows above;
* `not_codeOf_offset`: **negative**: code entered one byte into `clamp_i32` is not the file's
  `clamp_i32` (the symbol's `st_value` is the entry);
* `not_codeOf_symbol`: **negative**: `clamp_i32`'s code is not the file's `sat_add_u32`;
* `not_codeOf_bytes`: **negative**: the code with one byte changed is no function of the file;
* `not_available`: **negative**: the `arith.h` row is partial: it is not available (nor
  complete) header satisfaction.

OPEN: `silmaril.elf.abi.leaf_arith.gcd_u32` and `….bswap32_manual`, from
`Task.gcd_conforms` and `Task.bswap_conforms` (`gcd_row_of`, `bswap_row_of`: the file facts are
proved).
-/

@[expose] public section

namespace Silmaril.Elf.Abi.LeafArith

open Silmaril.Machine.Abi.Conformance.LeafArith (Task.gcd_conforms Task.bswap_conforms)

/-- **`clamp_i32` of the pinned `leaf-arith` conforms to the System V AMD64 psABI INTEGER fragment on `Open`.** -/
@[solves "silmaril.elf.abi.leaf_arith.clamp_i32"]
theorem clamp_row : silmaril.elf.abi.leaf_arith.clamp_i32 :=
  Silmaril.Proofs.Elf.Abi.LeafArith.clamp_row

/-- **`sat_add_u32` of the pinned `leaf-arith` conforms to the System V AMD64 psABI INTEGER fragment on `Open`.** -/
@[solves "silmaril.elf.abi.leaf_arith.sat_add_u32"]
theorem sat_row : silmaril.elf.abi.leaf_arith.sat_add_u32 :=
  Silmaril.Proofs.Elf.Abi.LeafArith.sat_row

/-- **`leaf-arith` satisfies the claimed part of `arith.h`** (partial: not header satisfaction). -/
@[solves "silmaril.elf.abi.leaf_arith.arith_h"]
theorem header_row : silmaril.elf.abi.leaf_arith.arith_h :=
  Silmaril.Proofs.Elf.Abi.LeafArith.header_row

theorem gcd_row_of (h : Task.gcd_conforms) : silmaril.elf.abi.leaf_arith.gcd_u32 :=
  Silmaril.Proofs.Elf.Abi.LeafArith.gcd_row_of h

theorem bswap_row_of (h : Task.bswap_conforms) : silmaril.elf.abi.leaf_arith.bswap32_manual :=
  Silmaril.Proofs.Elf.Abi.LeafArith.bswap_row_of h

/-- **Negative**: code entered one byte into `clamp_i32` is not the file's `clamp_i32`. -/
theorem not_codeOf_offset {n : Nat} :
    ¬ Silmaril.Elf.Abi.CodeOf Silmaril.Elf.Staged.Pinned.LeafArith.F .symtab "clamp_i32"
      (Silmaril.Machine.Abi.Conformance.LeafArith.region 0x31 n) :=
  Silmaril.Proofs.Elf.Abi.LeafArith.not_codeOf_offset

/-- **Negative**: `clamp_i32`'s code is not the file's `sat_add_u32` (wrong symbol). -/
theorem not_codeOf_symbol :
    ¬ Silmaril.Elf.Abi.CodeOf Silmaril.Elf.Staged.Pinned.LeafArith.F .symtab "sat_add_u32"
      Silmaril.Machine.Abi.Conformance.LeafArith.clampCode :=
  Silmaril.Proofs.Elf.Abi.LeafArith.not_codeOf_symbol

/-- **Negative**: `clamp_i32`'s code with its entry byte changed is no function of the file
(wrong code bytes). -/
theorem not_codeOf_bytes {b : Silmaril.Elf.Abi.Binding} {f : String} :
    ¬ Silmaril.Elf.Abi.CodeOf Silmaril.Elf.Staged.Pinned.LeafArith.F b f
      Silmaril.Elf.Abi.LeafArith.patched :=
  Silmaril.Proofs.Elf.Abi.LeafArith.not_codeOf_bytes

/-- **Negative**: the partial `arith.h` row is not available (hence not complete) header
satisfaction: functions of the file are left unclaimed. -/
theorem not_available {A : Silmaril.Machine.Abi.Conformance.AbiDef}
    {M : Silmaril.Machine.Abi.Conformance.Mach} {bind : String → Silmaril.Elf.Abi.Binding}
    {impl : String → Option (Silmaril.Machine.Abi.Conformance.Impl A)} :
    ¬ Silmaril.Elf.Abi.AbiHeaderSatAvailable A M Silmaril.Machine.Abi.Conformance.LeafArith.hdr
      Silmaril.Machine.Abi.Conformance.LeafArith.coverage
      Silmaril.Elf.Staged.Pinned.LeafArith.F bind impl :=
  Silmaril.Proofs.Elf.Abi.LeafArith.not_available

end Silmaril.Elf.Abi.LeafArith

end

silmaril group silmaril.abi
  (title := "ABI conformance: the shapes and the leaf-arith rows")
  (children := [silmaril.shapes.abi.conforms, silmaril.shapes.abi.conforms.sysv_int_open,
    silmaril.shapes.abi.conforms.sysv_int_open9, silmaril.shapes.abi.conforms.win64_int_open,
    silmaril.shapes.abi.conforms.sysv_scalar_open9, silmaril.shapes.abi.header_sat_partial,
    silmaril.shapes.abi.header_sat_available, silmaril.shapes.abi.header_sat_complete,
    silmaril.shapes.elf.abi_conforms,
    silmaril.shapes.elf.abi_conforms.sysv_int_open, silmaril.shapes.elf.abi_conforms.sysv_int_open9,
    silmaril.shapes.elf.abi_header_sat_partial, silmaril.shapes.elf.abi_header_sat_partial.sysv_int_open,
    silmaril.shapes.elf.abi_header_sat_available,
    silmaril.shapes.elf.abi_header_sat_available.sysv_int_open, silmaril.shapes.elf.abi_header_sat_complete,
    silmaril.shapes.elf.abi_header_sat_complete.sysv_int_open,
    silmaril.elf.abi.leaf_arith.clamp_i32, silmaril.elf.abi.leaf_arith.sat_add_u32,
    silmaril.elf.abi.leaf_arith.gcd_u32, silmaril.elf.abi.leaf_arith.bswap32_manual,
    silmaril.elf.abi.leaf_arith.arith_h])
